import V185TrunkScan22Chunk425

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3798513 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 3, 4]
def baseStart_3798513 : Nat := 118140960795 + 3798513 * 2 ^ 59
def prefixEnd_3798513 : Nat := 4983230072969 + 3 ^ 40 * 3798513 * 2
def baseEnd_3798513 : Nat := 1300308627568001356078975

theorem tailTrace_3798513 : CollatzResearch.WordTrace tailWord_3798513 prefixEnd_3798513 1300308627568001356078975 := by
  unfold tailWord_3798513
  simp only [CollatzResearch.WordTrace]
  refine ⟨138543150887643610217128193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92362100591762406811418795 138543150887643610217128193)
  ·
    refine ⟨103907363165732707662846145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138543150887643610217128193 103907363165732707662846145)
    ·
      refine ⟨77930522374299530747134609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103907363165732707662846145 77930522374299530747134609)
      ·
        refine ⟨58447891780724648060350957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77930522374299530747134609 58447891780724648060350957)
        ·
          refine ⟨21917959417771743022631609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58447891780724648060350957 21917959417771743022631609)
          ·
            refine ⟨16438469563328807266973707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21917959417771743022631609 16438469563328807266973707)
            ·
              refine ⟨24657704344993210900460561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16438469563328807266973707 24657704344993210900460561)
              ·
                refine ⟨18493278258744908175345421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24657704344993210900460561 18493278258744908175345421)
                ·
                  refine ⟨6934979347029340565754533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18493278258744908175345421 6934979347029340565754533)
                  ·
                    refine ⟨1300308627568001356078975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6934979347029340565754533 1300308627568001356078975)
                    ·
                      rfl

theorem cell22_3798513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_3798513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798513 prefixEnd_3798513 := by exact prefixLift 3798513
  have htrace : WordTrace (prefixWord ++ tailWord_3798513) baseStart_3798513 baseEnd_3798513 := by
    simpa [prefixWord, tailWord_3798513, baseEnd_3798513] using wordTrace_append hprefix tailTrace_3798513
  have hstable : (prefixWord ++ tailWord_3798513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798513).length < 2 ^ (prefixWord ++ tailWord_3798513).sum := by decide
  have hdescent : baseEnd_3798513 < baseStart_3798513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798545 : List Nat := [1, 2, 2, 1, 1, 2, 6, 3, 4]
def baseStart_3798545 : Nat := 118140960795 + 3798545 * 2 ^ 59
def prefixEnd_3798545 : Nat := 4983230072969 + 3 ^ 40 * 3798545 * 2
def baseEnd_3798545 : Nat := 433439860607321313092959

theorem tailTrace_3798545 : CollatzResearch.WordTrace tailWord_3798545 prefixEnd_3798545 433439860607321313092959 := by
  unfold tailWord_3798545
  simp only [CollatzResearch.WordTrace]
  refine ⟨138544318023527679682293089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92362878682351786454862059 138544318023527679682293089)
  ·
    refine ⟨103908238517645759761719817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138544318023527679682293089 103908238517645759761719817)
    ·
      refine ⟨77931178888234319821289863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103908238517645759761719817 77931178888234319821289863)
      ·
        refine ⟨116896768332351479731934795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77931178888234319821289863 116896768332351479731934795)
        ·
          refine ⟨175345152498527219597902193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116896768332351479731934795 175345152498527219597902193)
          ·
            refine ⟨131508864373895414698426645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175345152498527219597902193 131508864373895414698426645)
            ·
              refine ⟨6164478017526347563988749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 131508864373895414698426645 6164478017526347563988749)
              ·
                refine ⟨2311679256572380336495781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6164478017526347563988749 2311679256572380336495781)
                ·
                  refine ⟨433439860607321313092959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2311679256572380336495781 433439860607321313092959)
                  ·
                    rfl

theorem cell22_3798545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 4].length) (baseStart_3798545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798545 prefixEnd_3798545 := by exact prefixLift 3798545
  have htrace : WordTrace (prefixWord ++ tailWord_3798545) baseStart_3798545 baseEnd_3798545 := by
    simpa [prefixWord, tailWord_3798545, baseEnd_3798545] using wordTrace_append hprefix tailTrace_3798545
  have hstable : (prefixWord ++ tailWord_3798545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798545).length < 2 ^ (prefixWord ++ tailWord_3798545).sum := by decide
  have hdescent : baseEnd_3798545 < baseStart_3798545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798547 : List Nat := [1, 1, 1, 2, 1, 8, 2, 1, 1, 4]
def baseStart_3798547 : Nat := 118140960795 + 3798547 * 2 ^ 59
def prefixEnd_3798547 : Nat := 4983230072969 + 3 ^ 40 * 3798547 * 2
def baseEnd_3798547 : Nat := 1300320266462836600728871

theorem tailTrace_3798547 : CollatzResearch.WordTrace tailWord_3798547 prefixEnd_3798547 1300320266462836600728871 := by
  unfold tailWord_3798547
  simp only [CollatzResearch.WordTrace]
  refine ⟨138544390969520434023865895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92362927313013622682577263 138544390969520434023865895)
  ·
    refine ⟨207816586454280651035798843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138544390969520434023865895 207816586454280651035798843)
    ·
      refine ⟨311724879681420976553698265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207816586454280651035798843 311724879681420976553698265)
      ·
        refine ⟨233793659761065732415273699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311724879681420976553698265 233793659761065732415273699)
        ·
          refine ⟨350690489641598598622910549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233793659761065732415273699 350690489641598598622910549)
          ·
            refine ⟨4109654175487483577612233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 350690489641598598622910549 4109654175487483577612233)
            ·
              refine ⟨3082240631615612683209175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4109654175487483577612233 3082240631615612683209175)
              ·
                refine ⟨4623360947423419024813763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3082240631615612683209175 4623360947423419024813763)
                ·
                  refine ⟨6935041421135128537220645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4623360947423419024813763 6935041421135128537220645)
                  ·
                    refine ⟨1300320266462836600728871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6935041421135128537220645 1300320266462836600728871)
                    ·
                      rfl

theorem cell22_3798547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 1, 4].length) (baseStart_3798547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798547 prefixEnd_3798547 := by exact prefixLift 3798547
  have htrace : WordTrace (prefixWord ++ tailWord_3798547) baseStart_3798547 baseEnd_3798547 := by
    simpa [prefixWord, tailWord_3798547, baseEnd_3798547] using wordTrace_append hprefix tailTrace_3798547
  have hstable : (prefixWord ++ tailWord_3798547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798547).length < 2 ^ (prefixWord ++ tailWord_3798547).sum := by decide
  have hdescent : baseEnd_3798547 < baseStart_3798547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798633 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 2, 5]
def baseStart_3798633 : Nat := 118140960795 + 3798633 * 2 ^ 59
def prefixEnd_3798633 : Nat := 4983230072969 + 3 ^ 40 * 3798633 * 2
def baseEnd_3798633 : Nat := 1300349706020361043078607

theorem tailTrace_3798633 : CollatzResearch.WordTrace tailWord_3798633 prefixEnd_3798633 1300349706020361043078607 := by
  unfold tailWord_3798633
  simp only [CollatzResearch.WordTrace]
  refine ⟨138547527647208870711496553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92365018431472580474331035 138547527647208870711496553)
  ·
    refine ⟨103910645735406653033622415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138547527647208870711496553 103910645735406653033622415)
    ·
      refine ⟨155865968603109979550433623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103910645735406653033622415 155865968603109979550433623)
      ·
        refine ⟨233798952904664969325650435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155865968603109979550433623 233798952904664969325650435)
        ·
          refine ⟨350698429356997453988475653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233798952904664969325650435 350698429356997453988475653)
          ·
            refine ⟨65755955504437022622839185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 350698429356997453988475653 65755955504437022622839185)
            ·
              refine ⟨49316966628327766967129389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65755955504437022622839185 49316966628327766967129389)
              ·
                refine ⟨18493862485622912612673521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49316966628327766967129389 18493862485622912612673521)
                ·
                  refine ⟨13870396864217184459505141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18493862485622912612673521 13870396864217184459505141)
                  ·
                    refine ⟨1300349706020361043078607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13870396864217184459505141 1300349706020361043078607)
                    ·
                      rfl

theorem cell22_3798633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_3798633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798633 prefixEnd_3798633 := by exact prefixLift 3798633
  have htrace : WordTrace (prefixWord ++ tailWord_3798633) baseStart_3798633 baseEnd_3798633 := by
    simpa [prefixWord, tailWord_3798633, baseEnd_3798633] using wordTrace_append hprefix tailTrace_3798633
  have hstable : (prefixWord ++ tailWord_3798633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798633).length < 2 ^ (prefixWord ++ tailWord_3798633).sum := by decide
  have hdescent : baseEnd_3798633 < baseStart_3798633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798665 : List Nat := [1, 2, 1, 1, 4, 1, 2, 5, 1, 4]
def baseStart_3798665 : Nat := 118140960795 + 3798665 * 2 ^ 59
def prefixEnd_3798665 : Nat := 4983230072969 + 3 ^ 40 * 3798665 * 2
def baseEnd_3798665 : Nat := 1300360660274323626278509

theorem tailTrace_3798665 : CollatzResearch.WordTrace tailWord_3798665 prefixEnd_3798665 1300360660274323626278509 := by
  unfold tailWord_3798665
  simp only [CollatzResearch.WordTrace]
  refine ⟨138548694783092940176661449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92365796522061960117774299 138548694783092940176661449)
  ·
    refine ⟨103911521087319705132496087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138548694783092940176661449 103911521087319705132496087)
    ·
      refine ⟨155867281630979557698744131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103911521087319705132496087 155867281630979557698744131)
      ·
        refine ⟨233800922446469336548116197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155867281630979557698744131 233800922446469336548116197)
        ·
          refine ⟨43837672958713000602771787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233800922446469336548116197 43837672958713000602771787)
          ·
            refine ⟨65756509438069500904157681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43837672958713000602771787 65756509438069500904157681)
            ·
              refine ⟨49317382078552125678118261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65756509438069500904157681 49317382078552125678118261)
              ·
                refine ⟨4623504569864261782323587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49317382078552125678118261 4623504569864261782323587)
                ·
                  refine ⟨6935256854796392673485381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4623504569864261782323587 6935256854796392673485381)
                  ·
                    refine ⟨1300360660274323626278509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6935256854796392673485381 1300360660274323626278509)
                    ·
                      rfl

theorem cell22_3798665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 4].length) (baseStart_3798665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798665 prefixEnd_3798665 := by exact prefixLift 3798665
  have htrace : WordTrace (prefixWord ++ tailWord_3798665) baseStart_3798665 baseEnd_3798665 := by
    simpa [prefixWord, tailWord_3798665, baseEnd_3798665] using wordTrace_append hprefix tailTrace_3798665
  have hstable : (prefixWord ++ tailWord_3798665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798665).length < 2 ^ (prefixWord ++ tailWord_3798665).sum := by decide
  have hdescent : baseEnd_3798665 < baseStart_3798665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798723 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 3, 9]
def baseStart_3798723 : Nat := 118140960795 + 3798723 * 2 ^ 59
def prefixEnd_3798723 : Nat := 4983230072969 + 3 ^ 40 * 3798723 * 2
def baseEnd_3798723 : Nat := 1300380514859630808328331

theorem tailTrace_3798723 : CollatzResearch.WordTrace tailWord_3798723 prefixEnd_3798723 1300380514859630808328331 := by
  unfold tailWord_3798723
  simp only [CollatzResearch.WordTrace]
  refine ⟨138550810216882816082272823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92367206811255210721515215 138550810216882816082272823)
  ·
    refine ⟨207826215325324224123409235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138550810216882816082272823 207826215325324224123409235)
    ·
      refine ⟨311739322987986336185113853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207826215325324224123409235 311739322987986336185113853)
      ·
        refine ⟨116902246120494876069417695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311739322987986336185113853 116902246120494876069417695)
        ·
          refine ⟨175353369180742314104126543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116902246120494876069417695 175353369180742314104126543)
          ·
            refine ⟨263030053771113471156189815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175353369180742314104126543 263030053771113471156189815)
            ·
              refine ⟨394545080656670206734284723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263030053771113471156189815 394545080656670206734284723)
              ·
                refine ⟨591817620985005310101427085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394545080656670206734284723 591817620985005310101427085)
                ·
                  refine ⟨221931607869376991288035157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 591817620985005310101427085 221931607869376991288035157)
                  ·
                    refine ⟨1300380514859630808328331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 221931607869376991288035157 1300380514859630808328331)
                    ·
                      rfl

theorem cell22_3798723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 9].length) (baseStart_3798723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798723 prefixEnd_3798723 := by exact prefixLift 3798723
  have htrace : WordTrace (prefixWord ++ tailWord_3798723) baseStart_3798723 baseEnd_3798723 := by
    simpa [prefixWord, tailWord_3798723, baseEnd_3798723] using wordTrace_append hprefix tailTrace_3798723
  have hstable : (prefixWord ++ tailWord_3798723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798723).length < 2 ^ (prefixWord ++ tailWord_3798723).sum := by decide
  have hdescent : baseEnd_3798723 < baseStart_3798723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798757 : List Nat := [1, 3, 1, 4, 1, 1, 1, 4, 3, 3]
def baseStart_3798757 : Nat := 118140960795 + 3798757 * 2 ^ 59
def prefixEnd_3798757 : Nat := 4983230072969 + 3 ^ 40 * 3798757 * 2
def baseEnd_3798757 : Nat := 1300392153754466052978227

theorem tailTrace_3798757 : CollatzResearch.WordTrace tailWord_3798757 prefixEnd_3798757 1300392153754466052978227 := by
  unfold tailWord_3798757
  simp only [CollatzResearch.WordTrace]
  refine ⟨138552050298759639889010525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92368033532506426592673683 138552050298759639889010525)
  ·
    refine ⟨51957018862034864958378947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138552050298759639889010525 51957018862034864958378947)
    ·
      refine ⟨77935528293052297437568421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51957018862034864958378947 77935528293052297437568421)
      ·
        refine ⟨14612911554947305769544079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77935528293052297437568421 14612911554947305769544079)
        ·
          refine ⟨21919367332420958654316119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14612911554947305769544079 21919367332420958654316119)
          ·
            refine ⟨32879050998631437981474179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21919367332420958654316119 32879050998631437981474179)
            ·
              refine ⟨49318576497947156972211269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32879050998631437981474179 49318576497947156972211269)
              ·
                refine ⟨9247233093365091932289613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49318576497947156972211269 9247233093365091932289613)
                ·
                  refine ⟨3467712410011909474608605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9247233093365091932289613 3467712410011909474608605)
                  ·
                    refine ⟨1300392153754466052978227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3467712410011909474608605 1300392153754466052978227)
                    ·
                      rfl

theorem cell22_3798757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_3798757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798757 prefixEnd_3798757 := by exact prefixLift 3798757
  have htrace : WordTrace (prefixWord ++ tailWord_3798757) baseStart_3798757 baseEnd_3798757 := by
    simpa [prefixWord, tailWord_3798757, baseEnd_3798757] using wordTrace_append hprefix tailTrace_3798757
  have hstable : (prefixWord ++ tailWord_3798757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798757).length < 2 ^ (prefixWord ++ tailWord_3798757).sum := by decide
  have hdescent : baseEnd_3798757 < baseStart_3798757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798770 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 9]
def baseStart_3798770 : Nat := 118140960795 + 3798770 * 2 ^ 59
def prefixEnd_3798770 : Nat := 4983230072969 + 3 ^ 40 * 3798770 * 2
def baseEnd_3798770 : Nat := 433465534640046117467729

theorem tailTrace_3798770 : CollatzResearch.WordTrace tailWord_3798770 prefixEnd_3798770 433465534640046117467729 := by
  unfold tailWord_3798770
  simp only [CollatzResearch.WordTrace]
  refine ⟨34638131111928135777308441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92368349631808362072822509 34638131111928135777308441)
  ·
    refine ⟨25978598333946101832981331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34638131111928135777308441 25978598333946101832981331)
    ·
      refine ⟨38967897500919152749471997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25978598333946101832981331 38967897500919152749471997)
      ·
        refine ⟨14612961562844682281051999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38967897500919152749471997 14612961562844682281051999)
        ·
          refine ⟨21919442344267023421577999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14612961562844682281051999 21919442344267023421577999)
          ·
            refine ⟨32879163516400535132366999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21919442344267023421577999 32879163516400535132366999)
            ·
              refine ⟨49318745274600802698550499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32879163516400535132366999 49318745274600802698550499)
              ·
                refine ⟨73978117911901204047825749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49318745274600802698550499 73978117911901204047825749)
                ·
                  refine ⟨433465534640046117467729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73978117911901204047825749 433465534640046117467729)
                  ·
                    rfl

theorem cell22_3798770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_3798770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798770 prefixEnd_3798770 := by exact prefixLift 3798770
  have htrace : WordTrace (prefixWord ++ tailWord_3798770) baseStart_3798770 baseEnd_3798770 := by
    simpa [prefixWord, tailWord_3798770, baseEnd_3798770] using wordTrace_append hprefix tailTrace_3798770
  have hstable : (prefixWord ++ tailWord_3798770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798770).length < 2 ^ (prefixWord ++ tailWord_3798770).sum := by decide
  have hdescent : baseEnd_3798770 < baseStart_3798770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798785 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 4, 5]
def baseStart_3798785 : Nat := 118140960795 + 3798785 * 2 ^ 59
def prefixEnd_3798785 : Nat := 4983230072969 + 3 ^ 40 * 3798785 * 2
def baseEnd_3798785 : Nat := 1300401738726683313278141

theorem tailTrace_3798785 : CollatzResearch.WordTrace tailWord_3798785 prefixEnd_3798785 1300401738726683313278141 := by
  unfold tailWord_3798785
  simp only [CollatzResearch.WordTrace]
  refine ⟨138553071542658200671029809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92368714361772133780686539 138553071542658200671029809)
  ·
    refine ⟨103914803656993650503272357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138553071542658200671029809 103914803656993650503272357)
    ·
      refine ⟨19484025685686309469363567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103914803656993650503272357 19484025685686309469363567)
      ·
        refine ⟨29226038528529464204045351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19484025685686309469363567 29226038528529464204045351)
        ·
          refine ⟨43839057792794196306068027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29226038528529464204045351 43839057792794196306068027)
          ·
            refine ⟨65758586689191294459102041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43839057792794196306068027 65758586689191294459102041)
            ·
              refine ⟨49318940016893470844326531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65758586689191294459102041 49318940016893470844326531)
              ·
                refine ⟨73978410025340206266489797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49318940016893470844326531 73978410025340206266489797)
                ·
                  refine ⟨13870951879751288674966837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73978410025340206266489797 13870951879751288674966837)
                  ·
                    refine ⟨1300401738726683313278141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13870951879751288674966837 1300401738726683313278141)
                    ·
                      rfl

theorem cell22_3798785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_3798785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798785 prefixEnd_3798785 := by exact prefixLift 3798785
  have htrace : WordTrace (prefixWord ++ tailWord_3798785) baseStart_3798785 baseEnd_3798785 := by
    simpa [prefixWord, tailWord_3798785, baseEnd_3798785] using wordTrace_append hprefix tailTrace_3798785
  have hstable : (prefixWord ++ tailWord_3798785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798785).length < 2 ^ (prefixWord ++ tailWord_3798785).sum := by decide
  have hdescent : baseEnd_3798785 < baseStart_3798785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798791 : List Nat := [1, 1, 4, 4, 2, 2, 1, 1, 3, 3]
def baseStart_3798791 : Nat := 118140960795 + 3798791 * 2 ^ 59
def prefixEnd_3798791 : Nat := 4983230072969 + 3 ^ 40 * 3798791 * 2
def baseEnd_3798791 : Nat := 1300403792649301297628123

theorem tailTrace_3798791 : CollatzResearch.WordTrace tailWord_3798791 prefixEnd_3798791 1300403792649301297628123 := by
  unfold tailWord_3798791
  simp only [CollatzResearch.WordTrace]
  refine ⟨138553290380636463695748227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92368860253757642463832151 138553290380636463695748227)
  ·
    refine ⟨207829935570954695543622341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138553290380636463695748227 207829935570954695543622341)
    ·
      refine ⟨38968112919554005414429189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207829935570954695543622341 38968112919554005414429189)
      ·
        refine ⟨7306521172416376015205473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38968112919554005414429189 7306521172416376015205473)
        ·
          refine ⟨5479890879312282011404105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7306521172416376015205473 5479890879312282011404105)
          ·
            refine ⟨4109918159484211508553079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5479890879312282011404105 4109918159484211508553079)
            ·
              refine ⟨6164877239226317262829619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4109918159484211508553079 6164877239226317262829619)
              ·
                refine ⟨9247315858839475894244429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6164877239226317262829619 9247315858839475894244429)
                ·
                  refine ⟨3467743447064803460341661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9247315858839475894244429 3467743447064803460341661)
                  ·
                    refine ⟨1300403792649301297628123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3467743447064803460341661 1300403792649301297628123)
                    ·
                      rfl

theorem cell22_3798791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_3798791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798791 prefixEnd_3798791 := by exact prefixLift 3798791
  have htrace : WordTrace (prefixWord ++ tailWord_3798791) baseStart_3798791 baseEnd_3798791 := by
    simpa [prefixWord, tailWord_3798791, baseEnd_3798791] using wordTrace_append hprefix tailTrace_3798791
  have hstable : (prefixWord ++ tailWord_3798791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798791).length < 2 ^ (prefixWord ++ tailWord_3798791).sum := by decide
  have hdescent : baseEnd_3798791 < baseStart_3798791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798815 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 8]
def baseStart_3798815 : Nat := 118140960795 + 3798815 * 2 ^ 59
def prefixEnd_3798815 : Nat := 4983230072969 + 3 ^ 40 * 3798815 * 2
def baseEnd_3798815 : Nat := 433470669446591078342683

theorem tailTrace_3798815 : CollatzResearch.WordTrace tailWord_3798815 prefixEnd_3798815 433470669446591078342683 := by
  unfold tailWord_3798815
  simp only [CollatzResearch.WordTrace]
  refine ⟨138554165732549515794621899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92369443821699677196414599 138554165732549515794621899)
  ·
    refine ⟨207831248598824273691932849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138554165732549515794621899 207831248598824273691932849)
    ·
      refine ⟨155873436449118205268949637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207831248598824273691932849 155873436449118205268949637)
      ·
        refine ⟨29226269334209663487928057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155873436449118205268949637 29226269334209663487928057)
        ·
          refine ⟨21919702000657247615946043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29226269334209663487928057 21919702000657247615946043)
          ·
            refine ⟨32879553000985871423919065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21919702000657247615946043 32879553000985871423919065)
            ·
              refine ⟨24659664750739403567939299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32879553000985871423919065 24659664750739403567939299)
              ·
                refine ⟨36989497126109105351908949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24659664750739403567939299 36989497126109105351908949)
                ·
                  refine ⟨433470669446591078342683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36989497126109105351908949 433470669446591078342683)
                  ·
                    rfl

theorem cell22_3798815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 8].length) (baseStart_3798815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798815 prefixEnd_3798815 := by exact prefixLift 3798815
  have htrace : WordTrace (prefixWord ++ tailWord_3798815) baseStart_3798815 baseEnd_3798815 := by
    simpa [prefixWord, tailWord_3798815, baseEnd_3798815] using wordTrace_append hprefix tailTrace_3798815
  have hstable : (prefixWord ++ tailWord_3798815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798815).length < 2 ^ (prefixWord ++ tailWord_3798815).sum := by decide
  have hdescent : baseEnd_3798815 < baseStart_3798815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798817 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 3, 4]
def baseStart_3798817 : Nat := 118140960795 + 3798817 * 2 ^ 59
def prefixEnd_3798817 : Nat := 4983230072969 + 3 ^ 40 * 3798817 * 2
def baseEnd_3798817 : Nat := 1300412692980645896478043

theorem tailTrace_3798817 : CollatzResearch.WordTrace tailWord_3798817 prefixEnd_3798817 1300412692980645896478043 := by
  unfold tailWord_3798817
  simp only [CollatzResearch.WordTrace]
  refine ⟨138554238678542270136194705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92369492452361513424129803 138554238678542270136194705)
  ·
    refine ⟨103915679008906702602146029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138554238678542270136194705 103915679008906702602146029)
    ·
      refine ⟨38968379628340013475804761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103915679008906702602146029 38968379628340013475804761)
      ·
        refine ⟨29226284721255010106853571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38968379628340013475804761 29226284721255010106853571)
        ·
          refine ⟨43839427081882515160280357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29226284721255010106853571 43839427081882515160280357)
          ·
            refine ⟨8219892577852971592552567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43839427081882515160280357 8219892577852971592552567)
            ·
              refine ⟨12329838866779457388828851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8219892577852971592552567 12329838866779457388828851)
              ·
                refine ⟨18494758300169186083243277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12329838866779457388828851 18494758300169186083243277)
                ·
                  refine ⟨6935534362563444781216229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18494758300169186083243277 6935534362563444781216229)
                  ·
                    refine ⟨1300412692980645896478043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6935534362563444781216229 1300412692980645896478043)
                    ·
                      rfl

theorem cell22_3798817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_3798817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798817 prefixEnd_3798817 := by exact prefixLift 3798817
  have htrace : WordTrace (prefixWord ++ tailWord_3798817) baseStart_3798817 baseEnd_3798817 := by
    simpa [prefixWord, tailWord_3798817, baseEnd_3798817] using wordTrace_append hprefix tailTrace_3798817
  have hstable : (prefixWord ++ tailWord_3798817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798817).length < 2 ^ (prefixWord ++ tailWord_3798817).sum := by decide
  have hdescent : baseEnd_3798817 < baseStart_3798817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798879 : List Nat := [1, 1, 2, 3, 1, 6, 1, 1, 2, 4]
def baseStart_3798879 : Nat := 118140960795 + 3798879 * 2 ^ 59
def prefixEnd_3798879 : Nat := 4983230072969 + 3 ^ 40 * 3798879 * 2
def baseEnd_3798879 : Nat := 1300433916847698401427853

theorem tailTrace_3798879 : CollatzResearch.WordTrace tailWord_3798879 prefixEnd_3798879 1300433916847698401427853 := by
  unfold tailWord_3798879
  simp only [CollatzResearch.WordTrace]
  refine ⟨138556500004317654724951691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92371000002878436483301127 138556500004317654724951691)
  ·
    refine ⟨207834750006476482087427537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138556500004317654724951691 207834750006476482087427537)
    ·
      refine ⟨155876062504857361565570653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207834750006476482087427537 155876062504857361565570653)
      ·
        refine ⟨58453523439321510587088995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155876062504857361565570653 58453523439321510587088995)
        ·
          refine ⟨87680285158982265880633493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58453523439321510587088995 87680285158982265880633493)
          ·
            refine ⟨4110013366827293713154695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87680285158982265880633493 4110013366827293713154695)
            ·
              refine ⟨6165020050240940569732043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4110013366827293713154695 6165020050240940569732043)
              ·
                refine ⟨9247530075361410854598065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6165020050240940569732043 9247530075361410854598065)
                ·
                  refine ⟨6935647556521058140948549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9247530075361410854598065 6935647556521058140948549)
                  ·
                    refine ⟨1300433916847698401427853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6935647556521058140948549 1300433916847698401427853)
                    ·
                      rfl

theorem cell22_3798879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 4].length) (baseStart_3798879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798879 prefixEnd_3798879 := by exact prefixLift 3798879
  have htrace : WordTrace (prefixWord ++ tailWord_3798879) baseStart_3798879 baseEnd_3798879 := by
    simpa [prefixWord, tailWord_3798879, baseEnd_3798879] using wordTrace_append hprefix tailTrace_3798879
  have hstable : (prefixWord ++ tailWord_3798879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798879).length < 2 ^ (prefixWord ++ tailWord_3798879).sum := by decide
  have hdescent : baseEnd_3798879 < baseStart_3798879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799074 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 7]
def baseStart_3799074 : Nat := 118140960795 + 3799074 * 2 ^ 59
def prefixEnd_3799074 : Nat := 4983230072969 + 3 ^ 40 * 3799074 * 2
def baseEnd_3799074 : Nat := 433500223110927630934085

theorem tailTrace_3799074 : CollatzResearch.WordTrace tailWord_3799074 prefixEnd_3799074 433500223110927630934085 := by
  unfold tailWord_3799074
  simp only [CollatzResearch.WordTrace]
  refine ⟨34640903059652800757075069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92375741492407468685533517 34640903059652800757075069)
  ·
    refine ⟨12990338647369800283903151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34640903059652800757075069 12990338647369800283903151)
    ·
      refine ⟨19485507971054700425854727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12990338647369800283903151 19485507971054700425854727)
      ·
        refine ⟨29228261956582050638782091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19485507971054700425854727 29228261956582050638782091)
        ·
          refine ⟨43842392934873075958173137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29228261956582050638782091 43842392934873075958173137)
          ·
            refine ⟨32881794701154806968629853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43842392934873075958173137 32881794701154806968629853)
            ·
              refine ⟨12330673012933052613236195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32881794701154806968629853 12330673012933052613236195)
              ·
                refine ⟨18496009519399578919854293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12330673012933052613236195 18496009519399578919854293)
                ·
                  refine ⟨433500223110927630934085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18496009519399578919854293 433500223110927630934085)
                  ·
                    rfl

theorem cell22_3799074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_3799074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799074 prefixEnd_3799074 := by exact prefixLift 3799074
  have htrace : WordTrace (prefixWord ++ tailWord_3799074) baseStart_3799074 baseEnd_3799074 := by
    simpa [prefixWord, tailWord_3799074, baseEnd_3799074] using wordTrace_append hprefix tailTrace_3799074
  have hstable : (prefixWord ++ tailWord_3799074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799074).length < 2 ^ (prefixWord ++ tailWord_3799074).sum := by decide
  have hdescent : baseEnd_3799074 < baseStart_3799074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799087 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 2, 8]
def baseStart_3799087 : Nat := 118140960795 + 3799087 * 2 ^ 59
def prefixEnd_3799087 : Nat := 4983230072969 + 3 ^ 40 * 3799087 * 2
def baseEnd_3799087 : Nat := 1300505119498455192227215

theorem tailTrace_3799087 : CollatzResearch.WordTrace tailWord_3799087 prefixEnd_3799087 1300505119498455192227215 := by
  unfold tailWord_3799087
  simp only [CollatzResearch.WordTrace]
  refine ⟨138564086387564106248523515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92376057591709404165682343 138564086387564106248523515)
  ·
    refine ⟨207846129581346159372785273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138564086387564106248523515 207846129581346159372785273)
    ·
      refine ⟨155884597186009619529588955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207846129581346159372785273 155884597186009619529588955)
      ·
        refine ⟨233826895779014429294383433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155884597186009619529588955 233826895779014429294383433)
        ·
          refine ⟨175370171834260821970787575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233826895779014429294383433 175370171834260821970787575)
          ·
            refine ⟨263055257751391232956181363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175370171834260821970787575 263055257751391232956181363)
            ·
              refine ⟨394582886627086849434272045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263055257751391232956181363 394582886627086849434272045)
              ·
                refine ⟨147968582485157568537852017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 394582886627086849434272045 147968582485157568537852017)
                ·
                  refine ⟨110976436863868176403389013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147968582485157568537852017 110976436863868176403389013)
                  ·
                    refine ⟨1300505119498455192227215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110976436863868176403389013 1300505119498455192227215)
                    ·
                      rfl

theorem cell22_3799087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_3799087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799087 prefixEnd_3799087 := by exact prefixLift 3799087
  have htrace : WordTrace (prefixWord ++ tailWord_3799087) baseStart_3799087 baseEnd_3799087 := by
    simpa [prefixWord, tailWord_3799087, baseEnd_3799087] using wordTrace_append hprefix tailTrace_3799087
  have hstable : (prefixWord ++ tailWord_3799087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799087).length < 2 ^ (prefixWord ++ tailWord_3799087).sum := by decide
  have hdescent : baseEnd_3799087 < baseStart_3799087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799089 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 2, 5]
def baseStart_3799089 : Nat := 118140960795 + 3799089 * 2 ^ 59
def prefixEnd_3799089 : Nat := 4983230072969 + 3 ^ 40 * 3799089 * 2
def baseEnd_3799089 : Nat := 1300505804139327853677209

theorem tailTrace_3799089 : CollatzResearch.WordTrace tailWord_3799089 prefixEnd_3799089 1300505804139327853677209 := by
  unfold tailWord_3799089
  simp only [CollatzResearch.WordTrace]
  refine ⟨138564159333556860590096321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92376106222371240393397547 138564159333556860590096321)
  ·
    refine ⟨103923119500167645442572241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138564159333556860590096321 103923119500167645442572241)
    ·
      refine ⟨77942339625125734081929181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103923119500167645442572241 77942339625125734081929181)
      ·
        refine ⟨29228377359422150280723443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77942339625125734081929181 29228377359422150280723443)
        ·
          refine ⟨43842566039133225421085165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29228377359422150280723443 43842566039133225421085165)
          ·
            refine ⟨16440962264674959532906937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43842566039133225421085165 16440962264674959532906937)
            ·
              refine ⟨12330721698506219649680203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16440962264674959532906937 12330721698506219649680203)
              ·
                refine ⟨18496082547759329474520305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12330721698506219649680203 18496082547759329474520305)
                ·
                  refine ⟨13872061910819497105890229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18496082547759329474520305 13872061910819497105890229)
                  ·
                    refine ⟨1300505804139327853677209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13872061910819497105890229 1300505804139327853677209)
                    ·
                      rfl

theorem cell22_3799089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_3799089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799089 prefixEnd_3799089 := by exact prefixLift 3799089
  have htrace : WordTrace (prefixWord ++ tailWord_3799089) baseStart_3799089 baseEnd_3799089 := by
    simpa [prefixWord, tailWord_3799089, baseEnd_3799089] using wordTrace_append hprefix tailTrace_3799089
  have hstable : (prefixWord ++ tailWord_3799089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799089).length < 2 ^ (prefixWord ++ tailWord_3799089).sum := by decide
  have hdescent : baseEnd_3799089 < baseStart_3799089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799136 : List Nat := [2, 1, 1, 3, 2, 5, 1, 1, 6]
def baseStart_3799136 : Nat := 118140960795 + 3799136 * 2 ^ 59
def prefixEnd_3799136 : Nat := 4983230072969 + 3 ^ 40 * 3799136 * 2
def baseEnd_3799136 : Nat := 433507297733278465917355

theorem tailTrace_3799136 : CollatzResearch.WordTrace tailWord_3799136 prefixEnd_3799136 433507297733278465917355 := by
  unfold tailWord_3799136
  simp only [CollatzResearch.WordTrace]
  refine ⟨69282936782193293808528631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92377249042924391744704841 69282936782193293808528631)
  ·
    refine ⟨103924405173289940712792947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69282936782193293808528631 103924405173289940712792947)
    ·
      refine ⟨155886607759934911069189421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103924405173289940712792947 155886607759934911069189421)
      ·
        refine ⟨58457477909975591650946033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155886607759934911069189421 58457477909975591650946033)
        ·
          refine ⟨43843108432481693738209525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58457477909975591650946033 43843108432481693738209525)
          ·
            refine ⟨4110291415545158787957143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43843108432481693738209525 4110291415545158787957143)
            ·
              refine ⟨6165437123317738181935715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4110291415545158787957143 6165437123317738181935715)
              ·
                refine ⟨9248155684976607272903573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6165437123317738181935715 9248155684976607272903573)
                ·
                  refine ⟨433507297733278465917355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9248155684976607272903573 433507297733278465917355)
                  ·
                    rfl

theorem cell22_3799136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 6].length) (baseStart_3799136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799136 prefixEnd_3799136 := by exact prefixLift 3799136
  have htrace : WordTrace (prefixWord ++ tailWord_3799136) baseStart_3799136 baseEnd_3799136 := by
    simpa [prefixWord, tailWord_3799136, baseEnd_3799136] using wordTrace_append hprefix tailTrace_3799136
  have hstable : (prefixWord ++ tailWord_3799136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799136).length < 2 ^ (prefixWord ++ tailWord_3799136).sum := by decide
  have hdescent : baseEnd_3799136 < baseStart_3799136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799164 : List Nat := [2, 2, 2, 1, 1, 4, 2, 8]
def baseStart_3799164 : Nat := 118140960795 + 3799164 * 2 ^ 59
def prefixEnd_3799164 : Nat := 4983230072969 + 3 ^ 40 * 3799164 * 2
def baseEnd_3799164 : Nat := 144503497574672517561331

theorem tailTrace_3799164 : CollatzResearch.WordTrace tailWord_3799164 prefixEnd_3799164 144503497574672517561331 := by
  unfold tailWord_3799164
  simp only [CollatzResearch.WordTrace]
  refine ⟨69283447404142574199538273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92377929872190098932717697 69283447404142574199538273)
  ·
    refine ⟨51962585553106930649653705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69283447404142574199538273 51962585553106930649653705)
    ·
      refine ⟨38971939164830197987240279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51962585553106930649653705 38971939164830197987240279)
      ·
        refine ⟨58457908747245296980860419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38971939164830197987240279 58457908747245296980860419)
        ·
          refine ⟨87686863120867945471290629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58457908747245296980860419 87686863120867945471290629)
          ·
            refine ⟨16441286835162739775866993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87686863120867945471290629 16441286835162739775866993)
            ·
              refine ⟨12330965126372054831900245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16441286835162739775866993 12330965126372054831900245)
              ·
                refine ⟨144503497574672517561331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12330965126372054831900245 144503497574672517561331)
                ·
                  rfl

theorem cell22_3799164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 8].length) (baseStart_3799164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799164 prefixEnd_3799164 := by exact prefixLift 3799164
  have htrace : WordTrace (prefixWord ++ tailWord_3799164) baseStart_3799164 baseEnd_3799164 := by
    simpa [prefixWord, tailWord_3799164, baseEnd_3799164] using wordTrace_append hprefix tailTrace_3799164
  have hstable : (prefixWord ++ tailWord_3799164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799164).length < 2 ^ (prefixWord ++ tailWord_3799164).sum := by decide
  have hdescent : baseEnd_3799164 < baseStart_3799164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799213 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_3799213 : Nat := 118140960795 + 3799213 * 2 ^ 59
def prefixEnd_3799213 : Nat := 4983230072969 + 3 ^ 40 * 3799213 * 2
def baseEnd_3799213 : Nat := 1300548251873432863576829

theorem tailTrace_3799213 : CollatzResearch.WordTrace tailWord_3799213 prefixEnd_3799213 1300548251873432863576829 := by
  unfold tailWord_3799213
  simp only [CollatzResearch.WordTrace]
  refine ⟨138568681985107629767610293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92379121323405086511740195 138568681985107629767610293)
  ·
    refine ⟨12990813936103840290713465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138568681985107629767610293 12990813936103840290713465)
    ·
      refine ⟨9743110452077880218035099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12990813936103840290713465 9743110452077880218035099)
      ·
        refine ⟨14614665678116820327052649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9743110452077880218035099 14614665678116820327052649)
        ·
          refine ⟨10960999258587615245289487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14614665678116820327052649 10960999258587615245289487)
          ·
            refine ⟨16441498887881422867934231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10960999258587615245289487 16441498887881422867934231)
            ·
              refine ⟨24662248331822134301901347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16441498887881422867934231 24662248331822134301901347)
              ·
                refine ⟨36993372497733201452852021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24662248331822134301901347 36993372497733201452852021)
                ·
                  refine ⟨3468128671662487636204877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36993372497733201452852021 3468128671662487636204877)
                  ·
                    refine ⟨1300548251873432863576829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3468128671662487636204877 1300548251873432863576829)
                    ·
                      rfl

theorem cell22_3799213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_3799213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799213 prefixEnd_3799213 := by exact prefixLift 3799213
  have htrace : WordTrace (prefixWord ++ tailWord_3799213) baseStart_3799213 baseEnd_3799213 := by
    simpa [prefixWord, tailWord_3799213, baseEnd_3799213] using wordTrace_append hprefix tailTrace_3799213
  have hstable : (prefixWord ++ tailWord_3799213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799213).length < 2 ^ (prefixWord ++ tailWord_3799213).sum := by decide
  have hdescent : baseEnd_3799213 < baseStart_3799213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799224 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 1, 7]
def baseStart_3799224 : Nat := 118140960795 + 3799224 * 2 ^ 59
def prefixEnd_3799224 : Nat := 4983230072969 + 3 ^ 40 * 3799224 * 2
def baseEnd_3799224 : Nat := 1300552017398232501551795

theorem tailTrace_3799224 : CollatzResearch.WordTrace tailWord_3799224 prefixEnd_3799224 1300552017398232501551795 := by
  unfold tailWord_3799224
  simp only [CollatzResearch.WordTrace]
  refine ⟨69284541594033889323130363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92379388792045185764173817 69284541594033889323130363)
  ·
    refine ⟨103926812391050833984695545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69284541594033889323130363 103926812391050833984695545)
    ·
      refine ⟨77945109293288125488521659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103926812391050833984695545 77945109293288125488521659)
      ·
        refine ⟨116917663939932188232782489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77945109293288125488521659 116917663939932188232782489)
        ·
          refine ⟨87688247954949141174586867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116917663939932188232782489 87688247954949141174586867)
          ·
            refine ⟨131532371932423711761880301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87688247954949141174586867 131532371932423711761880301)
            ·
              refine ⟨49324639474658891910705113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131532371932423711761880301 49324639474658891910705113)
              ·
                refine ⟨36993479605994168933028835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49324639474658891910705113 36993479605994168933028835)
                ·
                  refine ⟨55490219408991253399543253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36993479605994168933028835 55490219408991253399543253)
                  ·
                    refine ⟨1300552017398232501551795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55490219408991253399543253 1300552017398232501551795)
                    ·
                      rfl

theorem cell22_3799224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_3799224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799224 prefixEnd_3799224 := by exact prefixLift 3799224
  have htrace : WordTrace (prefixWord ++ tailWord_3799224) baseStart_3799224 baseEnd_3799224 := by
    simpa [prefixWord, tailWord_3799224, baseEnd_3799224] using wordTrace_append hprefix tailTrace_3799224
  have hstable : (prefixWord ++ tailWord_3799224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799224).length < 2 ^ (prefixWord ++ tailWord_3799224).sum := by decide
  have hdescent : baseEnd_3799224 < baseStart_3799224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799305 : List Nat := [1, 2, 1, 1, 3, 5, 3, 2, 4]
def baseStart_3799305 : Nat := 118140960795 + 3799305 * 2 ^ 59
def prefixEnd_3799305 : Nat := 4983230072969 + 3 ^ 40 * 3799305 * 2
def baseEnd_3799305 : Nat := 433526581784525096758849

theorem tailTrace_3799305 : CollatzResearch.WordTrace tailWord_3799305 prefixEnd_3799305 433526581784525096758849 := by
  unfold tailWord_3799305
  simp only [CollatzResearch.WordTrace]
  refine ⟨138572037500774329479959369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92381358333849552986639579 138572037500774329479959369)
  ·
    refine ⟨103929028125580747109969527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138572037500774329479959369 103929028125580747109969527)
    ·
      refine ⟨155893542188371120664954291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103929028125580747109969527 155893542188371120664954291)
      ·
        refine ⟨233840313282556680997431437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155893542188371120664954291 233840313282556680997431437)
        ·
          refine ⟨87690117480958755374036789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233840313282556680997431437 87690117480958755374036789)
          ·
            refine ⟨8220948513839883316315949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87690117480958755374036789 8220948513839883316315949)
            ·
              refine ⟨3082855692689956243618481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8220948513839883316315949 3082855692689956243618481)
              ·
                refine ⟨2312141769517467182713861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3082855692689956243618481 2312141769517467182713861)
                ·
                  refine ⟨433526581784525096758849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2312141769517467182713861 433526581784525096758849)
                  ·
                    rfl

theorem cell22_3799305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 4].length) (baseStart_3799305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799305 prefixEnd_3799305 := by exact prefixLift 3799305
  have htrace : WordTrace (prefixWord ++ tailWord_3799305) baseStart_3799305 baseEnd_3799305 := by
    simpa [prefixWord, tailWord_3799305, baseEnd_3799305] using wordTrace_append hprefix tailTrace_3799305
  have hstable : (prefixWord ++ tailWord_3799305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799305).length < 2 ^ (prefixWord ++ tailWord_3799305).sum := by decide
  have hdescent : baseEnd_3799305 < baseStart_3799305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799376 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 1, 7]
def baseStart_3799376 : Nat := 118140960795 + 3799376 * 2 ^ 59
def prefixEnd_3799376 : Nat := 4983230072969 + 3 ^ 40 * 3799376 * 2
def baseEnd_3799376 : Nat := 1300604050104554771751329

theorem tailTrace_3799376 : CollatzResearch.WordTrace tailWord_3799376 prefixEnd_3799376 1300604050104554771751329 := by
  unfold tailWord_3799376
  simp only [CollatzResearch.WordTrace]
  refine ⟨69287313541758554302896991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92383084722344739070529321 69287313541758554302896991)
  ·
    refine ⟨103930970312637831454345487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69287313541758554302896991 103930970312637831454345487)
    ·
      refine ⟨155896455468956747181518231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103930970312637831454345487 155896455468956747181518231)
      ·
        refine ⟨233844683203435120772277347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155896455468956747181518231 233844683203435120772277347)
        ·
          refine ⟨350767024805152681158416021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233844683203435120772277347 350767024805152681158416021)
          ·
            refine ⟨16442204287741531929300751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 350767024805152681158416021 16442204287741531929300751)
            ·
              refine ⟨24663306431612297893951127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16442204287741531929300751 24663306431612297893951127)
              ·
                refine ⟨36994959647418446840926691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24663306431612297893951127 36994959647418446840926691)
                ·
                  refine ⟨55492439471127670261390037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36994959647418446840926691 55492439471127670261390037)
                  ·
                    refine ⟨1300604050104554771751329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55492439471127670261390037 1300604050104554771751329)
                    ·
                      rfl

theorem cell22_3799376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_3799376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799376 prefixEnd_3799376 := by exact prefixLift 3799376
  have htrace : WordTrace (prefixWord ++ tailWord_3799376) baseStart_3799376 baseEnd_3799376 := by
    simpa [prefixWord, tailWord_3799376, baseEnd_3799376] using wordTrace_append hprefix tailTrace_3799376
  have hstable : (prefixWord ++ tailWord_3799376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799376).length < 2 ^ (prefixWord ++ tailWord_3799376).sum := by decide
  have hdescent : baseEnd_3799376 < baseStart_3799376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799378 : List Nat := [3, 2, 2, 1, 1, 1, 4, 3, 5]
def baseStart_3799378 : Nat := 118140960795 + 3799378 * 2 ^ 59
def prefixEnd_3799378 : Nat := 4983230072969 + 3 ^ 40 * 3799378 * 2
def baseEnd_3799378 : Nat := 433534911581809144400441

theorem tailTrace_3799378 : CollatzResearch.WordTrace tailWord_3799378 prefixEnd_3799378 433534911581809144400441 := by
  unfold tailWord_3799378
  simp only [CollatzResearch.WordTrace]
  refine ⟨34643675007377465736841697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92383133353006575298244525 34643675007377465736841697)
  ·
    refine ⟨25982756255533099302631273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34643675007377465736841697 25982756255533099302631273)
    ·
      refine ⟨19487067191649824476973455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25982756255533099302631273 19487067191649824476973455)
      ·
        refine ⟨29230600787474736715460183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19487067191649824476973455 29230600787474736715460183)
        ·
          refine ⟨43845901181212105073190275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29230600787474736715460183 43845901181212105073190275)
          ·
            refine ⟨65768851771818157609785413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43845901181212105073190275 65768851771818157609785413)
            ·
              refine ⟨12331659707215904551834765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65768851771818157609785413 12331659707215904551834765)
              ·
                refine ⟨4624372390205964206938037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12331659707215904551834765 4624372390205964206938037)
                ·
                  refine ⟨433534911581809144400441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4624372390205964206938037 433534911581809144400441)
                  ·
                    rfl

theorem cell22_3799378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_3799378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799378 prefixEnd_3799378 := by exact prefixLift 3799378
  have htrace : WordTrace (prefixWord ++ tailWord_3799378) baseStart_3799378 baseEnd_3799378 := by
    simpa [prefixWord, tailWord_3799378, baseEnd_3799378] using wordTrace_append hprefix tailTrace_3799378
  have hstable : (prefixWord ++ tailWord_3799378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799378).length < 2 ^ (prefixWord ++ tailWord_3799378).sum := by decide
  have hdescent : baseEnd_3799378 < baseStart_3799378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799483 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 9, 3]
def baseStart_3799483 : Nat := 118140960795 + 3799483 * 2 ^ 59
def prefixEnd_3799483 : Nat := 4983230072969 + 3 ^ 40 * 3799483 * 2
def baseEnd_3799483 : Nat := 1300640678391242159326001

theorem tailTrace_3799483 : CollatzResearch.WordTrace tailWord_3799483 prefixEnd_3799483 1300640678391242159326001 := by
  unfold tailWord_3799483
  simp only [CollatzResearch.WordTrace]
  refine ⟨138578529694129465879939103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92385686462752977253292735 138578529694129465879939103)
  ·
    refine ⟨207867794541194198819908655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138578529694129465879939103 207867794541194198819908655)
    ·
      refine ⟨311801691811791298229862983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207867794541194198819908655 311801691811791298229862983)
      ·
        refine ⟨467702537717686947344794475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311801691811791298229862983 467702537717686947344794475)
        ·
          refine ⟨701553806576530421017191713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467702537717686947344794475 701553806576530421017191713)
          ·
            refine ⟨526165354932397815762893785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701553806576530421017191713 526165354932397815762893785)
            ·
              refine ⟨394624016199298361822170339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526165354932397815762893785 394624016199298361822170339)
              ·
                refine ⟨591936024298947542733255509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394624016199298361822170339 591936024298947542733255509)
                ·
                  refine ⟨3468375142376645758202669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 591936024298947542733255509 3468375142376645758202669)
                  ·
                    refine ⟨1300640678391242159326001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3468375142376645758202669 1300640678391242159326001)
                    ·
                      rfl

theorem cell22_3799483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 3].length) (baseStart_3799483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799483 prefixEnd_3799483 := by exact prefixLift 3799483
  have htrace : WordTrace (prefixWord ++ tailWord_3799483) baseStart_3799483 baseEnd_3799483 := by
    simpa [prefixWord, tailWord_3799483, baseEnd_3799483] using wordTrace_append hprefix tailTrace_3799483
  have hstable : (prefixWord ++ tailWord_3799483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799483).length < 2 ^ (prefixWord ++ tailWord_3799483).sum := by decide
  have hdescent : baseEnd_3799483 < baseStart_3799483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799530 : List Nat := [3, 1, 3, 1, 3, 1, 1, 4, 5]
def baseStart_3799530 : Nat := 118140960795 + 3799530 * 2 ^ 59
def prefixEnd_3799530 : Nat := 4983230072969 + 3 ^ 40 * 3799530 * 2
def baseEnd_3799530 : Nat := 433552255817249901133619

theorem tailTrace_3799530 : CollatzResearch.WordTrace tailWord_3799530 prefixEnd_3799530 433552255817249901133619 := by
  unfold tailWord_3799530
  simp only [CollatzResearch.WordTrace]
  refine ⟨34645060981239798226725011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92386829283306128604600029 34645060981239798226725011)
  ·
    refine ⟨51967591471859697340087517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34645060981239798226725011 51967591471859697340087517)
    ·
      refine ⟨19487846801947386502532819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51967591471859697340087517 19487846801947386502532819)
      ·
        refine ⟨29231770202921079753799229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19487846801947386502532819 29231770202921079753799229)
        ·
          refine ⟨10961913826095404907674711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29231770202921079753799229 10961913826095404907674711)
          ·
            refine ⟨16442870739143107361512067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10961913826095404907674711 16442870739143107361512067)
            ·
              refine ⟨24664306108714661042268101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16442870739143107361512067 24664306108714661042268101)
              ·
                refine ⟨4624557395383998945425269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24664306108714661042268101 4624557395383998945425269)
                ·
                  refine ⟨433552255817249901133619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4624557395383998945425269 433552255817249901133619)
                  ·
                    rfl

theorem cell22_3799530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_3799530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799530 prefixEnd_3799530 := by exact prefixLift 3799530
  have htrace : WordTrace (prefixWord ++ tailWord_3799530) baseStart_3799530 baseEnd_3799530 := by
    simpa [prefixWord, tailWord_3799530, baseEnd_3799530] using wordTrace_append hprefix tailTrace_3799530
  have hstable : (prefixWord ++ tailWord_3799530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799530).length < 2 ^ (prefixWord ++ tailWord_3799530).sum := by decide
  have hdescent : baseEnd_3799530 < baseStart_3799530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799534 : List Nat := [4, 1, 2, 1, 2, 3, 1, 4, 1, 3]
def baseStart_3799534 : Nat := 118140960795 + 3799534 * 2 ^ 59
def prefixEnd_3799534 : Nat := 4983230072969 + 3 ^ 40 * 3799534 * 2
def baseEnd_3799534 : Nat := 1300658136733495026300845

theorem tailTrace_3799534 : CollatzResearch.WordTrace tailWord_3799534 prefixEnd_3799534 1300658136733495026300845 := by
  unfold tailWord_3799534
  simp only [CollatzResearch.WordTrace]
  refine ⟨17322548727118087698755707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92386926544629801060030437 17322548727118087698755707)
  ·
    refine ⟨25983823090677131548133561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17322548727118087698755707 25983823090677131548133561)
    ·
      refine ⟨19487867318007848661100171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25983823090677131548133561 19487867318007848661100171)
      ·
        refine ⟨29231800977011772991650257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19487867318007848661100171 29231800977011772991650257)
        ·
          refine ⟨21923850732758829743737693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29231800977011772991650257 21923850732758829743737693)
          ·
            refine ⟨8221444024784561153901635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21923850732758829743737693 8221444024784561153901635)
            ·
              refine ⟨12332166037176841730852453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8221444024784561153901635 12332166037176841730852453)
              ·
                refine ⟨2312281131970657824534835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12332166037176841730852453 2312281131970657824534835)
                ·
                  refine ⟨3468421697955986736802253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2312281131970657824534835 3468421697955986736802253)
                  ·
                    refine ⟨1300658136733495026300845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3468421697955986736802253 1300658136733495026300845)
                    ·
                      rfl

theorem cell22_3799534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_3799534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799534 prefixEnd_3799534 := by exact prefixLift 3799534
  have htrace : WordTrace (prefixWord ++ tailWord_3799534) baseStart_3799534 baseEnd_3799534 := by
    simpa [prefixWord, tailWord_3799534, baseEnd_3799534] using wordTrace_append hprefix tailTrace_3799534
  have hstable : (prefixWord ++ tailWord_3799534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799534).length < 2 ^ (prefixWord ++ tailWord_3799534).sum := by decide
  have hdescent : baseEnd_3799534 < baseStart_3799534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799560 : List Nat := [2, 1, 3, 2, 1, 1, 1, 6, 1, 4]
def baseStart_3799560 : Nat := 118140960795 + 3799560 * 2 ^ 59
def prefixEnd_3799560 : Nat := 4983230072969 + 3 ^ 40 * 3799560 * 2
def baseEnd_3799560 : Nat := 1300667037064839625150765

theorem tailTrace_3799560 : CollatzResearch.WordTrace tailWord_3799560 prefixEnd_3799560 1300667037064839625150765 := by
  unfold tailWord_3799560
  simp only [CollatzResearch.WordTrace]
  refine ⟨69290669057425254015246067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92387558743233672020328089 69290669057425254015246067)
  ·
    refine ⟨103936003586137881022869101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69290669057425254015246067 103936003586137881022869101)
    ·
      refine ⟨38976001344801705383575913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103936003586137881022869101 38976001344801705383575913)
      ·
        refine ⟨29232001008601279037681935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38976001344801705383575913 29232001008601279037681935)
        ·
          refine ⟨43848001512901918556522903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29232001008601279037681935 43848001512901918556522903)
          ·
            refine ⟨65772002269352877834784355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43848001512901918556522903 65772002269352877834784355)
            ·
              refine ⟨98658003404029316752176533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65772002269352877834784355 98658003404029316752176533)
              ·
                refine ⟨4624593909563874222758275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98658003404029316752176533 4624593909563874222758275)
                ·
                  refine ⟨6936890864345811334137413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4624593909563874222758275 6936890864345811334137413)
                  ·
                    refine ⟨1300667037064839625150765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6936890864345811334137413 1300667037064839625150765)
                    ·
                      rfl

theorem cell22_3799560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_3799560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799560 prefixEnd_3799560 := by exact prefixLift 3799560
  have htrace : WordTrace (prefixWord ++ tailWord_3799560) baseStart_3799560 baseEnd_3799560 := by
    simpa [prefixWord, tailWord_3799560, baseEnd_3799560] using wordTrace_append hprefix tailTrace_3799560
  have hstable : (prefixWord ++ tailWord_3799560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799560).length < 2 ^ (prefixWord ++ tailWord_3799560).sum := by decide
  have hdescent : baseEnd_3799560 < baseStart_3799560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799592 : List Nat := [2, 1, 5, 2, 1, 2, 2, 1, 6]
def baseStart_3799592 : Nat := 118140960795 + 3799592 * 2 ^ 59
def prefixEnd_3799592 : Nat := 4983230072969 + 3 ^ 40 * 3799592 * 2
def baseEnd_3799592 : Nat := 433559330439600736116889

theorem tailTrace_3799592 : CollatzResearch.WordTrace tailWord_3799592 prefixEnd_3799592 433559330439600736116889 := by
  unfold tailWord_3799592
  simp only [CollatzResearch.WordTrace]
  refine ⟨69291252625367288747828515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92388336833823051663771353 69291252625367288747828515)
  ·
    refine ⟨103936878938050933121742773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69291252625367288747828515 103936878938050933121742773)
    ·
      refine ⟨9744082400442274980163385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103936878938050933121742773 9744082400442274980163385)
      ·
        refine ⟨7308061800331706235122539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9744082400442274980163385 7308061800331706235122539)
        ·
          refine ⟨10962092700497559352683809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7308061800331706235122539 10962092700497559352683809)
          ·
            refine ⟨8221569525373169514512857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10962092700497559352683809 8221569525373169514512857)
            ·
              refine ⟨6166177144029877135884643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8221569525373169514512857 6166177144029877135884643)
              ·
                refine ⟨9249265716044815703826965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6166177144029877135884643 9249265716044815703826965)
                ·
                  refine ⟨433559330439600736116889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9249265716044815703826965 433559330439600736116889)
                  ·
                    rfl

theorem cell22_3799592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 6].length) (baseStart_3799592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799592 prefixEnd_3799592 := by exact prefixLift 3799592
  have htrace : WordTrace (prefixWord ++ tailWord_3799592) baseStart_3799592 baseEnd_3799592 := by
    simpa [prefixWord, tailWord_3799592, baseEnd_3799592] using wordTrace_append hprefix tailTrace_3799592
  have hstable : (prefixWord ++ tailWord_3799592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799592).length < 2 ^ (prefixWord ++ tailWord_3799592).sum := by decide
  have hdescent : baseEnd_3799592 < baseStart_3799592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799603 : List Nat := [1, 1, 1, 2, 4, 2, 2, 9]
def baseStart_3799603 : Nat := 118140960795 + 3799603 * 2 ^ 59
def prefixEnd_3799603 : Nat := 4983230072969 + 3 ^ 40 * 3799603 * 2
def baseEnd_3799603 : Nat := 144520195204844649591737

theorem tailTrace_3799603 : CollatzResearch.WordTrace tailWord_3799603 prefixEnd_3799603 144520195204844649591737 := by
  unfold tailWord_3799603
  simp only [CollatzResearch.WordTrace]
  refine ⟨138582906453694726374307463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92388604302463150916204975 138582906453694726374307463)
  ·
    refine ⟨207874359680542089561461195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138582906453694726374307463 207874359680542089561461195)
    ·
      refine ⟨311811539520813134342191793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207874359680542089561461195 311811539520813134342191793)
      ·
        refine ⟨233858654640609850756643845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311811539520813134342191793 233858654640609850756643845)
        ·
          refine ⟨43848497745114347016870721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233858654640609850756643845 43848497745114347016870721)
          ·
            refine ⟨32886373308835760262653041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43848497745114347016870721 32886373308835760262653041)
            ·
              refine ⟨24664779981626820196989781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32886373308835760262653041 24664779981626820196989781)
              ·
                refine ⟨144520195204844649591737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24664779981626820196989781 144520195204844649591737)
                ·
                  rfl

theorem cell22_3799603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 9].length) (baseStart_3799603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799603 prefixEnd_3799603 := by exact prefixLift 3799603
  have htrace : WordTrace (prefixWord ++ tailWord_3799603) baseStart_3799603 baseEnd_3799603 := by
    simpa [prefixWord, tailWord_3799603, baseEnd_3799603] using wordTrace_append hprefix tailTrace_3799603
  have hstable : (prefixWord ++ tailWord_3799603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799603).length < 2 ^ (prefixWord ++ tailWord_3799603).sum := by decide
  have hdescent : baseEnd_3799603 < baseStart_3799603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799742 : List Nat := [4, 2, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_3799742 : Nat := 118140960795 + 3799742 * 2 ^ 59
def prefixEnd_3799742 : Nat := 4983230072969 + 3 ^ 40 * 3799742 * 2
def baseEnd_3799742 : Nat := 1300729339384251817100207

theorem tailTrace_3799742 : CollatzResearch.WordTrace tailWord_3799742 prefixEnd_3799742 1300729339384251817100207 := by
  unfold tailWord_3799742
  simp only [CollatzResearch.WordTrace]
  refine ⟨17323497025023894139202185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92391984133460768742411653 17323497025023894139202185)
  ·
    refine ⟨12992622768767920604401639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17323497025023894139202185 12992622768767920604401639)
    ·
      refine ⟨19488934153151880906602459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12992622768767920604401639 19488934153151880906602459)
      ·
        refine ⟨29233401229727821359903689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19488934153151880906602459 29233401229727821359903689)
        ·
          refine ⟨21925050922295866019927767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29233401229727821359903689 21925050922295866019927767)
          ·
            refine ⟨32887576383443799029891651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21925050922295866019927767 32887576383443799029891651)
            ·
              refine ⟨49331364575165698544837477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32887576383443799029891651 49331364575165698544837477)
              ·
                refine ⟨9249630857843568477157027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49331364575165698544837477 9249630857843568477157027)
                ·
                  refine ⟨13874446286765352715735541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9249630857843568477157027 13874446286765352715735541)
                  ·
                    refine ⟨1300729339384251817100207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13874446286765352715735541 1300729339384251817100207)
                    ·
                      rfl

theorem cell22_3799742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_3799742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799742 prefixEnd_3799742 := by exact prefixLift 3799742
  have htrace : WordTrace (prefixWord ++ tailWord_3799742) baseStart_3799742 baseEnd_3799742 := by
    simpa [prefixWord, tailWord_3799742, baseEnd_3799742] using wordTrace_append hprefix tailTrace_3799742
  have hstable : (prefixWord ++ tailWord_3799742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799742).length < 2 ^ (prefixWord ++ tailWord_3799742).sum := by decide
  have hdescent : baseEnd_3799742 < baseStart_3799742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799744 : List Nat := [2, 1, 1, 2, 4, 3, 2, 3, 4]
def baseStart_3799744 : Nat := 118140960795 + 3799744 * 2 ^ 59
def prefixEnd_3799744 : Nat := 4983230072969 + 3 ^ 40 * 3799744 * 2
def baseEnd_3799744 : Nat := 433576674675041492850067

theorem tailTrace_3799744 : CollatzResearch.WordTrace tailWord_3799744 prefixEnd_3799744 433576674675041492850067 := by
  unfold tailWord_3799744
  simp only [CollatzResearch.WordTrace]
  refine ⟨69294024573091953727595143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92392032764122604970126857 69294024573091953727595143)
  ·
    refine ⟨103941036859637930591392715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69294024573091953727595143 103941036859637930591392715)
    ·
      refine ⟨155911555289456895887089073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103941036859637930591392715 155911555289456895887089073)
      ·
        refine ⟨116933666467092671915316805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155911555289456895887089073 116933666467092671915316805)
        ·
          refine ⟨21925062462579875984121901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116933666467092671915316805 21925062462579875984121901)
          ·
            refine ⟨8221898423467453494045713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21925062462579875984121901 8221898423467453494045713)
            ·
              refine ⟨6166423817600590120534285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8221898423467453494045713 6166423817600590120534285)
              ·
                refine ⟨2312408931600221295200357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6166423817600590120534285 2312408931600221295200357)
                ·
                  refine ⟨433576674675041492850067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2312408931600221295200357 433576674675041492850067)
                  ·
                    rfl

theorem cell22_3799744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 4].length) (baseStart_3799744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799744 prefixEnd_3799744 := by exact prefixLift 3799744
  have htrace : WordTrace (prefixWord ++ tailWord_3799744) baseStart_3799744 baseEnd_3799744 := by
    simpa [prefixWord, tailWord_3799744, baseEnd_3799744] using wordTrace_append hprefix tailTrace_3799744
  have hstable : (prefixWord ++ tailWord_3799744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799744).length < 2 ^ (prefixWord ++ tailWord_3799744).sum := by decide
  have hdescent : baseEnd_3799744 < baseStart_3799744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799750 : List Nat := [6, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_3799750 : Nat := 118140960795 + 3799750 * 2 ^ 59
def prefixEnd_3799750 : Nat := 4983230072969 + 3 ^ 40 * 3799750 * 2
def baseEnd_3799750 : Nat := 433577359315914154300061

theorem tailTrace_3799750 : CollatzResearch.WordTrace tailWord_3799750 prefixEnd_3799750 433577359315914154300061 := by
  unfold tailWord_3799750
  simp only [CollatzResearch.WordTrace]
  refine ⟨4330883374505067827497147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92392178656108113653272469 4330883374505067827497147)
  ·
    refine ⟨6496325061757601741245721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4330883374505067827497147 6496325061757601741245721)
    ·
      refine ⟨4872243796318201305934291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6496325061757601741245721 4872243796318201305934291)
      ·
        refine ⟨7308365694477301958901437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4872243796318201305934291 7308365694477301958901437)
        ·
          refine ⟨2740637135428988234588039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7308365694477301958901437 2740637135428988234588039)
          ·
            refine ⟨4110955703143482351882059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2740637135428988234588039 4110955703143482351882059)
            ·
              refine ⟨6166433554715223527823089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4110955703143482351882059 6166433554715223527823089)
              ·
                refine ⟨4624825166036417645867317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6166433554715223527823089 4624825166036417645867317)
                ·
                  refine ⟨433577359315914154300061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4624825166036417645867317 433577359315914154300061)
                  ·
                    rfl

theorem cell22_3799750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_3799750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799750 prefixEnd_3799750 := by exact prefixLift 3799750
  have htrace : WordTrace (prefixWord ++ tailWord_3799750) baseStart_3799750 baseEnd_3799750 := by
    simpa [prefixWord, tailWord_3799750, baseEnd_3799750] using wordTrace_append hprefix tailTrace_3799750
  have hstable : (prefixWord ++ tailWord_3799750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799750).length < 2 ^ (prefixWord ++ tailWord_3799750).sum := by decide
  have hdescent : baseEnd_3799750 < baseStart_3799750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799785 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 2, 6]
def baseStart_3799785 : Nat := 118140960795 + 3799785 * 2 ^ 59
def prefixEnd_3799785 : Nat := 4983230072969 + 3 ^ 40 * 3799785 * 2
def baseEnd_3799785 : Nat := 1300744059163014038275075

theorem tailTrace_3799785 : CollatzResearch.WordTrace tailWord_3799785 prefixEnd_3799785 1300744059163014038275075 := by
  unfold tailWord_3799785
  simp only [CollatzResearch.WordTrace]
  refine ⟨138589544539035371457432809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92393029692690247638288539 138589544539035371457432809)
  ·
    refine ⟨103942158404276528593074607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138589544539035371457432809 103942158404276528593074607)
    ·
      refine ⟨155913237606414792889611911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103942158404276528593074607 155913237606414792889611911)
      ·
        refine ⟨233869856409622189334417867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155913237606414792889611911 233869856409622189334417867)
        ·
          refine ⟨350804784614433284001626801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233869856409622189334417867 350804784614433284001626801)
          ·
            refine ⟨263103588460824963001220101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350804784614433284001626801 263103588460824963001220101)
            ·
              refine ⟨49331922836404680562728769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 263103588460824963001220101 49331922836404680562728769)
              ·
                refine ⟨36998942127303510422046577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49331922836404680562728769 36998942127303510422046577)
                ·
                  refine ⟨27749206595477632816534933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36998942127303510422046577 27749206595477632816534933)
                  ·
                    refine ⟨1300744059163014038275075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27749206595477632816534933 1300744059163014038275075)
                    ·
                      rfl

theorem cell22_3799785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_3799785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799785 prefixEnd_3799785 := by exact prefixLift 3799785
  have htrace : WordTrace (prefixWord ++ tailWord_3799785) baseStart_3799785 baseEnd_3799785 := by
    simpa [prefixWord, tailWord_3799785, baseEnd_3799785] using wordTrace_append hprefix tailTrace_3799785
  have hstable : (prefixWord ++ tailWord_3799785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799785).length < 2 ^ (prefixWord ++ tailWord_3799785).sum := by decide
  have hdescent : baseEnd_3799785 < baseStart_3799785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799800 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 9]
def baseStart_3799800 : Nat := 118140960795 + 3799800 * 2 ^ 59
def prefixEnd_3799800 : Nat := 4983230072969 + 3 ^ 40 * 3799800 * 2
def baseEnd_3799800 : Nat := 433583064656519666383343

theorem tailTrace_3799800 : CollatzResearch.WordTrace tailWord_3799800 prefixEnd_3799800 433583064656519666383343 := by
  unfold tailWord_3799800
  simp only [CollatzResearch.WordTrace]
  refine ⟨69295045816990514509614427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92393394422654019346152569 69295045816990514509614427)
  ·
    refine ⟨103942568725485771764421641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69295045816990514509614427 103942568725485771764421641)
    ·
      refine ⟨77956926544114328823316231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103942568725485771764421641 77956926544114328823316231)
      ·
        refine ⟨116935389816171493234974347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77956926544114328823316231 116935389816171493234974347)
        ·
          refine ⟨175403084724257239852461521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116935389816171493234974347 175403084724257239852461521)
          ·
            refine ⟨131552313543192929889346141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175403084724257239852461521 131552313543192929889346141)
            ·
              refine ⟨49332117578697348708504803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131552313543192929889346141 49332117578697348708504803)
              ·
                refine ⟨73998176368046023062757205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49332117578697348708504803 73998176368046023062757205)
                ·
                  refine ⟨433583064656519666383343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73998176368046023062757205 433583064656519666383343)
                  ·
                    rfl

theorem cell22_3799800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 9].length) (baseStart_3799800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799800 prefixEnd_3799800 := by exact prefixLift 3799800
  have htrace : WordTrace (prefixWord ++ tailWord_3799800) baseStart_3799800 baseEnd_3799800 := by
    simpa [prefixWord, tailWord_3799800, baseEnd_3799800] using wordTrace_append hprefix tailTrace_3799800
  have hstable : (prefixWord ++ tailWord_3799800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799800).length < 2 ^ (prefixWord ++ tailWord_3799800).sum := by decide
  have hdescent : baseEnd_3799800 < baseStart_3799800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799909 : List Nat := [1, 3, 1, 3, 1, 1, 5, 1, 2, 4]
def baseStart_3799909 : Nat := 118140960795 + 3799909 * 2 ^ 59
def prefixEnd_3799909 : Nat := 4983230072969 + 3 ^ 40 * 3799909 * 2
def baseEnd_3799909 : Nat := 1300786506897119048174695

theorem tailTrace_3799909 : CollatzResearch.WordTrace tailWord_3799909 prefixEnd_3799909 1300786506897119048174695 := by
  unfold tailWord_3799909
  simp only [CollatzResearch.WordTrace]
  refine ⟨138594067190586140634946781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92396044793724093756631187 138594067190586140634946781)
  ·
    refine ⟨51972775196469802738105043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138594067190586140634946781 51972775196469802738105043)
    ·
      refine ⟨77959162794704704107157565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51972775196469802738105043 77959162794704704107157565)
      ·
        refine ⟨29234686048014264040184087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77959162794704704107157565 29234686048014264040184087)
        ·
          refine ⟨43852029072021396060276131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29234686048014264040184087 43852029072021396060276131)
          ·
            refine ⟨65778043608032094090414197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43852029072021396060276131 65778043608032094090414197)
            ·
              refine ⟨6166691588253008820976331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65778043608032094090414197 6166691588253008820976331)
              ·
                refine ⟨9250037382379513231464497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6166691588253008820976331 9250037382379513231464497)
                ·
                  refine ⟨6937528036784634923598373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9250037382379513231464497 6937528036784634923598373)
                  ·
                    refine ⟨1300786506897119048174695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6937528036784634923598373 1300786506897119048174695)
                    ·
                      rfl

theorem cell22_3799909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_3799909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799909 prefixEnd_3799909 := by exact prefixLift 3799909
  have htrace : WordTrace (prefixWord ++ tailWord_3799909) baseStart_3799909 baseEnd_3799909 := by
    simpa [prefixWord, tailWord_3799909, baseEnd_3799909] using wordTrace_append hprefix tailTrace_3799909
  have hstable : (prefixWord ++ tailWord_3799909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799909).length < 2 ^ (prefixWord ++ tailWord_3799909).sum := by decide
  have hdescent : baseEnd_3799909 < baseStart_3799909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799956 : List Nat := [2, 4, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_3799956 : Nat := 118140960795 + 3799956 * 2 ^ 59
def prefixEnd_3799956 : Nat := 4983230072969 + 3 ^ 40 * 3799956 * 2
def baseEnd_3799956 : Nat := 1300802595957626592249551

theorem tailTrace_3799956 : CollatzResearch.WordTrace tailWord_3799956 prefixEnd_3799956 1300802595957626592249551 := by
  unfold tailWord_3799956
  simp only [CollatzResearch.WordTrace]
  refine ⟨69297890710707933830953861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92397187614277245107938481 69297890710707933830953861)
  ·
    refine ⟨12993354508257737593303849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69297890710707933830953861 12993354508257737593303849)
    ·
      refine ⟨9745015881193303194977887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12993354508257737593303849 9745015881193303194977887)
      ·
        refine ⟨14617523821789954792466831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9745015881193303194977887 14617523821789954792466831)
        ·
          refine ⟨21926285732684932188700247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14617523821789954792466831 21926285732684932188700247)
          ·
            refine ⟨32889428599027398283050371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21926285732684932188700247 32889428599027398283050371)
            ·
              refine ⟨49334142898541097424575557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32889428599027398283050371 49334142898541097424575557)
              ·
                refine ⟨9250151793476455767107917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49334142898541097424575557 9250151793476455767107917)
                ·
                  refine ⟨3468806922553670912665469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9250151793476455767107917 3468806922553670912665469)
                  ·
                    refine ⟨1300802595957626592249551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3468806922553670912665469 1300802595957626592249551)
                    ·
                      rfl

theorem cell22_3799956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_3799956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799956 prefixEnd_3799956 := by exact prefixLift 3799956
  have htrace : WordTrace (prefixWord ++ tailWord_3799956) baseStart_3799956 baseEnd_3799956 := by
    simpa [prefixWord, tailWord_3799956, baseEnd_3799956] using wordTrace_append hprefix tailTrace_3799956
  have hstable : (prefixWord ++ tailWord_3799956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799956).length < 2 ^ (prefixWord ++ tailWord_3799956).sum := by decide
  have hdescent : baseEnd_3799956 < baseStart_3799956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799958 : List Nat := [5, 3, 1, 1, 1, 2, 1, 8]
def baseStart_3799958 : Nat := 118140960795 + 3799958 * 2 ^ 59
def prefixEnd_3799958 : Nat := 4983230072969 + 3 ^ 40 * 3799958 * 2
def baseEnd_3799958 : Nat := 144533697844277694855505

theorem tailTrace_3799958 : CollatzResearch.WordTrace tailWord_3799958 prefixEnd_3799958 144533697844277694855505 := by
  unfold tailWord_3799958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8662240897963038875217533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92397236244939081335653685 8662240897963038875217533)
  ·
    refine ⟨3248340336736139578206575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8662240897963038875217533 3248340336736139578206575)
    ·
      refine ⟨4872510505104209367309863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3248340336736139578206575 4872510505104209367309863)
      ·
        refine ⟨7308765757656314050964795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4872510505104209367309863 7308765757656314050964795)
        ·
          refine ⟨10963148636484471076447193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7308765757656314050964795 10963148636484471076447193)
          ·
            refine ⟨8222361477363353307335395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10963148636484471076447193 8222361477363353307335395)
            ·
              refine ⟨12333542216045029961003093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8222361477363353307335395 12333542216045029961003093)
              ·
                refine ⟨144533697844277694855505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12333542216045029961003093 144533697844277694855505)
                ·
                  rfl

theorem cell22_3799958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_3799958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799958 prefixEnd_3799958 := by exact prefixLift 3799958
  have htrace : WordTrace (prefixWord ++ tailWord_3799958) baseStart_3799958 baseEnd_3799958 := by
    simpa [prefixWord, tailWord_3799958, baseEnd_3799958] using wordTrace_append hprefix tailTrace_3799958
  have hstable : (prefixWord ++ tailWord_3799958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799958).length < 2 ^ (prefixWord ++ tailWord_3799958).sum := by decide
  have hdescent : baseEnd_3799958 < baseStart_3799958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3799969 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 7]
def baseStart_3799969 : Nat := 118140960795 + 3799969 * 2 ^ 59
def prefixEnd_3799969 : Nat := 4983230072969 + 3 ^ 40 * 3799969 * 2
def baseEnd_3799969 : Nat := 433602348707766297224837

theorem tailTrace_3799969 : CollatzResearch.WordTrace tailWord_3799969 prefixEnd_3799969 433602348707766297224837 := by
  unfold tailWord_3799969
  simp only [CollatzResearch.WordTrace]
  refine ⟨138596255570368770882130961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92397503713579180588087307 138596255570368770882130961)
  ·
    refine ⟨103947191677776578161598221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138596255570368770882130961 103947191677776578161598221)
    ·
      refine ⟨38980196879166216810599333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103947191677776578161598221 38980196879166216810599333)
      ·
        refine ⟨7308786914843665651987375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38980196879166216810599333 7308786914843665651987375)
        ·
          refine ⟨10963180372265498477981063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7308786914843665651987375 10963180372265498477981063)
          ·
            refine ⟨16444770558398247716971595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10963180372265498477981063 16444770558398247716971595)
            ·
              refine ⟨24667155837597371575457393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16444770558398247716971595 24667155837597371575457393)
              ·
                refine ⟨18500366878198028681593045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24667155837597371575457393 18500366878198028681593045)
                ·
                  refine ⟨433602348707766297224837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18500366878198028681593045 433602348707766297224837)
                  ·
                    rfl

theorem cell22_3799969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 7].length) (baseStart_3799969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3799969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3799969 prefixEnd_3799969 := by exact prefixLift 3799969
  have htrace : WordTrace (prefixWord ++ tailWord_3799969) baseStart_3799969 baseEnd_3799969 := by
    simpa [prefixWord, tailWord_3799969, baseEnd_3799969] using wordTrace_append hprefix tailTrace_3799969
  have hstable : (prefixWord ++ tailWord_3799969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3799969).length < 2 ^ (prefixWord ++ tailWord_3799969).sum := by decide
  have hdescent : baseEnd_3799969 < baseStart_3799969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3799969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800027 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 1, 12]
def baseStart_3800027 : Nat := 118140960795 + 3800027 * 2 ^ 59
def prefixEnd_3800027 : Nat := 4983230072969 + 3 ^ 40 * 3800027 * 2
def baseEnd_3800027 : Nat := 1300826900708606073724333

theorem tailTrace_3800027 : CollatzResearch.WordTrace tailWord_3800027 prefixEnd_3800027 1300826900708606073724333 := by
  unfold tailWord_3800027
  simp only [CollatzResearch.WordTrace]
  refine ⟨138598371004158646787742335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92398914002772431191828223 138598371004158646787742335)
  ·
    refine ⟨207897556506237970181613503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138598371004158646787742335 207897556506237970181613503)
    ·
      refine ⟨311846334759356955272420255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207897556506237970181613503 311846334759356955272420255)
      ·
        refine ⟨467769502139035432908630383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311846334759356955272420255 467769502139035432908630383)
        ·
          refine ⟨701654253208553149362945575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467769502139035432908630383 701654253208553149362945575)
          ·
            refine ⟨1052481379812829724044418363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701654253208553149362945575 1052481379812829724044418363)
            ·
              refine ⟨1578722069719244586066627545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052481379812829724044418363 1578722069719244586066627545)
              ·
                refine ⟨1184041552289433439549970659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1578722069719244586066627545 1184041552289433439549970659)
                ·
                  refine ⟨1776062328434150159324955989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1184041552289433439549970659 1776062328434150159324955989)
                  ·
                    refine ⟨1300826900708606073724333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1776062328434150159324955989 1300826900708606073724333)
                    ·
                      rfl

theorem cell22_3800027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 12].length) (baseStart_3800027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800027 prefixEnd_3800027 := by exact prefixLift 3800027
  have htrace : WordTrace (prefixWord ++ tailWord_3800027) baseStart_3800027 baseEnd_3800027 := by
    simpa [prefixWord, tailWord_3800027, baseEnd_3800027] using wordTrace_append hprefix tailTrace_3800027
  have hstable : (prefixWord ++ tailWord_3800027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800027).length < 2 ^ (prefixWord ++ tailWord_3800027).sum := by decide
  have hdescent : baseEnd_3800027 < baseStart_3800027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800052 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_3800052 : Nat := 118140960795 + 3800052 * 2 ^ 59
def prefixEnd_3800052 : Nat := 4983230072969 + 3 ^ 40 * 3800052 * 2
def baseEnd_3800052 : Nat := 1300835458719514341849257

theorem tailTrace_3800052 : CollatzResearch.WordTrace tailWord_3800052 prefixEnd_3800052 1300835458719514341849257 := by
  unfold tailWord_3800052
  simp only [CollatzResearch.WordTrace]
  refine ⟨69299641414534038028701205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92399521886045384038268273 69299641414534038028701205)
  ·
    refine ⟨3248420691306283032595369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69299641414534038028701205 3248420691306283032595369)
    ·
      refine ⟨2436315518479712274446527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3248420691306283032595369 2436315518479712274446527)
      ·
        refine ⟨3654473277719568411669791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2436315518479712274446527 3654473277719568411669791)
        ·
          refine ⟨5481709916579352617504687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3654473277719568411669791 5481709916579352617504687)
          ·
            refine ⟨8222564874869028926257031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5481709916579352617504687 8222564874869028926257031)
            ·
              refine ⟨12333847312303543389385547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8222564874869028926257031 12333847312303543389385547)
              ·
                refine ⟨18500770968455315084078321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12333847312303543389385547 18500770968455315084078321)
                ·
                  refine ⟨13875578226341486313058741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18500770968455315084078321 13875578226341486313058741)
                  ·
                    refine ⟨1300835458719514341849257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13875578226341486313058741 1300835458719514341849257)
                    ·
                      rfl

theorem cell22_3800052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_3800052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800052 prefixEnd_3800052 := by exact prefixLift 3800052
  have htrace : WordTrace (prefixWord ++ tailWord_3800052) baseStart_3800052 baseEnd_3800052 := by
    simpa [prefixWord, tailWord_3800052, baseEnd_3800052] using wordTrace_append hprefix tailTrace_3800052
  have hstable : (prefixWord ++ tailWord_3800052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800052).length < 2 ^ (prefixWord ++ tailWord_3800052).sum := by decide
  have hdescent : baseEnd_3800052 < baseStart_3800052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800076 : List Nat := [2, 2, 1, 2, 3, 3, 3, 6]
def baseStart_3800076 : Nat := 118140960795 + 3800076 * 2 ^ 59
def prefixEnd_3800076 : Nat := 4983230072969 + 3 ^ 40 * 3800076 * 2
def baseEnd_3800076 : Nat := 144538186045554031027687

theorem tailTrace_3800076 : CollatzResearch.WordTrace tailWord_3800076 prefixEnd_3800076 144538186045554031027687 := by
  unfold tailWord_3800076
  simp only [CollatzResearch.WordTrace]
  refine ⟨69300079090490564078138041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92400105453987418770850721 69300079090490564078138041)
  ·
    refine ⟨51975059317867923058603531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69300079090490564078138041 51975059317867923058603531)
    ·
      refine ⟨77962588976801884587905297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51975059317867923058603531 77962588976801884587905297)
      ·
        refine ⟨58471941732601413440928973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77962588976801884587905297 58471941732601413440928973)
        ·
          refine ⟨21926978149725530040348365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58471941732601413440928973 21926978149725530040348365)
          ·
            refine ⟨8222616806147073765130637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21926978149725530040348365 8222616806147073765130637)
            ·
              refine ⟨3083481302305152661923989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8222616806147073765130637 3083481302305152661923989)
              ·
                refine ⟨144538186045554031027687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3083481302305152661923989 144538186045554031027687)
                ·
                  rfl

theorem cell22_3800076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 6].length) (baseStart_3800076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800076 prefixEnd_3800076 := by exact prefixLift 3800076
  have htrace : WordTrace (prefixWord ++ tailWord_3800076) baseStart_3800076 baseEnd_3800076 := by
    simpa [prefixWord, tailWord_3800076, baseEnd_3800076] using wordTrace_append hprefix tailTrace_3800076
  have hstable : (prefixWord ++ tailWord_3800076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800076).length < 2 ^ (prefixWord ++ tailWord_3800076).sum := by decide
  have hdescent : baseEnd_3800076 < baseStart_3800076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800078 : List Nat := [4, 1, 1, 2, 2, 4, 1, 1, 2, 4]
def baseStart_3800078 : Nat := 118140960795 + 3800078 * 2 ^ 59
def prefixEnd_3800078 : Nat := 4983230072969 + 3 ^ 40 * 3800078 * 2
def baseEnd_3800078 : Nat := 1300844359050858940699177

theorem tailTrace_3800078 : CollatzResearch.WordTrace tailWord_3800078 prefixEnd_3800078 1300844359050858940699177 := by
  unfold tailWord_3800078
  simp only [CollatzResearch.WordTrace]
  refine ⟨17325028890871735312231111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92400154084649254998565925 17325028890871735312231111)
  ·
    refine ⟨25987543336307602968346667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17325028890871735312231111 25987543336307602968346667)
    ·
      refine ⟨38981315004461404452520001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25987543336307602968346667 38981315004461404452520001)
      ·
        refine ⟨29235986253346053339390001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38981315004461404452520001 29235986253346053339390001)
        ·
          refine ⟨21926989690009540004542501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29235986253346053339390001 21926989690009540004542501)
          ·
            refine ⟨4111310566876788750851719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21926989690009540004542501 4111310566876788750851719)
            ·
              refine ⟨6166965850315183126277579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4111310566876788750851719 6166965850315183126277579)
              ·
                refine ⟨9250448775472774689416369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6166965850315183126277579 9250448775472774689416369)
                ·
                  refine ⟨6937836581604581017062277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9250448775472774689416369 6937836581604581017062277)
                  ·
                    refine ⟨1300844359050858940699177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6937836581604581017062277 1300844359050858940699177)
                    ·
                      rfl

theorem cell22_3800078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_3800078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800078 prefixEnd_3800078 := by exact prefixLift 3800078
  have htrace : WordTrace (prefixWord ++ tailWord_3800078) baseStart_3800078 baseEnd_3800078 := by
    simpa [prefixWord, tailWord_3800078, baseEnd_3800078] using wordTrace_append hprefix tailTrace_3800078
  have hstable : (prefixWord ++ tailWord_3800078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800078).length < 2 ^ (prefixWord ++ tailWord_3800078).sum := by decide
  have hdescent : baseEnd_3800078 < baseStart_3800078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800108 : List Nat := [2, 2, 1, 1, 1, 2, 3, 6, 1, 3]
def baseStart_3800108 : Nat := 118140960795 + 3800108 * 2 ^ 59
def prefixEnd_3800108 : Nat := 4983230072969 + 3 ^ 40 * 3800108 * 2
def baseEnd_3800108 : Nat := 1300854628663948862449085

theorem tailTrace_3800108 : CollatzResearch.WordTrace tailWord_3800108 prefixEnd_3800108 1300854628663948862449085 := by
  unfold tailWord_3800108
  simp only [CollatzResearch.WordTrace]
  refine ⟨69300662658432598810720489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92400883544576798414293985 69300662658432598810720489)
  ·
    refine ⟨51975496993824449108040367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69300662658432598810720489 51975496993824449108040367)
    ·
      refine ⟨77963245490736673662060551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51975496993824449108040367 77963245490736673662060551)
      ·
        refine ⟨116944868236105010493090827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77963245490736673662060551 116944868236105010493090827)
        ·
          refine ⟨175417302354157515739636241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116944868236105010493090827 175417302354157515739636241)
          ·
            refine ⟨131562976765618136804727181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175417302354157515739636241 131562976765618136804727181)
            ·
              refine ⟨49336116287106801301772693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131562976765618136804727181 49336116287106801301772693)
              ·
                refine ⟨2312630450958131311020595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49336116287106801301772693 2312630450958131311020595)
                ·
                  refine ⟨3468945676437196966530893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2312630450958131311020595 3468945676437196966530893)
                  ·
                    refine ⟨1300854628663948862449085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3468945676437196966530893 1300854628663948862449085)
                    ·
                      rfl

theorem cell22_3800108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 1, 3].length) (baseStart_3800108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800108 prefixEnd_3800108 := by exact prefixLift 3800108
  have htrace : WordTrace (prefixWord ++ tailWord_3800108) baseStart_3800108 baseEnd_3800108 := by
    simpa [prefixWord, tailWord_3800108, baseEnd_3800108] using wordTrace_append hprefix tailTrace_3800108
  have hstable : (prefixWord ++ tailWord_3800108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800108).length < 2 ^ (prefixWord ++ tailWord_3800108).sum := by decide
  have hdescent : baseEnd_3800108 < baseStart_3800108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800185 : List Nat := [1, 2, 1, 3, 5, 2, 1, 2, 1, 4]
def baseStart_3800185 : Nat := 118140960795 + 3800185 * 2 ^ 59
def prefixEnd_3800185 : Nat := 4983230072969 + 3 ^ 40 * 3800185 * 2
def baseEnd_3800185 : Nat := 1300880987337546328273849

theorem tailTrace_3800185 : CollatzResearch.WordTrace tailWord_3800185 prefixEnd_3800185 1300880987337546328273849 := by
  unfold tailWord_3800185
  simp only [CollatzResearch.WordTrace]
  refine ⟨138604133737586239771994009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92402755825057493181329339 138604133737586239771994009)
  ·
    refine ⟨103953100303189679828995507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138604133737586239771994009 103953100303189679828995507)
    ·
      refine ⟨155929650454784519743493261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103953100303189679828995507 155929650454784519743493261)
      ·
        refine ⟨58473618920544194903809973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155929650454784519743493261 58473618920544194903809973)
        ·
          refine ⟨5481901773801018272232185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58473618920544194903809973 5481901773801018272232185)
          ·
            refine ⟨4111426330350763704174139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5481901773801018272232185 4111426330350763704174139)
            ·
              refine ⟨6167139495526145556261209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4111426330350763704174139 6167139495526145556261209)
              ·
                refine ⟨4625354621644609167195907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6167139495526145556261209 4625354621644609167195907)
                ·
                  refine ⟨6938031932466913750793861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4625354621644609167195907 6938031932466913750793861)
                  ·
                    refine ⟨1300880987337546328273849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6938031932466913750793861 1300880987337546328273849)
                    ·
                      rfl

theorem cell22_3800185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 4].length) (baseStart_3800185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800185 prefixEnd_3800185 := by exact prefixLift 3800185
  have htrace : WordTrace (prefixWord ++ tailWord_3800185) baseStart_3800185 baseEnd_3800185 := by
    simpa [prefixWord, tailWord_3800185, baseEnd_3800185] using wordTrace_append hprefix tailTrace_3800185
  have hstable : (prefixWord ++ tailWord_3800185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800185).length < 2 ^ (prefixWord ++ tailWord_3800185).sum := by decide
  have hdescent : baseEnd_3800185 < baseStart_3800185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800215 : List Nat := [1, 1, 3, 3, 3, 2, 2, 2, 2, 3]
def baseStart_3800215 : Nat := 118140960795 + 3800215 * 2 ^ 59
def prefixEnd_3800215 : Nat := 4983230072969 + 3 ^ 40 * 3800215 * 2
def baseEnd_3800215 : Nat := 1300891256950636250023757

theorem tailTrace_3800215 : CollatzResearch.WordTrace tailWord_3800215 prefixEnd_3800215 1300891256950636250023757 := by
  unfold tailWord_3800215
  simp only [CollatzResearch.WordTrace]
  refine ⟨138605227927477554895586099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92403485284985036597057399 138605227927477554895586099)
  ·
    refine ⟨207907841891216332343379149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138605227927477554895586099 207907841891216332343379149)
    ·
      refine ⟨77965440709206124628767181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207907841891216332343379149 77965440709206124628767181)
      ·
        refine ⟨29237040265952296735787693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77965440709206124628767181 29237040265952296735787693)
        ·
          refine ⟨10963890099732111275920385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29237040265952296735787693 10963890099732111275920385)
          ·
            refine ⟨8222917574799083456940289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10963890099732111275920385 8222917574799083456940289)
            ·
              refine ⟨6167188181099312592705217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8222917574799083456940289 6167188181099312592705217)
              ·
                refine ⟨4625391135824484444528913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6167188181099312592705217 4625391135824484444528913)
                ·
                  refine ⟨3469043351868363333396685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4625391135824484444528913 3469043351868363333396685)
                  ·
                    refine ⟨1300891256950636250023757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3469043351868363333396685 1300891256950636250023757)
                    ·
                      rfl

theorem cell22_3800215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_3800215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800215 prefixEnd_3800215 := by exact prefixLift 3800215
  have htrace : WordTrace (prefixWord ++ tailWord_3800215) baseStart_3800215 baseEnd_3800215 := by
    simpa [prefixWord, tailWord_3800215, baseEnd_3800215] using wordTrace_append hprefix tailTrace_3800215
  have hstable : (prefixWord ++ tailWord_3800215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800215).length < 2 ^ (prefixWord ++ tailWord_3800215).sum := by decide
  have hdescent : baseEnd_3800215 < baseStart_3800215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800228 : List Nat := [2, 3, 1, 2, 3, 3, 1, 7]
def baseStart_3800228 : Nat := 118140960795 + 3800228 * 2 ^ 59
def prefixEnd_3800228 : Nat := 4983230072969 + 3 ^ 40 * 3800228 * 2
def baseEnd_3800228 : Nat := 144543967457367616605413

theorem tailTrace_3800228 : CollatzResearch.WordTrace tailWord_3800228 prefixEnd_3800228 144543967457367616605413 := by
  unfold tailWord_3800228
  simp only [CollatzResearch.WordTrace]
  refine ⟨69302851038215229057904669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92403801384286972077206225 69302851038215229057904669)
  ·
    refine ⟨25988569139330710896714251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69302851038215229057904669 25988569139330710896714251)
    ·
      refine ⟨38982853708996066345071377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25988569139330710896714251 38982853708996066345071377)
      ·
        refine ⟨29237140281747049758803533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38982853708996066345071377 29237140281747049758803533)
        ·
          refine ⟨10963927605655143659551325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29237140281747049758803533 10963927605655143659551325)
          ·
            refine ⟨4111472852120678872331747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10963927605655143659551325 4111472852120678872331747)
            ·
              refine ⟨6167209278181018308497621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4111472852120678872331747 6167209278181018308497621)
              ·
                refine ⟨144543967457367616605413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6167209278181018308497621 144543967457367616605413)
                ·
                  rfl

theorem cell22_3800228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 7].length) (baseStart_3800228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800228 prefixEnd_3800228 := by exact prefixLift 3800228
  have htrace : WordTrace (prefixWord ++ tailWord_3800228) baseStart_3800228 baseEnd_3800228 := by
    simpa [prefixWord, tailWord_3800228, baseEnd_3800228] using wordTrace_append hprefix tailTrace_3800228
  have hstable : (prefixWord ++ tailWord_3800228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800228).length < 2 ^ (prefixWord ++ tailWord_3800228).sum := by decide
  have hdescent : baseEnd_3800228 < baseStart_3800228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800262 : List Nat := [6, 1, 2, 2, 1, 1, 9]
def baseStart_3800262 : Nat := 118140960795 + 3800262 * 2 ^ 59
def prefixEnd_3800262 : Nat := 4983230072969 + 3 ^ 40 * 3800262 * 2
def baseEnd_3800262 : Nat := 48181753555968288670319

theorem tailTrace_3800262 : CollatzResearch.WordTrace tailWord_3800262 prefixEnd_3800262 48181753555968288670319 := by
  unfold tailWord_3800262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4331466942447102560079595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92404628105538187948364693 4331466942447102560079595)
  ·
    refine ⟨6497200413670653840119393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4331466942447102560079595 6497200413670653840119393)
    ·
      refine ⟨4872900310252990380089545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6497200413670653840119393 4872900310252990380089545)
      ·
        refine ⟨3654675232689742785067159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4872900310252990380089545 3654675232689742785067159)
        ·
          refine ⟨5482012849034614177600739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3654675232689742785067159 5482012849034614177600739)
          ·
            refine ⟨8223019273551921266401109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5482012849034614177600739 8223019273551921266401109)
            ·
              refine ⟨48181753555968288670319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8223019273551921266401109 48181753555968288670319)
              ·
                rfl

theorem cell22_3800262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 9].length) (baseStart_3800262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800262 prefixEnd_3800262 := by exact prefixLift 3800262
  have htrace : WordTrace (prefixWord ++ tailWord_3800262) baseStart_3800262 baseEnd_3800262 := by
    simpa [prefixWord, tailWord_3800262, baseEnd_3800262] using wordTrace_append hprefix tailTrace_3800262
  have hstable : (prefixWord ++ tailWord_3800262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800262).length < 2 ^ (prefixWord ++ tailWord_3800262).sum := by decide
  have hdescent : baseEnd_3800262 < baseStart_3800262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800277 : List Nat := [1, 3, 2, 4, 1, 1, 2, 4, 1, 3]
def baseStart_3800277 : Nat := 118140960795 + 3800277 * 2 ^ 59
def prefixEnd_3800277 : Nat := 4983230072969 + 3 ^ 40 * 3800277 * 2
def baseEnd_3800277 : Nat := 1300912480817688754973567

theorem tailTrace_3800277 : CollatzResearch.WordTrace tailWord_3800277 prefixEnd_3800277 1300912480817688754973567 := by
  unfold tailWord_3800277
  simp only [CollatzResearch.WordTrace]
  refine ⟨138607489253252939484343085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92404992835501959656228723 138607489253252939484343085)
  ·
    refine ⟨51977808469969852306628657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138607489253252939484343085 51977808469969852306628657)
    ·
      refine ⟨38983356352477389229971493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51977808469969852306628657 38983356352477389229971493)
      ·
        refine ⟨7309379316089510480619655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38983356352477389229971493 7309379316089510480619655)
        ·
          refine ⟨10964068974134265720929483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7309379316089510480619655 10964068974134265720929483)
          ·
            refine ⟨16446103461201398581394225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10964068974134265720929483 16446103461201398581394225)
            ·
              refine ⟨12334577595901048936045669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16446103461201398581394225 12334577595901048936045669)
              ·
                refine ⟨2312733299231446675508563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12334577595901048936045669 2312733299231446675508563)
                ·
                  refine ⟨3469099948847170013262845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2312733299231446675508563 3469099948847170013262845)
                  ·
                    refine ⟨1300912480817688754973567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3469099948847170013262845 1300912480817688754973567)
                    ·
                      rfl

theorem cell22_3800277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_3800277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800277 prefixEnd_3800277 := by exact prefixLift 3800277
  have htrace : WordTrace (prefixWord ++ tailWord_3800277) baseStart_3800277 baseEnd_3800277 := by
    simpa [prefixWord, tailWord_3800277, baseEnd_3800277] using wordTrace_append hprefix tailTrace_3800277
  have hstable : (prefixWord ++ tailWord_3800277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800277).length < 2 ^ (prefixWord ++ tailWord_3800277).sum := by decide
  have hdescent : baseEnd_3800277 < baseStart_3800277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800354 : List Nat := [3, 3, 1, 1, 5, 1, 1, 2, 1, 4]
def baseStart_3800354 : Nat := 118140960795 + 3800354 * 2 ^ 59
def prefixEnd_3800354 : Nat := 4983230072969 + 3 ^ 40 * 3800354 * 2
def baseEnd_3800354 : Nat := 1300938839491286220798331

theorem tailTrace_3800354 : CollatzResearch.WordTrace tailWord_3800354 prefixEnd_3800354 1300938839491286220798331 := by
  unfold tailWord_3800354
  simp only [CollatzResearch.WordTrace]
  refine ⟨34652574418493495408724029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92406865115982654423264077 34652574418493495408724029)
  ·
    refine ⟨12994715406935060778271511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34652574418493495408724029 12994715406935060778271511)
    ·
      refine ⟨19492073110402591167407267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12994715406935060778271511 19492073110402591167407267)
      ·
        refine ⟨29238109665603886751110901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19492073110402591167407267 29238109665603886751110901)
        ·
          refine ⟨2741072781150364382916647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29238109665603886751110901 2741072781150364382916647)
          ·
            refine ⟨4111609171725546574374971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2741072781150364382916647 4111609171725546574374971)
            ·
              refine ⟨6167413757588319861562457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4111609171725546574374971 6167413757588319861562457)
              ·
                refine ⟨4625560318191239896171843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6167413757588319861562457 4625560318191239896171843)
                ·
                  refine ⟨6938340477286859844257765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4625560318191239896171843 6938340477286859844257765)
                  ·
                    refine ⟨1300938839491286220798331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6938340477286859844257765 1300938839491286220798331)
                    ·
                      rfl

theorem cell22_3800354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_3800354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800354 prefixEnd_3800354 := by exact prefixLift 3800354
  have htrace : WordTrace (prefixWord ++ tailWord_3800354) baseStart_3800354 baseEnd_3800354 := by
    simpa [prefixWord, tailWord_3800354, baseEnd_3800354] using wordTrace_append hprefix tailTrace_3800354
  have hstable : (prefixWord ++ tailWord_3800354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800354).length < 2 ^ (prefixWord ++ tailWord_3800354).sum := by decide
  have hdescent : baseEnd_3800354 < baseStart_3800354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800408 : List Nat := [2, 1, 2, 2, 1, 1, 3, 5, 5]
def baseStart_3800408 : Nat := 118140960795 + 3800408 * 2 ^ 59
def prefixEnd_3800408 : Nat := 4983230072969 + 3 ^ 40 * 3800408 * 2
def baseEnd_3800408 : Nat := 433652441598282693316055

theorem tailTrace_3800408 : CollatzResearch.WordTrace tailWord_3800408 prefixEnd_3800408 433652441598282693316055 := by
  unfold tailWord_3800408
  simp only [CollatzResearch.WordTrace]
  refine ⟨69306133607889174428680939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92408178143852232571574585 69306133607889174428680939)
  ·
    refine ⟨103959200411833761643021409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69306133607889174428680939 103959200411833761643021409)
    ·
      refine ⟨77969400308875321232266057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103959200411833761643021409 77969400308875321232266057)
      ·
        refine ⟨58477050231656490924199543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77969400308875321232266057 58477050231656490924199543)
        ·
          refine ⟨87715575347484736386299315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58477050231656490924199543 87715575347484736386299315)
          ·
            refine ⟨131573363021227104579448973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87715575347484736386299315 131573363021227104579448973)
            ·
              refine ⟨49340011132960164217293365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131573363021227104579448973 49340011132960164217293365)
              ·
                refine ⟨4625626043715015395371253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49340011132960164217293365 4625626043715015395371253)
                ·
                  refine ⟨433652441598282693316055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4625626043715015395371253 433652441598282693316055)
                  ·
                    rfl

theorem cell22_3800408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 5].length) (baseStart_3800408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800408 prefixEnd_3800408 := by exact prefixLift 3800408
  have htrace : WordTrace (prefixWord ++ tailWord_3800408) baseStart_3800408 baseEnd_3800408 := by
    simpa [prefixWord, tailWord_3800408, baseEnd_3800408] using wordTrace_append hprefix tailTrace_3800408
  have hstable : (prefixWord ++ tailWord_3800408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800408).length < 2 ^ (prefixWord ++ tailWord_3800408).sum := by decide
  have hdescent : baseEnd_3800408 < baseStart_3800408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800429 : List Nat := [1, 5, 1, 1, 1, 4, 2, 3, 1, 3]
def baseStart_3800429 : Nat := 118140960795 + 3800429 * 2 ^ 59
def prefixEnd_3800429 : Nat := 4983230072969 + 3 ^ 40 * 3800429 * 2
def baseEnd_3800429 : Nat := 1300964513524011025173101

theorem tailTrace_3800429 : CollatzResearch.WordTrace tailWord_3800429 prefixEnd_3800429 1300964513524011025173101 := by
  unfold tailWord_3800429
  simp only [CollatzResearch.WordTrace]
  refine ⟨138613033148702269443876341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92408688765801512962584227 138613033148702269443876341)
  ·
    refine ⟨12994971857690837760363407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138613033148702269443876341 12994971857690837760363407)
    ·
      refine ⟨19492457786536256640545111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12994971857690837760363407 19492457786536256640545111)
      ·
        refine ⟨29238686679804384960817667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19492457786536256640545111 29238686679804384960817667)
        ·
          refine ⟨43858030019706577441226501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29238686679804384960817667 43858030019706577441226501)
          ·
            refine ⟨8223380628694983270229969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43858030019706577441226501 8223380628694983270229969)
            ·
              refine ⟨6167535471521237452672477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8223380628694983270229969 6167535471521237452672477)
              ·
                refine ⟨2312825801820464044752179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6167535471521237452672477 2312825801820464044752179)
                ·
                  refine ⟨3469238702730696067128269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2312825801820464044752179 3469238702730696067128269)
                  ·
                    refine ⟨1300964513524011025173101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3469238702730696067128269 1300964513524011025173101)
                    ·
                      rfl

theorem cell22_3800429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_3800429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800429 prefixEnd_3800429 := by exact prefixLift 3800429
  have htrace : WordTrace (prefixWord ++ tailWord_3800429) baseStart_3800429 baseEnd_3800429 := by
    simpa [prefixWord, tailWord_3800429, baseEnd_3800429] using wordTrace_append hprefix tailTrace_3800429
  have hstable : (prefixWord ++ tailWord_3800429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800429).length < 2 ^ (prefixWord ++ tailWord_3800429).sum := by decide
  have hdescent : baseEnd_3800429 < baseStart_3800429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800446 : List Nat := [4, 2, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_3800446 : Nat := 118140960795 + 3800446 * 2 ^ 59
def prefixEnd_3800446 : Nat := 4983230072969 + 3 ^ 40 * 3800446 * 2
def baseEnd_3800446 : Nat := 1300970332971428647498049

theorem tailTrace_3800446 : CollatzResearch.WordTrace tailWord_3800446 prefixEnd_3800446 1300970332971428647498049 := by
  unfold tailWord_3800446
  simp only [CollatzResearch.WordTrace]
  refine ⟨17326706648705085168405649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92409102126427120898163461 17326706648705085168405649)
  ·
    refine ⟨12995029986528813876304237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17326706648705085168405649 12995029986528813876304237)
    ·
      refine ⟨4873136244948305203614089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12995029986528813876304237 4873136244948305203614089)
      ·
        refine ⟨3654852183711228902710567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4873136244948305203614089 3654852183711228902710567)
        ·
          refine ⟨5482278275566843354065851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3654852183711228902710567 5482278275566843354065851)
          ·
            refine ⟨8223417413350265031098777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5482278275566843354065851 8223417413350265031098777)
            ·
              refine ⟨6167563060012698773324083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8223417413350265031098777 6167563060012698773324083)
              ·
                refine ⟨9251344590019048159986125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6167563060012698773324083 9251344590019048159986125)
                ·
                  refine ⟨3469254221257143059994797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9251344590019048159986125 3469254221257143059994797)
                  ·
                    refine ⟨1300970332971428647498049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3469254221257143059994797 1300970332971428647498049)
                    ·
                      rfl

theorem cell22_3800446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_3800446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800446 prefixEnd_3800446 := by exact prefixLift 3800446
  have htrace : WordTrace (prefixWord ++ tailWord_3800446) baseStart_3800446 baseEnd_3800446 := by
    simpa [prefixWord, tailWord_3800446, baseEnd_3800446] using wordTrace_append hprefix tailTrace_3800446
  have hstable : (prefixWord ++ tailWord_3800446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800446).length < 2 ^ (prefixWord ++ tailWord_3800446).sum := by decide
  have hdescent : baseEnd_3800446 < baseStart_3800446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800453 : List Nat := [1, 3, 1, 1, 3, 1, 3, 3, 6]
def baseStart_3800453 : Nat := 118140960795 + 3800453 * 2 ^ 59
def prefixEnd_3800453 : Nat := 4983230072969 + 3 ^ 40 * 3800453 * 2
def baseEnd_3800453 : Nat := 433657576404827654191009

theorem tailTrace_3800453 : CollatzResearch.WordTrace tailWord_3800453 prefixEnd_3800453 433657576404827654191009 := by
  unfold tailWord_3800453
  simp only [CollatzResearch.WordTrace]
  refine ⟨138613908500615321542750013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92409272333743547695166675 138613908500615321542750013)
  ·
    refine ⟨51980215687730745578531255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138613908500615321542750013 51980215687730745578531255)
    ·
      refine ⟨77970323531596118367796883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51980215687730745578531255 77970323531596118367796883)
      ·
        refine ⟨116955485297394177551695325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77970323531596118367796883 116955485297394177551695325)
        ·
          refine ⟨43858306986522816581885747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116955485297394177551695325 43858306986522816581885747)
          ·
            refine ⟨65787460479784224872828621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43858306986522816581885747 65787460479784224872828621)
            ·
              refine ⟨24670297679919084327310733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65787460479784224872828621 24670297679919084327310733)
              ·
                refine ⟨9251361629969656622741525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24670297679919084327310733 9251361629969656622741525)
                ·
                  refine ⟨433657576404827654191009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9251361629969656622741525 433657576404827654191009)
                  ·
                    rfl

theorem cell22_3800453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_3800453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800453 prefixEnd_3800453 := by exact prefixLift 3800453
  have htrace : WordTrace (prefixWord ++ tailWord_3800453) baseStart_3800453 baseEnd_3800453 := by
    simpa [prefixWord, tailWord_3800453, baseEnd_3800453] using wordTrace_append hprefix tailTrace_3800453
  have hstable : (prefixWord ++ tailWord_3800453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800453).length < 2 ^ (prefixWord ++ tailWord_3800453).sum := by decide
  have hdescent : baseEnd_3800453 < baseStart_3800453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800483 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 1, 6]
def baseStart_3800483 : Nat := 118140960795 + 3800483 * 2 ^ 59
def prefixEnd_3800483 : Nat := 4983230072969 + 3 ^ 40 * 3800483 * 2
def baseEnd_3800483 : Nat := 1300982998827572884322935

theorem tailTrace_3800483 : CollatzResearch.WordTrace tailWord_3800483 prefixEnd_3800483 1300982998827572884322935 := by
  unfold tailWord_3800483
  simp only [CollatzResearch.WordTrace]
  refine ⟨138615002690506636666342103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92410001793671091110894735 138615002690506636666342103)
  ·
    refine ⟨207922504035759954999513155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138615002690506636666342103 207922504035759954999513155)
    ·
      refine ⟨311883756053639932499269733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207922504035759954999513155 311883756053639932499269733)
      ·
        refine ⟨58478204260057487343613075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311883756053639932499269733 58478204260057487343613075)
        ·
          refine ⟨87717306390086231015419613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58478204260057487343613075 87717306390086231015419613)
          ·
            refine ⟨32893989896282336630782355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87717306390086231015419613 32893989896282336630782355)
            ·
              refine ⟨49340984844423504946173533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32893989896282336630782355 49340984844423504946173533)
              ·
                refine ⟨18502869316658814354815075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49340984844423504946173533 18502869316658814354815075)
                ·
                  refine ⟨27754303974988221532222613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18502869316658814354815075 27754303974988221532222613)
                  ·
                    refine ⟨1300982998827572884322935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27754303974988221532222613 1300982998827572884322935)
                    ·
                      rfl

theorem cell22_3800483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 6].length) (baseStart_3800483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800483 prefixEnd_3800483 := by exact prefixLift 3800483
  have htrace : WordTrace (prefixWord ++ tailWord_3800483) baseStart_3800483 baseEnd_3800483 := by
    simpa [prefixWord, tailWord_3800483, baseEnd_3800483] using wordTrace_append hprefix tailTrace_3800483
  have hstable : (prefixWord ++ tailWord_3800483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800483).length < 2 ^ (prefixWord ++ tailWord_3800483).sum := by decide
  have hdescent : baseEnd_3800483 < baseStart_3800483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800528 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 2, 6]
def baseStart_3800528 : Nat := 118140960795 + 3800528 * 2 ^ 59
def prefixEnd_3800528 : Nat := 4983230072969 + 3 ^ 40 * 3800528 * 2
def baseEnd_3800528 : Nat := 1300998403247207766947797

theorem tailTrace_3800528 : CollatzResearch.WordTrace tailWord_3800528 prefixEnd_3800528 1300998403247207766947797 := by
  unfold tailWord_3800528
  simp only [CollatzResearch.WordTrace]
  refine ⟨69308321987671804675865119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92411095983562406234486825 69308321987671804675865119)
  ·
    refine ⟨103962482981507707013797679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69308321987671804675865119 103962482981507707013797679)
    ·
      refine ⟨155943724472261560520696519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103962482981507707013797679 155943724472261560520696519)
      ·
        refine ⟨233915586708392340781044779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155943724472261560520696519 233915586708392340781044779)
        ·
          refine ⟨350873380062588511171567169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233915586708392340781044779 350873380062588511171567169)
          ·
            refine ⟨263155035046941383378675377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350873380062588511171567169 263155035046941383378675377)
            ·
              refine ⟨197366276285206037534006533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263155035046941383378675377 197366276285206037534006533)
              ·
                refine ⟨37006176803476132037626225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197366276285206037534006533 37006176803476132037626225)
                ·
                  refine ⟨27754632602607099028219669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37006176803476132037626225 27754632602607099028219669)
                  ·
                    refine ⟨1300998403247207766947797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27754632602607099028219669 1300998403247207766947797)
                    ·
                      rfl

theorem cell22_3800528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_3800528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800528 prefixEnd_3800528 := by exact prefixLift 3800528
  have htrace : WordTrace (prefixWord ++ tailWord_3800528) baseStart_3800528 baseEnd_3800528 := by
    simpa [prefixWord, tailWord_3800528, baseEnd_3800528] using wordTrace_append hprefix tailTrace_3800528
  have hstable : (prefixWord ++ tailWord_3800528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800528).length < 2 ^ (prefixWord ++ tailWord_3800528).sum := by decide
  have hdescent : baseEnd_3800528 < baseStart_3800528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800534 : List Nat := [5, 2, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_3800534 : Nat := 118140960795 + 3800534 * 2 ^ 59
def prefixEnd_3800534 : Nat := 4983230072969 + 3 ^ 40 * 3800534 * 2
def baseEnd_3800534 : Nat := 1301000457169825751297779

theorem tailTrace_3800534 : CollatzResearch.WordTrace tailWord_3800534 prefixEnd_3800534 1301000457169825751297779 := by
  unfold tailWord_3800534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8663553925832617023528041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92411241875547914917632437 8663553925832617023528041)
  ·
    refine ⟨6497665444374462767646031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8663553925832617023528041 6497665444374462767646031)
    ·
      refine ⟨9746498166561694151469047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6497665444374462767646031 9746498166561694151469047)
      ·
        refine ⟨14619747249842541227203571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9746498166561694151469047 14619747249842541227203571)
        ·
          refine ⟨21929620874763811840805357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14619747249842541227203571 21929620874763811840805357)
          ·
            refine ⟨8223607828036429440302009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21929620874763811840805357 8223607828036429440302009)
            ·
              refine ⟨6167705871027322080226507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8223607828036429440302009 6167705871027322080226507)
              ·
                refine ⟨9251558806540983120339761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6167705871027322080226507 9251558806540983120339761)
                ·
                  refine ⟨6938669104905737340254821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9251558806540983120339761 6938669104905737340254821)
                  ·
                    refine ⟨1301000457169825751297779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6938669104905737340254821 1301000457169825751297779)
                    ·
                      rfl

theorem cell22_3800534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_3800534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800534 prefixEnd_3800534 := by exact prefixLift 3800534
  have htrace : WordTrace (prefixWord ++ tailWord_3800534) baseStart_3800534 baseEnd_3800534 := by
    simpa [prefixWord, tailWord_3800534, baseEnd_3800534] using wordTrace_append hprefix tailTrace_3800534
  have hstable : (prefixWord ++ tailWord_3800534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800534).length < 2 ^ (prefixWord ++ tailWord_3800534).sum := by decide
  have hdescent : baseEnd_3800534 < baseStart_3800534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800560 : List Nat := [2, 1, 1, 1, 3, 4, 1, 4, 5]
def baseStart_3800560 : Nat := 118140960795 + 3800560 * 2 ^ 59
def prefixEnd_3800560 : Nat := 4983230072969 + 3 ^ 40 * 3800560 * 2
def baseEnd_3800560 : Nat := 433669785833723450049233

theorem tailTrace_3800560 : CollatzResearch.WordTrace tailWord_3800560 prefixEnd_3800560 433669785833723450049233 := by
  unfold tailWord_3800560
  simp only [CollatzResearch.WordTrace]
  refine ⟨69308905555613839408447567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92411874074151785877930089 69308905555613839408447567)
  ·
    refine ⟨103963358333420759112671351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69308905555613839408447567 103963358333420759112671351)
    ·
      refine ⟨155945037500131138669007027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103963358333420759112671351 155945037500131138669007027)
      ·
        refine ⟨233917556250196708003510541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155945037500131138669007027 233917556250196708003510541)
        ·
          refine ⟨87719083593823765501316453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233917556250196708003510541 87719083593823765501316453)
          ·
            refine ⟨16447328173841956031496835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87719083593823765501316453 16447328173841956031496835)
            ·
              refine ⟨24670992260762934047245253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16447328173841956031496835 24670992260762934047245253)
              ·
                refine ⟨4625811048893050133858485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24670992260762934047245253 4625811048893050133858485)
                ·
                  refine ⟨433669785833723450049233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4625811048893050133858485 433669785833723450049233)
                  ·
                    rfl

theorem cell22_3800560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 5].length) (baseStart_3800560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800560 prefixEnd_3800560 := by exact prefixLift 3800560
  have htrace : WordTrace (prefixWord ++ tailWord_3800560) baseStart_3800560 baseEnd_3800560 := by
    simpa [prefixWord, tailWord_3800560, baseEnd_3800560] using wordTrace_append hprefix tailTrace_3800560
  have hstable : (prefixWord ++ tailWord_3800560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800560).length < 2 ^ (prefixWord ++ tailWord_3800560).sum := by decide
  have hdescent : baseEnd_3800560 < baseStart_3800560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800605 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 8]
def baseStart_3800605 : Nat := 118140960795 + 3800605 * 2 ^ 59
def prefixEnd_3800605 : Nat := 4983230072969 + 3 ^ 40 * 3800605 * 2
def baseEnd_3800605 : Nat := 433674920640268410924187

theorem tailTrace_3800605 : CollatzResearch.WordTrace tailWord_3800605 prefixEnd_3800605 433674920640268410924187 := by
  unfold tailWord_3800605
  simp only [CollatzResearch.WordTrace]
  refine ⟨138619452396064651502283269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92412968264043101001522179 138619452396064651502283269)
  ·
    refine ⟨25991147324262122156678113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138619452396064651502283269 25991147324262122156678113)
    ·
      refine ⟨19493360493196591617508585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25991147324262122156678113 19493360493196591617508585)
      ·
        refine ⟨14620020369897443713131439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19493360493196591617508585 14620020369897443713131439)
        ·
          refine ⟨21930030554846165569697159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14620020369897443713131439 21930030554846165569697159)
          ·
            refine ⟨32895045832269248354545739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21930030554846165569697159 32895045832269248354545739)
            ·
              refine ⟨49342568748403872531818609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32895045832269248354545739 49342568748403872531818609)
              ·
                refine ⟨37006926561302904398863957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49342568748403872531818609 37006926561302904398863957)
                ·
                  refine ⟨433674920640268410924187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37006926561302904398863957 433674920640268410924187)
                  ·
                    rfl

theorem cell22_3800605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_3800605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800605 prefixEnd_3800605 := by exact prefixLift 3800605
  have htrace : WordTrace (prefixWord ++ tailWord_3800605) baseStart_3800605 baseEnd_3800605 := by
    simpa [prefixWord, tailWord_3800605, baseEnd_3800605] using wordTrace_append hprefix tailTrace_3800605
  have hstable : (prefixWord ++ tailWord_3800605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800605).length < 2 ^ (prefixWord ++ tailWord_3800605).sum := by decide
  have hdescent : baseEnd_3800605 < baseStart_3800605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800622 : List Nat := [4, 1, 3, 1, 2, 1, 1, 3, 6]
def baseStart_3800622 : Nat := 118140960795 + 3800622 * 2 ^ 59
def prefixEnd_3800622 : Nat := 4983230072969 + 3 ^ 40 * 3800622 * 2
def baseEnd_3800622 : Nat := 433676860456074285032503

theorem tailTrace_3800622 : CollatzResearch.WordTrace tailWord_3800622 prefixEnd_3800622 433676860456074285032503 := by
  unfold tailWord_3800622
  simp only [CollatzResearch.WordTrace]
  refine ⟨17327509054625382925706515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92413381624668708937101413 17327509054625382925706515)
  ·
    refine ⟨25991263581938074388559773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17327509054625382925706515 25991263581938074388559773)
    ·
      refine ⟨9746723843226777895709915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25991263581938074388559773 9746723843226777895709915)
      ·
        refine ⟨14620085764840166843564873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9746723843226777895709915 14620085764840166843564873)
        ·
          refine ⟨10965064323630125132673655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14620085764840166843564873 10965064323630125132673655)
          ·
            refine ⟨16447596485445187699010483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10965064323630125132673655 16447596485445187699010483)
            ·
              refine ⟨24671394728167781548515725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16447596485445187699010483 24671394728167781548515725)
              ·
                refine ⟨9251773023062918080693397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24671394728167781548515725 9251773023062918080693397)
                ·
                  refine ⟨433676860456074285032503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9251773023062918080693397 433676860456074285032503)
                  ·
                    rfl

theorem cell22_3800622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_3800622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800622 prefixEnd_3800622 := by exact prefixLift 3800622
  have htrace : WordTrace (prefixWord ++ tailWord_3800622) baseStart_3800622 baseEnd_3800622 := by
    simpa [prefixWord, tailWord_3800622, baseEnd_3800622] using wordTrace_append hprefix tailTrace_3800622
  have hstable : (prefixWord ++ tailWord_3800622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800622).length < 2 ^ (prefixWord ++ tailWord_3800622).sum := by decide
  have hdescent : baseEnd_3800622 < baseStart_3800622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800650 : List Nat := [3, 1, 2, 1, 1, 3, 3, 8]
def baseStart_3800650 : Nat := 118140960795 + 3800650 * 2 ^ 59
def prefixEnd_3800650 : Nat := 4983230072969 + 3 ^ 40 * 3800650 * 2
def baseEnd_3800650 : Nat := 144560018482271123933047

theorem tailTrace_3800650 : CollatzResearch.WordTrace tailWord_3800650 prefixEnd_3800650 144560018482271123933047 := by
  unfold tailWord_3800650
  simp only [CollatzResearch.WordTrace]
  refine ⟨34655273420225406046917851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92414062453934416125114269 34655273420225406046917851)
  ·
    refine ⟨51982910130338109070376777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34655273420225406046917851 51982910130338109070376777)
    ·
      refine ⟨38987182597753581802782583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51982910130338109070376777 38987182597753581802782583)
      ·
        refine ⟨58480773896630372704173875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38987182597753581802782583 58480773896630372704173875)
        ·
          refine ⟨87721160844945559056260813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58480773896630372704173875 87721160844945559056260813)
          ·
            refine ⟨32895435316854584646097805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87721160844945559056260813 32895435316854584646097805)
            ·
              refine ⟨12335788243820469242286677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32895435316854584646097805 12335788243820469242286677)
              ·
                refine ⟨144560018482271123933047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12335788243820469242286677 144560018482271123933047)
                ·
                  rfl

theorem cell22_3800650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 8].length) (baseStart_3800650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800650 prefixEnd_3800650 := by exact prefixLift 3800650
  have htrace : WordTrace (prefixWord ++ tailWord_3800650) baseStart_3800650 baseEnd_3800650 := by
    simpa [prefixWord, tailWord_3800650, baseEnd_3800650] using wordTrace_append hprefix tailTrace_3800650
  have hstable : (prefixWord ++ tailWord_3800650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800650).length < 2 ^ (prefixWord ++ tailWord_3800650).sum := by decide
  have hdescent : baseEnd_3800650 < baseStart_3800650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800864 : List Nat := [2, 1, 1, 5, 1, 1, 3, 3, 5]
def baseStart_3800864 : Nat := 118140960795 + 3800864 * 2 ^ 59
def prefixEnd_3800864 : Nat := 4983230072969 + 3 ^ 40 * 3800864 * 2
def baseEnd_3800864 : Nat := 433704474304604963515589

theorem tailTrace_3800864 : CollatzResearch.WordTrace tailWord_3800864 prefixEnd_3800864 433704474304604963515589 := by
  unfold tailWord_3800864
  simp only [CollatzResearch.WordTrace]
  refine ⟨69314449451063169367980823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92419265934750892490641097 69314449451063169367980823)
  ·
    refine ⟨103971674176594754051971235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69314449451063169367980823 103971674176594754051971235)
    ·
      refine ⟨155957511264892131077956853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103971674176594754051971235 155957511264892131077956853)
      ·
        refine ⟨14621016681083637288558455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155957511264892131077956853 14621016681083637288558455)
        ·
          refine ⟨21931525021625455932837683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14621016681083637288558455 21931525021625455932837683)
          ·
            refine ⟨32897287532438183899256525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21931525021625455932837683 32897287532438183899256525)
            ·
              refine ⟨12336482824664318962221197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32897287532438183899256525 12336482824664318962221197)
              ·
                refine ⟨4626181059249119610832949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12336482824664318962221197 4626181059249119610832949)
                ·
                  refine ⟨433704474304604963515589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4626181059249119610832949 433704474304604963515589)
                  ·
                    rfl

theorem cell22_3800864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 5].length) (baseStart_3800864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800864 prefixEnd_3800864 := by exact prefixLift 3800864
  have htrace : WordTrace (prefixWord ++ tailWord_3800864) baseStart_3800864 baseEnd_3800864 := by
    simpa [prefixWord, tailWord_3800864, baseEnd_3800864] using wordTrace_append hprefix tailTrace_3800864
  have hstable : (prefixWord ++ tailWord_3800864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800864).length < 2 ^ (prefixWord ++ tailWord_3800864).sum := by decide
  have hdescent : baseEnd_3800864 < baseStart_3800864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800902 : List Nat := [6, 1, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_3800902 : Nat := 118140960795 + 3800902 * 2 ^ 59
def prefixEnd_3800902 : Nat := 4983230072969 + 3 ^ 40 * 3800902 * 2
def baseEnd_3800902 : Nat := 1301126431090395458096651

theorem tailTrace_3800902 : CollatzResearch.WordTrace tailWord_3800902 prefixEnd_3800902 1301126431090395458096651 := by
  unfold tailWord_3800902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4332196402374645975807655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92420189917325780817229973 4332196402374645975807655)
  ·
    refine ⟨6498294603561968963711483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4332196402374645975807655 6498294603561968963711483)
    ·
      refine ⟨9747441905342953445567225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6498294603561968963711483 9747441905342953445567225)
      ·
        refine ⟨7310581429007215084175419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9747441905342953445567225 7310581429007215084175419)
        ·
          refine ⟨10965872143510822626263129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7310581429007215084175419 10965872143510822626263129)
          ·
            refine ⟨8224404107633116969697347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10965872143510822626263129 8224404107633116969697347)
            ·
              refine ⟨12336606161449675454546021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8224404107633116969697347 12336606161449675454546021)
              ·
                refine ⟨2313113655271814147727379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12336606161449675454546021 2313113655271814147727379)
                ·
                  refine ⟨3469670482907721221591069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2313113655271814147727379 3469670482907721221591069)
                  ·
                    refine ⟨1301126431090395458096651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3469670482907721221591069 1301126431090395458096651)
                    ·
                      rfl

theorem cell22_3800902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_3800902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800902 prefixEnd_3800902 := by exact prefixLift 3800902
  have htrace : WordTrace (prefixWord ++ tailWord_3800902) baseStart_3800902 baseEnd_3800902 := by
    simpa [prefixWord, tailWord_3800902, baseEnd_3800902] using wordTrace_append hprefix tailTrace_3800902
  have hstable : (prefixWord ++ tailWord_3800902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800902).length < 2 ^ (prefixWord ++ tailWord_3800902).sum := by decide
  have hdescent : baseEnd_3800902 < baseStart_3800902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800937 : List Nat := [1, 2, 1, 1, 1, 3, 1, 12]
def baseStart_3800937 : Nat := 118140960795 + 3800937 * 2 ^ 59
def prefixEnd_3800937 : Nat := 4983230072969 + 3 ^ 40 * 3800937 * 2
def baseEnd_3800937 : Nat := 144570934700629670385727

theorem tailTrace_3800937 : CollatzResearch.WordTrace tailWord_3800937 prefixEnd_3800937 144570934700629670385727 := by
  unfold tailWord_3800937
  simp only [CollatzResearch.WordTrace]
  refine ⟨138631561430861872203369065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92421040953907914802246043 138631561430861872203369065)
  ·
    refine ⟨103973671073146404152526799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138631561430861872203369065 103973671073146404152526799)
    ·
      refine ⟨155960506609719606228790199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103973671073146404152526799 155960506609719606228790199)
      ·
        refine ⟨233940759914579409343185299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155960506609719606228790199 233940759914579409343185299)
        ·
          refine ⟨350911139871869114014777949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233940759914579409343185299 350911139871869114014777949)
          ·
            refine ⟨131591677451950917755541731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350911139871869114014777949 131591677451950917755541731)
            ·
              refine ⟨197387516177926376633312597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131591677451950917755541731 197387516177926376633312597)
              ·
                refine ⟨144570934700629670385727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 197387516177926376633312597 144570934700629670385727)
                ·
                  rfl

theorem cell22_3800937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 12].length) (baseStart_3800937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800937 prefixEnd_3800937 := by exact prefixLift 3800937
  have htrace : WordTrace (prefixWord ++ tailWord_3800937) baseStart_3800937 baseEnd_3800937 := by
    simpa [prefixWord, tailWord_3800937, baseEnd_3800937] using wordTrace_append hprefix tailTrace_3800937
  have hstable : (prefixWord ++ tailWord_3800937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800937).length < 2 ^ (prefixWord ++ tailWord_3800937).sum := by decide
  have hdescent : baseEnd_3800937 < baseStart_3800937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3800988 : List Nat := [2, 2, 3, 3, 1, 3, 2, 6]
def baseStart_3800988 : Nat := 118140960795 + 3800988 * 2 ^ 59
def prefixEnd_3800988 : Nat := 4983230072969 + 3 ^ 40 * 3800988 * 2
def baseEnd_3800988 : Nat := 144572874516435544494043

theorem tailTrace_3800988 : CollatzResearch.WordTrace tailWord_3800988 prefixEnd_3800988 144572874516435544494043 := by
  unfold tailWord_3800988
  simp only [CollatzResearch.WordTrace]
  refine ⟨69316710776838553956737809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92422281035784738608983745 69316710776838553956737809)
  ·
    refine ⟨51987533082628915467553357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69316710776838553956737809 51987533082628915467553357)
    ·
      refine ⟨19495324905985843300332509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51987533082628915467553357 19495324905985843300332509)
      ·
        refine ⟨7310746839744691237624691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19495324905985843300332509 7310746839744691237624691)
        ·
          refine ⟨10966120259617036856437037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7310746839744691237624691 10966120259617036856437037)
          ·
            refine ⟨4112295097356388821163889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10966120259617036856437037 4112295097356388821163889)
            ·
              refine ⟨3084221323017291615872917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4112295097356388821163889 3084221323017291615872917)
              ·
                refine ⟨144572874516435544494043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3084221323017291615872917 144572874516435544494043)
                ·
                  rfl

theorem cell22_3800988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 6].length) (baseStart_3800988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3800988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3800988 prefixEnd_3800988 := by exact prefixLift 3800988
  have htrace : WordTrace (prefixWord ++ tailWord_3800988) baseStart_3800988 baseEnd_3800988 := by
    simpa [prefixWord, tailWord_3800988, baseEnd_3800988] using wordTrace_append hprefix tailTrace_3800988
  have hstable : (prefixWord ++ tailWord_3800988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3800988).length < 2 ^ (prefixWord ++ tailWord_3800988).sum := by decide
  have hdescent : baseEnd_3800988 < baseStart_3800988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3800988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801093 : List Nat := [1, 3, 1, 1, 2, 4, 2, 3, 2, 3]
def baseStart_3801093 : Nat := 118140960795 + 3801093 * 2 ^ 59
def prefixEnd_3801093 : Nat := 4983230072969 + 3 ^ 40 * 3801093 * 2
def baseEnd_3801093 : Nat := 1301191814293734626571065

theorem tailTrace_3801093 : CollatzResearch.WordTrace tailWord_3801093 prefixEnd_3801093 1301191814293734626571065 := by
  unfold tailWord_3801093
  simp only [CollatzResearch.WordTrace]
  refine ⟨138637251218296710846047933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92424834145531140564031955 138637251218296710846047933)
  ·
    refine ⟨51988969206861266567267975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138637251218296710846047933 51988969206861266567267975)
    ·
      refine ⟨77983453810291899850901963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51988969206861266567267975 77983453810291899850901963)
      ·
        refine ⟨116975180715437849776352945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77983453810291899850901963 116975180715437849776352945)
        ·
          refine ⟨87731385536578387332264709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116975180715437849776352945 87731385536578387332264709)
          ·
            refine ⟨16449634788108447624799633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87731385536578387332264709 16449634788108447624799633)
            ·
              refine ⟨12337226091081335718599725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16449634788108447624799633 12337226091081335718599725)
              ·
                refine ⟨4626459784155500894474897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12337226091081335718599725 4626459784155500894474897)
                ·
                  refine ⟨3469844838116625670856173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4626459784155500894474897 3469844838116625670856173)
                  ·
                    refine ⟨1301191814293734626571065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3469844838116625670856173 1301191814293734626571065)
                    ·
                      rfl

theorem cell22_3801093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_3801093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801093 prefixEnd_3801093 := by exact prefixLift 3801093
  have htrace : WordTrace (prefixWord ++ tailWord_3801093) baseStart_3801093 baseEnd_3801093 := by
    simpa [prefixWord, tailWord_3801093, baseEnd_3801093] using wordTrace_append hprefix tailTrace_3801093
  have hstable : (prefixWord ++ tailWord_3801093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801093).length < 2 ^ (prefixWord ++ tailWord_3801093).sum := by decide
  have hdescent : baseEnd_3801093 < baseStart_3801093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801104 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 2, 7]
def baseStart_3801104 : Nat := 118140960795 + 3801104 * 2 ^ 59
def prefixEnd_3801104 : Nat := 4983230072969 + 3 ^ 40 * 3801104 * 2
def baseEnd_3801104 : Nat := 1301195579818534264546031

theorem tailTrace_3801104 : CollatzResearch.WordTrace tailWord_3801104 prefixEnd_3801104 1301195579818534264546031 := by
  unfold tailWord_3801104
  simp only [CollatzResearch.WordTrace]
  refine ⟨69318826210628429862349183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92425101614171239816465577 69318826210628429862349183)
  ·
    refine ⟨103978239315942644793523775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69318826210628429862349183 103978239315942644793523775)
    ·
      refine ⟨155967358973913967190285663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103978239315942644793523775 155967358973913967190285663)
      ·
        refine ⟨233951038460870950785428495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155967358973913967190285663 233951038460870950785428495)
        ·
          refine ⟨350926557691306426178142743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233951038460870950785428495 350926557691306426178142743)
          ·
            refine ⟨526389836536959639267214115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350926557691306426178142743 526389836536959639267214115)
            ·
              refine ⟨789584754805439458900821173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526389836536959639267214115 789584754805439458900821173)
              ·
                refine ⟨74023570763009949271951985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 789584754805439458900821173 74023570763009949271951985)
                ·
                  refine ⟨55517678072257461953963989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74023570763009949271951985 55517678072257461953963989)
                  ·
                    refine ⟨1301195579818534264546031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55517678072257461953963989 1301195579818534264546031)
                    ·
                      rfl

theorem cell22_3801104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_3801104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801104 prefixEnd_3801104 := by exact prefixLift 3801104
  have htrace : WordTrace (prefixWord ++ tailWord_3801104) baseStart_3801104 baseEnd_3801104 := by
    simpa [prefixWord, tailWord_3801104, baseEnd_3801104] using wordTrace_append hprefix tailTrace_3801104
  have hstable : (prefixWord ++ tailWord_3801104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801104).length < 2 ^ (prefixWord ++ tailWord_3801104).sum := by decide
  have hdescent : baseEnd_3801104 < baseStart_3801104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801138 : List Nat := [3, 2, 1, 1, 2, 3, 1, 3, 3, 3]
def baseStart_3801138 : Nat := 118140960795 + 3801138 * 2 ^ 59
def prefixEnd_3801138 : Nat := 4983230072969 + 3 ^ 40 * 3801138 * 2
def baseEnd_3801138 : Nat := 1301207218713369509195927

theorem tailTrace_3801138 : CollatzResearch.WordTrace tailWord_3801138 prefixEnd_3801138 1301207218713369509195927 := by
  unfold tailWord_3801138
  simp only [CollatzResearch.WordTrace]
  refine ⟨34659723125783420882859017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92425928335422455687624045 34659723125783420882859017)
  ·
    refine ⟨25994792344337565662144263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34659723125783420882859017 25994792344337565662144263)
    ·
      refine ⟨38992188516506348493216395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25994792344337565662144263 38992188516506348493216395)
      ·
        refine ⟨58488282774759522739824593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38992188516506348493216395 58488282774759522739824593)
        ·
          refine ⟨43866212081069642054868445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58488282774759522739824593 43866212081069642054868445)
          ·
            refine ⟨16449829530401115770575667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43866212081069642054868445 16449829530401115770575667)
            ·
              refine ⟨24674744295601673655863501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16449829530401115770575667 24674744295601673655863501)
              ·
                refine ⟨9253029110850627620948813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24674744295601673655863501 9253029110850627620948813)
                ·
                  refine ⟨3469885916568985357855805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9253029110850627620948813 3469885916568985357855805)
                  ·
                    refine ⟨1301207218713369509195927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3469885916568985357855805 1301207218713369509195927)
                    ·
                      rfl

theorem cell22_3801138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_3801138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801138 prefixEnd_3801138 := by exact prefixLift 3801138
  have htrace : WordTrace (prefixWord ++ tailWord_3801138) baseStart_3801138 baseEnd_3801138 := by
    simpa [prefixWord, tailWord_3801138, baseEnd_3801138] using wordTrace_append hprefix tailTrace_3801138
  have hstable : (prefixWord ++ tailWord_3801138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801138).length < 2 ^ (prefixWord ++ tailWord_3801138).sum := by decide
  have hdescent : baseEnd_3801138 < baseStart_3801138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801151 : List Nat := [1, 1, 2, 2, 3, 1, 2, 5, 5]
def baseStart_3801151 : Nat := 118140960795 + 3801151 * 2 ^ 59
def prefixEnd_3801151 : Nat := 4983230072969 + 3 ^ 40 * 3801151 * 2
def baseEnd_3801151 : Nat := 433737222959680602873629

theorem tailTrace_3801151 : CollatzResearch.WordTrace tailWord_3801151 prefixEnd_3801151 433737222959680602873629 := by
  unfold tailWord_3801151
  simp only [CollatzResearch.WordTrace]
  refine ⟨138639366652086586751659307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92426244434724391167772871 138639366652086586751659307)
  ·
    refine ⟨207959049978129880127488961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138639366652086586751659307 207959049978129880127488961)
    ·
      refine ⟨155969287483597410095616721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207959049978129880127488961 155969287483597410095616721)
      ·
        refine ⟨116976965612698057571712541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155969287483597410095616721 116976965612698057571712541)
        ·
          refine ⟨43866362104761771589392203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116976965612698057571712541 43866362104761771589392203)
          ·
            refine ⟨65799543157142657384088305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43866362104761771589392203 65799543157142657384088305)
            ·
              refine ⟨49349657367856993038066229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65799543157142657384088305 49349657367856993038066229)
              ·
                refine ⟨4626530378236593097318709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49349657367856993038066229 4626530378236593097318709)
                ·
                  refine ⟨433737222959680602873629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4626530378236593097318709 433737222959680602873629)
                  ·
                    rfl

theorem cell22_3801151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 5].length) (baseStart_3801151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801151 prefixEnd_3801151 := by exact prefixLift 3801151
  have htrace : WordTrace (prefixWord ++ tailWord_3801151) baseStart_3801151 baseEnd_3801151 := by
    simpa [prefixWord, tailWord_3801151, baseEnd_3801151] using wordTrace_append hprefix tailTrace_3801151
  have hstable : (prefixWord ++ tailWord_3801151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801151).length < 2 ^ (prefixWord ++ tailWord_3801151).sum := by decide
  have hdescent : baseEnd_3801151 < baseStart_3801151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801198 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_3801198 : Nat := 118140960795 + 3801198 * 2 ^ 59
def prefixEnd_3801198 : Nat := 4983230072969 + 3 ^ 40 * 3801198 * 2
def baseEnd_3801198 : Nat := 1301227757939549352695743

theorem tailTrace_3801198 : CollatzResearch.WordTrace tailWord_3801198 prefixEnd_3801198 1301227757939549352695743 := by
  unfold tailWord_3801198
  simp only [CollatzResearch.WordTrace]
  refine ⟨17330135110364539222327531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92427387255277542519080165 17330135110364539222327531)
  ·
    refine ⟨25995202665546808833491297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17330135110364539222327531 25995202665546808833491297)
    ·
      refine ⟨19496401999160106625118473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25995202665546808833491297 19496401999160106625118473)
      ·
        refine ⟨14622301499370079968838855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19496401999160106625118473 14622301499370079968838855)
        ·
          refine ⟨21933452249055119953258283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14622301499370079968838855 21933452249055119953258283)
          ·
            refine ⟨32900178373582679929887425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21933452249055119953258283 32900178373582679929887425)
            ·
              refine ⟨24675133780187009947415569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32900178373582679929887425 24675133780187009947415569)
              ·
                refine ⟨18506350335140257460561677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24675133780187009947415569 18506350335140257460561677)
                ·
                  refine ⟨6939881375677596547710629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18506350335140257460561677 6939881375677596547710629)
                  ·
                    refine ⟨1301227757939549352695743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6939881375677596547710629 1301227757939549352695743)
                    ·
                      rfl

theorem cell22_3801198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_3801198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801198 prefixEnd_3801198 := by exact prefixLift 3801198
  have htrace : WordTrace (prefixWord ++ tailWord_3801198) baseStart_3801198 baseEnd_3801198 := by
    simpa [prefixWord, tailWord_3801198, baseEnd_3801198] using wordTrace_append hprefix tailTrace_3801198
  have hstable : (prefixWord ++ tailWord_3801198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801198).length < 2 ^ (prefixWord ++ tailWord_3801198).sum := by decide
  have hdescent : baseEnd_3801198 < baseStart_3801198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801245 : List Nat := [1, 4, 2, 1, 1, 3, 1, 4, 2, 3]
def baseStart_3801245 : Nat := 118140960795 + 3801245 * 2 ^ 59
def prefixEnd_3801245 : Nat := 4983230072969 + 3 ^ 40 * 3801245 * 2
def baseEnd_3801245 : Nat := 1301243847000056896770599

theorem tailTrace_3801245 : CollatzResearch.WordTrace tailWord_3801245 prefixEnd_3801245 1301243847000056896770599 := by
  unfold tailWord_3801245
  simp only [CollatzResearch.WordTrace]
  refine ⟨138642795113746040805581189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92428530075830693870387459 138642795113746040805581189)
  ·
    refine ⟨25995524083827382651046473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138642795113746040805581189 25995524083827382651046473)
    ·
      refine ⟨19496643062870536988284855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25995524083827382651046473 19496643062870536988284855)
      ·
        refine ⟨29244964594305805482427283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19496643062870536988284855 29244964594305805482427283)
        ·
          refine ⟨43867446891458708223640925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29244964594305805482427283 43867446891458708223640925)
          ·
            refine ⟨16450292584297015583865347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43867446891458708223640925 16450292584297015583865347)
            ·
              refine ⟨24675438876445523375798021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16450292584297015583865347 24675438876445523375798021)
              ·
                refine ⟨4626644789333535632962129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24675438876445523375798021 4626644789333535632962129)
                ·
                  refine ⟨3469983592000151724721597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4626644789333535632962129 3469983592000151724721597)
                  ·
                    refine ⟨1301243847000056896770599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3469983592000151724721597 1301243847000056896770599)
                    ·
                      rfl

theorem cell22_3801245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_3801245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801245 prefixEnd_3801245 := by exact prefixLift 3801245
  have htrace : WordTrace (prefixWord ++ tailWord_3801245) baseStart_3801245 baseEnd_3801245 := by
    simpa [prefixWord, tailWord_3801245, baseEnd_3801245] using wordTrace_append hprefix tailTrace_3801245
  have hstable : (prefixWord ++ tailWord_3801245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801245).length < 2 ^ (prefixWord ++ tailWord_3801245).sum := by decide
  have hdescent : baseEnd_3801245 < baseStart_3801245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801247 : List Nat := [1, 1, 2, 6, 1, 1, 4, 2, 4]
def baseStart_3801247 : Nat := 118140960795 + 3801247 * 2 ^ 59
def prefixEnd_3801247 : Nat := 4983230072969 + 3 ^ 40 * 3801247 * 2
def baseEnd_3801247 : Nat := 433748177213643186073531

theorem tailTrace_3801247 : CollatzResearch.WordTrace tailWord_3801247 prefixEnd_3801247 433748177213643186073531 := by
  unfold tailWord_3801247
  simp only [CollatzResearch.WordTrace]
  refine ⟨138642868059738795147153995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92428578706492530098102663 138642868059738795147153995)
  ·
    refine ⟨207964302089608192720730993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138642868059738795147153995 207964302089608192720730993)
    ·
      refine ⟨155973226567206144540548245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207964302089608192720730993 155973226567206144540548245)
      ·
        refine ⟨7311244995337788025338199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 155973226567206144540548245 7311244995337788025338199)
        ·
          refine ⟨10966867493006682038007299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7311244995337788025338199 10966867493006682038007299)
          ·
            refine ⟨16450301239510023057010949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10966867493006682038007299 16450301239510023057010949)
            ·
              refine ⟨3084431482408129323189553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16450301239510023057010949 3084431482408129323189553)
              ·
                refine ⟨2313323611806096992392165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3084431482408129323189553 2313323611806096992392165)
                ·
                  refine ⟨433748177213643186073531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2313323611806096992392165 433748177213643186073531)
                  ·
                    rfl

theorem cell22_3801247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 4].length) (baseStart_3801247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801247 prefixEnd_3801247 := by exact prefixLift 3801247
  have htrace : WordTrace (prefixWord ++ tailWord_3801247) baseStart_3801247 baseEnd_3801247 := by
    simpa [prefixWord, tailWord_3801247, baseEnd_3801247] using wordTrace_append hprefix tailTrace_3801247
  have hstable : (prefixWord ++ tailWord_3801247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801247).length < 2 ^ (prefixWord ++ tailWord_3801247).sum := by decide
  have hdescent : baseEnd_3801247 < baseStart_3801247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801365 : List Nat := [1, 3, 2, 1, 2, 1, 2, 6, 4]
def baseStart_3801365 : Nat := 118140960795 + 3801365 * 2 ^ 59
def prefixEnd_3801365 : Nat := 4983230072969 + 3 ^ 40 * 3801365 * 2
def baseEnd_3801365 : Nat := 433761641817472194590077

theorem tailTrace_3801365 : CollatzResearch.WordTrace tailWord_3801365 prefixEnd_3801365 433761641817472194590077 := by
  unfold tailWord_3801365
  simp only [CollatzResearch.WordTrace]
  refine ⟨138647171873311301299949549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92431447915540867533299699 138647171873311301299949549)
  ·
    refine ⟨51992689452491737987481081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138647171873311301299949549 51992689452491737987481081)
    ·
      refine ⟨38994517089368803490610811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51992689452491737987481081 38994517089368803490610811)
      ·
        refine ⟨58491775634053205235916217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38994517089368803490610811 58491775634053205235916217)
        ·
          refine ⟨43868831725539903926937163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58491775634053205235916217 43868831725539903926937163)
          ·
            refine ⟨65803247588309855890405745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43868831725539903926937163 65803247588309855890405745)
            ·
              refine ⟨49352435691232391917804309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65803247588309855890405745 49352435691232391917804309)
              ·
                refine ⟨2313395423026518371147077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49352435691232391917804309 2313395423026518371147077)
                ·
                  refine ⟨433761641817472194590077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2313395423026518371147077 433761641817472194590077)
                  ·
                    rfl

theorem cell22_3801365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 4].length) (baseStart_3801365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801365 prefixEnd_3801365 := by exact prefixLift 3801365
  have htrace : WordTrace (prefixWord ++ tailWord_3801365) baseStart_3801365 baseEnd_3801365 := by
    simpa [prefixWord, tailWord_3801365, baseEnd_3801365] using wordTrace_append hprefix tailTrace_3801365
  have hstable : (prefixWord ++ tailWord_3801365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801365).length < 2 ^ (prefixWord ++ tailWord_3801365).sum := by decide
  have hdescent : baseEnd_3801365 < baseStart_3801365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801384 : List Nat := [2, 1, 5, 1, 3, 2, 1, 2, 1, 4]
def baseStart_3801384 : Nat := 118140960795 + 3801384 * 2 ^ 59
def prefixEnd_3801384 : Nat := 4983230072969 + 3 ^ 40 * 3801384 * 2
def baseEnd_3801384 : Nat := 1301291429540706867545173

theorem tailTrace_3801384 : CollatzResearch.WordTrace tailWord_3801384 prefixEnd_3801384 1301291429540706867545173 := by
  unfold tailWord_3801384
  simp only [CollatzResearch.WordTrace]
  refine ⟨69323932430121233772445603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92431909906828311696594137 69323932430121233772445603)
  ·
    refine ⟨103985898645181850658668405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69323932430121233772445603 103985898645181850658668405)
    ·
      refine ⟨9748677997985798499250163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103985898645181850658668405 9748677997985798499250163)
      ·
        refine ⟨14623016996978697748875245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9748677997985798499250163 14623016996978697748875245)
        ·
          refine ⟨5483631373867011655828217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14623016996978697748875245 5483631373867011655828217)
          ·
            refine ⟨4112723530400258741871163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5483631373867011655828217 4112723530400258741871163)
            ·
              refine ⟨6169085295600388112806745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4112723530400258741871163 6169085295600388112806745)
              ·
                refine ⟨4626813971700291084605059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6169085295600388112806745 4626813971700291084605059)
                ·
                  refine ⟨6940220957550436626907589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4626813971700291084605059 6940220957550436626907589)
                  ·
                    refine ⟨1301291429540706867545173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6940220957550436626907589 1301291429540706867545173)
                    ·
                      rfl

theorem cell22_3801384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_3801384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801384 prefixEnd_3801384 := by exact prefixLift 3801384
  have htrace : WordTrace (prefixWord ++ tailWord_3801384) baseStart_3801384 baseEnd_3801384 := by
    simpa [prefixWord, tailWord_3801384, baseEnd_3801384] using wordTrace_append hprefix tailTrace_3801384
  have hstable : (prefixWord ++ tailWord_3801384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801384).length < 2 ^ (prefixWord ++ tailWord_3801384).sum := by decide
  have hdescent : baseEnd_3801384 < baseStart_3801384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801395 : List Nat := [1, 1, 1, 2, 5, 1, 4, 1, 2, 4]
def baseStart_3801395 : Nat := 118140960795 + 3801395 * 2 ^ 59
def prefixEnd_3801395 : Nat := 4983230072969 + 3 ^ 40 * 3801395 * 2
def baseEnd_3801395 : Nat := 1301295195065506505520139

theorem tailTrace_3801395 : CollatzResearch.WordTrace tailWord_3801395 prefixEnd_3801395 1301295195065506505520139 := by
  unfold tailWord_3801395
  simp only [CollatzResearch.WordTrace]
  refine ⟨138648266063202616423541639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92432177375468410949027759 138648266063202616423541639)
  ·
    refine ⟨207972399094803924635312459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138648266063202616423541639 207972399094803924635312459)
    ·
      refine ⟨311958598642205886952968689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207972399094803924635312459 311958598642205886952968689)
      ·
        refine ⟨233968948981654415214726517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311958598642205886952968689 233968948981654415214726517)
        ·
          refine ⟨21934588967030101426380611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233968948981654415214726517 21934588967030101426380611)
          ·
            refine ⟨32901883450545152139570917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21934588967030101426380611 32901883450545152139570917)
            ·
              refine ⟨6169103146977216026169547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32901883450545152139570917 6169103146977216026169547)
              ·
                refine ⟨9253654720465824039254321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6169103146977216026169547 9253654720465824039254321)
                ·
                  refine ⟨6940241040349368029440741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9253654720465824039254321 6940241040349368029440741)
                  ·
                    refine ⟨1301295195065506505520139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6940241040349368029440741 1301295195065506505520139)
                    ·
                      rfl

theorem cell22_3801395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 4].length) (baseStart_3801395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801395 prefixEnd_3801395 := by exact prefixLift 3801395
  have htrace : WordTrace (prefixWord ++ tailWord_3801395) baseStart_3801395 baseEnd_3801395 := by
    simpa [prefixWord, tailWord_3801395, baseEnd_3801395] using wordTrace_append hprefix tailTrace_3801395
  have hstable : (prefixWord ++ tailWord_3801395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801395).length < 2 ^ (prefixWord ++ tailWord_3801395).sum := by decide
  have hdescent : baseEnd_3801395 < baseStart_3801395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801442 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_3801442 : Nat := 118140960795 + 3801442 * 2 ^ 59
def prefixEnd_3801442 : Nat := 4983230072969 + 3 ^ 40 * 3801442 * 2
def baseEnd_3801442 : Nat := 1301311284126014049594995

theorem tailTrace_3801442 : CollatzResearch.WordTrace tailWord_3801442 prefixEnd_3801442 1301311284126014049594995 := by
  unfold tailWord_3801442
  simp only [CollatzResearch.WordTrace]
  refine ⟨34662495073508085862625645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92433320196021562300335053 34662495073508085862625645)
  ·
    refine ⟨12998435652565532198484617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34662495073508085862625645 12998435652565532198484617)
    ·
      refine ⟨9748826739424149148863463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12998435652565532198484617 9748826739424149148863463)
      ·
        refine ⟨14623240109136223723295195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9748826739424149148863463 14623240109136223723295195)
        ·
          refine ⟨21934860163704335584942793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14623240109136223723295195 21934860163704335584942793)
          ·
            refine ⟨16451145122778251688707095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21934860163704335584942793 16451145122778251688707095)
            ·
              refine ⟨24676717684167377533060643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16451145122778251688707095 24676717684167377533060643)
              ·
                refine ⟨37015076526251066299590965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24676717684167377533060643 37015076526251066299590965)
                ·
                  refine ⟨3470163424336037465586653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37015076526251066299590965 3470163424336037465586653)
                  ·
                    refine ⟨1301311284126014049594995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3470163424336037465586653 1301311284126014049594995)
                    ·
                      rfl

theorem cell22_3801442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_3801442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801442 prefixEnd_3801442 := by exact prefixLift 3801442
  have htrace : WordTrace (prefixWord ++ tailWord_3801442) baseStart_3801442 baseEnd_3801442 := by
    simpa [prefixWord, tailWord_3801442, baseEnd_3801442] using wordTrace_append hprefix tailTrace_3801442
  have hstable : (prefixWord ++ tailWord_3801442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801442).length < 2 ^ (prefixWord ++ tailWord_3801442).sum := by decide
  have hdescent : baseEnd_3801442 < baseStart_3801442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801605 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 1, 7]
def baseStart_3801605 : Nat := 118140960795 + 3801605 * 2 ^ 59
def prefixEnd_3801605 : Nat := 4983230072969 + 3 ^ 40 * 3801605 * 2
def baseEnd_3801605 : Nat := 1301367082357135957769495

theorem tailTrace_3801605 : CollatzResearch.WordTrace tailWord_3801605 prefixEnd_3801605 1301367082357135957769495 := by
  unfold tailWord_3801605
  simp only [CollatzResearch.WordTrace]
  refine ⟨138655925392441822288686269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92437283594961214859124179 138655925392441822288686269)
  ·
    refine ⟨51995972022165683358257351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138655925392441822288686269 51995972022165683358257351)
    ·
      refine ⟨77993958033248525037386027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51995972022165683358257351 77993958033248525037386027)
      ·
        refine ⟨116990937049872787556079041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77993958033248525037386027 116990937049872787556079041)
        ·
          refine ⟨87743202787404590667059281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116990937049872787556079041 87743202787404590667059281)
          ·
            refine ⟨65807402090553443000294461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87743202787404590667059281 65807402090553443000294461)
            ·
              refine ⟨24677775783957541125110423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65807402090553443000294461 24677775783957541125110423)
              ·
                refine ⟨37016663675936311687665635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24677775783957541125110423 37016663675936311687665635)
                ·
                  refine ⟨55524995513904467531498453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37016663675936311687665635 55524995513904467531498453)
                  ·
                    refine ⟨1301367082357135957769495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55524995513904467531498453 1301367082357135957769495)
                    ·
                      rfl

theorem cell22_3801605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_3801605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801605 prefixEnd_3801605 := by exact prefixLift 3801605
  have htrace : WordTrace (prefixWord ++ tailWord_3801605) baseStart_3801605 baseEnd_3801605 := by
    simpa [prefixWord, tailWord_3801605, baseEnd_3801605] using wordTrace_append hprefix tailTrace_3801605
  have hstable : (prefixWord ++ tailWord_3801605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801605).length < 2 ^ (prefixWord ++ tailWord_3801605).sum := by decide
  have hdescent : baseEnd_3801605 < baseStart_3801605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801645 : List Nat := [1, 5, 4, 1, 1, 1, 2, 1, 3, 3]
def baseStart_3801645 : Nat := 118140960795 + 3801645 * 2 ^ 59
def prefixEnd_3801645 : Nat := 4983230072969 + 3 ^ 40 * 3801645 * 2
def baseEnd_3801645 : Nat := 1301380775174589186769373

theorem tailTrace_3801645 : CollatzResearch.WordTrace tailWord_3801645 prefixEnd_3801645 1301380775174589186769373 := by
  unfold tailWord_3801645
  simp only [CollatzResearch.WordTrace]
  refine ⟨138657384312296909120142389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92438256208197939413428259 138657384312296909120142389)
  ·
    refine ⟨12999129779277835230013349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138657384312296909120142389 12999129779277835230013349)
    ·
      refine ⟨2437336833614594105627503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12999129779277835230013349 2437336833614594105627503)
      ·
        refine ⟨3656005250421891158441255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2437336833614594105627503 3656005250421891158441255)
        ·
          refine ⟨5484007875632836737661883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3656005250421891158441255 5484007875632836737661883)
          ·
            refine ⟨8226011813449255106492825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5484007875632836737661883 8226011813449255106492825)
            ·
              refine ⟨6169508860086941329869619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8226011813449255106492825 6169508860086941329869619)
              ·
                refine ⟨9254263290130411994804429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6169508860086941329869619 9254263290130411994804429)
                ·
                  refine ⟨3470348733798904498051661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9254263290130411994804429 3470348733798904498051661)
                  ·
                    refine ⟨1301380775174589186769373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3470348733798904498051661 1301380775174589186769373)
                    ·
                      rfl

theorem cell22_3801645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_3801645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801645 prefixEnd_3801645 := by exact prefixLift 3801645
  have htrace : WordTrace (prefixWord ++ tailWord_3801645) baseStart_3801645 baseEnd_3801645 := by
    simpa [prefixWord, tailWord_3801645, baseEnd_3801645] using wordTrace_append hprefix tailTrace_3801645
  have hstable : (prefixWord ++ tailWord_3801645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801645).length < 2 ^ (prefixWord ++ tailWord_3801645).sum := by decide
  have hdescent : baseEnd_3801645 < baseStart_3801645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801682 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_3801682 : Nat := 118140960795 + 3801682 * 2 ^ 59
def prefixEnd_3801682 : Nat := 4983230072969 + 3 ^ 40 * 3801682 * 2
def baseEnd_3801682 : Nat := 1301393441030733423594259

theorem tailTrace_3801682 : CollatzResearch.WordTrace tailWord_3801682 prefixEnd_3801682 1301393441030733423594259 := by
  unfold tailWord_3801682
  simp only [CollatzResearch.WordTrace]
  refine ⟨34664683453290716109809825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92439155875441909626159533 34664683453290716109809825)
  ·
    refine ⟨25998512589968037082357369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34664683453290716109809825 25998512589968037082357369)
    ·
      refine ⟨19498884442476027811768027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25998512589968037082357369 19498884442476027811768027)
      ·
        refine ⟨29248326663714041717652041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19498884442476027811768027 29248326663714041717652041)
        ·
          refine ⟨21936244997785531288239031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29248326663714041717652041 21936244997785531288239031)
          ·
            refine ⟨32904367496678296932358547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21936244997785531288239031 32904367496678296932358547)
            ·
              refine ⟨49356551245017445398537821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32904367496678296932358547 49356551245017445398537821)
              ·
                refine ⟨18508706716881542024451683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49356551245017445398537821 18508706716881542024451683)
                ·
                  refine ⟨27763060075322313036677525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18508706716881542024451683 27763060075322313036677525)
                  ·
                    refine ⟨1301393441030733423594259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27763060075322313036677525 1301393441030733423594259)
                    ·
                      rfl

theorem cell22_3801682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_3801682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801682 prefixEnd_3801682 := by exact prefixLift 3801682
  have htrace : WordTrace (prefixWord ++ tailWord_3801682) baseStart_3801682 baseEnd_3801682 := by
    simpa [prefixWord, tailWord_3801682, baseEnd_3801682] using wordTrace_append hprefix tailTrace_3801682
  have hstable : (prefixWord ++ tailWord_3801682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801682).length < 2 ^ (prefixWord ++ tailWord_3801682).sum := by decide
  have hdescent : baseEnd_3801682 < baseStart_3801682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801684 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_3801684 : Nat := 118140960795 + 3801684 * 2 ^ 59
def prefixEnd_3801684 : Nat := 4983230072969 + 3 ^ 40 * 3801684 * 2
def baseEnd_3801684 : Nat := 1301394125671606085044253

theorem tailTrace_3801684 : CollatzResearch.WordTrace tailWord_3801684 prefixEnd_3801684 1301394125671606085044253 := by
  unfold tailWord_3801684
  simp only [CollatzResearch.WordTrace]
  refine ⟨69329403379577809390406053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92439204506103745853874737 69329403379577809390406053)
  ·
    refine ⟨12999263133670839260701135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69329403379577809390406053 12999263133670839260701135)
    ·
      refine ⟨19498894700506258891051703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12999263133670839260701135 19498894700506258891051703)
      ·
        refine ⟨29248342050759388336577555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19498894700506258891051703 29248342050759388336577555)
        ·
          refine ⟨43872513076139082504866333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29248342050759388336577555 43872513076139082504866333)
          ·
            refine ⟨16452192403552155939324875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43872513076139082504866333 16452192403552155939324875)
            ·
              refine ⟨24678288605328233908987313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16452192403552155939324875 24678288605328233908987313)
              ·
                refine ⟨18508716453996175431740485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24678288605328233908987313 18508716453996175431740485)
                ·
                  refine ⟨3470384335124282893451341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18508716453996175431740485 3470384335124282893451341)
                  ·
                    refine ⟨1301394125671606085044253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3470384335124282893451341 1301394125671606085044253)
                    ·
                      rfl

theorem cell22_3801684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_3801684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801684 prefixEnd_3801684 := by exact prefixLift 3801684
  have htrace : WordTrace (prefixWord ++ tailWord_3801684) baseStart_3801684 baseEnd_3801684 := by
    simpa [prefixWord, tailWord_3801684, baseEnd_3801684] using wordTrace_append hprefix tailTrace_3801684
  have hstable : (prefixWord ++ tailWord_3801684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801684).length < 2 ^ (prefixWord ++ tailWord_3801684).sum := by decide
  have hdescent : baseEnd_3801684 < baseStart_3801684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801697 : List Nat := [1, 2, 3, 1, 1, 6, 8]
def baseStart_3801697 : Nat := 118140960795 + 3801697 * 2 ^ 59
def prefixEnd_3801697 : Nat := 4983230072969 + 3 ^ 40 * 3801697 * 2
def baseEnd_3801697 : Nat := 48199947253232532758119

theorem tailTrace_3801697 : CollatzResearch.WordTrace tailWord_3801697 prefixEnd_3801697 48199947253232532758119 := by
  unfold tailWord_3801697
  simp only [CollatzResearch.WordTrace]
  refine ⟨138659280908108522001035345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92439520605405681334023563 138659280908108522001035345)
  ·
    refine ⟨103994460681081391500776509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138659280908108522001035345 103994460681081391500776509)
    ·
      refine ⟨38997922755405521812791191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103994460681081391500776509 38997922755405521812791191)
      ·
        refine ⟨58496884133108282719186787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38997922755405521812791191 58496884133108282719186787)
        ·
          refine ⟨87745326199662424078780181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58496884133108282719186787 87745326199662424078780181)
          ·
            refine ⟨4113062165609176128692821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87745326199662424078780181 4113062165609176128692821)
            ·
              refine ⟨48199947253232532758119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4113062165609176128692821 48199947253232532758119)
              ·
                rfl

theorem cell22_3801697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 8].length) (baseStart_3801697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801697 prefixEnd_3801697 := by exact prefixLift 3801697
  have htrace : WordTrace (prefixWord ++ tailWord_3801697) baseStart_3801697 baseEnd_3801697 := by
    simpa [prefixWord, tailWord_3801697, baseEnd_3801697] using wordTrace_append hprefix tailTrace_3801697
  have hstable : (prefixWord ++ tailWord_3801697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801697).length < 2 ^ (prefixWord ++ tailWord_3801697).sum := by decide
  have hdescent : baseEnd_3801697 < baseStart_3801697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801714 : List Nat := [3, 2, 1, 2, 4, 1, 2, 7]
def baseStart_3801714 : Nat := 118140960795 + 3801714 * 2 ^ 59
def prefixEnd_3801714 : Nat := 4983230072969 + 3 ^ 40 * 3801714 * 2
def baseEnd_3801714 : Nat := 144600488364966222977129

theorem tailTrace_3801714 : CollatzResearch.WordTrace tailWord_3801714 prefixEnd_3801714 144600488364966222977129 := by
  unfold tailWord_3801714
  simp only [CollatzResearch.WordTrace]
  refine ⟨34664975237261733476101049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92439933966031289269602797 34664975237261733476101049)
  ·
    refine ⟨25998731427946300107075787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34664975237261733476101049 25998731427946300107075787)
    ·
      refine ⟨38998097141919450160613681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25998731427946300107075787 38998097141919450160613681)
      ·
        refine ⟨29248572856439587620460261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38998097141919450160613681 29248572856439587620460261)
        ·
          refine ⟨5484107410582422678836299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29248572856439587620460261 5484107410582422678836299)
          ·
            refine ⟨8226161115873634018254449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5484107410582422678836299 8226161115873634018254449)
            ·
              refine ⟨6169620836905225513690837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8226161115873634018254449 6169620836905225513690837)
              ·
                refine ⟨144600488364966222977129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6169620836905225513690837 144600488364966222977129)
                ·
                  rfl

theorem cell22_3801714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 7].length) (baseStart_3801714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801714 prefixEnd_3801714 := by exact prefixLift 3801714
  have htrace : WordTrace (prefixWord ++ tailWord_3801714) baseStart_3801714 baseEnd_3801714 := by
    simpa [prefixWord, tailWord_3801714, baseEnd_3801714] using wordTrace_append hprefix tailTrace_3801714
  have hstable : (prefixWord ++ tailWord_3801714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801714).length < 2 ^ (prefixWord ++ tailWord_3801714).sum := by decide
  have hdescent : baseEnd_3801714 < baseStart_3801714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801718 : List Nat := [5, 1, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_3801718 : Nat := 118140960795 + 3801718 * 2 ^ 59
def prefixEnd_3801718 : Nat := 4983230072969 + 3 ^ 40 * 3801718 * 2
def baseEnd_3801718 : Nat := 1301405764566441329694149

theorem tailTrace_3801718 : CollatzResearch.WordTrace tailWord_3801718 prefixEnd_3801718 1301405764566441329694149 := by
  unfold tailWord_3801718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8666252927564527661721863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92440031227354961725033205 8666252927564527661721863)
  ·
    refine ⟨12999379391346791492582795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8666252927564527661721863 12999379391346791492582795)
    ·
      refine ⟨19499069087020187238874193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12999379391346791492582795 19499069087020187238874193)
      ·
        refine ⟨14624301815265140429155645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19499069087020187238874193 14624301815265140429155645)
        ·
          refine ⟨5484113180724427660933367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14624301815265140429155645 5484113180724427660933367)
          ·
            refine ⟨8226169771086641491400051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5484113180724427660933367 8226169771086641491400051)
            ·
              refine ⟨12339254656629962237100077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8226169771086641491400051 12339254656629962237100077)
              ·
                refine ⟨4627220496236235838912529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12339254656629962237100077 4627220496236235838912529)
                ·
                  refine ⟨3470415372177176879184397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4627220496236235838912529 3470415372177176879184397)
                  ·
                    refine ⟨1301405764566441329694149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3470415372177176879184397 1301405764566441329694149)
                    ·
                      rfl

theorem cell22_3801718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_3801718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801718 prefixEnd_3801718 := by exact prefixLift 3801718
  have htrace : WordTrace (prefixWord ++ tailWord_3801718) baseStart_3801718 baseEnd_3801718 := by
    simpa [prefixWord, tailWord_3801718, baseEnd_3801718] using wordTrace_append hprefix tailTrace_3801718
  have hstable : (prefixWord ++ tailWord_3801718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801718).length < 2 ^ (prefixWord ++ tailWord_3801718).sum := by decide
  have hdescent : baseEnd_3801718 < baseStart_3801718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801729 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 5, 3]
def baseStart_3801729 : Nat := 118140960795 + 3801729 * 2 ^ 59
def prefixEnd_3801729 : Nat := 4983230072969 + 3 ^ 40 * 3801729 * 2
def baseEnd_3801729 : Nat := 1301409530091240967669115

theorem tailTrace_3801729 : CollatzResearch.WordTrace tailWord_3801729 prefixEnd_3801729 1301409530091240967669115 := by
  unfold tailWord_3801729
  simp only [CollatzResearch.WordTrace]
  refine ⟨138660448043992591466200241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92440298695995060977466827 138660448043992591466200241)
  ·
    refine ⟨103995336032994443599650181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138660448043992591466200241 103995336032994443599650181)
    ·
      refine ⟨19499125506186458174934409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103995336032994443599650181 19499125506186458174934409)
      ·
        refine ⟨14624344129639843631200807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19499125506186458174934409 14624344129639843631200807)
        ·
          refine ⟨21936516194459765446801211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14624344129639843631200807 21936516194459765446801211)
          ·
            refine ⟨32904774291689648170201817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21936516194459765446801211 32904774291689648170201817)
            ·
              refine ⟨24678580718767236127651363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32904774291689648170201817 24678580718767236127651363)
              ·
                refine ⟨37017871078150854191477045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24678580718767236127651363 37017871078150854191477045)
                ·
                  refine ⟨3470425413576642580450973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37017871078150854191477045 3470425413576642580450973)
                  ·
                    refine ⟨1301409530091240967669115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3470425413576642580450973 1301409530091240967669115)
                    ·
                      rfl

theorem cell22_3801729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_3801729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801729 prefixEnd_3801729 := by exact prefixLift 3801729
  have htrace : WordTrace (prefixWord ++ tailWord_3801729) baseStart_3801729 baseEnd_3801729 := by
    simpa [prefixWord, tailWord_3801729, baseEnd_3801729] using wordTrace_append hprefix tailTrace_3801729
  have hstable : (prefixWord ++ tailWord_3801729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801729).length < 2 ^ (prefixWord ++ tailWord_3801729).sum := by decide
  have hdescent : baseEnd_3801729 < baseStart_3801729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801789 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_3801789 : Nat := 118140960795 + 3801789 * 2 ^ 59
def prefixEnd_3801789 : Nat := 4983230072969 + 3 ^ 40 * 3801789 * 2
def baseEnd_3801789 : Nat := 1301430069317420811168931

theorem tailTrace_3801789 : CollatzResearch.WordTrace tailWord_3801789 prefixEnd_3801789 1301430069317420811168931 := by
  unfold tailWord_3801789
  simp only [CollatzResearch.WordTrace]
  refine ⟨138662636423775221713384421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92441757615850147808922947 138662636423775221713384421)
  ·
    refine ⟨25999244329457854071259579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138662636423775221713384421 25999244329457854071259579)
    ·
      refine ⟨38998866494186781106889369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25999244329457854071259579 38998866494186781106889369)
      ·
        refine ⟨29249149870640085830167027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38998866494186781106889369 29249149870640085830167027)
        ·
          refine ⟨43873724805960128745250541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29249149870640085830167027 43873724805960128745250541)
          ·
            refine ⟨16452646802235048279468953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43873724805960128745250541 16452646802235048279468953)
            ·
              refine ⟨12339485101676286209601715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16452646802235048279468953 12339485101676286209601715)
              ·
                refine ⟨18509227652514429314402573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12339485101676286209601715 18509227652514429314402573)
                ·
                  refine ⟨6940960369692910992900965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18509227652514429314402573 6940960369692910992900965)
                  ·
                    refine ⟨1301430069317420811168931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6940960369692910992900965 1301430069317420811168931)
                    ·
                      rfl

theorem cell22_3801789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_3801789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801789 prefixEnd_3801789 := by exact prefixLift 3801789
  have htrace : WordTrace (prefixWord ++ tailWord_3801789) baseStart_3801789 baseEnd_3801789 := by
    simpa [prefixWord, tailWord_3801789, baseEnd_3801789] using wordTrace_append hprefix tailTrace_3801789
  have hstable : (prefixWord ++ tailWord_3801789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801789).length < 2 ^ (prefixWord ++ tailWord_3801789).sum := by decide
  have hdescent : baseEnd_3801789 < baseStart_3801789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801806 : List Nat := [4, 1, 1, 1, 3, 3, 1, 3, 1, 4]
def baseStart_3801806 : Nat := 118140960795 + 3801806 * 2 ^ 59
def prefixEnd_3801806 : Nat := 4983230072969 + 3 ^ 40 * 3801806 * 2
def baseEnd_3801806 : Nat := 1301435888764838433493879

theorem tailTrace_3801806 : CollatzResearch.WordTrace tailWord_3801806 prefixEnd_3801806 1301435888764838433493879 := by
  unfold tailWord_3801806
  simp only [CollatzResearch.WordTrace]
  refine ⟨17332907058089204202094159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92442170976475755744502181 17332907058089204202094159)
  ·
    refine ⟨25999360587133806303141239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17332907058089204202094159 25999360587133806303141239)
    ·
      refine ⟨38999040880700709454711859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25999360587133806303141239 38999040880700709454711859)
      ·
        refine ⟨58498561321051064182067789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38999040880700709454711859 58498561321051064182067789)
        ·
          refine ⟨21936960495394149068275421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58498561321051064182067789 21936960495394149068275421)
          ·
            refine ⟨8226360185772805900603283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21936960495394149068275421 8226360185772805900603283)
            ·
              refine ⟨12339540278659208850904925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8226360185772805900603283 12339540278659208850904925)
              ·
                refine ⟨4627327604497203319089347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12339540278659208850904925 4627327604497203319089347)
                ·
                  refine ⟨6940991406745804978634021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4627327604497203319089347 6940991406745804978634021)
                  ·
                    refine ⟨1301435888764838433493879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6940991406745804978634021 1301435888764838433493879)
                    ·
                      rfl

theorem cell22_3801806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_3801806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801806 prefixEnd_3801806 := by exact prefixLift 3801806
  have htrace : WordTrace (prefixWord ++ tailWord_3801806) baseStart_3801806 baseEnd_3801806 := by
    simpa [prefixWord, tailWord_3801806, baseEnd_3801806] using wordTrace_append hprefix tailTrace_3801806
  have hstable : (prefixWord ++ tailWord_3801806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801806).length < 2 ^ (prefixWord ++ tailWord_3801806).sum := by decide
  have hdescent : baseEnd_3801806 < baseStart_3801806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801847 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 1, 9]
def baseStart_3801847 : Nat := 118140960795 + 3801847 * 2 ^ 59
def prefixEnd_3801847 : Nat := 4983230072969 + 3 ^ 40 * 3801847 * 2
def baseEnd_3801847 : Nat := 1301449923902727993218753

theorem tailTrace_3801847 : CollatzResearch.WordTrace tailWord_3801847 prefixEnd_3801847 1301449923902727993218753 := by
  unfold tailWord_3801847
  simp only [CollatzResearch.WordTrace]
  refine ⟨138664751857565097618995795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92443167905043398412663863 138664751857565097618995795)
  ·
    refine ⟨207997127786347646428493693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138664751857565097618995795 207997127786347646428493693)
    ·
      refine ⟨77998922919880367410685135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207997127786347646428493693 77998922919880367410685135)
      ·
        refine ⟨116998384379820551116027703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77998922919880367410685135 116998384379820551116027703)
        ·
          refine ⟨175497576569730826674041555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116998384379820551116027703 175497576569730826674041555)
          ·
            refine ⟨263246364854596240011062333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175497576569730826674041555 263246364854596240011062333)
            ·
              refine ⟨98717386820473590004148375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263246364854596240011062333 98717386820473590004148375)
              ·
                refine ⟨148076080230710385006222563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98717386820473590004148375 148076080230710385006222563)
                ·
                  refine ⟨222114120346065577509333845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148076080230710385006222563 222114120346065577509333845)
                  ·
                    refine ⟨1301449923902727993218753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 222114120346065577509333845 1301449923902727993218753)
                    ·
                      rfl

theorem cell22_3801847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_3801847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801847 prefixEnd_3801847 := by exact prefixLift 3801847
  have htrace : WordTrace (prefixWord ++ tailWord_3801847) baseStart_3801847 baseEnd_3801847 := by
    simpa [prefixWord, tailWord_3801847, baseEnd_3801847] using wordTrace_append hprefix tailTrace_3801847
  have hstable : (prefixWord ++ tailWord_3801847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801847).length < 2 ^ (prefixWord ++ tailWord_3801847).sum := by decide
  have hdescent : baseEnd_3801847 < baseStart_3801847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801932 : List Nat := [2, 2, 1, 3, 3, 3, 2, 2, 1, 3]
def baseStart_3801932 : Nat := 118140960795 + 3801932 * 2 ^ 59
def prefixEnd_3801932 : Nat := 4983230072969 + 3 ^ 40 * 3801932 * 2
def baseEnd_3801932 : Nat := 1301479021139816104843493

theorem tailTrace_3801932 : CollatzResearch.WordTrace tailWord_3801932 prefixEnd_3801932 1301479021139816104843493 := by
  unfold tailWord_3801932
  simp only [CollatzResearch.WordTrace]
  refine ⟨69333926031128578567920025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92445234708171438090560033 69333926031128578567920025)
  ·
    refine ⟨52000444523346433925940019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69333926031128578567920025 52000444523346433925940019)
    ·
      refine ⟨78000666785019650888910029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52000444523346433925940019 78000666785019650888910029)
      ·
        refine ⟨29250250044382369083341261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78000666785019650888910029 29250250044382369083341261)
        ·
          refine ⟨10968843766643388406252973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29250250044382369083341261 10968843766643388406252973)
          ·
            refine ⟨4113316412491270652344865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10968843766643388406252973 4113316412491270652344865)
            ·
              refine ⟨3084987309368452989258649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4113316412491270652344865 3084987309368452989258649)
              ·
                refine ⟨2313740482026339741943987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3084987309368452989258649 2313740482026339741943987)
                ·
                  refine ⟨3470610723039509612915981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2313740482026339741943987 3470610723039509612915981)
                  ·
                    refine ⟨1301479021139816104843493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3470610723039509612915981 1301479021139816104843493)
                    ·
                      rfl

theorem cell22_3801932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 1, 3].length) (baseStart_3801932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801932 prefixEnd_3801932 := by exact prefixLift 3801932
  have htrace : WordTrace (prefixWord ++ tailWord_3801932) baseStart_3801932 baseEnd_3801932 := by
    simpa [prefixWord, tailWord_3801932, baseEnd_3801932] using wordTrace_append hprefix tailTrace_3801932
  have hstable : (prefixWord ++ tailWord_3801932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801932).length < 2 ^ (prefixWord ++ tailWord_3801932).sum := by decide
  have hdescent : baseEnd_3801932 < baseStart_3801932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801956 : List Nat := [2, 3, 1, 1, 4, 2, 1, 2, 6]
def baseStart_3801956 : Nat := 118140960795 + 3801956 * 2 ^ 59
def prefixEnd_3801956 : Nat := 4983230072969 + 3 ^ 40 * 3801956 * 2
def baseEnd_3801956 : Nat := 433829078943429347414473

theorem tailTrace_3801956 : CollatzResearch.WordTrace tailWord_3801956 prefixEnd_3801956 433829078943429347414473 := by
  unfold tailWord_3801956
  simp only [CollatzResearch.WordTrace]
  refine ⟨69334363707085104617356861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92445818276113472823142481 69334363707085104617356861)
  ·
    refine ⟨26000386390156914231508823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69334363707085104617356861 26000386390156914231508823)
    ·
      refine ⟨39000579585235371347263235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26000386390156914231508823 39000579585235371347263235)
      ·
        refine ⟨58500869377853057020894853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39000579585235371347263235 58500869377853057020894853)
        ·
          refine ⟨10968913008347448191417785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58500869377853057020894853 10968913008347448191417785)
          ·
            refine ⟨8226684756260586143563339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10968913008347448191417785 8226684756260586143563339)
            ·
              refine ⟨12340027134390879215345009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8226684756260586143563339 12340027134390879215345009)
              ·
                refine ⟨9255020350793159411508757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12340027134390879215345009 9255020350793159411508757)
                ·
                  refine ⟨433829078943429347414473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9255020350793159411508757 433829078943429347414473)
                  ·
                    rfl

theorem cell22_3801956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_3801956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801956 prefixEnd_3801956 := by exact prefixLift 3801956
  have htrace : WordTrace (prefixWord ++ tailWord_3801956) baseStart_3801956 baseEnd_3801956 := by
    simpa [prefixWord, tailWord_3801956, baseEnd_3801956] using wordTrace_append hprefix tailTrace_3801956
  have hstable : (prefixWord ++ tailWord_3801956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801956).length < 2 ^ (prefixWord ++ tailWord_3801956).sum := by decide
  have hdescent : baseEnd_3801956 < baseStart_3801956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3801973 : List Nat := [1, 3, 4, 1, 1, 2, 1, 5, 4]
def baseStart_3801973 : Nat := 118140960795 + 3801973 * 2 ^ 59
def prefixEnd_3801973 : Nat := 4983230072969 + 3 ^ 40 * 3801973 * 2
def baseEnd_3801973 : Nat := 433831018759235221522789

theorem tailTrace_3801973 : CollatzResearch.WordTrace tailWord_3801973 prefixEnd_3801973 433831018759235221522789 := by
  unfold tailWord_3801973
  simp only [CollatzResearch.WordTrace]
  refine ⟨138669347455108621138082573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92446231636739080758721715 138669347455108621138082573)
  ·
    refine ⟨52001005295665732926780965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138669347455108621138082573 52001005295665732926780965)
    ·
      refine ⟨9750188492937324923771431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52001005295665732926780965 9750188492937324923771431)
      ·
        refine ⟨14625282739405987385657147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9750188492937324923771431 14625282739405987385657147)
        ·
          refine ⟨21937924109108981078485721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14625282739405987385657147 21937924109108981078485721)
          ·
            refine ⟨16453443081831735808864291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21937924109108981078485721 16453443081831735808864291)
            ·
              refine ⟨24680164622747603713296437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16453443081831735808864291 24680164622747603713296437)
              ·
                refine ⟨2313765433382587848121541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24680164622747603713296437 2313765433382587848121541)
                ·
                  refine ⟨433831018759235221522789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2313765433382587848121541 433831018759235221522789)
                  ·
                    rfl

theorem cell22_3801973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 4].length) (baseStart_3801973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3801973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3801973 prefixEnd_3801973 := by exact prefixLift 3801973
  have htrace : WordTrace (prefixWord ++ tailWord_3801973) baseStart_3801973 baseEnd_3801973 := by
    simpa [prefixWord, tailWord_3801973, baseEnd_3801973] using wordTrace_append hprefix tailTrace_3801973
  have hstable : (prefixWord ++ tailWord_3801973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3801973).length < 2 ^ (prefixWord ++ tailWord_3801973).sum := by decide
  have hdescent : baseEnd_3801973 < baseStart_3801973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3801973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802005 : List Nat := [1, 3, 2, 1, 1, 5, 3, 1, 2, 3]
def baseStart_3802005 : Nat := 118140960795 + 3802005 * 2 ^ 59
def prefixEnd_3802005 : Nat := 4983230072969 + 3 ^ 40 * 3802005 * 2
def baseEnd_3802005 : Nat := 1301504010531668247768269

theorem tailTrace_3802005 : CollatzResearch.WordTrace tailWord_3802005 prefixEnd_3802005 1301504010531668247768269 := by
  unfold tailWord_3802005
  simp only [CollatzResearch.WordTrace]
  refine ⟨138670514590992690603247469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92447009727328460402164979 138670514590992690603247469)
  ·
    refine ⟨52001442971622258976217801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138670514590992690603247469 52001442971622258976217801)
    ·
      refine ⟨39001082228716694232163351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52001442971622258976217801 39001082228716694232163351)
      ·
        refine ⟨58501623343075041348245027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39001082228716694232163351 58501623343075041348245027)
        ·
          refine ⟨87752435014612562022367541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58501623343075041348245027 87752435014612562022367541)
          ·
            refine ⟨8226790782619927689596957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87752435014612562022367541 8226790782619927689596957)
            ·
              refine ⟨3085046543482472883598859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8226790782619927689596957 3085046543482472883598859)
              ·
                refine ⟨4627569815223709325398289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3085046543482472883598859 4627569815223709325398289)
                ·
                  refine ⟨3470677361417781994048717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4627569815223709325398289 3470677361417781994048717)
                  ·
                    refine ⟨1301504010531668247768269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3470677361417781994048717 1301504010531668247768269)
                    ·
                      rfl

theorem cell22_3802005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_3802005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802005 prefixEnd_3802005 := by exact prefixLift 3802005
  have htrace : WordTrace (prefixWord ++ tailWord_3802005) baseStart_3802005 baseEnd_3802005 := by
    simpa [prefixWord, tailWord_3802005, baseEnd_3802005] using wordTrace_append hprefix tailTrace_3802005
  have hstable : (prefixWord ++ tailWord_3802005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802005).length < 2 ^ (prefixWord ++ tailWord_3802005).sum := by decide
  have hdescent : baseEnd_3802005 < baseStart_3802005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802018 : List Nat := [3, 3, 1, 2, 2, 1, 4, 6]
def baseStart_3802018 : Nat := 118140960795 + 3802018 * 2 ^ 59
def prefixEnd_3802018 : Nat := 4983230072969 + 3 ^ 40 * 3802018 * 2
def baseEnd_3802018 : Nat := 144612051188593394132581

theorem tailTrace_3802018 : CollatzResearch.WordTrace tailWord_3802018 prefixEnd_3802018 144612051188593394132581 := by
  unfold tailWord_3802018
  simp only [CollatzResearch.WordTrace]
  refine ⟨34667747184986398455867677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92447325826630395882313805 34667747184986398455867677)
  ·
    refine ⟨13000405194369899420950379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34667747184986398455867677 13000405194369899420950379)
    ·
      refine ⟨19500607791554849131425569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13000405194369899420950379 19500607791554849131425569)
      ·
        refine ⟨14625455843666136848569177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19500607791554849131425569 14625455843666136848569177)
        ·
          refine ⟨10969091882749602636426883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14625455843666136848569177 10969091882749602636426883)
          ·
            refine ⟨16453637824124403954640325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10969091882749602636426883 16453637824124403954640325)
            ·
              refine ⟨3085057092023325741495061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16453637824124403954640325 3085057092023325741495061)
              ·
                refine ⟨144612051188593394132581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3085057092023325741495061 144612051188593394132581)
                ·
                  rfl

theorem cell22_3802018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 6].length) (baseStart_3802018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802018 prefixEnd_3802018 := by exact prefixLift 3802018
  have htrace : WordTrace (prefixWord ++ tailWord_3802018) baseStart_3802018 baseEnd_3802018 := by
    simpa [prefixWord, tailWord_3802018, baseEnd_3802018] using wordTrace_append hprefix tailTrace_3802018
  have hstable : (prefixWord ++ tailWord_3802018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802018).length < 2 ^ (prefixWord ++ tailWord_3802018).sum := by decide
  have hdescent : baseEnd_3802018 < baseStart_3802018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802046 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 7]
def baseStart_3802046 : Nat := 118140960795 + 3802046 * 2 ^ 59
def prefixEnd_3802046 : Nat := 4983230072969 + 3 ^ 40 * 3802046 * 2
def baseEnd_3802046 : Nat := 433839348556519269164381

theorem tailTrace_3802046 : CollatzResearch.WordTrace tailWord_3802046 prefixEnd_3802046 433839348556519269164381 := by
  unfold tailWord_3802046
  simp only [CollatzResearch.WordTrace]
  refine ⟨17334001247980519325686249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92448006655896103070326661 17334001247980519325686249)
  ·
    refine ⟨13000500935985389494264687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17334001247980519325686249 13000500935985389494264687)
    ·
      refine ⟨19500751403978084241397031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13000500935985389494264687 19500751403978084241397031)
      ·
        refine ⟨29251127105967126362095547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19500751403978084241397031 29251127105967126362095547)
        ·
          refine ⟨43876690658950689543143321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29251127105967126362095547 43876690658950689543143321)
          ·
            refine ⟨32907517994213017157357491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43876690658950689543143321 32907517994213017157357491)
            ·
              refine ⟨49361276991319525736036237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32907517994213017157357491 49361276991319525736036237)
              ·
                refine ⟨18510478871744822151013589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49361276991319525736036237 18510478871744822151013589)
                ·
                  refine ⟨433839348556519269164381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18510478871744822151013589 433839348556519269164381)
                  ·
                    rfl

theorem cell22_3802046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_3802046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802046 prefixEnd_3802046 := by exact prefixLift 3802046
  have htrace : WordTrace (prefixWord ++ tailWord_3802046) baseStart_3802046 baseEnd_3802046 := by
    simpa [prefixWord, tailWord_3802046, baseEnd_3802046] using wordTrace_append hprefix tailTrace_3802046
  have hstable : (prefixWord ++ tailWord_3802046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802046).length < 2 ^ (prefixWord ++ tailWord_3802046).sum := by decide
  have hdescent : baseEnd_3802046 < baseStart_3802046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802063 : List Nat := [1, 1, 2, 1, 1, 6, 4, 1, 5]
def baseStart_3802063 : Nat := 118140960795 + 3802063 * 2 ^ 59
def prefixEnd_3802063 : Nat := 4983230072969 + 3 ^ 40 * 3802063 * 2
def baseEnd_3802063 : Nat := 433841288372325143272697

theorem tailTrace_3802063 : CollatzResearch.WordTrace tailWord_3802063 prefixEnd_3802063 433841288372325143272697 := by
  unfold tailWord_3802063
  simp only [CollatzResearch.WordTrace]
  refine ⟨138672630024782566508858843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92448420016521711005905895 138672630024782566508858843)
  ·
    refine ⟨208008945037173849763288265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138672630024782566508858843 208008945037173849763288265)
    ·
      refine ⟨156006708777880387322466199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208008945037173849763288265 156006708777880387322466199)
      ·
        refine ⟨234010063166820580983699299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156006708777880387322466199 234010063166820580983699299)
        ·
          refine ⟨351015094750230871475548949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234010063166820580983699299 351015094750230871475548949)
          ·
            refine ⟨16453832566417072100416357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 351015094750230871475548949 16453832566417072100416357)
            ·
              refine ⟨3085093606203201018828067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16453832566417072100416357 3085093606203201018828067)
              ·
                refine ⟨4627640409304801528242101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3085093606203201018828067 4627640409304801528242101)
                ·
                  refine ⟨433841288372325143272697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4627640409304801528242101 433841288372325143272697)
                  ·
                    rfl

theorem cell22_3802063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 5].length) (baseStart_3802063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802063 prefixEnd_3802063 := by exact prefixLift 3802063
  have htrace : WordTrace (prefixWord ++ tailWord_3802063) baseStart_3802063 baseEnd_3802063 := by
    simpa [prefixWord, tailWord_3802063, baseEnd_3802063] using wordTrace_append hprefix tailTrace_3802063
  have hstable : (prefixWord ++ tailWord_3802063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802063).length < 2 ^ (prefixWord ++ tailWord_3802063).sum := by decide
  have hdescent : baseEnd_3802063 < baseStart_3802063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802121 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 4, 4]
def baseStart_3802121 : Nat := 118140960795 + 3802121 * 2 ^ 59
def prefixEnd_3802121 : Nat := 4983230072969 + 3 ^ 40 * 3802121 * 2
def baseEnd_3802121 : Nat := 1301543719702282611867913

theorem tailTrace_3802121 : CollatzResearch.WordTrace tailWord_3802121 prefixEnd_3802121 1301543719702282611867913 := by
  unfold tailWord_3802121
  simp only [CollatzResearch.WordTrace]
  refine ⟨138674745458572442414470217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92449830305714961609646811 138674745458572442414470217)
  ·
    refine ⟨104006059093929331810852663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138674745458572442414470217 104006059093929331810852663)
    ·
      refine ⟨156009088640893997716278995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104006059093929331810852663 156009088640893997716278995)
      ·
        refine ⟨234013632961340996574418493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156009088640893997716278995 234013632961340996574418493)
        ·
          refine ⟨87755112360502873715406935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234013632961340996574418493 87755112360502873715406935)
          ·
            refine ⟨131632668540754310573110403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87755112360502873715406935 131632668540754310573110403)
            ·
              refine ⟨197449002811131465859665605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131632668540754310573110403 197449002811131465859665605)
              ·
                refine ⟨37021688027087149848687301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197449002811131465859665605 37021688027087149848687301)
                ·
                  refine ⟨6941566505078840596628869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37021688027087149848687301 6941566505078840596628869)
                  ·
                    refine ⟨1301543719702282611867913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6941566505078840596628869 1301543719702282611867913)
                    ·
                      rfl

theorem cell22_3802121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 4].length) (baseStart_3802121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802121 prefixEnd_3802121 := by exact prefixLift 3802121
  have htrace : WordTrace (prefixWord ++ tailWord_3802121) baseStart_3802121 baseEnd_3802121 := by
    simpa [prefixWord, tailWord_3802121, baseEnd_3802121] using wordTrace_append hprefix tailTrace_3802121
  have hstable : (prefixWord ++ tailWord_3802121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802121).length < 2 ^ (prefixWord ++ tailWord_3802121).sum := by decide
  have hdescent : baseEnd_3802121 < baseStart_3802121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802123 : List Nat := [1, 1, 1, 1, 6, 3, 2, 1, 1, 5]
def baseStart_3802123 : Nat := 118140960795 + 3802123 * 2 ^ 59
def prefixEnd_3802123 : Nat := 4983230072969 + 3 ^ 40 * 3802123 * 2
def baseEnd_3802123 : Nat := 1301544404343155273317907

theorem tailTrace_3802123 : CollatzResearch.WordTrace tailWord_3802123 prefixEnd_3802123 1301544404343155273317907 := by
  unfold tailWord_3802123
  simp only [CollatzResearch.WordTrace]
  refine ⟨138674818404565196756043023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92449878936376797837362015 138674818404565196756043023)
  ·
    refine ⟨208012227606847795134064535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138674818404565196756043023 208012227606847795134064535)
    ·
      refine ⟨312018341410271692701096803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208012227606847795134064535 312018341410271692701096803)
      ·
        refine ⟨468027512115407539051645205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312018341410271692701096803 468027512115407539051645205)
        ·
          refine ⟨21938789630409728393045869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 468027512115407539051645205 21938789630409728393045869)
          ·
            refine ⟨8227046111403648147392201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21938789630409728393045869 8227046111403648147392201)
            ·
              refine ⟨6170284583552736110544151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8227046111403648147392201 6170284583552736110544151)
              ·
                refine ⟨9255426875329104165816227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6170284583552736110544151 9255426875329104165816227)
                ·
                  refine ⟨13883140312993656248724341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9255426875329104165816227 13883140312993656248724341)
                  ·
                    refine ⟨1301544404343155273317907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13883140312993656248724341 1301544404343155273317907)
                    ·
                      rfl

theorem cell22_3802123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 5].length) (baseStart_3802123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802123 prefixEnd_3802123 := by exact prefixLift 3802123
  have htrace : WordTrace (prefixWord ++ tailWord_3802123) baseStart_3802123 baseEnd_3802123 := by
    simpa [prefixWord, tailWord_3802123, baseEnd_3802123] using wordTrace_append hprefix tailTrace_3802123
  have hstable : (prefixWord ++ tailWord_3802123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802123).length < 2 ^ (prefixWord ++ tailWord_3802123).sum := by decide
  have hdescent : baseEnd_3802123 < baseStart_3802123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802144 : List Nat := [2, 1, 1, 7, 1, 2, 2, 1, 1, 4]
def baseStart_3802144 : Nat := 118140960795 + 3802144 * 2 ^ 59
def prefixEnd_3802144 : Nat := 4983230072969 + 3 ^ 40 * 3802144 * 2
def baseEnd_3802144 : Nat := 1301551593072318218542843

theorem tailTrace_3802144 : CollatzResearch.WordTrace tailWord_3802144 prefixEnd_3802144 1301551593072318218542843 := by
  unfold tailWord_3802144
  simp only [CollatzResearch.WordTrace]
  refine ⟨69337792168744558671278743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92450389558326078228371657 69337792168744558671278743)
  ·
    refine ⟨104006688253116838006918115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69337792168744558671278743 104006688253116838006918115)
    ·
      refine ⟨156010032379675257010377173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104006688253116838006918115 156010032379675257010377173)
      ·
        refine ⟨3656485133898638836180715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 156010032379675257010377173 3656485133898638836180715)
        ·
          refine ⟨5484727700847958254271073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3656485133898638836180715 5484727700847958254271073)
          ·
            refine ⟨4113545775635968690703305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5484727700847958254271073 4113545775635968690703305)
            ·
              refine ⟨3085159331726976518027479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4113545775635968690703305 3085159331726976518027479)
              ·
                refine ⟨4627738997590464777041219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3085159331726976518027479 4627738997590464777041219)
                ·
                  refine ⟨6941608496385697165561829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4627738997590464777041219 6941608496385697165561829)
                  ·
                    refine ⟨1301551593072318218542843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6941608496385697165561829 1301551593072318218542843)
                    ·
                      rfl

theorem cell22_3802144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 1, 4].length) (baseStart_3802144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802144 prefixEnd_3802144 := by exact prefixLift 3802144
  have htrace : WordTrace (prefixWord ++ tailWord_3802144) baseStart_3802144 baseEnd_3802144 := by
    simpa [prefixWord, tailWord_3802144, baseEnd_3802144] using wordTrace_append hprefix tailTrace_3802144
  have hstable : (prefixWord ++ tailWord_3802144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802144).length < 2 ^ (prefixWord ++ tailWord_3802144).sum := by decide
  have hdescent : baseEnd_3802144 < baseStart_3802144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802174 : List Nat := [4, 2, 1, 3, 1, 2, 3, 1, 2, 3]
def baseStart_3802174 : Nat := 118140960795 + 3802174 * 2 ^ 59
def prefixEnd_3802174 : Nat := 4983230072969 + 3 ^ 40 * 3802174 * 2
def baseEnd_3802174 : Nat := 1301561862685408140292751

theorem tailTrace_3802174 : CollatzResearch.WordTrace tailWord_3802174 prefixEnd_3802174 1301561862685408140292751 := by
  unfold tailWord_3802174
  simp only [CollatzResearch.WordTrace]
  refine ⟨17334584815922554058268697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92451119018253621644099717 17334584815922554058268697)
  ·
    refine ⟨13000938611941915543701523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17334584815922554058268697 13000938611941915543701523)
    ·
      refine ⟨19501407917912873315552285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13000938611941915543701523 19501407917912873315552285)
      ·
        refine ⟨7313027969217327493332107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19501407917912873315552285 7313027969217327493332107)
        ·
          refine ⟨10969541953825991239998161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7313027969217327493332107 10969541953825991239998161)
          ·
            refine ⟨8227156465369493429998621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10969541953825991239998161 8227156465369493429998621)
            ·
              refine ⟨3085183674513560036249483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8227156465369493429998621 3085183674513560036249483)
              ·
                refine ⟨4627775511770340054374225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3085183674513560036249483 4627775511770340054374225)
                ·
                  refine ⟨3470831633827755040780669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4627775511770340054374225 3470831633827755040780669)
                  ·
                    refine ⟨1301561862685408140292751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3470831633827755040780669 1301561862685408140292751)
                    ·
                      rfl

theorem cell22_3802174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_3802174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802174 prefixEnd_3802174 := by exact prefixLift 3802174
  have htrace : WordTrace (prefixWord ++ tailWord_3802174) baseStart_3802174 baseEnd_3802174 := by
    simpa [prefixWord, tailWord_3802174, baseEnd_3802174] using wordTrace_append hprefix tailTrace_3802174
  have hstable : (prefixWord ++ tailWord_3802174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802174).length < 2 ^ (prefixWord ++ tailWord_3802174).sum := by decide
  have hdescent : baseEnd_3802174 < baseStart_3802174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802245 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 3, 4]
def baseStart_3802245 : Nat := 118140960795 + 3802245 * 2 ^ 59
def prefixEnd_3802245 : Nat := 4983230072969 + 3 ^ 40 * 3802245 * 2
def baseEnd_3802245 : Nat := 1301586167436387621767533

theorem tailTrace_3802245 : CollatzResearch.WordTrace tailWord_3802245 prefixEnd_3802245 1301586167436387621767533 := by
  unfold tailWord_3802245
  simp only [CollatzResearch.WordTrace]
  refine ⟨138679268110123211591984189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92452845406748807727989459 138679268110123211591984189)
  ·
    refine ⟨52004725541296204346994071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138679268110123211591984189 52004725541296204346994071)
    ·
      refine ⟨78007088311944306520491107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52004725541296204346994071 78007088311944306520491107)
      ·
        refine ⟨117010632467916459780736661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78007088311944306520491107 117010632467916459780736661)
        ·
          refine ⟨5484873396933584052222031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 117010632467916459780736661 5484873396933584052222031)
          ·
            refine ⟨8227310095400376078333047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5484873396933584052222031 8227310095400376078333047)
            ·
              refine ⟨12340965143100564117499571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8227310095400376078333047 12340965143100564117499571)
              ·
                refine ⟨18511447714650846176249357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12340965143100564117499571 18511447714650846176249357)
                ·
                  refine ⟨6941792892994067316093509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18511447714650846176249357 6941792892994067316093509)
                  ·
                    refine ⟨1301586167436387621767533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6941792892994067316093509 1301586167436387621767533)
                    ·
                      rfl

theorem cell22_3802245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_3802245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802245 prefixEnd_3802245 := by exact prefixLift 3802245
  have htrace : WordTrace (prefixWord ++ tailWord_3802245) baseStart_3802245 baseEnd_3802245 := by
    simpa [prefixWord, tailWord_3802245, baseEnd_3802245] using wordTrace_append hprefix tailTrace_3802245
  have hstable : (prefixWord ++ tailWord_3802245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802245).length < 2 ^ (prefixWord ++ tailWord_3802245).sum := by decide
  have hdescent : baseEnd_3802245 < baseStart_3802245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802277 : List Nat := [1, 3, 1, 2, 1, 4, 4, 2, 4]
def baseStart_3802277 : Nat := 118140960795 + 3802277 * 2 ^ 59
def prefixEnd_3802277 : Nat := 4983230072969 + 3 ^ 40 * 3802277 * 2
def baseEnd_3802277 : Nat := 433865707230116734989145

theorem tailTrace_3802277 : CollatzResearch.WordTrace tailWord_3802277 prefixEnd_3802277 433865707230116734989145 := by
  unfold tailWord_3802277
  simp only [CollatzResearch.WordTrace]
  refine ⟨138680435246007281057149085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92453623497338187371432723 138680435246007281057149085)
  ·
    refine ⟨52005163217252730396430907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138680435246007281057149085 52005163217252730396430907)
    ·
      refine ⟨78007744825879095594646361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52005163217252730396430907 78007744825879095594646361)
      ·
        refine ⟨58505808619409321695984771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78007744825879095594646361 58505808619409321695984771)
        ·
          refine ⟨87758712929113982543977157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58505808619409321695984771 87758712929113982543977157)
          ·
            refine ⟨16454758674208871726995717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87758712929113982543977157 16454758674208871726995717)
            ·
              refine ⟨3085267251414163448811697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16454758674208871726995717 3085267251414163448811697)
              ·
                refine ⟨2313950438560622586608773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3085267251414163448811697 2313950438560622586608773)
                ·
                  refine ⟨433865707230116734989145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2313950438560622586608773 433865707230116734989145)
                  ·
                    rfl

theorem cell22_3802277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 4].length) (baseStart_3802277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802277 prefixEnd_3802277 := by exact prefixLift 3802277
  have htrace : WordTrace (prefixWord ++ tailWord_3802277) baseStart_3802277 baseEnd_3802277 := by
    simpa [prefixWord, tailWord_3802277, baseEnd_3802277] using wordTrace_append hprefix tailTrace_3802277
  have hstable : (prefixWord ++ tailWord_3802277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802277).length < 2 ^ (prefixWord ++ tailWord_3802277).sum := by decide
  have hdescent : baseEnd_3802277 < baseStart_3802277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802294 : List Nat := [5, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_3802294 : Nat := 118140960795 + 3802294 * 2 ^ 59
def prefixEnd_3802294 : Nat := 4983230072969 + 3 ^ 40 * 3802294 * 2
def baseEnd_3802294 : Nat := 433867647045922609097461

theorem tailTrace_3802294 : CollatzResearch.WordTrace tailWord_3802294 prefixEnd_3802294 433867647045922609097461 := by
  unfold tailWord_3802294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8667565955434105810032371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92454036857963795307011957 8667565955434105810032371)
  ·
    refine ⟨13001348933151158715048557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8667565955434105810032371 13001348933151158715048557)
    ·
      refine ⟨4875505849931684518143209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13001348933151158715048557 4875505849931684518143209)
      ·
        refine ⟨3656629387448763388607407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4875505849931684518143209 3656629387448763388607407)
        ·
          refine ⟨5484944081173145082911111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3656629387448763388607407 5484944081173145082911111)
          ·
            refine ⟨8227416121759717624366667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5484944081173145082911111 8227416121759717624366667)
            ·
              refine ⟨12341124182639576436550001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8227416121759717624366667 12341124182639576436550001)
              ·
                refine ⟨9255843136979682327412501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12341124182639576436550001 9255843136979682327412501)
                ·
                  refine ⟨433867647045922609097461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9255843136979682327412501 433867647045922609097461)
                  ·
                    rfl

theorem cell22_3802294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_3802294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802294 prefixEnd_3802294 := by exact prefixLift 3802294
  have htrace : WordTrace (prefixWord ++ tailWord_3802294) baseStart_3802294 baseEnd_3802294 := by
    simpa [prefixWord, tailWord_3802294, baseEnd_3802294] using wordTrace_append hprefix tailTrace_3802294
  have hstable : (prefixWord ++ tailWord_3802294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802294).length < 2 ^ (prefixWord ++ tailWord_3802294).sum := by decide
  have hdescent : baseEnd_3802294 < baseStart_3802294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802337 : List Nat := [1, 2, 3, 1, 3, 3, 2, 1, 3, 3]
def baseStart_3802337 : Nat := 118140960795 + 3802337 * 2 ^ 59
def prefixEnd_3802337 : Nat := 4983230072969 + 3 ^ 40 * 3802337 * 2
def baseEnd_3802337 : Nat := 1301617660916530048467251

theorem tailTrace_3802337 : CollatzResearch.WordTrace tailWord_3802337 prefixEnd_3802337 1301617660916530048467251 := by
  unfold tailWord_3802337
  simp only [CollatzResearch.WordTrace]
  refine ⟨138682623625789911304333265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92455082417193274202888843 138682623625789911304333265)
  ·
    refine ⟨104011967719342433478249949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138682623625789911304333265 104011967719342433478249949)
    ·
      refine ⟨39004487894753412554343731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104011967719342433478249949 39004487894753412554343731)
      ·
        refine ⟨58506731842130118831515597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39004487894753412554343731 58506731842130118831515597)
        ·
          refine ⟨21940024440798794561818349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58506731842130118831515597 21940024440798794561818349)
          ·
            refine ⟨8227509165299547960681881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21940024440798794561818349 8227509165299547960681881)
            ·
              refine ⟨6170631873974660970511411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8227509165299547960681881 6170631873974660970511411)
              ·
                refine ⟨9255947810961991455767117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6170631873974660970511411 9255947810961991455767117)
                ·
                  refine ⟨3470980429110746795912669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9255947810961991455767117 3470980429110746795912669)
                  ·
                    refine ⟨1301617660916530048467251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3470980429110746795912669 1301617660916530048467251)
                    ·
                      rfl

theorem cell22_3802337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_3802337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802337 prefixEnd_3802337 := by exact prefixLift 3802337
  have htrace : WordTrace (prefixWord ++ tailWord_3802337) baseStart_3802337 baseEnd_3802337 := by
    simpa [prefixWord, tailWord_3802337, baseEnd_3802337] using wordTrace_append hprefix tailTrace_3802337
  have hstable : (prefixWord ++ tailWord_3802337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802337).length < 2 ^ (prefixWord ++ tailWord_3802337).sum := by decide
  have hdescent : baseEnd_3802337 < baseStart_3802337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802350 : List Nat := [4, 1, 2, 1, 1, 1, 2, 5, 5]
def baseStart_3802350 : Nat := 118140960795 + 3802350 * 2 ^ 59
def prefixEnd_3802350 : Nat := 4983230072969 + 3 ^ 40 * 3802350 * 2
def baseEnd_3802350 : Nat := 433874037027400782630737

theorem tailTrace_3802350 : CollatzResearch.WordTrace tailWord_3802350 prefixEnd_3802350 433874037027400782630737 := by
  unfold tailWord_3802350
  simp only [CollatzResearch.WordTrace]
  refine ⟨17335387221842851815569563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92455398516495209683037669 17335387221842851815569563)
  ·
    refine ⟨26003080832764277723354345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17335387221842851815569563 26003080832764277723354345)
    ·
      refine ⟨19502310624573208292515759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26003080832764277723354345 19502310624573208292515759)
      ·
        refine ⟨29253465936859812438773639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19502310624573208292515759 29253465936859812438773639)
        ·
          refine ⟨43880198905289718658160459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29253465936859812438773639 43880198905289718658160459)
          ·
            refine ⟨65820298357934577987240689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43880198905289718658160459 65820298357934577987240689)
            ·
              refine ⟨49365223768450933490430517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65820298357934577987240689 49365223768450933490430517)
              ·
                refine ⟨4627989728292275014727861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49365223768450933490430517 4627989728292275014727861)
                ·
                  refine ⟨433874037027400782630737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4627989728292275014727861 433874037027400782630737)
                  ·
                    rfl

theorem cell22_3802350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_3802350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802350 prefixEnd_3802350 := by exact prefixLift 3802350
  have htrace : WordTrace (prefixWord ++ tailWord_3802350) baseStart_3802350 baseEnd_3802350 := by
    simpa [prefixWord, tailWord_3802350, baseEnd_3802350] using wordTrace_append hprefix tailTrace_3802350
  have hstable : (prefixWord ++ tailWord_3802350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802350).length < 2 ^ (prefixWord ++ tailWord_3802350).sum := by decide
  have hdescent : baseEnd_3802350 < baseStart_3802350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802444 : List Nat := [2, 2, 1, 3, 2, 3, 2, 2, 2, 3]
def baseStart_3802444 : Nat := 118140960795 + 3802444 * 2 ^ 59
def prefixEnd_3802444 : Nat := 4983230072969 + 3 ^ 40 * 3802444 * 2
def baseEnd_3802444 : Nat := 1301654289203217436041923

theorem tailTrace_3802444 : CollatzResearch.WordTrace tailWord_3802444 prefixEnd_3802444 1301654289203217436041923 := by
  unfold tailWord_3802444
  simp only [CollatzResearch.WordTrace]
  refine ⟨69343263118201134289239193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92457684157601512385652257 69343263118201134289239193)
  ·
    refine ⟨52007447338650850716929395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69343263118201134289239193 52007447338650850716929395)
    ·
      refine ⟨78011171007976276075394093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52007447338650850716929395 78011171007976276075394093)
      ·
        refine ⟨29254189127991103528272785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78011171007976276075394093 29254189127991103528272785)
        ·
          refine ⟨21940641845993327646204589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29254189127991103528272785 21940641845993327646204589)
          ·
            refine ⟨8227740692247497867326721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21940641845993327646204589 8227740692247497867326721)
            ·
              refine ⟨6170805519185623400495041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8227740692247497867326721 6170805519185623400495041)
              ·
                refine ⟨4628104139389217550371281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6170805519185623400495041 4628104139389217550371281)
                ·
                  refine ⟨3471078104541913162778461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4628104139389217550371281 3471078104541913162778461)
                  ·
                    refine ⟨1301654289203217436041923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3471078104541913162778461 1301654289203217436041923)
                    ·
                      rfl

theorem cell22_3802444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_3802444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802444 prefixEnd_3802444 := by exact prefixLift 3802444
  have htrace : WordTrace (prefixWord ++ tailWord_3802444) baseStart_3802444 baseEnd_3802444 := by
    simpa [prefixWord, tailWord_3802444, baseEnd_3802444] using wordTrace_append hprefix tailTrace_3802444
  have hstable : (prefixWord ++ tailWord_3802444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802444).length < 2 ^ (prefixWord ++ tailWord_3802444).sum := by decide
  have hdescent : baseEnd_3802444 < baseStart_3802444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802474 : List Nat := [3, 1, 3, 3, 2, 1, 3, 6]
def baseStart_3802474 : Nat := 118140960795 + 3802474 * 2 ^ 59
def prefixEnd_3802474 : Nat := 4983230072969 + 3 ^ 40 * 3802474 * 2
def baseEnd_3802474 : Nat := 144629395424034150865759

theorem tailTrace_3802474 : CollatzResearch.WordTrace tailWord_3802474 prefixEnd_3802474 144629395424034150865759 := by
  unfold tailWord_3802474
  simp only [CollatzResearch.WordTrace]
  refine ⟨34671905106573395925517619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92458413617529055801380317 34671905106573395925517619)
  ·
    refine ⟨52007857659860093888276429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34671905106573395925517619 52007857659860093888276429)
    ·
      refine ⟨19502946622447535208103661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52007857659860093888276429 19502946622447535208103661)
      ·
        refine ⟨7313604983417825703038873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19502946622447535208103661 7313604983417825703038873)
        ·
          refine ⟨5485203737563369277279155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7313604983417825703038873 5485203737563369277279155)
          ·
            refine ⟨8227805606345053915918733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5485203737563369277279155 8227805606345053915918733)
            ·
              refine ⟨3085427102379395218469525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8227805606345053915918733 3085427102379395218469525)
              ·
                refine ⟨144629395424034150865759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3085427102379395218469525 144629395424034150865759)
                ·
                  rfl

theorem cell22_3802474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 6].length) (baseStart_3802474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802474 prefixEnd_3802474 := by exact prefixLift 3802474
  have htrace : WordTrace (prefixWord ++ tailWord_3802474) baseStart_3802474 baseEnd_3802474 := by
    simpa [prefixWord, tailWord_3802474, baseEnd_3802474] using wordTrace_append hprefix tailTrace_3802474
  have hstable : (prefixWord ++ tailWord_3802474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802474).length < 2 ^ (prefixWord ++ tailWord_3802474).sum := by decide
  have hdescent : baseEnd_3802474 < baseStart_3802474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802489 : List Nat := [1, 2, 1, 3, 2, 1, 3, 5, 1, 3]
def baseStart_3802489 : Nat := 118140960795 + 3802489 * 2 ^ 59
def prefixEnd_3802489 : Nat := 4983230072969 + 3 ^ 40 * 3802489 * 2
def baseEnd_3802489 : Nat := 1301669693622852318666785

theorem tailTrace_3802489 : CollatzResearch.WordTrace tailWord_3802489 prefixEnd_3802489 1301669693622852318666785 := by
  unfold tailWord_3802489
  simp only [CollatzResearch.WordTrace]
  refine ⟨138688167521239241263866521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92458778347492827509244347 138688167521239241263866521)
  ·
    refine ⟨104016125640929430947899891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138688167521239241263866521 104016125640929430947899891)
    ·
      refine ⟨156024188461394146421849837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104016125640929430947899891 156024188461394146421849837)
      ·
        refine ⟨58509070673022804908193689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156024188461394146421849837 58509070673022804908193689)
        ·
          refine ⟨43881803004767103681145267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58509070673022804908193689 43881803004767103681145267)
          ·
            refine ⟨65822704507150655521717901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43881803004767103681145267 65822704507150655521717901)
            ·
              refine ⟨24683514190181495820644213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65822704507150655521717901 24683514190181495820644213)
              ·
                refine ⟨2314079455329515233185395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24683514190181495820644213 2314079455329515233185395)
                ·
                  refine ⟨3471119182994272849778093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2314079455329515233185395 3471119182994272849778093)
                  ·
                    refine ⟨1301669693622852318666785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3471119182994272849778093 1301669693622852318666785)
                    ·
                      rfl

theorem cell22_3802489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 1, 3].length) (baseStart_3802489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802489 prefixEnd_3802489 := by exact prefixLift 3802489
  have htrace : WordTrace (prefixWord ++ tailWord_3802489) baseStart_3802489 baseEnd_3802489 := by
    simpa [prefixWord, tailWord_3802489, baseEnd_3802489] using wordTrace_append hprefix tailTrace_3802489
  have hstable : (prefixWord ++ tailWord_3802489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802489).length < 2 ^ (prefixWord ++ tailWord_3802489).sum := by decide
  have hdescent : baseEnd_3802489 < baseStart_3802489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802549 : List Nat := [1, 3, 3, 2, 2, 1, 2, 3, 1, 4]
def baseStart_3802549 : Nat := 118140960795 + 3802549 * 2 ^ 59
def prefixEnd_3802549 : Nat := 4983230072969 + 3 ^ 40 * 3802549 * 2
def baseEnd_3802549 : Nat := 1301690232849032162166601

theorem tailTrace_3802549 : CollatzResearch.WordTrace tailWord_3802549 prefixEnd_3802549 1301690232849032162166601 := by
  unfold tailWord_3802549
  simp only [CollatzResearch.WordTrace]
  refine ⟨138690355901021871511050701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92460237267347914340700467 138690355901021871511050701)
  ·
    refine ⟨52008883462883201816644013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138690355901021871511050701 52008883462883201816644013)
    ·
      refine ⟨19503331298581200681241505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52008883462883201816644013 19503331298581200681241505)
      ·
        refine ⟨14627498473935900510931129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19503331298581200681241505 14627498473935900510931129)
        ·
          refine ⟨10970623855451925383198347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14627498473935900510931129 10970623855451925383198347)
          ·
            refine ⟨16455935783177888074797521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10970623855451925383198347 16455935783177888074797521)
            ·
              refine ⟨12341951837383416056098141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16455935783177888074797521 12341951837383416056098141)
              ·
                refine ⟨4628231939018781021036803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12341951837383416056098141 4628231939018781021036803)
                ·
                  refine ⟨6942347908528171531555205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4628231939018781021036803 6942347908528171531555205)
                  ·
                    refine ⟨1301690232849032162166601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6942347908528171531555205 1301690232849032162166601)
                    ·
                      rfl

theorem cell22_3802549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_3802549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802549 prefixEnd_3802549 := by exact prefixLift 3802549
  have htrace : WordTrace (prefixWord ++ tailWord_3802549) baseStart_3802549 baseEnd_3802549 := by
    simpa [prefixWord, tailWord_3802549, baseEnd_3802549] using wordTrace_append hprefix tailTrace_3802549
  have hstable : (prefixWord ++ tailWord_3802549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802549).length < 2 ^ (prefixWord ++ tailWord_3802549).sum := by decide
  have hdescent : baseEnd_3802549 < baseStart_3802549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802564 : List Nat := [2, 3, 3, 2, 1, 1, 3, 1, 6]
def baseStart_3802564 : Nat := 118140960795 + 3802564 * 2 ^ 59
def prefixEnd_3802564 : Nat := 4983230072969 + 3 ^ 40 * 3802564 * 2
def baseEnd_3802564 : Nat := 433898455885192374347185

theorem tailTrace_3802564 : CollatzResearch.WordTrace tailWord_3802564 prefixEnd_3802564 433898455885192374347185 := by
  unfold tailWord_3802564
  simp only [CollatzResearch.WordTrace]
  refine ⟨69345451497983764536423373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92460601997311686048564497 69345451497983764536423373)
  ·
    refine ⟨26004544311743911701158765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69345451497983764536423373 26004544311743911701158765)
    ·
      refine ⟨9751704116903966887934537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26004544311743911701158765 9751704116903966887934537)
      ·
        refine ⟨7313778087677975165950903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9751704116903966887934537 7313778087677975165950903)
        ·
          refine ⟨10970667131516962748926355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7313778087677975165950903 10970667131516962748926355)
          ·
            refine ⟨16456000697275444123389533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10970667131516962748926355 16456000697275444123389533)
            ·
              refine ⟨6171000261478291546271075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16456000697275444123389533 6171000261478291546271075)
              ·
                refine ⟨9256500392217437319406613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6171000261478291546271075 9256500392217437319406613)
                ·
                  refine ⟨433898455885192374347185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9256500392217437319406613 433898455885192374347185)
                  ·
                    rfl

theorem cell22_3802564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_3802564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802564 prefixEnd_3802564 := by exact prefixLift 3802564
  have htrace : WordTrace (prefixWord ++ tailWord_3802564) baseStart_3802564 baseEnd_3802564 := by
    simpa [prefixWord, tailWord_3802564, baseEnd_3802564] using wordTrace_append hprefix tailTrace_3802564
  have hstable : (prefixWord ++ tailWord_3802564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802564).length < 2 ^ (prefixWord ++ tailWord_3802564).sum := by decide
  have hdescent : baseEnd_3802564 < baseStart_3802564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802575 : List Nat := [1, 1, 2, 1, 1, 4, 3, 9]
def baseStart_3802575 : Nat := 118140960795 + 3802575 * 2 ^ 59
def prefixEnd_3802575 : Nat := 4983230072969 + 3 ^ 40 * 3802575 * 2
def baseEnd_3802575 : Nat := 144633237020041862335169

theorem tailTrace_3802575 : CollatzResearch.WordTrace tailWord_3802575 prefixEnd_3802575 144633237020041862335169 := by
  unfold tailWord_3802575
  simp only [CollatzResearch.WordTrace]
  refine ⟨138691304198927677951497179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92460869465951785300998119 138691304198927677951497179)
  ·
    refine ⟨208036956298391516927245769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138691304198927677951497179 208036956298391516927245769)
    ·
      refine ⟨156027717223793637695434327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208036956298391516927245769 156027717223793637695434327)
      ·
        refine ⟨234041575835690456543151491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156027717223793637695434327 234041575835690456543151491)
        ·
          refine ⟨351062363753535684814727237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234041575835690456543151491 351062363753535684814727237)
          ·
            refine ⟨65824193203787940902761357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 351062363753535684814727237 65824193203787940902761357)
            ·
              refine ⟨24684072451420477838535509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65824193203787940902761357 24684072451420477838535509)
              ·
                refine ⟨144633237020041862335169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24684072451420477838535509 144633237020041862335169)
                ·
                  rfl

theorem cell22_3802575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 9].length) (baseStart_3802575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802575 prefixEnd_3802575 := by exact prefixLift 3802575
  have htrace : WordTrace (prefixWord ++ tailWord_3802575) baseStart_3802575 baseEnd_3802575 := by
    simpa [prefixWord, tailWord_3802575, baseEnd_3802575] using wordTrace_append hprefix tailTrace_3802575
  have hstable : (prefixWord ++ tailWord_3802575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802575).length < 2 ^ (prefixWord ++ tailWord_3802575).sum := by decide
  have hdescent : baseEnd_3802575 < baseStart_3802575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802613 : List Nat := [1, 3, 5, 1, 1, 2, 2, 2, 2, 3]
def baseStart_3802613 : Nat := 118140960795 + 3802613 * 2 ^ 59
def prefixEnd_3802613 : Nat := 4983230072969 + 3 ^ 40 * 3802613 * 2
def baseEnd_3802613 : Nat := 1301712141356957328566405

theorem tailTrace_3802613 : CollatzResearch.WordTrace tailWord_3802613 prefixEnd_3802613 1301712141356957328566405 := by
  unfold tailWord_3802613
  simp only [CollatzResearch.WordTrace]
  refine ⟨138692690172790010441380493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92461793448526673627586995 138692690172790010441380493)
  ·
    refine ⟨52009758814796253915517685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138692690172790010441380493 52009758814796253915517685)
    ·
      refine ⟨4875914888887148804579783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52009758814796253915517685 4875914888887148804579783)
      ·
        refine ⟨7313872333330723206869675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4875914888887148804579783 7313872333330723206869675)
        ·
          refine ⟨10970808499996084810304513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7313872333330723206869675 10970808499996084810304513)
          ·
            refine ⟨8228106374997063607728385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10970808499996084810304513 8228106374997063607728385)
            ·
              refine ⟨6171079781247797705796289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8228106374997063607728385 6171079781247797705796289)
              ·
                refine ⟨4628309835935848279347217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6171079781247797705796289 4628309835935848279347217)
                ·
                  refine ⟨3471232376951886209510413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4628309835935848279347217 3471232376951886209510413)
                  ·
                    refine ⟨1301712141356957328566405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3471232376951886209510413 1301712141356957328566405)
                    ·
                      rfl

theorem cell22_3802613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_3802613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802613 prefixEnd_3802613 := by exact prefixLift 3802613
  have htrace : WordTrace (prefixWord ++ tailWord_3802613) baseStart_3802613 baseEnd_3802613 := by
    simpa [prefixWord, tailWord_3802613, baseEnd_3802613] using wordTrace_append hprefix tailTrace_3802613
  have hstable : (prefixWord ++ tailWord_3802613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802613).length < 2 ^ (prefixWord ++ tailWord_3802613).sum := by decide
  have hdescent : baseEnd_3802613 < baseStart_3802613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802626 : List Nat := [3, 4, 1, 2, 1, 3, 1, 7]
def baseStart_3802626 : Nat := 118140960795 + 3802626 * 2 ^ 59
def prefixEnd_3802626 : Nat := 4983230072969 + 3 ^ 40 * 3802626 * 2
def baseEnd_3802626 : Nat := 144635176835847736443485

theorem tailTrace_3802626 : CollatzResearch.WordTrace tailWord_3802626 prefixEnd_3802626 144635176835847736443485 := by
  unfold tailWord_3802626
  simp only [CollatzResearch.WordTrace]
  refine ⟨34673291080435728415400933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92462109547828609107735821 34673291080435728415400933)
  ·
    refine ⟨6501242077581699077887675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34673291080435728415400933 6501242077581699077887675)
    ·
      refine ⟨9751863116372548616831513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6501242077581699077887675 9751863116372548616831513)
      ·
        refine ⟨7313897337279411462623635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9751863116372548616831513 7313897337279411462623635)
        ·
          refine ⟨10970846005919117193935453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7313897337279411462623635 10970846005919117193935453)
          ·
            refine ⟨4114067252219668947725795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10970846005919117193935453 4114067252219668947725795)
            ·
              refine ⟨6171100878329503421588693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4114067252219668947725795 6171100878329503421588693)
              ·
                refine ⟨144635176835847736443485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6171100878329503421588693 144635176835847736443485)
                ·
                  rfl

theorem cell22_3802626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 7].length) (baseStart_3802626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802626 prefixEnd_3802626 := by exact prefixLift 3802626
  have htrace : WordTrace (prefixWord ++ tailWord_3802626) baseStart_3802626 baseEnd_3802626 := by
    simpa [prefixWord, tailWord_3802626, baseEnd_3802626] using wordTrace_append hprefix tailTrace_3802626
  have hstable : (prefixWord ++ tailWord_3802626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802626).length < 2 ^ (prefixWord ++ tailWord_3802626).sum := by decide
  have hdescent : baseEnd_3802626 < baseStart_3802626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802630 : List Nat := [6, 2, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_3802630 : Nat := 118140960795 + 3802630 * 2 ^ 59
def prefixEnd_3802630 : Nat := 4983230072969 + 3 ^ 40 * 3802630 * 2
def baseEnd_3802630 : Nat := 1301717960804374950891353

theorem tailTrace_3802630 : CollatzResearch.WordTrace tailWord_3802630 prefixEnd_3802630 1301717960804374950891353 := by
  unfold tailWord_3802630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4334165944179013198273417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92462206809152281563166229 4334165944179013198273417)
  ·
    refine ⟨3250624458134259898705063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4334165944179013198273417 3250624458134259898705063)
    ·
      refine ⟨4875936687201389848057595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3250624458134259898705063 4875936687201389848057595)
      ·
        refine ⟨7313905030802084772086393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4875936687201389848057595 7313905030802084772086393)
        ·
          refine ⟨5485428773101563579064795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7313905030802084772086393 5485428773101563579064795)
          ·
            refine ⟨8228143159652345368597193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5485428773101563579064795 8228143159652345368597193)
            ·
              refine ⟨6171107369739259026447895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8228143159652345368597193 6171107369739259026447895)
              ·
                refine ⟨9256661054608888539671843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6171107369739259026447895 9256661054608888539671843)
                ·
                  refine ⟨13884991581913332809507765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9256661054608888539671843 13884991581913332809507765)
                  ·
                    refine ⟨1301717960804374950891353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13884991581913332809507765 1301717960804374950891353)
                    ·
                      rfl

theorem cell22_3802630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_3802630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802630 prefixEnd_3802630 := by exact prefixLift 3802630
  have htrace : WordTrace (prefixWord ++ tailWord_3802630) baseStart_3802630 baseEnd_3802630 := by
    simpa [prefixWord, tailWord_3802630, baseEnd_3802630] using wordTrace_append hprefix tailTrace_3802630
  have hstable : (prefixWord ++ tailWord_3802630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802630).length < 2 ^ (prefixWord ++ tailWord_3802630).sum := by decide
  have hdescent : baseEnd_3802630 < baseStart_3802630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802652 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 1, 7]
def baseStart_3802652 : Nat := 118140960795 + 3802652 * 2 ^ 59
def prefixEnd_3802652 : Nat := 4983230072969 + 3 ^ 40 * 3802652 * 2
def baseEnd_3802652 : Nat := 1301725491853974226841285

theorem tailTrace_3802652 : CollatzResearch.WordTrace tailWord_3802652 prefixEnd_3802652 1301725491853974226841285 := by
  unfold tailWord_3802652
  simp only [CollatzResearch.WordTrace]
  refine ⟨69347056309824360051025105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92462741746432480068033473 69347056309824360051025105)
  ·
    refine ⟨52010292232368270038268829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69347056309824360051025105 52010292232368270038268829)
    ·
      refine ⟨19503859587138101264350811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52010292232368270038268829 19503859587138101264350811)
      ·
        refine ⟨29255789380707151896526217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19503859587138101264350811 29255789380707151896526217)
        ·
          refine ⟨21941842035530363922394663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29255789380707151896526217 21941842035530363922394663)
          ·
            refine ⟨32912763053295545883591995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21941842035530363922394663 32912763053295545883591995)
            ·
              refine ⟨49369144579943318825387993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32912763053295545883591995 49369144579943318825387993)
              ·
                refine ⟨37026858434957489119040995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49369144579943318825387993 37026858434957489119040995)
                ·
                  refine ⟨55540287652436233678561493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37026858434957489119040995 55540287652436233678561493)
                  ·
                    refine ⟨1301725491853974226841285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55540287652436233678561493 1301725491853974226841285)
                    ·
                      rfl

theorem cell22_3802652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_3802652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802652 prefixEnd_3802652 := by exact prefixLift 3802652
  have htrace : WordTrace (prefixWord ++ tailWord_3802652) baseStart_3802652 baseEnd_3802652 := by
    simpa [prefixWord, tailWord_3802652, baseEnd_3802652] using wordTrace_append hprefix tailTrace_3802652
  have hstable : (prefixWord ++ tailWord_3802652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802652).length < 2 ^ (prefixWord ++ tailWord_3802652).sum := by decide
  have hdescent : baseEnd_3802652 < baseStart_3802652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802727 : List Nat := [1, 1, 5, 1, 1, 1, 12]
def baseStart_3802727 : Nat := 118140960795 + 3802727 * 2 ^ 59
def prefixEnd_3802727 : Nat := 4983230072969 + 3 ^ 40 * 3802727 * 2
def baseEnd_3802727 : Nat := 48213006143951815970965

theorem tailTrace_3802727 : CollatzResearch.WordTrace tailWord_3802727 prefixEnd_3802727 48213006143951815970965 := by
  unfold tailWord_3802727
  simp only [CollatzResearch.WordTrace]
  refine ⟨138696848094377007911030435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92464565396251338607353623 138696848094377007911030435)
  ·
    refine ⟨208045272141565511866545653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138696848094377007911030435 208045272141565511866545653)
    ·
      refine ⟨19504244263271766737488655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208045272141565511866545653 19504244263271766737488655)
      ·
        refine ⟨29256366394907650106232983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19504244263271766737488655 29256366394907650106232983)
        ·
          refine ⟨43884549592361475159349475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29256366394907650106232983 43884549592361475159349475)
          ·
            refine ⟨65826824388542212739024213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43884549592361475159349475 65826824388542212739024213)
            ·
              refine ⟨48213006143951815970965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 65826824388542212739024213 48213006143951815970965)
              ·
                rfl

theorem cell22_3802727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 12].length) (baseStart_3802727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802727 prefixEnd_3802727 := by exact prefixLift 3802727
  have htrace : WordTrace (prefixWord ++ tailWord_3802727) baseStart_3802727 baseEnd_3802727 := by
    simpa [prefixWord, tailWord_3802727, baseEnd_3802727] using wordTrace_append hprefix tailTrace_3802727
  have hstable : (prefixWord ++ tailWord_3802727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802727).length < 2 ^ (prefixWord ++ tailWord_3802727).sum := by decide
  have hdescent : baseEnd_3802727 < baseStart_3802727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802733 : List Nat := [1, 5, 1, 1, 5, 1, 1, 1, 6]
def baseStart_3802733 : Nat := 118140960795 + 3802733 * 2 ^ 59
def prefixEnd_3802733 : Nat := 4983230072969 + 3 ^ 40 * 3802733 * 2
def baseEnd_3802733 : Nat := 433917739936439005188679

theorem tailTrace_3802733 : CollatzResearch.WordTrace tailWord_3802733 prefixEnd_3802733 433917739936439005188679 := by
  unfold tailWord_3802733
  simp only [CollatzResearch.WordTrace]
  refine ⟨138697066932355270935748853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92464711288236847290499235 138697066932355270935748853)
  ·
    refine ⟨13002850024908306650226455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138697066932355270935748853 13002850024908306650226455)
    ·
      refine ⟨19504275037362459975339683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13002850024908306650226455 19504275037362459975339683)
      ·
        refine ⟨29256412556043689963009525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19504275037362459975339683 29256412556043689963009525)
        ·
          refine ⟨2742788677129095934032143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29256412556043689963009525 2742788677129095934032143)
          ·
            refine ⟨4114183015693643901048215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2742788677129095934032143 4114183015693643901048215)
            ·
              refine ⟨6171274523540465851572323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4114183015693643901048215 6171274523540465851572323)
              ·
                refine ⟨9256911785310698777358485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6171274523540465851572323 9256911785310698777358485)
                ·
                  refine ⟨433917739936439005188679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9256911785310698777358485 433917739936439005188679)
                  ·
                    rfl

theorem cell22_3802733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_3802733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802733 prefixEnd_3802733 := by exact prefixLift 3802733
  have htrace : WordTrace (prefixWord ++ tailWord_3802733) baseStart_3802733 baseEnd_3802733 := by
    simpa [prefixWord, tailWord_3802733, baseEnd_3802733] using wordTrace_append hprefix tailTrace_3802733
  have hstable : (prefixWord ++ tailWord_3802733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802733).length < 2 ^ (prefixWord ++ tailWord_3802733).sum := by decide
  have hdescent : baseEnd_3802733 < baseStart_3802733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802789 : List Nat := [1, 3, 1, 2, 1, 2, 3, 4, 5]
def baseStart_3802789 : Nat := 118140960795 + 3802789 * 2 ^ 59
def prefixEnd_3802789 : Nat := 4983230072969 + 3 ^ 40 * 3802789 * 2
def baseEnd_3802789 : Nat := 433924129917917178721955

theorem tailTrace_3802789 : CollatzResearch.WordTrace tailWord_3802789 prefixEnd_3802789 433924129917917178721955 := by
  unfold tailWord_3802789
  simp only [CollatzResearch.WordTrace]
  refine ⟨138699109420152392499787421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92466072946768261666524947 138699109420152392499787421)
  ·
    refine ⟨52012166032557147187420283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138699109420152392499787421 52012166032557147187420283)
    ·
      refine ⟨78018249048835720781130425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52012166032557147187420283 78018249048835720781130425)
      ·
        refine ⟨58513686786626790585847819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78018249048835720781130425 58513686786626790585847819)
        ·
          refine ⟨87770530179940185878771729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58513686786626790585847819 87770530179940185878771729)
          ·
            refine ⟨65827897634955139409078797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87770530179940185878771729 65827897634955139409078797)
            ·
              refine ⟨24685461613108177278404549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65827897634955139409078797 24685461613108177278404549)
              ·
                refine ⟨4628524052457783239700853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24685461613108177278404549 4628524052457783239700853)
                ·
                  refine ⟨433924129917917178721955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4628524052457783239700853 433924129917917178721955)
                  ·
                    rfl

theorem cell22_3802789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_3802789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802789 prefixEnd_3802789 := by exact prefixLift 3802789
  have htrace : WordTrace (prefixWord ++ tailWord_3802789) baseStart_3802789 baseEnd_3802789 := by
    simpa [prefixWord, tailWord_3802789, baseEnd_3802789] using wordTrace_append hprefix tailTrace_3802789
  have hstable : (prefixWord ++ tailWord_3802789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802789).length < 2 ^ (prefixWord ++ tailWord_3802789).sum := by decide
  have hdescent : baseEnd_3802789 < baseStart_3802789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802864 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 6, 4]
def baseStart_3802864 : Nat := 118140960795 + 3802864 * 2 ^ 59
def prefixEnd_3802864 : Nat := 4983230072969 + 3 ^ 40 * 3802864 * 2
def baseEnd_3802864 : Nat := 1301798063786476340540635

theorem tailTrace_3802864 : CollatzResearch.WordTrace tailWord_3802864 prefixEnd_3802864 1301798063786476340540635 := by
  unfold tailWord_3802864
  simp only [CollatzResearch.WordTrace]
  refine ⟨69350922447440340154383823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92467896596587120205845097 69350922447440340154383823)
  ·
    refine ⟨104026383671160510231575735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69350922447440340154383823 104026383671160510231575735)
    ·
      refine ⟨156039575506740765347363603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104026383671160510231575735 156039575506740765347363603)
      ·
        refine ⟨234059363260111148021045405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156039575506740765347363603 234059363260111148021045405)
        ·
          refine ⟨87772261222541680507892027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234059363260111148021045405 87772261222541680507892027)
          ·
            refine ⟨131658391833812520761838041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87772261222541680507892027 131658391833812520761838041)
            ·
              refine ⟨98743793875359390571378531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131658391833812520761838041 98743793875359390571378531)
              ·
                refine ⟨148115690813039085857067797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98743793875359390571378531 148115690813039085857067797)
                ·
                  refine ⟨6942923006861207149550053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148115690813039085857067797 6942923006861207149550053)
                  ·
                    refine ⟨1301798063786476340540635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6942923006861207149550053 1301798063786476340540635)
                    ·
                      rfl

theorem cell22_3802864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 6, 4].length) (baseStart_3802864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802864 prefixEnd_3802864 := by exact prefixLift 3802864
  have htrace : WordTrace (prefixWord ++ tailWord_3802864) baseStart_3802864 baseEnd_3802864 := by
    simpa [prefixWord, tailWord_3802864, baseEnd_3802864] using wordTrace_append hprefix tailTrace_3802864
  have hstable : (prefixWord ++ tailWord_3802864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802864).length < 2 ^ (prefixWord ++ tailWord_3802864).sum := by decide
  have hdescent : baseEnd_3802864 < baseStart_3802864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802898 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3802898 : Nat := 118140960795 + 3802898 * 2 ^ 59
def prefixEnd_3802898 : Nat := 4983230072969 + 3 ^ 40 * 3802898 * 2
def baseEnd_3802898 : Nat := 1301809702681311585190531

theorem tailTrace_3802898 : CollatzResearch.WordTrace tailWord_3802898 prefixEnd_3802898 1301809702681311585190531 := by
  unfold tailWord_3802898
  simp only [CollatzResearch.WordTrace]
  refine ⟨34675771244189376028876337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92468723317838336077003565 34675771244189376028876337)
  ·
    refine ⟨26006828433142032021657253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34675771244189376028876337 26006828433142032021657253)
    ·
      refine ⟨4876280331214131004060735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26006828433142032021657253 4876280331214131004060735)
      ·
        refine ⟨7314420496821196506091103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4876280331214131004060735 7314420496821196506091103)
        ·
          refine ⟨10971630745231794759136655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7314420496821196506091103 10971630745231794759136655)
          ·
            refine ⟨16457446117847692138704983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10971630745231794759136655 16457446117847692138704983)
            ·
              refine ⟨24686169176771538208057475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16457446117847692138704983 24686169176771538208057475)
              ·
                refine ⟨37029253765157307312086213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24686169176771538208057475 37029253765157307312086213)
                ·
                  refine ⟨6942985080966995121016165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37029253765157307312086213 6942985080966995121016165)
                  ·
                    refine ⟨1301809702681311585190531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6942985080966995121016165 1301809702681311585190531)
                    ·
                      rfl

theorem cell22_3802898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3802898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802898 prefixEnd_3802898 := by exact prefixLift 3802898
  have htrace : WordTrace (prefixWord ++ tailWord_3802898) baseStart_3802898 baseEnd_3802898 := by
    simpa [prefixWord, tailWord_3802898, baseEnd_3802898] using wordTrace_append hprefix tailTrace_3802898
  have hstable : (prefixWord ++ tailWord_3802898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802898).length < 2 ^ (prefixWord ++ tailWord_3802898).sum := by decide
  have hdescent : baseEnd_3802898 < baseStart_3802898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3802962 : List Nat := [3, 2, 2, 1, 1, 3, 4, 2, 1, 3]
def baseStart_3802962 : Nat := 118140960795 + 3802962 * 2 ^ 59
def prefixEnd_3802962 : Nat := 4983230072969 + 3 ^ 40 * 3802962 * 2
def baseEnd_3802962 : Nat := 1301831611189236751590335

theorem tailTrace_3802962 : CollatzResearch.WordTrace tailWord_3802962 prefixEnd_3802962 1301831611189236751590335 := by
  unfold tailWord_3802962
  simp only [CollatzResearch.WordTrace]
  refine ⟨34676354812131410761458785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92470279499017095363890093 34676354812131410761458785)
  ·
    refine ⟨26007266109098558071094089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34676354812131410761458785 26007266109098558071094089)
    ·
      refine ⟨19505449581823918553320567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26007266109098558071094089 19505449581823918553320567)
      ·
        refine ⟨29258174372735877829980851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19505449581823918553320567 29258174372735877829980851)
        ·
          refine ⟨43887261559103816744971277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29258174372735877829980851 43887261559103816744971277)
          ·
            refine ⟨16457723084663931279364229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43887261559103816744971277 16457723084663931279364229)
            ·
              refine ⟨3085823078374487114880793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16457723084663931279364229 3085823078374487114880793)
              ·
                refine ⟨2314367308780865336160595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3085823078374487114880793 2314367308780865336160595)
                ·
                  refine ⟨3471550963171298004240893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2314367308780865336160595 3471550963171298004240893)
                  ·
                    refine ⟨1301831611189236751590335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3471550963171298004240893 1301831611189236751590335)
                    ·
                      rfl

theorem cell22_3802962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_3802962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3802962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3802962 prefixEnd_3802962 := by exact prefixLift 3802962
  have htrace : WordTrace (prefixWord ++ tailWord_3802962) baseStart_3802962 baseEnd_3802962 := by
    simpa [prefixWord, tailWord_3802962, baseEnd_3802962] using wordTrace_append hprefix tailTrace_3802962
  have hstable : (prefixWord ++ tailWord_3802962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3802962).length < 2 ^ (prefixWord ++ tailWord_3802962).sum := by decide
  have hdescent : baseEnd_3802962 < baseStart_3802962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3802962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803001 : List Nat := [1, 2, 1, 3, 2, 2, 1, 4, 1, 5]
def baseStart_3803001 : Nat := 118140960795 + 3803001 * 2 ^ 59
def prefixEnd_3803001 : Nat := 4983230072969 + 3 ^ 40 * 3803001 * 2
def baseEnd_3803001 : Nat := 1301844961686253649865215

theorem tailTrace_3803001 : CollatzResearch.WordTrace tailWord_3803001 prefixEnd_3803001 1301844961686253649865215 := by
  unfold tailWord_3803001
  simp only [CollatzResearch.WordTrace]
  refine ⟨138706841695384352706504857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92471227796922901804336571 138706841695384352706504857)
  ·
    refine ⟨104030131271538264529878643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138706841695384352706504857 104030131271538264529878643)
    ·
      refine ⟨156045196907307396794817965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104030131271538264529878643 156045196907307396794817965)
      ·
        refine ⟨58516948840240273798056737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156045196907307396794817965 58516948840240273798056737)
        ·
          refine ⟨43887711630180205348542553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58516948840240273798056737 43887711630180205348542553)
          ·
            refine ⟨32915783722635154011406915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43887711630180205348542553 32915783722635154011406915)
            ·
              refine ⟨49373675583952731017110373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32915783722635154011406915 49373675583952731017110373)
              ·
                refine ⟨9257564171991137065708195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49373675583952731017110373 9257564171991137065708195)
                ·
                  refine ⟨13886346257986705598562293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9257564171991137065708195 13886346257986705598562293)
                  ·
                    refine ⟨1301844961686253649865215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13886346257986705598562293 1301844961686253649865215)
                    ·
                      rfl

theorem cell22_3803001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 5].length) (baseStart_3803001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803001 prefixEnd_3803001 := by exact prefixLift 3803001
  have htrace : WordTrace (prefixWord ++ tailWord_3803001) baseStart_3803001 baseEnd_3803001 := by
    simpa [prefixWord, tailWord_3803001, baseEnd_3803001] using wordTrace_append hprefix tailTrace_3803001
  have hstable : (prefixWord ++ tailWord_3803001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803001).length < 2 ^ (prefixWord ++ tailWord_3803001).sum := by decide
  have hdescent : baseEnd_3803001 < baseStart_3803001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803080 : List Nat := [2, 1, 3, 1, 4, 1, 3, 1, 3, 3]
def baseStart_3803080 : Nat := 118140960795 + 3803080 * 2 ^ 59
def prefixEnd_3803080 : Nat := 4983230072969 + 3 ^ 40 * 3803080 * 2
def baseEnd_3803080 : Nat := 1301872005000723777139973

theorem tailTrace_3803080 : CollatzResearch.WordTrace tailWord_3803080 prefixEnd_3803080 1301872005000723777139973 := by
  unfold tailWord_3803080
  simp only [CollatzResearch.WordTrace]
  refine ⟨69354861531049074599315347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92473148708065432799087129 69354861531049074599315347)
  ·
    refine ⟨104032292296573611898973021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69354861531049074599315347 104032292296573611898973021)
    ·
      refine ⟨39012109611215104462114883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104032292296573611898973021 39012109611215104462114883)
      ·
        refine ⟨58518164416822656693172325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39012109611215104462114883 58518164416822656693172325)
        ·
          refine ⟨10972155828154248129969811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58518164416822656693172325 10972155828154248129969811)
          ·
            refine ⟨16458233742231372194954717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10972155828154248129969811 16458233742231372194954717)
            ·
              refine ⟨6171837653336764573108019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16458233742231372194954717 6171837653336764573108019)
              ·
                refine ⟨9257756480005146859662029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6171837653336764573108019 9257756480005146859662029)
                ·
                  refine ⟨3471658680001930072373261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9257756480005146859662029 3471658680001930072373261)
                  ·
                    refine ⟨1301872005000723777139973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3471658680001930072373261 1301872005000723777139973)
                    ·
                      rfl

theorem cell22_3803080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_3803080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803080 prefixEnd_3803080 := by exact prefixLift 3803080
  have htrace : WordTrace (prefixWord ++ tailWord_3803080) baseStart_3803080 baseEnd_3803080 := by
    simpa [prefixWord, tailWord_3803080, baseEnd_3803080] using wordTrace_append hprefix tailTrace_3803080
  have hstable : (prefixWord ++ tailWord_3803080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803080).length < 2 ^ (prefixWord ++ tailWord_3803080).sum := by decide
  have hdescent : baseEnd_3803080 < baseStart_3803080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803123 : List Nat := [1, 1, 1, 2, 2, 2, 1, 7, 1, 4]
def baseStart_3803123 : Nat := 118140960795 + 3803123 * 2 ^ 59
def prefixEnd_3803123 : Nat := 4983230072969 + 3 ^ 40 * 3803123 * 2
def baseEnd_3803123 : Nat := 1301886724779485998314841

theorem tailTrace_3803123 : CollatzResearch.WordTrace tailWord_3803123 prefixEnd_3803123 1301886724779485998314841 := by
  unfold tailWord_3803123
  simp only [CollatzResearch.WordTrace]
  refine ⟨138711291400942367542446023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92474194267294911694964015 138711291400942367542446023)
  ·
    refine ⟨208066937101413551313669035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138711291400942367542446023 208066937101413551313669035)
    ·
      refine ⟨312100405652120326970503553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208066937101413551313669035 312100405652120326970503553)
      ·
        refine ⟨234075304239090245227877665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312100405652120326970503553 234075304239090245227877665)
        ·
          refine ⟨175556478179317683920908249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234075304239090245227877665 175556478179317683920908249)
          ·
            refine ⟨131667358634488262940681187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175556478179317683920908249 131667358634488262940681187)
            ·
              refine ⟨197501037951732394411021781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131667358634488262940681187 197501037951732394411021781)
              ·
                refine ⟨4628930576993727994008323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 197501037951732394411021781 4628930576993727994008323)
                ·
                  refine ⟨6943395865490591991012485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4628930576993727994008323 6943395865490591991012485)
                  ·
                    refine ⟨1301886724779485998314841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6943395865490591991012485 1301886724779485998314841)
                    ·
                      rfl

theorem cell22_3803123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 4].length) (baseStart_3803123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803123 prefixEnd_3803123 := by exact prefixLift 3803123
  have htrace : WordTrace (prefixWord ++ tailWord_3803123) baseStart_3803123 baseEnd_3803123 := by
    simpa [prefixWord, tailWord_3803123, baseEnd_3803123] using wordTrace_append hprefix tailTrace_3803123
  have hstable : (prefixWord ++ tailWord_3803123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803123).length < 2 ^ (prefixWord ++ tailWord_3803123).sum := by decide
  have hdescent : baseEnd_3803123 < baseStart_3803123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803153 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 8, 3]
def baseStart_3803153 : Nat := 118140960795 + 3803153 * 2 ^ 59
def prefixEnd_3803153 : Nat := 4983230072969 + 3 ^ 40 * 3803153 * 2
def baseEnd_3803153 : Nat := 1301896994392575920064749

theorem tailTrace_3803153 : CollatzResearch.WordTrace tailWord_3803153 prefixEnd_3803153 1301896994392575920064749 := by
  unfold tailWord_3803153
  simp only [CollatzResearch.WordTrace]
  refine ⟨138712385590833682666038113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92474923727222455110692075 138712385590833682666038113)
  ·
    refine ⟨104034289193125261999528585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138712385590833682666038113 104034289193125261999528585)
    ·
      refine ⟨78025716894843946499646439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104034289193125261999528585 78025716894843946499646439)
      ·
        refine ⟨117038575342265919749469659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78025716894843946499646439 117038575342265919749469659)
        ·
          refine ⟨175557863013398879624204489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117038575342265919749469659 175557863013398879624204489)
          ·
            refine ⟨131668397260049159718153367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175557863013398879624204489 131668397260049159718153367)
            ·
              refine ⟨197502595890073739577230051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131668397260049159718153367 197502595890073739577230051)
              ·
                refine ⟨296253893835110609365845077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197502595890073739577230051 296253893835110609365845077)
                ·
                  refine ⟨3471725318380202453505997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 296253893835110609365845077 3471725318380202453505997)
                  ·
                    refine ⟨1301896994392575920064749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3471725318380202453505997 1301896994392575920064749)
                    ·
                      rfl

theorem cell22_3803153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_3803153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803153 prefixEnd_3803153 := by exact prefixLift 3803153
  have htrace : WordTrace (prefixWord ++ tailWord_3803153) baseStart_3803153 baseEnd_3803153 := by
    simpa [prefixWord, tailWord_3803153, baseEnd_3803153] using wordTrace_append hprefix tailTrace_3803153
  have hstable : (prefixWord ++ tailWord_3803153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803153).length < 2 ^ (prefixWord ++ tailWord_3803153).sum := by decide
  have hdescent : baseEnd_3803153 < baseStart_3803153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803170 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_3803170 : Nat := 118140960795 + 3803170 * 2 ^ 59
def prefixEnd_3803170 : Nat := 4983230072969 + 3 ^ 40 * 3803170 * 2
def baseEnd_3803170 : Nat := 1301902813839993542389697

theorem tailTrace_3803170 : CollatzResearch.WordTrace tailWord_3803170 prefixEnd_3803170 1301902813839993542389697 := by
  unfold tailWord_3803170
  simp only [CollatzResearch.WordTrace]
  refine ⟨34678251407943023642351741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92475337087848063046271309 34678251407943023642351741)
  ·
    refine ⟨13004344277978633865881903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34678251407943023642351741 13004344277978633865881903)
    ·
      refine ⟨19506516416967950798822855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13004344277978633865881903 19506516416967950798822855)
      ·
        refine ⟨29259774625451926198234283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19506516416967950798822855 29259774625451926198234283)
        ·
          refine ⟨43889661938177889297351425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29259774625451926198234283 43889661938177889297351425)
          ·
            refine ⟨32917246453633416973013569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43889661938177889297351425 32917246453633416973013569)
            ·
              refine ⟨24687934840225062729760177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32917246453633416973013569 24687934840225062729760177)
              ·
                refine ⟨18515951130168797047320133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24687934840225062729760177 18515951130168797047320133)
                ·
                  refine ⟨3471740836906649446372525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18515951130168797047320133 3471740836906649446372525)
                  ·
                    refine ⟨1301902813839993542389697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3471740836906649446372525 1301902813839993542389697)
                    ·
                      rfl

theorem cell22_3803170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_3803170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803170 prefixEnd_3803170 := by exact prefixLift 3803170
  have htrace : WordTrace (prefixWord ++ tailWord_3803170) baseStart_3803170 baseEnd_3803170 := by
    simpa [prefixWord, tailWord_3803170, baseEnd_3803170] using wordTrace_append hprefix tailTrace_3803170
  have hstable : (prefixWord ++ tailWord_3803170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803170).length < 2 ^ (prefixWord ++ tailWord_3803170).sum := by decide
  have hdescent : baseEnd_3803170 < baseStart_3803170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803245 : List Nat := [1, 5, 1, 1, 2, 1, 2, 4, 5]
def baseStart_3803245 : Nat := 118140960795 + 3803245 * 2 ^ 59
def prefixEnd_3803245 : Nat := 4983230072969 + 3 ^ 40 * 3803245 * 2
def baseEnd_3803245 : Nat := 433976162624239448921489

theorem tailTrace_3803245 : CollatzResearch.WordTrace tailWord_3803245 prefixEnd_3803245 433976162624239448921489 := by
  unfold tailWord_3803245
  simp only [CollatzResearch.WordTrace]
  refine ⟨138715741106500382378387189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92477160737666921585591459 138715741106500382378387189)
  ·
    refine ⟨13004600728734410847973799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138715741106500382378387189 13004600728734410847973799)
    ·
      refine ⟨19506901093101616271960699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13004600728734410847973799 19506901093101616271960699)
      ·
        refine ⟨29260351639652424407941049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19506901093101616271960699 29260351639652424407941049)
        ·
          refine ⟨21945263729739318305955787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29260351639652424407941049 21945263729739318305955787)
          ·
            refine ⟨32917895594608977458933681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21945263729739318305955787 32917895594608977458933681)
            ·
              refine ⟨24688421695956733094200261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32917895594608977458933681 24688421695956733094200261)
              ·
                refine ⟨4629079067991887455162549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24688421695956733094200261 4629079067991887455162549)
                ·
                  refine ⟨433976162624239448921489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4629079067991887455162549 433976162624239448921489)
                  ·
                    rfl

theorem cell22_3803245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_3803245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803245 prefixEnd_3803245 := by exact prefixLift 3803245
  have htrace : WordTrace (prefixWord ++ tailWord_3803245) baseStart_3803245 baseEnd_3803245 := by
    simpa [prefixWord, tailWord_3803245, baseEnd_3803245] using wordTrace_append hprefix tailTrace_3803245
  have hstable : (prefixWord ++ tailWord_3803245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803245).length < 2 ^ (prefixWord ++ tailWord_3803245).sum := by decide
  have hdescent : baseEnd_3803245 < baseStart_3803245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803249 : List Nat := [1, 2, 2, 2, 1, 1, 7, 2, 1, 3]
def baseStart_3803249 : Nat := 118140960795 + 3803249 * 2 ^ 59
def prefixEnd_3803249 : Nat := 4983230072969 + 3 ^ 40 * 3803249 * 2
def baseEnd_3803249 : Nat := 1301929857154463669664455

theorem tailTrace_3803249 : CollatzResearch.WordTrace tailWord_3803249 prefixEnd_3803249 1301929857154463669664455 := by
  unfold tailWord_3803249
  simp only [CollatzResearch.WordTrace]
  refine ⟨138715886998485891061532801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92477257998990594041021867 138715886998485891061532801)
  ·
    refine ⟨104036915248864418296149601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138715886998485891061532801 104036915248864418296149601)
    ·
      refine ⟨78027686436648313722112201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104036915248864418296149601 78027686436648313722112201)
      ·
        refine ⟨58520764827486235291584151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78027686436648313722112201 58520764827486235291584151)
        ·
          refine ⟨87781147241229352937376227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58520764827486235291584151 87781147241229352937376227)
          ·
            refine ⟨131671720861844029406064341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87781147241229352937376227 131671720861844029406064341)
            ·
              refine ⟨3086055957699469439204633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 131671720861844029406064341 3086055957699469439204633)
              ·
                refine ⟨2314541968274602079403475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3086055957699469439204633 2314541968274602079403475)
                ·
                  refine ⟨3471812952411903119105213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2314541968274602079403475 3471812952411903119105213)
                  ·
                    refine ⟨1301929857154463669664455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3471812952411903119105213 1301929857154463669664455)
                    ·
                      rfl

theorem cell22_3803249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 1, 3].length) (baseStart_3803249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803249 prefixEnd_3803249 := by exact prefixLift 3803249
  have htrace : WordTrace (prefixWord ++ tailWord_3803249) baseStart_3803249 baseEnd_3803249 := by
    simpa [prefixWord, tailWord_3803249, baseEnd_3803249] using wordTrace_append hprefix tailTrace_3803249
  have hstable : (prefixWord ++ tailWord_3803249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803249).length < 2 ^ (prefixWord ++ tailWord_3803249).sum := by decide
  have hdescent : baseEnd_3803249 < baseStart_3803249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803273 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 8]
def baseStart_3803273 : Nat := 118140960795 + 3803273 * 2 ^ 59
def prefixEnd_3803273 : Nat := 4983230072969 + 3 ^ 40 * 3803273 * 2
def baseEnd_3803273 : Nat := 433979357614978535688127

theorem tailTrace_3803273 : CollatzResearch.WordTrace tailWord_3803273 prefixEnd_3803273 433979357614978535688127 := by
  unfold tailWord_3803273
  simp only [CollatzResearch.WordTrace]
  refine ⟨138716762350398943160406473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92477841566932628773604315 138716762350398943160406473)
  ·
    refine ⟨104037571762799207370304855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138716762350398943160406473 104037571762799207370304855)
    ·
      refine ⟨156056357644198811055457283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104037571762799207370304855 156056357644198811055457283)
      ·
        refine ⟨234084536466298216583185925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156056357644198811055457283 234084536466298216583185925)
        ·
          refine ⟨43890850587430915609347361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234084536466298216583185925 43890850587430915609347361)
          ·
            refine ⟨32918137940573186707010521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43890850587430915609347361 32918137940573186707010521)
            ·
              refine ⟨24688603455429890030257891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32918137940573186707010521 24688603455429890030257891)
              ·
                refine ⟨37032905183144835045386837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24688603455429890030257891 37032905183144835045386837)
                ·
                  refine ⟨433979357614978535688127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37032905183144835045386837 433979357614978535688127)
                  ·
                    rfl

theorem cell22_3803273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 8].length) (baseStart_3803273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803273 prefixEnd_3803273 := by exact prefixLift 3803273
  have htrace : WordTrace (prefixWord ++ tailWord_3803273) baseStart_3803273 baseEnd_3803273 := by
    simpa [prefixWord, tailWord_3803273, baseEnd_3803273] using wordTrace_append hprefix tailTrace_3803273
  have hstable : (prefixWord ++ tailWord_3803273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803273).length < 2 ^ (prefixWord ++ tailWord_3803273).sum := by decide
  have hdescent : baseEnd_3803273 < baseStart_3803273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803322 : List Nat := [3, 1, 1, 1, 2, 2, 4, 3, 2, 3]
def baseStart_3803322 : Nat := 118140960795 + 3803322 * 2 ^ 59
def prefixEnd_3803322 : Nat := 4983230072969 + 3 ^ 40 * 3803322 * 2
def baseEnd_3803322 : Nat := 1301954846546315812589231

theorem tailTrace_3803322 : CollatzResearch.WordTrace tailWord_3803322 prefixEnd_3803322 1301954846546315812589231 := by
  unfold tailWord_3803322
  simp only [CollatzResearch.WordTrace]
  refine ⟨34679637381805356132235055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92479033018147616352626813 34679637381805356132235055)
  ·
    refine ⟨52019456072708034198352583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34679637381805356132235055 52019456072708034198352583)
    ·
      refine ⟨78029184109062051297528875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52019456072708034198352583 78029184109062051297528875)
      ·
        refine ⟨117043776163593076946293313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78029184109062051297528875 117043776163593076946293313)
        ·
          refine ⟨87782832122694807709719985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117043776163593076946293313 87782832122694807709719985)
          ·
            refine ⟨65837124092021105782289989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87782832122694807709719985 65837124092021105782289989)
            ·
              refine ⟨12344460767253957334179373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65837124092021105782289989 12344460767253957334179373)
              ·
                refine ⟨4629172787720234000317265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12344460767253957334179373 4629172787720234000317265)
                ·
                  refine ⟨3471879590790175500237949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4629172787720234000317265 3471879590790175500237949)
                  ·
                    refine ⟨1301954846546315812589231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3471879590790175500237949 1301954846546315812589231)
                    ·
                      rfl

theorem cell22_3803322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_3803322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803322 prefixEnd_3803322 := by exact prefixLift 3803322
  have htrace : WordTrace (prefixWord ++ tailWord_3803322) baseStart_3803322 baseEnd_3803322 := by
    simpa [prefixWord, tailWord_3803322, baseEnd_3803322] using wordTrace_append hprefix tailTrace_3803322
  have hstable : (prefixWord ++ tailWord_3803322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803322).length < 2 ^ (prefixWord ++ tailWord_3803322).sum := by decide
  have hdescent : baseEnd_3803322 < baseStart_3803322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803356 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 4, 3]
def baseStart_3803356 : Nat := 118140960795 + 3803356 * 2 ^ 59
def prefixEnd_3803356 : Nat := 4983230072969 + 3 ^ 40 * 3803356 * 2
def baseEnd_3803356 : Nat := 1301966485441151057239127

theorem tailTrace_3803356 : CollatzResearch.WordTrace tailWord_3803356 prefixEnd_3803356 1301966485441151057239127 := by
  unfold tailWord_3803356
  simp only [CollatzResearch.WordTrace]
  refine ⟨69359894804549124167838961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92479859739398832223785281 69359894804549124167838961)
  ·
    refine ⟨52019921103411843125879221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69359894804549124167838961 52019921103411843125879221)
    ·
      refine ⟨4876867603444860293051177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52019921103411843125879221 4876867603444860293051177)
      ·
        refine ⟨3657650702583645219788383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4876867603444860293051177 3657650702583645219788383)
        ·
          refine ⟨5486476053875467829682575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3657650702583645219788383 5486476053875467829682575)
          ·
            refine ⟨8229714080813201744523863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5486476053875467829682575 8229714080813201744523863)
            ·
              refine ⟨12344571121219802616785795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8229714080813201744523863 12344571121219802616785795)
              ·
                refine ⟨18516856681829703925178693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12344571121219802616785795 18516856681829703925178693)
                ·
                  refine ⟨3471910627843069485971005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18516856681829703925178693 3471910627843069485971005)
                  ·
                    refine ⟨1301966485441151057239127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3471910627843069485971005 1301966485441151057239127)
                    ·
                      rfl

theorem cell22_3803356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_3803356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803356 prefixEnd_3803356 := by exact prefixLift 3803356
  have htrace : WordTrace (prefixWord ++ tailWord_3803356) baseStart_3803356 baseEnd_3803356 := by
    simpa [prefixWord, tailWord_3803356, baseEnd_3803356] using wordTrace_append hprefix tailTrace_3803356
  have hstable : (prefixWord ++ tailWord_3803356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803356).length < 2 ^ (prefixWord ++ tailWord_3803356).sum := by decide
  have hdescent : baseEnd_3803356 < baseStart_3803356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803401 : List Nat := [1, 2, 1, 1, 3, 6, 1, 3, 1, 3]
def baseStart_3803401 : Nat := 118140960795 + 3803401 * 2 ^ 59
def prefixEnd_3803401 : Nat := 4983230072969 + 3 ^ 40 * 3803401 * 2
def baseEnd_3803401 : Nat := 1301981889860785939863989

theorem tailTrace_3803401 : CollatzResearch.WordTrace tailWord_3803401 prefixEnd_3803401 1301981889860785939863989 := by
  unfold tailWord_3803401
  simp only [CollatzResearch.WordTrace]
  refine ⟨138721430893935221021066057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92480953929290147347377371 138721430893935221021066057)
  ·
    refine ⟨104041073170451415765799543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138721430893935221021066057 104041073170451415765799543)
    ·
      refine ⟨156061609755677123648699315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104041073170451415765799543 156061609755677123648699315)
      ·
        refine ⟨234092414633515685473048973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156061609755677123648699315 234092414633515685473048973)
        ·
          refine ⟨87784655487568382052393365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234092414633515685473048973 87784655487568382052393365)
          ·
            refine ⟨4114905725979767908705939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87784655487568382052393365 4114905725979767908705939)
            ·
              refine ⟨6172358588969651863058909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4114905725979767908705939 6172358588969651863058909)
              ·
                refine ⟨2314634470863619448647091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6172358588969651863058909 2314634470863619448647091)
                ·
                  refine ⟨3471951706295429172970637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2314634470863619448647091 3471951706295429172970637)
                  ·
                    refine ⟨1301981889860785939863989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3471951706295429172970637 1301981889860785939863989)
                    ·
                      rfl

theorem cell22_3803401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 1, 3].length) (baseStart_3803401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803401 prefixEnd_3803401 := by exact prefixLift 3803401
  have htrace : WordTrace (prefixWord ++ tailWord_3803401) baseStart_3803401 baseEnd_3803401 := by
    simpa [prefixWord, tailWord_3803401, baseEnd_3803401] using wordTrace_append hprefix tailTrace_3803401
  have hstable : (prefixWord ++ tailWord_3803401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803401).length < 2 ^ (prefixWord ++ tailWord_3803401).sum := by decide
  have hdescent : baseEnd_3803401 < baseStart_3803401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803418 : List Nat := [3, 1, 1, 3, 4, 1, 3, 2, 1, 3]
def baseStart_3803418 : Nat := 118140960795 + 3803418 * 2 ^ 59
def prefixEnd_3803418 : Nat := 4983230072969 + 3 ^ 40 * 3803418 * 2
def baseEnd_3803418 : Nat := 1301987709308203562188937

theorem tailTrace_3803418 : CollatzResearch.WordTrace tailWord_3803418 prefixEnd_3803418 1301987709308203562188937 := by
  unfold tailWord_3803418
  simp only [CollatzResearch.WordTrace]
  refine ⟨34680512733718408231108727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92481367289915755282956605 34680512733718408231108727)
  ·
    refine ⟨52020769100577612346663091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34680512733718408231108727 52020769100577612346663091)
    ·
      refine ⟨78031153650866418519994637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52020769100577612346663091 78031153650866418519994637)
      ·
        refine ⟨29261682619074906944997989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78031153650866418519994637 29261682619074906944997989)
        ·
          refine ⟨5486565491076545052187123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29261682619074906944997989 5486565491076545052187123)
          ·
            refine ⟨8229848236614817578280685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5486565491076545052187123 8229848236614817578280685)
            ·
              refine ⟨3086193088730556591855257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8229848236614817578280685 3086193088730556591855257)
              ·
                refine ⟨2314644816547917443891443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3086193088730556591855257 2314644816547917443891443)
                ·
                  refine ⟨3471967224821876165837165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2314644816547917443891443 3471967224821876165837165)
                  ·
                    refine ⟨1301987709308203562188937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3471967224821876165837165 1301987709308203562188937)
                    ·
                      rfl

theorem cell22_3803418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 1, 3].length) (baseStart_3803418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803418 prefixEnd_3803418 := by exact prefixLift 3803418
  have htrace : WordTrace (prefixWord ++ tailWord_3803418) baseStart_3803418 baseEnd_3803418 := by
    simpa [prefixWord, tailWord_3803418, baseEnd_3803418] using wordTrace_append hprefix tailTrace_3803418
  have hstable : (prefixWord ++ tailWord_3803418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803418).length < 2 ^ (prefixWord ++ tailWord_3803418).sum := by decide
  have hdescent : baseEnd_3803418 < baseStart_3803418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803444 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_3803444 : Nat := 118140960795 + 3803444 * 2 ^ 59
def prefixEnd_3803444 : Nat := 4983230072969 + 3 ^ 40 * 3803444 * 2
def baseEnd_3803444 : Nat := 1301996609639548161038857

theorem tailTrace_3803444 : CollatzResearch.WordTrace tailWord_3803444 prefixEnd_3803444 1301996609639548161038857 := by
  unfold tailWord_3803444
  simp only [CollatzResearch.WordTrace]
  refine ⟨69361499616389719682440693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92481999488519626243254257 69361499616389719682440693)
  ·
    refine ⟨6502640589036536220228815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69361499616389719682440693 6502640589036536220228815)
    ·
      refine ⟨9753960883554804330343223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6502640589036536220228815 9753960883554804330343223)
      ·
        refine ⟨14630941325332206495514835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9753960883554804330343223 14630941325332206495514835)
        ·
          refine ⟨21946411987998309743272253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14630941325332206495514835 21946411987998309743272253)
          ·
            refine ⟨8229904495499366153727095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21946411987998309743272253 8229904495499366153727095)
            ·
              refine ⟨12344856743249049230590643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8229904495499366153727095 12344856743249049230590643)
              ·
                refine ⟨18517285114873573845885965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12344856743249049230590643 18517285114873573845885965)
                ·
                  refine ⟨6943981918077590192207237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18517285114873573845885965 6943981918077590192207237)
                  ·
                    refine ⟨1301996609639548161038857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6943981918077590192207237 1301996609639548161038857)
                    ·
                      rfl

theorem cell22_3803444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_3803444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803444 prefixEnd_3803444 := by exact prefixLift 3803444
  have htrace : WordTrace (prefixWord ++ tailWord_3803444) baseStart_3803444 baseEnd_3803444 := by
    simpa [prefixWord, tailWord_3803444, baseEnd_3803444] using wordTrace_append hprefix tailTrace_3803444
  have hstable : (prefixWord ++ tailWord_3803444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803444).length < 2 ^ (prefixWord ++ tailWord_3803444).sum := by decide
  have hdescent : baseEnd_3803444 < baseStart_3803444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803472 : List Nat := [2, 1, 1, 1, 1, 6, 2, 2, 2, 4]
def baseStart_3803472 : Nat := 118140960795 + 3803472 * 2 ^ 59
def prefixEnd_3803472 : Nat := 4983230072969 + 3 ^ 40 * 3803472 * 2
def baseEnd_3803472 : Nat := 1302006194611765421338771

theorem tailTrace_3803472 : CollatzResearch.WordTrace tailWord_3803472 prefixEnd_3803472 1302006194611765421338771 := by
  unfold tailWord_3803472
  simp only [CollatzResearch.WordTrace]
  refine ⟨69362010238339000073450335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92482680317785333431267113 69362010238339000073450335)
  ·
    refine ⟨104043015357508500110175503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69362010238339000073450335 104043015357508500110175503)
    ·
      refine ⟨156064523036262750165263255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104043015357508500110175503 156064523036262750165263255)
      ·
        refine ⟨234096784554394125247894883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156064523036262750165263255 234096784554394125247894883)
        ·
          refine ⟨351145176831591187871842325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234096784554394125247894883 351145176831591187871842325)
          ·
            refine ⟨16459930163980836931492609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 351145176831591187871842325 16459930163980836931492609)
            ·
              refine ⟨12344947622985627698619457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16459930163980836931492609 12344947622985627698619457)
              ·
                refine ⟨9258710717239220773964593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12344947622985627698619457 9258710717239220773964593)
                ·
                  refine ⟨6944033037929415580473445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9258710717239220773964593 6944033037929415580473445)
                  ·
                    refine ⟨1302006194611765421338771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6944033037929415580473445 1302006194611765421338771)
                    ·
                      rfl

theorem cell22_3803472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 2, 4].length) (baseStart_3803472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803472 prefixEnd_3803472 := by exact prefixLift 3803472
  have htrace : WordTrace (prefixWord ++ tailWord_3803472) baseStart_3803472 baseEnd_3803472 := by
    simpa [prefixWord, tailWord_3803472, baseEnd_3803472] using wordTrace_append hprefix tailTrace_3803472
  have hstable : (prefixWord ++ tailWord_3803472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803472).length < 2 ^ (prefixWord ++ tailWord_3803472).sum := by decide
  have hdescent : baseEnd_3803472 < baseStart_3803472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803474 : List Nat := [3, 2, 2, 1, 1, 1, 3, 4, 2, 3]
def baseStart_3803474 : Nat := 118140960795 + 3803474 * 2 ^ 59
def prefixEnd_3803474 : Nat := 4983230072969 + 3 ^ 40 * 3803474 * 2
def baseEnd_3803474 : Nat := 1302006879252638082788765

theorem tailTrace_3803474 : CollatzResearch.WordTrace tailWord_3803474 prefixEnd_3803474 1302006879252638082788765 := by
  unfold tailWord_3803474
  simp only [CollatzResearch.WordTrace]
  refine ⟨34681023355667688622118369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92482728948447169658982317 34681023355667688622118369)
  ·
    refine ⟨26010767516750766466588777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34681023355667688622118369 26010767516750766466588777)
    ·
      refine ⟨19508075637563074849941583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26010767516750766466588777 19508075637563074849941583)
      ·
        refine ⟨29262113456344612274912375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19508075637563074849941583 29262113456344612274912375)
        ·
          refine ⟨43893170184516918412368563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29262113456344612274912375 43893170184516918412368563)
          ·
            refine ⟨65839755276775377618552845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43893170184516918412368563 65839755276775377618552845)
            ·
              refine ⟨24689908228790766606957317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65839755276775377618552845 24689908228790766606957317)
              ·
                refine ⟨4629357792898268738804497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24689908228790766606957317 4629357792898268738804497)
                ·
                  refine ⟨3472018344673701554103373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4629357792898268738804497 3472018344673701554103373)
                  ·
                    refine ⟨1302006879252638082788765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3472018344673701554103373 1302006879252638082788765)
                    ·
                      rfl

theorem cell22_3803474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_3803474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803474 prefixEnd_3803474 := by exact prefixLift 3803474
  have htrace : WordTrace (prefixWord ++ tailWord_3803474) baseStart_3803474 baseEnd_3803474 := by
    simpa [prefixWord, tailWord_3803474, baseEnd_3803474] using wordTrace_append hprefix tailTrace_3803474
  have hstable : (prefixWord ++ tailWord_3803474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803474).length < 2 ^ (prefixWord ++ tailWord_3803474).sum := by decide
  have hdescent : baseEnd_3803474 < baseStart_3803474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803476 : List Nat := [2, 4, 1, 1, 2, 2, 4, 2, 4]
def baseStart_3803476 : Nat := 118140960795 + 3803476 * 2 ^ 59
def prefixEnd_3803476 : Nat := 4983230072969 + 3 ^ 40 * 3803476 * 2
def baseEnd_3803476 : Nat := 434002521297836914746253

theorem tailTrace_3803476 : CollatzResearch.WordTrace tailWord_3803476 prefixEnd_3803476 434002521297836914746253 := by
  unfold tailWord_3803476
  simp only [CollatzResearch.WordTrace]
  refine ⟨69362083184331754415023141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92482777579109005886697521 69362083184331754415023141)
  ·
    refine ⟨13005390597062203952816839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69362083184331754415023141 13005390597062203952816839)
    ·
      refine ⟨19508085895593305929225259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13005390597062203952816839 19508085895593305929225259)
      ·
        refine ⟨29262128843389958893837889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19508085895593305929225259 29262128843389958893837889)
        ·
          refine ⟨21946596632542469170378417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29262128843389958893837889 21946596632542469170378417)
          ·
            refine ⟨16459947474406851877783813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21946596632542469170378417 16459947474406851877783813)
            ·
              refine ⟨3086240151451284727084465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16459947474406851877783813 3086240151451284727084465)
              ·
                refine ⟨2314680113588463545313349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3086240151451284727084465 2314680113588463545313349)
                ·
                  refine ⟨434002521297836914746253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2314680113588463545313349 434002521297836914746253)
                  ·
                    rfl

theorem cell22_3803476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_3803476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803476 prefixEnd_3803476 := by exact prefixLift 3803476
  have htrace : WordTrace (prefixWord ++ tailWord_3803476) baseStart_3803476 baseEnd_3803476 := by
    simpa [prefixWord, tailWord_3803476, baseEnd_3803476] using wordTrace_append hprefix tailTrace_3803476
  have hstable : (prefixWord ++ tailWord_3803476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803476).length < 2 ^ (prefixWord ++ tailWord_3803476).sum := by decide
  have hdescent : baseEnd_3803476 < baseStart_3803476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803532 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 7]
def baseStart_3803532 : Nat := 118140960795 + 3803532 * 2 ^ 59
def prefixEnd_3803532 : Nat := 4983230072969 + 3 ^ 40 * 3803532 * 2
def baseEnd_3803532 : Nat := 434008911279315088279529

theorem tailTrace_3803532 : CollatzResearch.WordTrace tailWord_3803532 prefixEnd_3803532 434008911279315088279529 := by
  unfold tailWord_3803532
  simp only [CollatzResearch.WordTrace]
  refine ⟨69363104428230315197042425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92484139237640420262723233 69363104428230315197042425)
  ·
    refine ⟨52022328321172736397781819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69363104428230315197042425 52022328321172736397781819)
    ·
      refine ⟨78033492481759104596672729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52022328321172736397781819 78033492481759104596672729)
      ·
        refine ⟨58525119361319328447504547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78033492481759104596672729 58525119361319328447504547)
        ·
          refine ⟨87787679041978992671256821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58525119361319328447504547 87787679041978992671256821)
          ·
            refine ⟨8230094910185530562930327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87787679041978992671256821 8230094910185530562930327)
            ·
              refine ⟨12345142365278295844395491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8230094910185530562930327 12345142365278295844395491)
              ·
                refine ⟨18517713547917443766593237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12345142365278295844395491 18517713547917443766593237)
                ·
                  refine ⟨434008911279315088279529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18517713547917443766593237 434008911279315088279529)
                  ·
                    rfl

theorem cell22_3803532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_3803532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803532 prefixEnd_3803532 := by exact prefixLift 3803532
  have htrace : WordTrace (prefixWord ++ tailWord_3803532) baseStart_3803532 baseEnd_3803532 := by
    simpa [prefixWord, tailWord_3803532, baseEnd_3803532] using wordTrace_append hprefix tailTrace_3803532
  have hstable : (prefixWord ++ tailWord_3803532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803532).length < 2 ^ (prefixWord ++ tailWord_3803532).sum := by decide
  have hdescent : baseEnd_3803532 < baseStart_3803532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803542 : List Nat := [5, 3, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_3803542 : Nat := 118140960795 + 3803542 * 2 ^ 59
def prefixEnd_3803542 : Nat := 4983230072969 + 3 ^ 40 * 3803542 * 2
def baseEnd_3803542 : Nat := 1302030157042308572088557

theorem tailTrace_3803542 : CollatzResearch.WordTrace tailWord_3803542 prefixEnd_3803542 1302030157042308572088557 := by
  unfold tailWord_3803542
  simp only [CollatzResearch.WordTrace]
  refine ⟨8670410849151525131371805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92484382390949601401299253 8670410849151525131371805)
  ·
    refine ⟨3251404068431821924264427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8670410849151525131371805 3251404068431821924264427)
    ·
      refine ⟨4877106102647732886396641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3251404068431821924264427 4877106102647732886396641)
      ·
        refine ⟨3657829576985799664797481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4877106102647732886396641 3657829576985799664797481)
        ·
          refine ⟨2743372182739349748598111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3657829576985799664797481 2743372182739349748598111)
          ·
            refine ⟨4115058274109024622897167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743372182739349748598111 4115058274109024622897167)
            ·
              refine ⟨6172587411163536934345751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4115058274109024622897167 6172587411163536934345751)
              ·
                refine ⟨9258881116745305401518627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6172587411163536934345751 9258881116745305401518627)
                ·
                  refine ⟨13888321675117958102277941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9258881116745305401518627 13888321675117958102277941)
                  ·
                    refine ⟨1302030157042308572088557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13888321675117958102277941 1302030157042308572088557)
                    ·
                      rfl

theorem cell22_3803542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_3803542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803542 prefixEnd_3803542 := by exact prefixLift 3803542
  have htrace : WordTrace (prefixWord ++ tailWord_3803542) baseStart_3803542 baseEnd_3803542 := by
    simpa [prefixWord, tailWord_3803542, baseEnd_3803542] using wordTrace_append hprefix tailTrace_3803542
  have hstable : (prefixWord ++ tailWord_3803542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803542).length < 2 ^ (prefixWord ++ tailWord_3803542).sum := by decide
  have hdescent : baseEnd_3803542 < baseStart_3803542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803624 : List Nat := [2, 1, 4, 1, 1, 3, 1, 3, 2, 4]
def baseStart_3803624 : Nat := 118140960795 + 3803624 * 2 ^ 59
def prefixEnd_3803624 : Nat := 4983230072969 + 3 ^ 40 * 3803624 * 2
def baseEnd_3803624 : Nat := 1302058227318087691538305

theorem tailTrace_3803624 : CollatzResearch.WordTrace tailWord_3803624 prefixEnd_3803624 1302058227318087691538305 := by
  unfold tailWord_3803624
  simp only [CollatzResearch.WordTrace]
  refine ⟨69364782186063665053216963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92486376248084886737622617 69364782186063665053216963)
  ·
    refine ⟨104047173279095497579825445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69364782186063665053216963 104047173279095497579825445)
    ·
      refine ⟨19508844989830405796217271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104047173279095497579825445 19508844989830405796217271)
      ·
        refine ⟨29263267484745608694325907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19508844989830405796217271 29263267484745608694325907)
        ·
          refine ⟨43894901227118413041488861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29263267484745608694325907 43894901227118413041488861)
          ·
            refine ⟨16460587960169404890558323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43894901227118413041488861 16460587960169404890558323)
            ·
              refine ⟨24690881940254107335837485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16460587960169404890558323 24690881940254107335837485)
              ·
                refine ⟨9259080727595290250939057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24690881940254107335837485 9259080727595290250939057)
                ·
                  refine ⟨6944310545696467688204293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9259080727595290250939057 6944310545696467688204293)
                  ·
                    refine ⟨1302058227318087691538305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6944310545696467688204293 1302058227318087691538305)
                    ·
                      rfl

theorem cell22_3803624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_3803624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803624 prefixEnd_3803624 := by exact prefixLift 3803624
  have htrace : WordTrace (prefixWord ++ tailWord_3803624) baseStart_3803624 baseEnd_3803624 := by
    simpa [prefixWord, tailWord_3803624, baseEnd_3803624] using wordTrace_append hprefix tailTrace_3803624
  have hstable : (prefixWord ++ tailWord_3803624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803624).length < 2 ^ (prefixWord ++ tailWord_3803624).sum := by decide
  have hdescent : baseEnd_3803624 < baseStart_3803624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803729 : List Nat := [1, 2, 2, 1, 3, 3, 2, 2, 6]
def baseStart_3803729 : Nat := 118140960795 + 3803729 * 2 ^ 59
def prefixEnd_3803729 : Nat := 4983230072969 + 3 ^ 40 * 3803729 * 2
def baseEnd_3803729 : Nat := 434031390321300805887661

theorem tailTrace_3803729 : CollatzResearch.WordTrace tailWord_3803729 prefixEnd_3803729 434031390321300805887661 := by
  unfold tailWord_3803729
  simp only [CollatzResearch.WordTrace]
  refine ⟨138733394036746933039006241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92488929357831288692670827 138733394036746933039006241)
  ·
    refine ⟨104050045527560199779254681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138733394036746933039006241 104050045527560199779254681)
    ·
      refine ⟨78037534145670149834441011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104050045527560199779254681 78037534145670149834441011)
      ·
        refine ⟨117056301218505224751661517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78037534145670149834441011 117056301218505224751661517)
        ·
          refine ⟨43896112956939459281873069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117056301218505224751661517 43896112956939459281873069)
          ·
            refine ⟨16461042358852297230702401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43896112956939459281873069 16461042358852297230702401)
            ·
              refine ⟨12345781769139222923026801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16461042358852297230702401 12345781769139222923026801)
              ·
                refine ⟨9259336326854417192270101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12345781769139222923026801 9259336326854417192270101)
                ·
                  refine ⟨434031390321300805887661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9259336326854417192270101 434031390321300805887661)
                  ·
                    rfl

theorem cell22_3803729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 6].length) (baseStart_3803729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803729 prefixEnd_3803729 := by exact prefixLift 3803729
  have htrace : WordTrace (prefixWord ++ tailWord_3803729) baseStart_3803729 baseEnd_3803729 := by
    simpa [prefixWord, tailWord_3803729, baseEnd_3803729] using wordTrace_append hprefix tailTrace_3803729
  have hstable : (prefixWord ++ tailWord_3803729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803729).length < 2 ^ (prefixWord ++ tailWord_3803729).sum := by decide
  have hdescent : baseEnd_3803729 < baseStart_3803729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803744 : List Nat := [2, 1, 1, 3, 2, 1, 2, 4, 1, 5]
def baseStart_3803744 : Nat := 118140960795 + 3803744 * 2 ^ 59
def prefixEnd_3803744 : Nat := 4983230072969 + 3 ^ 40 * 3803744 * 2
def baseEnd_3803744 : Nat := 1302099305770447378537937

theorem tailTrace_3803744 : CollatzResearch.WordTrace tailWord_3803744 prefixEnd_3803744 1302099305770447378537937 := by
  unfold tailWord_3803744
  simp only [CollatzResearch.WordTrace]
  refine ⟨69366970565846295300401143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92489294087795060400534857 69366970565846295300401143)
  ·
    refine ⟨104050455848769442950601715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69366970565846295300401143 104050455848769442950601715)
    ·
      refine ⟨156075683773154164425902573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104050455848769442950601715 156075683773154164425902573)
      ·
        refine ⟨58528381414932811659713465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156075683773154164425902573 58528381414932811659713465)
        ·
          refine ⟨43896286061199608744785099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58528381414932811659713465 43896286061199608744785099)
          ·
            refine ⟨65844429091799413117177649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43896286061199608744785099 65844429091799413117177649)
            ·
              refine ⟨49383321818849559837883237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65844429091799413117177649 49383321818849559837883237)
              ·
                refine ⟨9259372841034292469603107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49383321818849559837883237 9259372841034292469603107)
                ·
                  refine ⟨13889059261551438704404661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9259372841034292469603107 13889059261551438704404661)
                  ·
                    refine ⟨1302099305770447378537937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13889059261551438704404661 1302099305770447378537937)
                    ·
                      rfl

theorem cell22_3803744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 1, 5].length) (baseStart_3803744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803744 prefixEnd_3803744 := by exact prefixLift 3803744
  have htrace : WordTrace (prefixWord ++ tailWord_3803744) baseStart_3803744 baseEnd_3803744 := by
    simpa [prefixWord, tailWord_3803744, baseEnd_3803744] using wordTrace_append hprefix tailTrace_3803744
  have hstable : (prefixWord ++ tailWord_3803744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803744).length < 2 ^ (prefixWord ++ tailWord_3803744).sum := by decide
  have hdescent : baseEnd_3803744 < baseStart_3803744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803759 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 4, 4]
def baseStart_3803759 : Nat := 118140960795 + 3803759 * 2 ^ 59
def prefixEnd_3803759 : Nat := 4983230072969 + 3 ^ 40 * 3803759 * 2
def baseEnd_3803759 : Nat := 1302104440576992339412891

theorem tailTrace_3803759 : CollatzResearch.WordTrace tailWord_3803759 prefixEnd_3803759 1302104440576992339412891 := by
  unfold tailWord_3803759
  simp only [CollatzResearch.WordTrace]
  refine ⟨138734488226638248162598331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92489658817758832108398887 138734488226638248162598331)
  ·
    refine ⟨208101732339957372243897497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138734488226638248162598331 208101732339957372243897497)
    ·
      refine ⟨156076299254968029182923123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208101732339957372243897497 156076299254968029182923123)
      ·
        refine ⟨234114448882452043774384685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156076299254968029182923123 234114448882452043774384685)
        ·
          refine ⟨87792918330919516415394257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234114448882452043774384685 87792918330919516415394257)
          ·
            refine ⟨65844688748189637311545693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87792918330919516415394257 65844688748189637311545693)
            ·
              refine ⟨24691758280571113991829635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65844688748189637311545693 24691758280571113991829635)
              ·
                refine ⟨37037637420856670987744453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24691758280571113991829635 37037637420856670987744453)
                ·
                  refine ⟨6944557016410625810202085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37037637420856670987744453 6944557016410625810202085)
                  ·
                    refine ⟨1302104440576992339412891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6944557016410625810202085 1302104440576992339412891)
                    ·
                      rfl

theorem cell22_3803759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 4].length) (baseStart_3803759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803759 prefixEnd_3803759 := by exact prefixLift 3803759
  have htrace : WordTrace (prefixWord ++ tailWord_3803759) baseStart_3803759 baseEnd_3803759 := by
    simpa [prefixWord, tailWord_3803759, baseEnd_3803759] using wordTrace_append hprefix tailTrace_3803759
  have hstable : (prefixWord ++ tailWord_3803759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803759).length < 2 ^ (prefixWord ++ tailWord_3803759).sum := by decide
  have hdescent : baseEnd_3803759 < baseStart_3803759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803821 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_3803821 : Nat := 118140960795 + 3803821 * 2 ^ 59
def prefixEnd_3803821 : Nat := 4983230072969 + 3 ^ 40 * 3803821 * 2
def baseEnd_3803821 : Nat := 1302125664444044844362701

theorem tailTrace_3803821 : CollatzResearch.WordTrace tailWord_3803821 prefixEnd_3803821 1302125664444044844362701 := by
  unfold tailWord_3803821
  simp only [CollatzResearch.WordTrace]
  refine ⟨138736749552413632751355317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92491166368275755167570211 138736749552413632751355317)
  ·
    refine ⟨13006570270538778070439561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138736749552413632751355317 13006570270538778070439561)
    ·
      refine ⟨9754927702904083552829671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13006570270538778070439561 9754927702904083552829671)
      ·
        refine ⟨14632391554356125329244507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9754927702904083552829671 14632391554356125329244507)
        ·
          refine ⟨21948587331534187993866761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14632391554356125329244507 21948587331534187993866761)
          ·
            refine ⟨16461440498650640995400071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21948587331534187993866761 16461440498650640995400071)
            ·
              refine ⟨24692160747975961493100107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16461440498650640995400071 24692160747975961493100107)
              ·
                refine ⟨37038241121963942239650161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24692160747975961493100107 37038241121963942239650161)
                ·
                  refine ⟨27778680841472956679737621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37038241121963942239650161 27778680841472956679737621)
                  ·
                    refine ⟨1302125664444044844362701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27778680841472956679737621 1302125664444044844362701)
                    ·
                      rfl

theorem cell22_3803821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_3803821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803821 prefixEnd_3803821 := by exact prefixLift 3803821
  have htrace : WordTrace (prefixWord ++ tailWord_3803821) baseStart_3803821 baseEnd_3803821 := by
    simpa [prefixWord, tailWord_3803821, baseEnd_3803821] using wordTrace_append hprefix tailTrace_3803821
  have hstable : (prefixWord ++ tailWord_3803821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803821).length < 2 ^ (prefixWord ++ tailWord_3803821).sum := by decide
  have hdescent : baseEnd_3803821 < baseStart_3803821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803825 : List Nat := [1, 2, 2, 6, 2, 1, 1, 7]
def baseStart_3803825 : Nat := 118140960795 + 3803825 * 2 ^ 59
def prefixEnd_3803825 : Nat := 4983230072969 + 3 ^ 40 * 3803825 * 2
def baseEnd_3803825 : Nat := 144680781525087796362521

theorem tailTrace_3803825 : CollatzResearch.WordTrace tailWord_3803825 prefixEnd_3803825 144680781525087796362521 := by
  unfold tailWord_3803825
  simp only [CollatzResearch.WordTrace]
  refine ⟨138736895444399141434500929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92491263629599427623000619 138736895444399141434500929)
  ·
    refine ⟨104052671583299356075875697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138736895444399141434500929 104052671583299356075875697)
    ·
      refine ⟨78039503687474517056906773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104052671583299356075875697 78039503687474517056906773)
      ·
        refine ⟨3658101735350367987042505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 78039503687474517056906773 3658101735350367987042505)
        ·
          refine ⟨2743576301512775990281879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3658101735350367987042505 2743576301512775990281879)
          ·
            refine ⟨4115364452269163985422819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743576301512775990281879 4115364452269163985422819)
            ·
              refine ⟨6173046678403745978134229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4115364452269163985422819 6173046678403745978134229)
              ·
                refine ⟨144680781525087796362521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6173046678403745978134229 144680781525087796362521)
                ·
                  rfl

theorem cell22_3803825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 7].length) (baseStart_3803825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803825 prefixEnd_3803825 := by exact prefixLift 3803825
  have htrace : WordTrace (prefixWord ++ tailWord_3803825) baseStart_3803825 baseEnd_3803825 := by
    simpa [prefixWord, tailWord_3803825, baseEnd_3803825] using wordTrace_append hprefix tailTrace_3803825
  have hstable : (prefixWord ++ tailWord_3803825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803825).length < 2 ^ (prefixWord ++ tailWord_3803825).sum := by decide
  have hdescent : baseEnd_3803825 < baseStart_3803825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803836 : List Nat := [2, 2, 2, 3, 1, 1, 1, 5, 5]
def baseStart_3803836 : Nat := 118140960795 + 3803836 * 2 ^ 59
def prefixEnd_3803836 : Nat := 4983230072969 + 3 ^ 40 * 3803836 * 2
def baseEnd_3803836 : Nat := 434043599750196601745885

theorem tailTrace_3803836 : CollatzResearch.WordTrace tailWord_3803836 prefixEnd_3803836 434043599750196601745885 := by
  unfold tailWord_3803836
  simp only [CollatzResearch.WordTrace]
  refine ⟨69368648323679645156575681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92491531098239526875434241 69368648323679645156575681)
  ·
    refine ⟨52026486242759733867431761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69368648323679645156575681 52026486242759733867431761)
    ·
      refine ⟨39019864682069800400573821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52026486242759733867431761 39019864682069800400573821)
      ·
        refine ⟨14632449255776175150215183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39019864682069800400573821 14632449255776175150215183)
        ·
          refine ⟨21948673883664262725322775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14632449255776175150215183 21948673883664262725322775)
          ·
            refine ⟨32923010825496394087984163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21948673883664262725322775 32923010825496394087984163)
            ·
              refine ⟨49384516238244591131976245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32923010825496394087984163 49384516238244591131976245)
              ·
                refine ⟨4629798397335430418622773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49384516238244591131976245 4629798397335430418622773)
                ·
                  refine ⟨434043599750196601745885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4629798397335430418622773 434043599750196601745885)
                  ·
                    rfl

theorem cell22_3803836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_3803836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803836 prefixEnd_3803836 := by exact prefixLift 3803836
  have htrace : WordTrace (prefixWord ++ tailWord_3803836) baseStart_3803836 baseEnd_3803836 := by
    simpa [prefixWord, tailWord_3803836, baseEnd_3803836] using wordTrace_append hprefix tailTrace_3803836
  have hstable : (prefixWord ++ tailWord_3803836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803836).length < 2 ^ (prefixWord ++ tailWord_3803836).sum := by decide
  have hdescent : baseEnd_3803836 < baseStart_3803836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803868 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 2, 5]
def baseStart_3803868 : Nat := 118140960795 + 3803868 * 2 ^ 59
def prefixEnd_3803868 : Nat := 4983230072969 + 3 ^ 40 * 3803868 * 2
def baseEnd_3803868 : Nat := 1302141753504552388437557

theorem tailTrace_3803868 : CollatzResearch.WordTrace tailWord_3803868 prefixEnd_3803868 1302141753504552388437557 := by
  unfold tailWord_3803868
  simp only [CollatzResearch.WordTrace]
  refine ⟨69369231891621679889158129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92492309188828906518877505 69369231891621679889158129)
  ·
    refine ⟨52026923918716259916868597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69369231891621679889158129 52026923918716259916868597)
    ·
      refine ⟨4877524117379649367206431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52026923918716259916868597 4877524117379649367206431)
      ·
        refine ⟨7316286176069474050809647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4877524117379649367206431 7316286176069474050809647)
        ·
          refine ⟨10974429264104211076214471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7316286176069474050809647 10974429264104211076214471)
          ·
            refine ⟨16461643896156316614321707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10974429264104211076214471 16461643896156316614321707)
            ·
              refine ⟨24692465844234474921482561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16461643896156316614321707 24692465844234474921482561)
              ·
                refine ⟨18519349383175856191111921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24692465844234474921482561 18519349383175856191111921)
                ·
                  refine ⟨13889512037381892143333941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18519349383175856191111921 13889512037381892143333941)
                  ·
                    refine ⟨1302141753504552388437557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13889512037381892143333941 1302141753504552388437557)
                    ·
                      rfl

theorem cell22_3803868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_3803868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803868 prefixEnd_3803868 := by exact prefixLift 3803868
  have htrace : WordTrace (prefixWord ++ tailWord_3803868) baseStart_3803868 baseEnd_3803868 := by
    simpa [prefixWord, tailWord_3803868, baseEnd_3803868] using wordTrace_append hprefix tailTrace_3803868
  have hstable : (prefixWord ++ tailWord_3803868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803868).length < 2 ^ (prefixWord ++ tailWord_3803868).sum := by decide
  have hdescent : baseEnd_3803868 < baseStart_3803868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3803975 : List Nat := [1, 1, 4, 1, 2, 1, 1, 7, 1, 3]
def baseStart_3803975 : Nat := 118140960795 + 3803975 * 2 ^ 59
def prefixEnd_3803975 : Nat := 4983230072969 + 3 ^ 40 * 3803975 * 2
def baseEnd_3803975 : Nat := 1302178381791239776012229

theorem tailTrace_3803975 : CollatzResearch.WordTrace tailWord_3803975 prefixEnd_3803975 1302178381791239776012229 := by
  unfold tailWord_3803975
  simp only [CollatzResearch.WordTrace]
  refine ⟨138742366393855717052461379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92494910929237144701640919 138742366393855717052461379)
  ·
    refine ⟨208113549590783575578692069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138742366393855717052461379 208113549590783575578692069)
    ·
      refine ⟨39021290548271920421004763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208113549590783575578692069 39021290548271920421004763)
      ·
        refine ⟨58531935822407880631507145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39021290548271920421004763 58531935822407880631507145)
        ·
          refine ⟨43898951866805910473630359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58531935822407880631507145 43898951866805910473630359)
          ·
            refine ⟨65848427800208865710445539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43898951866805910473630359 65848427800208865710445539)
            ·
              refine ⟨98772641700313298565668309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65848427800208865710445539 98772641700313298565668309)
              ·
                refine ⟨2314983789851092935132851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 98772641700313298565668309 2314983789851092935132851)
                ·
                  refine ⟨3472475684776639402699277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2314983789851092935132851 3472475684776639402699277)
                  ·
                    refine ⟨1302178381791239776012229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3472475684776639402699277 1302178381791239776012229)
                    ·
                      rfl

theorem cell22_3803975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_3803975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3803975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3803975 prefixEnd_3803975 := by exact prefixLift 3803975
  have htrace : WordTrace (prefixWord ++ tailWord_3803975) baseStart_3803975 baseEnd_3803975 := by
    simpa [prefixWord, tailWord_3803975, baseEnd_3803975] using wordTrace_append hprefix tailTrace_3803975
  have hstable : (prefixWord ++ tailWord_3803975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3803975).length < 2 ^ (prefixWord ++ tailWord_3803975).sum := by decide
  have hdescent : baseEnd_3803975 < baseStart_3803975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3803975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804003 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 2, 5]
def baseStart_3804003 : Nat := 118140960795 + 3804003 * 2 ^ 59
def prefixEnd_3804003 : Nat := 4983230072969 + 3 ^ 40 * 3804003 * 2
def baseEnd_3804003 : Nat := 1302187966763457036312143

theorem tailTrace_3804003 : CollatzResearch.WordTrace tailWord_3804003 prefixEnd_3804003 1302187966763457036312143 := by
  unfold tailWord_3804003
  simp only [CollatzResearch.WordTrace]
  refine ⟨138743387637754277834480663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92495591758502851889653775 138743387637754277834480663)
  ·
    refine ⟨208115081456631416751720995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138743387637754277834480663 208115081456631416751720995)
    ·
      refine ⟨312172622184947125127581493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208115081456631416751720995 312172622184947125127581493)
      ·
        refine ⟨29266183329838792980710765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 312172622184947125127581493 29266183329838792980710765)
        ·
          refine ⟨10974818748689547367766537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29266183329838792980710765 10974818748689547367766537)
          ·
            refine ⟨8231114061517160525824903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10974818748689547367766537 8231114061517160525824903)
            ·
              refine ⟨12346671092275740788737355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8231114061517160525824903 12346671092275740788737355)
              ·
                refine ⟨18520006638413611183106033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12346671092275740788737355 18520006638413611183106033)
                ·
                  refine ⟨13890004978810208387329525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18520006638413611183106033 13890004978810208387329525)
                  ·
                    refine ⟨1302187966763457036312143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13890004978810208387329525 1302187966763457036312143)
                    ·
                      rfl

theorem cell22_3804003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 5].length) (baseStart_3804003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804003 prefixEnd_3804003 := by exact prefixLift 3804003
  have htrace : WordTrace (prefixWord ++ tailWord_3804003) baseStart_3804003 baseEnd_3804003 := by
    simpa [prefixWord, tailWord_3804003, baseEnd_3804003] using wordTrace_append hprefix tailTrace_3804003
  have hstable : (prefixWord ++ tailWord_3804003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804003).length < 2 ^ (prefixWord ++ tailWord_3804003).sum := by decide
  have hdescent : baseEnd_3804003 < baseStart_3804003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804016 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 8]
def baseStart_3804016 : Nat := 118140960795 + 3804016 * 2 ^ 59
def prefixEnd_3804016 : Nat := 4983230072969 + 3 ^ 40 * 3804016 * 2
def baseEnd_3804016 : Nat := 434064138976376445245701

theorem tailTrace_3804016 : CollatzResearch.WordTrace tailWord_3804016 prefixEnd_3804016 434064138976376445245701 := by
  unfold tailWord_3804016
  simp only [CollatzResearch.WordTrace]
  refine ⟨69371930893353590527351951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92495907857804787369802601 69371930893353590527351951)
  ·
    refine ⟨104057896340030385791027927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69371930893353590527351951 104057896340030385791027927)
    ·
      refine ⟨156086844510045578686541891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104057896340030385791027927 156086844510045578686541891)
      ·
        refine ⟨234130266765068368029812837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156086844510045578686541891 234130266765068368029812837)
        ·
          refine ⟨43899425018450319005589907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234130266765068368029812837 43899425018450319005589907)
          ·
            refine ⟨65849137527675478508384861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43899425018450319005589907 65849137527675478508384861)
            ·
              refine ⟨24693426572878304440644323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65849137527675478508384861 24693426572878304440644323)
              ·
                refine ⟨37040139859317456660966485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24693426572878304440644323 37040139859317456660966485)
                ·
                  refine ⟨434064138976376445245701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37040139859317456660966485 434064138976376445245701)
                  ·
                    rfl

theorem cell22_3804016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 8].length) (baseStart_3804016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804016 prefixEnd_3804016 := by exact prefixLift 3804016
  have htrace : WordTrace (prefixWord ++ tailWord_3804016) baseStart_3804016 baseEnd_3804016 := by
    simpa [prefixWord, tailWord_3804016, baseEnd_3804016] using wordTrace_append hprefix tailTrace_3804016
  have hstable : (prefixWord ++ tailWord_3804016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804016).length < 2 ^ (prefixWord ++ tailWord_3804016).sum := by decide
  have hdescent : baseEnd_3804016 < baseStart_3804016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804018 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_3804018 : Nat := 118140960795 + 3804018 * 2 ^ 59
def prefixEnd_3804018 : Nat := 4983230072969 + 3 ^ 40 * 3804018 * 2
def baseEnd_3804018 : Nat := 1302193101570001997187097

theorem tailTrace_3804018 : CollatzResearch.WordTrace tailWord_3804018 prefixEnd_3804018 1302193101570001997187097 := by
  unfold tailWord_3804018
  simp only [CollatzResearch.WordTrace]
  refine ⟨34685983683174983849069177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92495956488466623597517805 34685983683174983849069177)
  ·
    refine ⟨26014487762381237886801883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34685983683174983849069177 26014487762381237886801883)
    ·
      refine ⟨39021731643571856830202825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26014487762381237886801883 39021731643571856830202825)
      ·
        refine ⟨29266298732678892622652119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39021731643571856830202825 29266298732678892622652119)
        ·
          refine ⟨43899448099018338933978179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29266298732678892622652119 43899448099018338933978179)
          ·
            refine ⟨65849172148527508400967269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43899448099018338933978179 65849172148527508400967269)
            ·
              refine ⟨12346719777848907825181363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65849172148527508400967269 12346719777848907825181363)
              ·
                refine ⟨18520079666773361737772045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12346719777848907825181363 18520079666773361737772045)
                ·
                  refine ⟨6945029875040010651664517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18520079666773361737772045 6945029875040010651664517)
                  ·
                    refine ⟨1302193101570001997187097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6945029875040010651664517 1302193101570001997187097)
                    ·
                      rfl

theorem cell22_3804018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_3804018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804018 prefixEnd_3804018 := by exact prefixLift 3804018
  have htrace : WordTrace (prefixWord ++ tailWord_3804018) baseStart_3804018 baseEnd_3804018 := by
    simpa [prefixWord, tailWord_3804018, baseEnd_3804018] using wordTrace_append hprefix tailTrace_3804018
  have hstable : (prefixWord ++ tailWord_3804018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804018).length < 2 ^ (prefixWord ++ tailWord_3804018).sum := by decide
  have hdescent : baseEnd_3804018 < baseStart_3804018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804063 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 1, 6]
def baseStart_3804063 : Nat := 118140960795 + 3804063 * 2 ^ 59
def prefixEnd_3804063 : Nat := 4983230072969 + 3 ^ 40 * 3804063 * 2
def baseEnd_3804063 : Nat := 1302208505989636879811959

theorem tailTrace_3804063 : CollatzResearch.WordTrace tailWord_3804063 prefixEnd_3804063 1302208505989636879811959 := by
  unfold tailWord_3804063
  simp only [CollatzResearch.WordTrace]
  refine ⟨138745576017536908081664843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92497050678357938721109895 138745576017536908081664843)
  ·
    refine ⟨208118364026305362122497265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138745576017536908081664843 208118364026305362122497265)
    ·
      refine ⟨156088773019729021591872949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208118364026305362122497265 156088773019729021591872949)
      ·
        refine ⟨14633322470599595774238089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156088773019729021591872949 14633322470599595774238089)
        ·
          refine ⟨10974991852949696830678567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14633322470599595774238089 10974991852949696830678567)
          ·
            refine ⟨16462487779424545246017851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10974991852949696830678567 16462487779424545246017851)
            ·
              refine ⟨24693731669136817869026777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16462487779424545246017851 24693731669136817869026777)
              ·
                refine ⟨18520298751852613401770083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24693731669136817869026777 18520298751852613401770083)
                ·
                  refine ⟨27780448127778920102655125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18520298751852613401770083 27780448127778920102655125)
                  ·
                    refine ⟨1302208505989636879811959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27780448127778920102655125 1302208505989636879811959)
                    ·
                      rfl

theorem cell22_3804063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_3804063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804063 prefixEnd_3804063 := by exact prefixLift 3804063
  have htrace : WordTrace (prefixWord ++ tailWord_3804063) baseStart_3804063 baseEnd_3804063 := by
    simpa [prefixWord, tailWord_3804063, baseEnd_3804063] using wordTrace_append hprefix tailTrace_3804063
  have hstable : (prefixWord ++ tailWord_3804063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804063).length < 2 ^ (prefixWord ++ tailWord_3804063).sum := by decide
  have hdescent : baseEnd_3804063 < baseStart_3804063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804065 : List Nat := [1, 2, 3, 4, 1, 1, 3, 1, 1, 5]
def baseStart_3804065 : Nat := 118140960795 + 3804065 * 2 ^ 59
def prefixEnd_3804065 : Nat := 4983230072969 + 3 ^ 40 * 3804065 * 2
def baseEnd_3804065 : Nat := 1302209190630509541261953

theorem tailTrace_3804065 : CollatzResearch.WordTrace tailWord_3804065 prefixEnd_3804065 1302209190630509541261953 := by
  unfold tailWord_3804065
  simp only [CollatzResearch.WordTrace]
  refine ⟨138745648963529662423237649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92497099309019774948825099 138745648963529662423237649)
  ·
    refine ⟨104059236722647246817428237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138745648963529662423237649 104059236722647246817428237)
    ·
      refine ⟨39022213770992717556535589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104059236722647246817428237 39022213770992717556535589)
      ·
        refine ⟨7316665082061134541850423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39022213770992717556535589 7316665082061134541850423)
        ·
          refine ⟨10974997623091701812775635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7316665082061134541850423 10974997623091701812775635)
          ·
            refine ⟨16462496434637552719163453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10974997623091701812775635 16462496434637552719163453)
            ·
              refine ⟨6173436162989082269686295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16462496434637552719163453 6173436162989082269686295)
              ·
                refine ⟨9260154244483623404529443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6173436162989082269686295 9260154244483623404529443)
                ·
                  refine ⟨13890231366725435106794165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9260154244483623404529443 13890231366725435106794165)
                  ·
                    refine ⟨1302209190630509541261953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13890231366725435106794165 1302209190630509541261953)
                    ·
                      rfl

theorem cell22_3804065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_3804065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804065 prefixEnd_3804065 := by exact prefixLift 3804065
  have htrace : WordTrace (prefixWord ++ tailWord_3804065) baseStart_3804065 baseEnd_3804065 := by
    simpa [prefixWord, tailWord_3804065, baseEnd_3804065] using wordTrace_append hprefix tailTrace_3804065
  have hstable : (prefixWord ++ tailWord_3804065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804065).length < 2 ^ (prefixWord ++ tailWord_3804065).sum := by decide
  have hdescent : baseEnd_3804065 < baseStart_3804065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804084 : List Nat := [2, 5, 2, 1, 1, 1, 3, 3, 4]
def baseStart_3804084 : Nat := 118140960795 + 3804084 * 2 ^ 59
def prefixEnd_3804084 : Nat := 4983230072969 + 3 ^ 40 * 3804084 * 2
def baseEnd_3804084 : Nat := 434071898239599941678965

theorem tailTrace_3804084 : CollatzResearch.WordTrace tailWord_3804084 prefixEnd_3804084 434071898239599941678965 := by
  unfold tailWord_3804084
  simp only [CollatzResearch.WordTrace]
  refine ⟨69373170975230414334089653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92497561300307219112119537 69373170975230414334089653)
  ·
    refine ⟨6503734778927851343820905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69373170975230414334089653 6503734778927851343820905)
    ·
      refine ⟨4877801084195888507865679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6503734778927851343820905 4877801084195888507865679)
      ·
        refine ⟨7316701626293832761798519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4877801084195888507865679 7316701626293832761798519)
        ·
          refine ⟨10975052439440749142697779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7316701626293832761798519 10975052439440749142697779)
          ·
            refine ⟨16462578659161123714046669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10975052439440749142697779 16462578659161123714046669)
            ·
              refine ⟨6173466997185421392767501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16462578659161123714046669 6173466997185421392767501)
              ·
                refine ⟨2315050123944533022287813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6173466997185421392767501 2315050123944533022287813)
                ·
                  refine ⟨434071898239599941678965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2315050123944533022287813 434071898239599941678965)
                  ·
                    rfl

theorem cell22_3804084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_3804084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804084 prefixEnd_3804084 := by exact prefixLift 3804084
  have htrace : WordTrace (prefixWord ++ tailWord_3804084) baseStart_3804084 baseEnd_3804084 := by
    simpa [prefixWord, tailWord_3804084, baseEnd_3804084] using wordTrace_append hprefix tailTrace_3804084
  have hstable : (prefixWord ++ tailWord_3804084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804084).length < 2 ^ (prefixWord ++ tailWord_3804084).sum := by decide
  have hdescent : baseEnd_3804084 < baseStart_3804084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804108 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 2, 6]
def baseStart_3804108 : Nat := 118140960795 + 3804108 * 2 ^ 59
def prefixEnd_3804108 : Nat := 4983230072969 + 3 ^ 40 * 3804108 * 2
def baseEnd_3804108 : Nat := 1302223910409271762436821

theorem tailTrace_3804108 : CollatzResearch.WordTrace tailWord_3804108 prefixEnd_3804108 1302223910409271762436821 := by
  unfold tailWord_3804108
  simp only [CollatzResearch.WordTrace]
  refine ⟨69373608651186940383526489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92498144868249253844701985 69373608651186940383526489)
  ·
    refine ⟨52030206488390205287644867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69373608651186940383526489 52030206488390205287644867)
    ·
      refine ⟨78045309732585307931467301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52030206488390205287644867 78045309732585307931467301)
      ·
        refine ⟨14633495574859745237150119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78045309732585307931467301 14633495574859745237150119)
        ·
          refine ⟨21950243362289617855725179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14633495574859745237150119 21950243362289617855725179)
          ·
            refine ⟨32925365043434426783587769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21950243362289617855725179 32925365043434426783587769)
            ·
              refine ⟨24694023782575820087690827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32925365043434426783587769 24694023782575820087690827)
              ·
                refine ⟨37041035673863730131536241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24694023782575820087690827 37041035673863730131536241)
                ·
                  refine ⟨27780776755397797598652181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37041035673863730131536241 27780776755397797598652181)
                  ·
                    refine ⟨1302223910409271762436821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27780776755397797598652181 1302223910409271762436821)
                    ·
                      rfl

theorem cell22_3804108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_3804108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804108 prefixEnd_3804108 := by exact prefixLift 3804108
  have htrace : WordTrace (prefixWord ++ tailWord_3804108) baseStart_3804108 baseEnd_3804108 := by
    simpa [prefixWord, tailWord_3804108, baseEnd_3804108] using wordTrace_append hprefix tailTrace_3804108
  have hstable : (prefixWord ++ tailWord_3804108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804108).length < 2 ^ (prefixWord ++ tailWord_3804108).sum := by decide
  have hdescent : baseEnd_3804108 < baseStart_3804108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804161 : List Nat := [1, 2, 4, 1, 2, 4, 2, 2, 1, 3]
def baseStart_3804161 : Nat := 118140960795 + 3804161 * 2 ^ 59
def prefixEnd_3804161 : Nat := 4983230072969 + 3 ^ 40 * 3804161 * 2
def baseEnd_3804161 : Nat := 1302242053392397290861659

theorem tailTrace_3804161 : CollatzResearch.WordTrace tailWord_3804161 prefixEnd_3804161 1302242053392397290861659 := by
  unfold tailWord_3804161
  simp only [CollatzResearch.WordTrace]
  refine ⟨138749150371181870818732337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92499433580787913879154891 138749150371181870818732337)
  ·
    refine ⟨104061862778386403114049253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138749150371181870818732337 104061862778386403114049253)
    ·
      refine ⟨19511599270947450583884235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104061862778386403114049253 19511599270947450583884235)
      ·
        refine ⟨29267398906421175875826353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19511599270947450583884235 29267398906421175875826353)
        ·
          refine ⟨21950549179815881906869765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29267398906421175875826353 21950549179815881906869765)
          ·
            refine ⟨4115727971215477857538081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21950549179815881906869765 4115727971215477857538081)
            ·
              refine ⟨3086795978411608393153561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4115727971215477857538081 3086795978411608393153561)
              ·
                refine ⟨2315096983808706294865171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3086795978411608393153561 2315096983808706294865171)
                ·
                  refine ⟨3472645475713059442297757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2315096983808706294865171 3472645475713059442297757)
                  ·
                    refine ⟨1302242053392397290861659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3472645475713059442297757 1302242053392397290861659)
                    ·
                      rfl

theorem cell22_3804161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_3804161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804161 prefixEnd_3804161 := by exact prefixLift 3804161
  have htrace : WordTrace (prefixWord ++ tailWord_3804161) baseStart_3804161 baseEnd_3804161 := by
    simpa [prefixWord, tailWord_3804161, baseEnd_3804161] using wordTrace_append hprefix tailTrace_3804161
  have hstable : (prefixWord ++ tailWord_3804161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804161).length < 2 ^ (prefixWord ++ tailWord_3804161).sum := by decide
  have hdescent : baseEnd_3804161 < baseStart_3804161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804170 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 3, 4]
def baseStart_3804170 : Nat := 118140960795 + 3804170 * 2 ^ 59
def prefixEnd_3804170 : Nat := 4983230072969 + 3 ^ 40 * 3804170 * 2
def baseEnd_3804170 : Nat := 1302245134276324267386631

theorem tailTrace_3804170 : CollatzResearch.WordTrace tailWord_3804170 prefixEnd_3804170 1302245134276324267386631 := by
  unfold tailWord_3804170
  simp only [CollatzResearch.WordTrace]
  refine ⟨34687369657037316338952491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92499652418766176903873309 34687369657037316338952491)
  ·
    refine ⟨52031054485555974508428737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34687369657037316338952491 52031054485555974508428737)
    ·
      refine ⟨39023290864166980881321553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52031054485555974508428737 39023290864166980881321553)
      ·
        refine ⟨29267468148125235660991165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39023290864166980881321553 29267468148125235660991165)
        ·
          refine ⟨10975300555546963372871687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29267468148125235660991165 10975300555546963372871687)
          ·
            refine ⟨16462950833320445059307531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10975300555546963372871687 16462950833320445059307531)
            ·
              refine ⟨24694426249980667588961297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16462950833320445059307531 24694426249980667588961297)
              ·
                refine ⟨18520819687485500691720973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24694426249980667588961297 18520819687485500691720973)
                ·
                  refine ⟨6945307382807062759395365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18520819687485500691720973 6945307382807062759395365)
                  ·
                    refine ⟨1302245134276324267386631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6945307382807062759395365 1302245134276324267386631)
                    ·
                      rfl

theorem cell22_3804170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_3804170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804170 prefixEnd_3804170 := by exact prefixLift 3804170
  have htrace : WordTrace (prefixWord ++ tailWord_3804170) baseStart_3804170 baseEnd_3804170 := by
    simpa [prefixWord, tailWord_3804170, baseEnd_3804170] using wordTrace_append hprefix tailTrace_3804170
  have hstable : (prefixWord ++ tailWord_3804170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804170).length < 2 ^ (prefixWord ++ tailWord_3804170).sum := by decide
  have hdescent : baseEnd_3804170 < baseStart_3804170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804217 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 4, 3]
def baseStart_3804217 : Nat := 118140960795 + 3804217 * 2 ^ 59
def prefixEnd_3804217 : Nat := 4983230072969 + 3 ^ 40 * 3804217 * 2
def baseEnd_3804217 : Nat := 1302261223336831811461487

theorem tailTrace_3804217 : CollatzResearch.WordTrace tailWord_3804217 prefixEnd_3804217 1302261223336831811461487 := by
  unfold tailWord_3804217
  simp only [CollatzResearch.WordTrace]
  refine ⟨138751192858978992382770905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92500795239319328255180603 138751192858978992382770905)
  ·
    refine ⟨104063394644234244287078179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138751192858978992382770905 104063394644234244287078179)
    ·
      refine ⟨156095091966351366430617269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104063394644234244287078179 156095091966351366430617269)
      ·
        refine ⟨14633914871845440602870369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156095091966351366430617269 14633914871845440602870369)
        ·
          refine ⟨10975436153884080452152777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14633914871845440602870369 10975436153884080452152777)
          ·
            refine ⟨8231577115413060339114583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10975436153884080452152777 8231577115413060339114583)
            ·
              refine ⟨12347365673119590508671875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8231577115413060339114583 12347365673119590508671875)
              ·
                refine ⟨18521048509679385763007813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12347365673119590508671875 18521048509679385763007813)
                ·
                  refine ⟨3472696595564884830563965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18521048509679385763007813 3472696595564884830563965)
                  ·
                    refine ⟨1302261223336831811461487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3472696595564884830563965 1302261223336831811461487)
                    ·
                      rfl

theorem cell22_3804217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 3].length) (baseStart_3804217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804217 prefixEnd_3804217 := by exact prefixLift 3804217
  have htrace : WordTrace (prefixWord ++ tailWord_3804217) baseStart_3804217 baseEnd_3804217 := by
    simpa [prefixWord, tailWord_3804217, baseEnd_3804217] using wordTrace_append hprefix tailTrace_3804217
  have hstable : (prefixWord ++ tailWord_3804217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804217).length < 2 ^ (prefixWord ++ tailWord_3804217).sum := by decide
  have hdescent : baseEnd_3804217 < baseStart_3804217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804243 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 4, 6]
def baseStart_3804243 : Nat := 118140960795 + 3804243 * 2 ^ 59
def prefixEnd_3804243 : Nat := 4983230072969 + 3 ^ 40 * 3804243 * 2
def baseEnd_3804243 : Nat := 1302270123668176410311407

theorem tailTrace_3804243 : CollatzResearch.WordTrace tailWord_3804243 prefixEnd_3804243 1302270123668176410311407 := by
  unfold tailWord_3804243
  simp only [CollatzResearch.WordTrace]
  refine ⟨138752141156884798823217383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92501427437923199215478255 138752141156884798823217383)
  ·
    refine ⟨208128211735327198234826075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138752141156884798823217383 208128211735327198234826075)
    ·
      refine ⟨312192317602990797352239113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208128211735327198234826075 312192317602990797352239113)
      ·
        refine ⟨234144238202243098014179335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312192317602990797352239113 234144238202243098014179335)
        ·
          refine ⟨351216357303364647021269003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234144238202243098014179335 351216357303364647021269003)
          ·
            refine ⟨526824535955046970531903505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351216357303364647021269003 526824535955046970531903505)
            ·
              refine ⟨395118401966285227898927629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526824535955046970531903505 395118401966285227898927629)
              ·
                refine ⟨148169400737356960462097861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395118401966285227898927629 148169400737356960462097861)
                ·
                  refine ⟨27781762638254430086643349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148169400737356960462097861 27781762638254430086643349)
                  ·
                    refine ⟨1302270123668176410311407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27781762638254430086643349 1302270123668176410311407)
                    ·
                      rfl

theorem cell22_3804243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 6].length) (baseStart_3804243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804243 prefixEnd_3804243 := by exact prefixLift 3804243
  have htrace : WordTrace (prefixWord ++ tailWord_3804243) baseStart_3804243 baseEnd_3804243 := by
    simpa [prefixWord, tailWord_3804243, baseEnd_3804243] using wordTrace_append hprefix tailTrace_3804243
  have hstable : (prefixWord ++ tailWord_3804243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804243).length < 2 ^ (prefixWord ++ tailWord_3804243).sum := by decide
  have hdescent : baseEnd_3804243 < baseStart_3804243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804253 : List Nat := [1, 4, 4, 1, 3, 1, 1, 3, 4]
def baseStart_3804253 : Nat := 118140960795 + 3804253 * 2 ^ 59
def prefixEnd_3804253 : Nat := 4983230072969 + 3 ^ 40 * 3804253 * 2
def baseEnd_3804253 : Nat := 434091182290846572520459

theorem tailTrace_3804253 : CollatzResearch.WordTrace tailWord_3804253 prefixEnd_3804253 434091182290846572520459 := by
  unfold tailWord_3804253
  simp only [CollatzResearch.WordTrace]
  refine ⟨138752505886848570531081413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92501670591232380354054275 138752505886848570531081413)
  ·
    refine ⟨26016094853784106974577765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138752505886848570531081413 26016094853784106974577765)
    ·
      refine ⟨4878017785084520057733331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26016094853784106974577765 4878017785084520057733331)
      ·
        refine ⟨7317026677626780086599997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4878017785084520057733331 7317026677626780086599997)
        ·
          refine ⟨2743885004110042532474999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7317026677626780086599997 2743885004110042532474999)
          ·
            refine ⟨4115827506165063798712499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743885004110042532474999 4115827506165063798712499)
            ·
              refine ⟨6173741259247595698068749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4115827506165063798712499 6173741259247595698068749)
              ·
                refine ⟨2315152972217848386775781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6173741259247595698068749 2315152972217848386775781)
                ·
                  refine ⟨434091182290846572520459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2315152972217848386775781 434091182290846572520459)
                  ·
                    rfl

theorem cell22_3804253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_3804253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804253 prefixEnd_3804253 := by exact prefixLift 3804253
  have htrace : WordTrace (prefixWord ++ tailWord_3804253) baseStart_3804253 baseEnd_3804253 := by
    simpa [prefixWord, tailWord_3804253, baseEnd_3804253] using wordTrace_append hprefix tailTrace_3804253
  have hstable : (prefixWord ++ tailWord_3804253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804253).length < 2 ^ (prefixWord ++ tailWord_3804253).sum := by decide
  have hdescent : baseEnd_3804253 < baseStart_3804253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804264 : List Nat := [2, 1, 4, 4, 2, 1, 8]
def baseStart_3804264 : Nat := 118140960795 + 3804264 * 2 ^ 59
def prefixEnd_3804264 : Nat := 4983230072969 + 3 ^ 40 * 3804264 * 2
def baseEnd_3804264 : Nat := 48232493051753309464309

theorem tailTrace_3804264 : CollatzResearch.WordTrace tailWord_3804264 prefixEnd_3804264 48232493051753309464309 := by
  unfold tailWord_3804264
  simp only [CollatzResearch.WordTrace]
  refine ⟨69376453544904359704865923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92501938059872479606487897 69376453544904359704865923)
  ·
    refine ⟨104064680317356539557298885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69376453544904359704865923 104064680317356539557298885)
    ·
      refine ⟨19512127559504351166993541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104064680317356539557298885 19512127559504351166993541)
      ·
        refine ⟨3658523917407065843811289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19512127559504351166993541 3658523917407065843811289)
        ·
          refine ⟨2743892938055299382858467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3658523917407065843811289 2743892938055299382858467)
          ·
            refine ⟨4115839407082949074287701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743892938055299382858467 4115839407082949074287701)
            ·
              refine ⟨48232493051753309464309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4115839407082949074287701 48232493051753309464309)
              ·
                rfl

theorem cell22_3804264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 8].length) (baseStart_3804264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804264 prefixEnd_3804264 := by exact prefixLift 3804264
  have htrace : WordTrace (prefixWord ++ tailWord_3804264) baseStart_3804264 baseEnd_3804264 := by
    simpa [prefixWord, tailWord_3804264, baseEnd_3804264] using wordTrace_append hprefix tailTrace_3804264
  have hstable : (prefixWord ++ tailWord_3804264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804264).length < 2 ^ (prefixWord ++ tailWord_3804264).sum := by decide
  have hdescent : baseEnd_3804264 < baseStart_3804264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804292 : List Nat := [2, 3, 2, 1, 2, 3, 1, 3, 5]
def baseStart_3804292 : Nat := 118140960795 + 3804292 * 2 ^ 59
def prefixEnd_3804292 : Nat := 4983230072969 + 3 ^ 40 * 3804292 * 2
def baseEnd_3804292 : Nat := 434095632456518871945419

theorem tailTrace_3804292 : CollatzResearch.WordTrace tailWord_3804292 prefixEnd_3804292 434095632456518871945419 := by
  unfold tailWord_3804292
  simp only [CollatzResearch.WordTrace]
  refine ⟨69376964166853640095875565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92502618889138186794500753 69376964166853640095875565)
  ·
    refine ⟨26016361562570115035953337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69376964166853640095875565 26016361562570115035953337)
    ·
      refine ⟨19512271171927586276965003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26016361562570115035953337 19512271171927586276965003)
      ·
        refine ⟨29268406757891379415447505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19512271171927586276965003 29268406757891379415447505)
        ·
          refine ⟨21951305068418534561585629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29268406757891379415447505 21951305068418534561585629)
          ·
            refine ⟨8231739400656950460594611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21951305068418534561585629 8231739400656950460594611)
            ·
              refine ⟨12347609100985425690891917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8231739400656950460594611 12347609100985425690891917)
              ·
                refine ⟨4630353412869534634084469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12347609100985425690891917 4630353412869534634084469)
                ·
                  refine ⟨434095632456518871945419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4630353412869534634084469 434095632456518871945419)
                  ·
                    rfl

theorem cell22_3804292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_3804292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804292 prefixEnd_3804292 := by exact prefixLift 3804292
  have htrace : WordTrace (prefixWord ++ tailWord_3804292) baseStart_3804292 baseEnd_3804292 := by
    simpa [prefixWord, tailWord_3804292, baseEnd_3804292] using wordTrace_append hprefix tailTrace_3804292
  have hstable : (prefixWord ++ tailWord_3804292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804292).length < 2 ^ (prefixWord ++ tailWord_3804292).sum := by decide
  have hdescent : baseEnd_3804292 < baseStart_3804292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804330 : List Nat := [3, 1, 5, 1, 1, 3, 2, 2, 1, 3]
def baseStart_3804330 : Nat := 118140960795 + 3804330 * 2 ^ 59
def prefixEnd_3804330 : Nat := 4983230072969 + 3 ^ 40 * 3804330 * 2
def baseEnd_3804330 : Nat := 1302299905546137183386141

theorem tailTrace_3804330 : CollatzResearch.WordTrace tailWord_3804330 prefixEnd_3804330 1302299905546137183386141 := by
  unfold tailWord_3804330
  simp only [CollatzResearch.WordTrace]
  refine ⟨34688828576892403170408611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92503542871713075121089629 34688828576892403170408611)
  ·
    refine ⟨52033242865338604755612917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34688828576892403170408611 52033242865338604755612917)
    ·
      refine ⟨4878116518625494195838711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52033242865338604755612917 4878116518625494195838711)
      ·
        refine ⟨7317174777938241293758067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4878116518625494195838711 7317174777938241293758067)
        ·
          refine ⟨10975762166907361940637101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7317174777938241293758067 10975762166907361940637101)
          ·
            refine ⟨4115910812590260727738913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10975762166907361940637101 4115910812590260727738913)
            ·
              refine ⟨3086933109442695545804185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4115910812590260727738913 3086933109442695545804185)
              ·
                refine ⟨2315199832082021659353139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3086933109442695545804185 2315199832082021659353139)
                ·
                  refine ⟨3472799748123032489029709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2315199832082021659353139 3472799748123032489029709)
                  ·
                    refine ⟨1302299905546137183386141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3472799748123032489029709 1302299905546137183386141)
                    ·
                      rfl

theorem cell22_3804330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_3804330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804330 prefixEnd_3804330 := by exact prefixLift 3804330
  have htrace : WordTrace (prefixWord ++ tailWord_3804330) baseStart_3804330 baseEnd_3804330 := by
    simpa [prefixWord, tailWord_3804330, baseEnd_3804330] using wordTrace_append hprefix tailTrace_3804330
  have hstable : (prefixWord ++ tailWord_3804330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804330).length < 2 ^ (prefixWord ++ tailWord_3804330).sum := by decide
  have hdescent : baseEnd_3804330 < baseStart_3804330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804448 : List Nat := [2, 1, 1, 5, 4, 1, 1, 1, 3, 3]
def baseStart_3804448 : Nat := 118140960795 + 3804448 * 2 ^ 59
def prefixEnd_3804448 : Nat := 4983230072969 + 3 ^ 40 * 3804448 * 2
def baseEnd_3804448 : Nat := 1302340299357624208935779

theorem tailTrace_3804448 : CollatzResearch.WordTrace tailWord_3804448 prefixEnd_3804448 1302340299357624208935779 := by
  unfold tailWord_3804448
  simp only [CollatzResearch.WordTrace]
  refine ⟨69379809060571059417214999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92506412080761412556286665 69379809060571059417214999)
  ·
    refine ⟨104069713590856589125822499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69379809060571059417214999 104069713590856589125822499)
    ·
      refine ⟨156104570386284883688733749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104069713590856589125822499 156104570386284883688733749)
      ·
        refine ⟨14634803473714207845818789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156104570386284883688733749 14634803473714207845818789)
        ·
          refine ⟨2744025651321413971091023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14634803473714207845818789 2744025651321413971091023)
          ·
            refine ⟨4116038476982120956636535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2744025651321413971091023 4116038476982120956636535)
            ·
              refine ⟨6174057715473181434954803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4116038476982120956636535 6174057715473181434954803)
              ·
                refine ⟨9261086573209772152432205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6174057715473181434954803 9261086573209772152432205)
                ·
                  refine ⟨3472907464953664557162077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9261086573209772152432205 3472907464953664557162077)
                  ·
                    refine ⟨1302340299357624208935779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3472907464953664557162077 1302340299357624208935779)
                    ·
                      rfl

theorem cell22_3804448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 3, 3].length) (baseStart_3804448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804448 prefixEnd_3804448 := by exact prefixLift 3804448
  have htrace : WordTrace (prefixWord ++ tailWord_3804448) baseStart_3804448 baseEnd_3804448 := by
    simpa [prefixWord, tailWord_3804448, baseEnd_3804448] using wordTrace_append hprefix tailTrace_3804448
  have hstable : (prefixWord ++ tailWord_3804448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804448).length < 2 ^ (prefixWord ++ tailWord_3804448).sum := by decide
  have hdescent : baseEnd_3804448 < baseStart_3804448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804461 : List Nat := [1, 5, 3, 1, 1, 2, 1, 3, 5]
def baseStart_3804461 : Nat := 118140960795 + 3804461 * 2 ^ 59
def prefixEnd_3804461 : Nat := 4983230072969 + 3 ^ 40 * 3804461 * 2
def baseEnd_3804461 : Nat := 434114916507765502786913

theorem tailTrace_3804461 : CollatzResearch.WordTrace tailWord_3804461 prefixEnd_3804461 434114916507765502786913 := by
  unfold tailWord_3804461
  simp only [CollatzResearch.WordTrace]
  refine ⟨138760092270095022054653237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92506728180063348036435491 138760092270095022054653237)
  ·
    refine ⟨13008758650321408317623741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138760092270095022054653237 13008758650321408317623741)
    ·
      refine ⟨4878284493870528119108903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13008758650321408317623741 4878284493870528119108903)
      ·
        refine ⟨7317426740805792178663355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4878284493870528119108903 7317426740805792178663355)
        ·
          refine ⟨10976140111208688267995033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7317426740805792178663355 10976140111208688267995033)
          ·
            refine ⟨8232105083406516200996275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10976140111208688267995033 8232105083406516200996275)
            ·
              refine ⟨12348157625109774301494413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8232105083406516200996275 12348157625109774301494413)
              ·
                refine ⟨4630559109416165363060405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12348157625109774301494413 4630559109416165363060405)
                ·
                  refine ⟨434114916507765502786913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4630559109416165363060405 434114916507765502786913)
                  ·
                    rfl

theorem cell22_3804461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_3804461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804461 prefixEnd_3804461 := by exact prefixLift 3804461
  have htrace : WordTrace (prefixWord ++ tailWord_3804461) baseStart_3804461 baseEnd_3804461 := by
    simpa [prefixWord, tailWord_3804461, baseEnd_3804461] using wordTrace_append hprefix tailTrace_3804461
  have hstable : (prefixWord ++ tailWord_3804461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804461).length < 2 ^ (prefixWord ++ tailWord_3804461).sum := by decide
  have hdescent : baseEnd_3804461 < baseStart_3804461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804487 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 3, 5]
def baseStart_3804487 : Nat := 118140960795 + 3804487 * 2 ^ 59
def prefixEnd_3804487 : Nat := 4983230072969 + 3 ^ 40 * 3804487 * 2
def baseEnd_3804487 : Nat := 1302353649854641107210659

theorem tailTrace_3804487 : CollatzResearch.WordTrace tailWord_3804487 prefixEnd_3804487 1302353649854641107210659 := by
  unfold tailWord_3804487
  simp only [CollatzResearch.WordTrace]
  refine ⟨138761040568000828495099715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92507360378667218996733143 138761040568000828495099715)
  ·
    refine ⟨208141560852001242742649573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138761040568000828495099715 208141560852001242742649573)
    ·
      refine ⟨39026542659750233014246795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208141560852001242742649573 39026542659750233014246795)
      ·
        refine ⟨58539813989625349521370193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39026542659750233014246795 58539813989625349521370193)
        ·
          refine ⟨43904860492219012141027645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58539813989625349521370193 43904860492219012141027645)
          ·
            refine ⟨16464322684582129552885367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43904860492219012141027645 16464322684582129552885367)
            ·
              refine ⟨24696484026873194329328051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16464322684582129552885367 24696484026873194329328051)
              ·
                refine ⟨37044726040309791493992077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24696484026873194329328051 37044726040309791493992077)
                ·
                  refine ⟨13891772265116171810247029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37044726040309791493992077 13891772265116171810247029)
                  ·
                    refine ⟨1302353649854641107210659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13891772265116171810247029 1302353649854641107210659)
                    ·
                      rfl

theorem cell22_3804487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_3804487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804487 prefixEnd_3804487 := by exact prefixLift 3804487
  have htrace : WordTrace (prefixWord ++ tailWord_3804487) baseStart_3804487 baseEnd_3804487 := by
    simpa [prefixWord, tailWord_3804487, baseEnd_3804487] using wordTrace_append hprefix tailTrace_3804487
  have hstable : (prefixWord ++ tailWord_3804487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804487).length < 2 ^ (prefixWord ++ tailWord_3804487).sum := by decide
  have hdescent : baseEnd_3804487 < baseStart_3804487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804506 : List Nat := [3, 1, 1, 2, 1, 2, 6, 2, 4]
def baseStart_3804506 : Nat := 118140960795 + 3804506 * 2 ^ 59
def prefixEnd_3804506 : Nat := 4983230072969 + 3 ^ 40 * 3804506 * 2
def baseEnd_3804506 : Nat := 434120051314310463661867

theorem tailTrace_3804506 : CollatzResearch.WordTrace tailWord_3804506 prefixEnd_3804506 434120051314310463661867 := by
  unfold tailWord_3804506
  simp only [CollatzResearch.WordTrace]
  refine ⟨34690433388732998685010343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92507822369954663160027581 34690433388732998685010343)
  ·
    refine ⟨52035650083099498027515515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34690433388732998685010343 52035650083099498027515515)
    ·
      refine ⟨78053475124649247041273273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52035650083099498027515515 78053475124649247041273273)
      ·
        refine ⟨58540106343486935280954955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78053475124649247041273273 58540106343486935280954955)
        ·
          refine ⟨87810159515230402921432433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58540106343486935280954955 87810159515230402921432433)
          ·
            refine ⟨65857619636422802191074325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87810159515230402921432433 65857619636422802191074325)
            ·
              refine ⟨3087075920457318852706609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65857619636422802191074325 3087075920457318852706609)
              ·
                refine ⟨2315306940342989139529957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3087075920457318852706609 2315306940342989139529957)
                ·
                  refine ⟨434120051314310463661867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2315306940342989139529957 434120051314310463661867)
                  ·
                    rfl

theorem cell22_3804506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 4].length) (baseStart_3804506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804506 prefixEnd_3804506 := by exact prefixLift 3804506
  have htrace : WordTrace (prefixWord ++ tailWord_3804506) baseStart_3804506 baseEnd_3804506 := by
    simpa [prefixWord, tailWord_3804506, baseEnd_3804506] using wordTrace_append hprefix tailTrace_3804506
  have hstable : (prefixWord ++ tailWord_3804506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804506).length < 2 ^ (prefixWord ++ tailWord_3804506).sum := by decide
  have hdescent : baseEnd_3804506 < baseStart_3804506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804542 : List Nat := [4, 2, 3, 2, 1, 2, 2, 1, 1, 4]
def baseStart_3804542 : Nat := 118140960795 + 3804542 * 2 ^ 59
def prefixEnd_3804542 : Nat := 4983230072969 + 3 ^ 40 * 3804542 * 2
def baseEnd_3804542 : Nat := 1302372477478639297085491

theorem tailTrace_3804542 : CollatzResearch.WordTrace tailWord_3804542 prefixEnd_3804542 1302372477478639297085491 := by
  unfold tailWord_3804542
  simp only [CollatzResearch.WordTrace]
  refine ⟨17345380822850196611043985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92508697721867715258901253 17345380822850196611043985)
  ·
    refine ⟨13009035617137647458282989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17345380822850196611043985 13009035617137647458282989)
    ·
      refine ⟨4878388356426617796856121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13009035617137647458282989 4878388356426617796856121)
      ·
        refine ⟨3658791267319963347642091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4878388356426617796856121 3658791267319963347642091)
        ·
          refine ⟨5488186900979945021463137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3658791267319963347642091 5488186900979945021463137)
          ·
            refine ⟨4116140175734958766097353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5488186900979945021463137 4116140175734958766097353)
            ·
              refine ⟨3087105131801219074573015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4116140175734958766097353 3087105131801219074573015)
              ·
                refine ⟨4630657697701828611859523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3087105131801219074573015 4630657697701828611859523)
                ·
                  refine ⟨6945986546552742917789285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4630657697701828611859523 6945986546552742917789285)
                  ·
                    refine ⟨1302372477478639297085491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6945986546552742917789285 1302372477478639297085491)
                    ·
                      rfl

theorem cell22_3804542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_3804542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804542 prefixEnd_3804542 := by exact prefixLift 3804542
  have htrace : WordTrace (prefixWord ++ tailWord_3804542) baseStart_3804542 baseEnd_3804542 := by
    simpa [prefixWord, tailWord_3804542, baseEnd_3804542] using wordTrace_append hprefix tailTrace_3804542
  have hstable : (prefixWord ++ tailWord_3804542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804542).length < 2 ^ (prefixWord ++ tailWord_3804542).sum := by decide
  have hdescent : baseEnd_3804542 < baseStart_3804542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804607 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 8]
def baseStart_3804607 : Nat := 118140960795 + 3804607 * 2 ^ 59
def prefixEnd_3804607 : Nat := 4983230072969 + 3 ^ 40 * 3804607 * 2
def baseEnd_3804607 : Nat := 434131576102333598070097

theorem tailTrace_3804607 : CollatzResearch.WordTrace tailWord_3804607 prefixEnd_3804607 434131576102333598070097 := by
  unfold tailWord_3804607
  simp only [CollatzResearch.WordTrace]
  refine ⟨138765417327566088989468075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92510278218377392659645383 138765417327566088989468075)
  ·
    refine ⟨208148125991349133484202113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138765417327566088989468075 208148125991349133484202113)
    ·
      refine ⟨156111094493511850113151585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208148125991349133484202113 156111094493511850113151585)
      ·
        refine ⟨117083320870133887584863689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156111094493511850113151585 117083320870133887584863689)
        ·
          refine ⟨87812490652600415688647767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117083320870133887584863689 87812490652600415688647767)
          ·
            refine ⟨131718735978900623532971651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87812490652600415688647767 131718735978900623532971651)
            ·
              refine ⟨197578103968350935299457477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131718735978900623532971651 197578103968350935299457477)
              ·
                refine ⟨37045894494065800368648277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197578103968350935299457477 37045894494065800368648277)
                ·
                  refine ⟨434131576102333598070097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37045894494065800368648277 434131576102333598070097)
                  ·
                    rfl

theorem cell22_3804607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 8].length) (baseStart_3804607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804607 prefixEnd_3804607 := by exact prefixLift 3804607
  have htrace : WordTrace (prefixWord ++ tailWord_3804607) baseStart_3804607 baseEnd_3804607 := by
    simpa [prefixWord, tailWord_3804607, baseEnd_3804607] using wordTrace_append hprefix tailTrace_3804607
  have hstable : (prefixWord ++ tailWord_3804607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804607).length < 2 ^ (prefixWord ++ tailWord_3804607).sum := by decide
  have hdescent : baseEnd_3804607 < baseStart_3804607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804630 : List Nat := [5, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_3804630 : Nat := 118140960795 + 3804630 * 2 ^ 59
def prefixEnd_3804630 : Nat := 4983230072969 + 3 ^ 40 * 3804630 * 2
def baseEnd_3804630 : Nat := 434134200559012133628407

theorem tailTrace_3804630 : CollatzResearch.WordTrace tailWord_3804630 prefixEnd_3804630 434134200559012133628407 := by
  unfold tailWord_3804630
  simp only [CollatzResearch.WordTrace]
  refine ⟨8672891012905172744847209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92510837470988509278370229 8672891012905172744847209)
  ·
    refine ⟨6504668259678879558635407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8672891012905172744847209 6504668259678879558635407)
    ·
      refine ⟨9757002389518319337953111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6504668259678879558635407 9757002389518319337953111)
      ·
        refine ⟨14635503584277479006929667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9757002389518319337953111 14635503584277479006929667)
        ·
          refine ⟨21953255376416218510394501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14635503584277479006929667 21953255376416218510394501)
          ·
            refine ⟨4116235383078040970698969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21953255376416218510394501 4116235383078040970698969)
            ·
              refine ⟨3087176537308530728024227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4116235383078040970698969 3087176537308530728024227)
              ·
                refine ⟨4630764805962796092036341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3087176537308530728024227 4630764805962796092036341)
                ·
                  refine ⟨434134200559012133628407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4630764805962796092036341 434134200559012133628407)
                  ·
                    rfl

theorem cell22_3804630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_3804630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804630 prefixEnd_3804630 := by exact prefixLift 3804630
  have htrace : WordTrace (prefixWord ++ tailWord_3804630) baseStart_3804630 baseEnd_3804630 := by
    simpa [prefixWord, tailWord_3804630, baseEnd_3804630] using wordTrace_append hprefix tailTrace_3804630
  have hstable : (prefixWord ++ tailWord_3804630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804630).length < 2 ^ (prefixWord ++ tailWord_3804630).sum := by decide
  have hdescent : baseEnd_3804630 < baseStart_3804630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804639 : List Nat := [1, 1, 2, 3, 3, 1, 2, 3, 1, 5]
def baseStart_3804639 : Nat := 118140960795 + 3804639 * 2 ^ 59
def prefixEnd_3804639 : Nat := 4983230072969 + 3 ^ 40 * 3804639 * 2
def baseEnd_3804639 : Nat := 1302405682560963377410193

theorem tailTrace_3804639 : CollatzResearch.WordTrace tailWord_3804639 prefixEnd_3804639 1302405682560963377410193 := by
  unfold tailWord_3804639
  simp only [CollatzResearch.WordTrace]
  refine ⟨138766584463450158454632971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92511056308966772303088647 138766584463450158454632971)
  ·
    refine ⟨208149876695175237681949457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138766584463450158454632971 208149876695175237681949457)
    ·
      refine ⟨156112407521381428261462093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208149876695175237681949457 156112407521381428261462093)
      ·
        refine ⟨58542152820518035598048285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156112407521381428261462093 58542152820518035598048285)
        ·
          refine ⟨21953307307694263349268107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58542152820518035598048285 21953307307694263349268107)
          ·
            refine ⟨32929960961541395023902161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21953307307694263349268107 32929960961541395023902161)
            ·
              refine ⟨24697470721156046267926621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32929960961541395023902161 24697470721156046267926621)
              ·
                refine ⟨9261551520433517350472483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24697470721156046267926621 9261551520433517350472483)
                ·
                  refine ⟨13892327280650276025708725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9261551520433517350472483 13892327280650276025708725)
                  ·
                    refine ⟨1302405682560963377410193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13892327280650276025708725 1302405682560963377410193)
                    ·
                      rfl

theorem cell22_3804639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 5].length) (baseStart_3804639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804639 prefixEnd_3804639 := by exact prefixLift 3804639
  have htrace : WordTrace (prefixWord ++ tailWord_3804639) baseStart_3804639 baseEnd_3804639 := by
    simpa [prefixWord, tailWord_3804639, baseEnd_3804639] using wordTrace_append hprefix tailTrace_3804639
  have hstable : (prefixWord ++ tailWord_3804639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804639).length < 2 ^ (prefixWord ++ tailWord_3804639).sum := by decide
  have hdescent : baseEnd_3804639 < baseStart_3804639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804643 : List Nat := [1, 1, 1, 6, 2, 3, 1, 2, 1, 4]
def baseStart_3804643 : Nat := 118140960795 + 3804643 * 2 ^ 59
def prefixEnd_3804643 : Nat := 4983230072969 + 3 ^ 40 * 3804643 * 2
def baseEnd_3804643 : Nat := 1302407051842708700310181

theorem tailTrace_3804643 : CollatzResearch.WordTrace tailWord_3804643 prefixEnd_3804643 1302407051842708700310181 := by
  unfold tailWord_3804643
  simp only [CollatzResearch.WordTrace]
  refine ⟨138766730355435667137778583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92511153570290444758519055 138766730355435667137778583)
  ·
    refine ⟨208150095533153500706667875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138766730355435667137778583 208150095533153500706667875)
    ·
      refine ⟨312225143299730251060001813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208150095533153500706667875 312225143299730251060001813)
      ·
        refine ⟨14635553592174855518437585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 312225143299730251060001813 14635553592174855518437585)
        ·
          refine ⟨10976665194131141638828189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14635553592174855518437585 10976665194131141638828189)
          ·
            refine ⟨4116249447799178114560571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10976665194131141638828189 4116249447799178114560571)
            ·
              refine ⟨6174374171698767171840857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4116249447799178114560571 6174374171698767171840857)
              ·
                refine ⟨4630780628774075378880643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6174374171698767171840857 4630780628774075378880643)
                ·
                  refine ⟨6946170943161113068320965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4630780628774075378880643 6946170943161113068320965)
                  ·
                    refine ⟨1302407051842708700310181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6946170943161113068320965 1302407051842708700310181)
                    ·
                      rfl

theorem cell22_3804643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 4].length) (baseStart_3804643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804643 prefixEnd_3804643 := by exact prefixLift 3804643
  have htrace : WordTrace (prefixWord ++ tailWord_3804643) baseStart_3804643 baseEnd_3804643 := by
    simpa [prefixWord, tailWord_3804643, baseEnd_3804643] using wordTrace_append hprefix tailTrace_3804643
  have hstable : (prefixWord ++ tailWord_3804643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804643).length < 2 ^ (prefixWord ++ tailWord_3804643).sum := by decide
  have hdescent : baseEnd_3804643 < baseStart_3804643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804748 : List Nat := [2, 2, 1, 3, 1, 4, 3, 1, 5]
def baseStart_3804748 : Nat := 118140960795 + 3804748 * 2 ^ 59
def prefixEnd_3804748 : Nat := 4983230072969 + 3 ^ 40 * 3804748 * 2
def baseEnd_3804748 : Nat := 434147665162841142144953

theorem tailTrace_3804748 : CollatzResearch.WordTrace tailWord_3804748 prefixEnd_3804748 434147665162841142144953 := by
  unfold tailWord_3804748
  simp only [CollatzResearch.WordTrace]
  refine ⟨69385280010027635035175449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92513706680036846713567265 69385280010027635035175449)
  ·
    refine ⟨52038960007520726276381587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69385280010027635035175449 52038960007520726276381587)
    ·
      refine ⟨78058440011281089414572381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52038960007520726276381587 78058440011281089414572381)
      ·
        refine ⟨29271915004230408530464643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78058440011281089414572381 29271915004230408530464643)
        ·
          refine ⟨43907872506345612795696965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29271915004230408530464643 43907872506345612795696965)
          ·
            refine ⟨8232726094939802399193181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43907872506345612795696965 8232726094939802399193181)
            ·
              refine ⟨3087272285602425899697443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8232726094939802399193181 3087272285602425899697443)
              ·
                refine ⟨4630908428403638849546165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3087272285602425899697443 4630908428403638849546165)
                ·
                  refine ⟨434147665162841142144953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4630908428403638849546165 434147665162841142144953)
                  ·
                    rfl

theorem cell22_3804748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 5].length) (baseStart_3804748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804748 prefixEnd_3804748 := by exact prefixLift 3804748
  have htrace : WordTrace (prefixWord ++ tailWord_3804748) baseStart_3804748 baseEnd_3804748 := by
    simpa [prefixWord, tailWord_3804748, baseEnd_3804748] using wordTrace_append hprefix tailTrace_3804748
  have hstable : (prefixWord ++ tailWord_3804748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804748).length < 2 ^ (prefixWord ++ tailWord_3804748).sum := by decide
  have hdescent : baseEnd_3804748 < baseStart_3804748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804778 : List Nat := [3, 1, 3, 2, 1, 2, 2, 3, 1, 4]
def baseStart_3804778 : Nat := 118140960795 + 3804778 * 2 ^ 59
def prefixEnd_3804778 : Nat := 4983230072969 + 3 ^ 40 * 3804778 * 2
def baseEnd_3804778 : Nat := 1302453265101613348184767

theorem tailTrace_3804778 : CollatzResearch.WordTrace tailWord_3804778 prefixEnd_3804778 1302453265101613348184767 := by
  unfold tailWord_3804778
  simp only [CollatzResearch.WordTrace]
  refine ⟨34692913552486646298485747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92514436139964390129295325 34692913552486646298485747)
  ·
    refine ⟨52039370328729969447728621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34692913552486646298485747 52039370328729969447728621)
    ·
      refine ⟨19514763873273738542898233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52039370328729969447728621 19514763873273738542898233)
      ·
        refine ⟨14636072904955303907173675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19514763873273738542898233 14636072904955303907173675)
        ·
          refine ⟨21954109357432955860760513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14636072904955303907173675 21954109357432955860760513)
          ·
            refine ⟨16465582018074716895570385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21954109357432955860760513 16465582018074716895570385)
            ·
              refine ⟨12349186513556037671677789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16465582018074716895570385 12349186513556037671677789)
              ·
                refine ⟨4630944942583514126879171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12349186513556037671677789 4630944942583514126879171)
                ·
                  refine ⟨6946417413875271190318757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4630944942583514126879171 6946417413875271190318757)
                  ·
                    refine ⟨1302453265101613348184767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6946417413875271190318757 1302453265101613348184767)
                    ·
                      rfl

theorem cell22_3804778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_3804778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804778 prefixEnd_3804778 := by exact prefixLift 3804778
  have htrace : WordTrace (prefixWord ++ tailWord_3804778) baseStart_3804778 baseEnd_3804778 := by
    simpa [prefixWord, tailWord_3804778, baseEnd_3804778] using wordTrace_append hprefix tailTrace_3804778
  have hstable : (prefixWord ++ tailWord_3804778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804778).length < 2 ^ (prefixWord ++ tailWord_3804778).sum := by decide
  have hdescent : baseEnd_3804778 < baseStart_3804778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804823 : List Nat := [1, 1, 3, 3, 2, 3, 2, 1, 2, 4]
def baseStart_3804823 : Nat := 118140960795 + 3804823 * 2 ^ 59
def prefixEnd_3804823 : Nat := 4983230072969 + 3 ^ 40 * 3804823 * 2
def baseEnd_3804823 : Nat := 1302468669521248230809629

theorem tailTrace_3804823 : CollatzResearch.WordTrace tailWord_3804823 prefixEnd_3804823 1302468669521248230809629 := by
  unfold tailWord_3804823
  simp only [CollatzResearch.WordTrace]
  refine ⟨138773295494783557879331123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92515530329855705252887415 138773295494783557879331123)
  ·
    refine ⟨208159943242175336818996685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138773295494783557879331123 208159943242175336818996685)
    ·
      refine ⟨78059978715815751307123757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208159943242175336818996685 78059978715815751307123757)
      ·
        refine ⟨29272492018430906740171409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78059978715815751307123757 29272492018430906740171409)
        ·
          refine ⟨21954369013823180055128557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29272492018430906740171409 21954369013823180055128557)
          ·
            refine ⟨8232888380183692520673209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21954369013823180055128557 8232888380183692520673209)
            ·
              refine ⟨6174666285137769390504907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8232888380183692520673209 6174666285137769390504907)
              ·
                refine ⟨9261999427706654085757361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6174666285137769390504907 9261999427706654085757361)
                ·
                  refine ⟨6946499570779990564318021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9261999427706654085757361 6946499570779990564318021)
                  ·
                    refine ⟨1302468669521248230809629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6946499570779990564318021 1302468669521248230809629)
                    ·
                      rfl

theorem cell22_3804823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_3804823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804823 prefixEnd_3804823 := by exact prefixLift 3804823
  have htrace : WordTrace (prefixWord ++ tailWord_3804823) baseStart_3804823 baseEnd_3804823 := by
    simpa [prefixWord, tailWord_3804823, baseEnd_3804823] using wordTrace_append hprefix tailTrace_3804823
  have hstable : (prefixWord ++ tailWord_3804823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804823).length < 2 ^ (prefixWord ++ tailWord_3804823).sum := by decide
  have hdescent : baseEnd_3804823 < baseStart_3804823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804960 : List Nat := [2, 1, 1, 5, 1, 1, 2, 4, 2, 3]
def baseStart_3804960 : Nat := 118140960795 + 3804960 * 2 ^ 59
def prefixEnd_3804960 : Nat := 4983230072969 + 3 ^ 40 * 3804960 * 2
def baseEnd_3804960 : Nat := 1302515567421025540134209

theorem tailTrace_3804960 : CollatzResearch.WordTrace tailWord_3804960 prefixEnd_3804960 1302515567421025540134209 := by
  unfold tailWord_3804960
  simp only [CollatzResearch.WordTrace]
  refine ⟨69389146147643615138534167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92518861530191486851378889 69389146147643615138534167)
  ·
    refine ⟨104083719221465422707801251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69389146147643615138534167 104083719221465422707801251)
    ·
      refine ⟨156125578832198134061701877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104083719221465422707801251 156125578832198134061701877)
      ·
        refine ⟨14636773015518575068284551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156125578832198134061701877 14636773015518575068284551)
        ·
          refine ⟨21955159523277862602426827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14636773015518575068284551 21955159523277862602426827)
          ·
            refine ⟨32932739284916793903640241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21955159523277862602426827 32932739284916793903640241)
            ·
              refine ⟨24699554463687595427730181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32932739284916793903640241 24699554463687595427730181)
              ·
                refine ⟨4631166461941424142699409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24699554463687595427730181 4631166461941424142699409)
                ·
                  refine ⟨3473374846456068107024557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4631166461941424142699409 3473374846456068107024557)
                  ·
                    refine ⟨1302515567421025540134209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3473374846456068107024557 1302515567421025540134209)
                    ·
                      rfl

theorem cell22_3804960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 2, 3].length) (baseStart_3804960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804960 prefixEnd_3804960 := by exact prefixLift 3804960
  have htrace : WordTrace (prefixWord ++ tailWord_3804960) baseStart_3804960 baseEnd_3804960 := by
    simpa [prefixWord, tailWord_3804960, baseEnd_3804960] using wordTrace_append hprefix tailTrace_3804960
  have hstable : (prefixWord ++ tailWord_3804960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804960).length < 2 ^ (prefixWord ++ tailWord_3804960).sum := by decide
  have hdescent : baseEnd_3804960 < baseStart_3804960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804962 : List Nat := [3, 3, 1, 1, 2, 1, 5, 2, 4]
def baseStart_3804962 : Nat := 118140960795 + 3804962 * 2 ^ 59
def prefixEnd_3804962 : Nat := 4983230072969 + 3 ^ 40 * 3804962 * 2
def baseEnd_3804962 : Nat := 434172084020632733861401

theorem tailTrace_3804962 : CollatzResearch.WordTrace tailWord_3804962 prefixEnd_3804962 434172084020632733861401 := by
  unfold tailWord_3804962
  simp only [CollatzResearch.WordTrace]
  refine ⟨34694591310319996154660285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92518910160853323079094093 34694591310319996154660285)
  ·
    refine ⟨13010471741369998557997607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34694591310319996154660285 13010471741369998557997607)
    ·
      refine ⟨19515707612054997836996411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13010471741369998557997607 19515707612054997836996411)
      ·
        refine ⟨29273561418082496755494617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19515707612054997836996411 29273561418082496755494617)
        ·
          refine ⟨21955171063561872566620963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29273561418082496755494617 21955171063561872566620963)
          ·
            refine ⟨32932756595342808849931445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21955171063561872566620963 32932756595342808849931445)
            ·
              refine ⟨3087445930813388329681073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32932756595342808849931445 3087445930813388329681073)
              ·
                refine ⟨2315584448110041247260805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3087445930813388329681073 2315584448110041247260805)
                ·
                  refine ⟨434172084020632733861401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2315584448110041247260805 434172084020632733861401)
                  ·
                    rfl

theorem cell22_3804962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_3804962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804962 prefixEnd_3804962 := by exact prefixLift 3804962
  have htrace : WordTrace (prefixWord ++ tailWord_3804962) baseStart_3804962 baseEnd_3804962 := by
    simpa [prefixWord, tailWord_3804962, baseEnd_3804962] using wordTrace_append hprefix tailTrace_3804962
  have hstable : (prefixWord ++ tailWord_3804962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804962).length < 2 ^ (prefixWord ++ tailWord_3804962).sum := by decide
  have hdescent : baseEnd_3804962 < baseStart_3804962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3804977 : List Nat := [1, 2, 2, 3, 2, 2, 4, 1, 2, 3]
def baseStart_3804977 : Nat := 118140960795 + 3804977 * 2 ^ 59
def prefixEnd_3804977 : Nat := 4983230072969 + 3 ^ 40 * 3804977 * 2
def baseEnd_3804977 : Nat := 1302521386868443162459157

theorem tailTrace_3804977 : CollatzResearch.WordTrace tailWord_3804977 prefixEnd_3804977 1302521386868443162459157 := by
  unfold tailWord_3804977
  simp only [CollatzResearch.WordTrace]
  refine ⟨138778912336225642180437185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92519274890817094786958123 138778912336225642180437185)
  ·
    refine ⟨104084184252169231635327889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138778912336225642180437185 104084184252169231635327889)
    ·
      refine ⟨78063138189126923726495917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104084184252169231635327889 78063138189126923726495917)
      ·
        refine ⟨29273676820922596397435969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78063138189126923726495917 29273676820922596397435969)
        ·
          refine ⟨21955257615691947298076977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29273676820922596397435969 21955257615691947298076977)
          ·
            refine ⟨16466443211768960473557733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21955257615691947298076977 16466443211768960473557733)
            ·
              refine ⟨3087458102206680088792075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16466443211768960473557733 3087458102206680088792075)
              ·
                refine ⟨4631187153310020133188113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3087458102206680088792075 4631187153310020133188113)
                ·
                  refine ⟨3473390364982515099891085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4631187153310020133188113 3473390364982515099891085)
                  ·
                    refine ⟨1302521386868443162459157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3473390364982515099891085 1302521386868443162459157)
                    ·
                      rfl

theorem cell22_3804977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 2, 3].length) (baseStart_3804977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3804977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3804977 prefixEnd_3804977 := by exact prefixLift 3804977
  have htrace : WordTrace (prefixWord ++ tailWord_3804977) baseStart_3804977 baseEnd_3804977 := by
    simpa [prefixWord, tailWord_3804977, baseEnd_3804977] using wordTrace_append hprefix tailTrace_3804977
  have hstable : (prefixWord ++ tailWord_3804977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3804977).length < 2 ^ (prefixWord ++ tailWord_3804977).sum := by decide
  have hdescent : baseEnd_3804977 < baseStart_3804977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3804977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805065 : List Nat := [1, 2, 1, 1, 5, 1, 3, 3, 1, 4]
def baseStart_3805065 : Nat := 118140960795 + 3805065 * 2 ^ 59
def prefixEnd_3805065 : Nat := 4983230072969 + 3 ^ 40 * 3805065 * 2
def baseEnd_3805065 : Nat := 1302551511066840266258887

theorem tailTrace_3805065 : CollatzResearch.WordTrace tailWord_3805065 prefixEnd_3805065 1302551511066840266258887 := by
  unfold tailWord_3805065
  simp only [CollatzResearch.WordTrace]
  refine ⟨138782121959906833209640649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92521414639937888806427099 138782121959906833209640649)
  ·
    refine ⟨104086591469930124907230487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138782121959906833209640649 104086591469930124907230487)
    ·
      refine ⟨156129887204895187360845731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104086591469930124907230487 156129887204895187360845731)
      ·
        refine ⟨234194830807342781041268597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156129887204895187360845731 234194830807342781041268597)
        ·
          refine ⟨21955765388188385722618931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 234194830807342781041268597 21955765388188385722618931)
          ·
            refine ⟨32933648082282578583928397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21955765388188385722618931 32933648082282578583928397)
            ·
              refine ⟨12350118030855966968973149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32933648082282578583928397 12350118030855966968973149)
              ·
                refine ⟨4631294261570987613364931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12350118030855966968973149 4631294261570987613364931)
                ·
                  refine ⟨6946941392356481420047397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4631294261570987613364931 6946941392356481420047397)
                  ·
                    refine ⟨1302551511066840266258887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6946941392356481420047397 1302551511066840266258887)
                    ·
                      rfl

theorem cell22_3805065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 4].length) (baseStart_3805065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805065 prefixEnd_3805065 := by exact prefixLift 3805065
  have htrace : WordTrace (prefixWord ++ tailWord_3805065) baseStart_3805065 baseEnd_3805065 := by
    simpa [prefixWord, tailWord_3805065, baseEnd_3805065] using wordTrace_append hprefix tailTrace_3805065
  have hstable : (prefixWord ++ tailWord_3805065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805065).length < 2 ^ (prefixWord ++ tailWord_3805065).sum := by decide
  have hdescent : baseEnd_3805065 < baseStart_3805065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805086 : List Nat := [4, 3, 1, 3, 1, 1, 3, 1, 5]
def baseStart_3805086 : Nat := 118140960795 + 3805086 * 2 ^ 59
def prefixEnd_3805086 : Nat := 4983230072969 + 3 ^ 40 * 3805086 * 2
def baseEnd_3805086 : Nat := 434186233265334403827941

theorem tailTrace_3805086 : CollatzResearch.WordTrace tailWord_3805086 prefixEnd_3805086 434186233265334403827941 := by
  unfold tailWord_3805086
  simp only [CollatzResearch.WordTrace]
  refine ⟨17347860986603844224519389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92521925261887169197436741 17347860986603844224519389)
  ·
    refine ⟨6505447869976441584194771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17347860986603844224519389 6505447869976441584194771)
    ·
      refine ⟨9758171804964662376292157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6505447869976441584194771 9758171804964662376292157)
      ·
        refine ⟨3659314426861748391109559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9758171804964662376292157 3659314426861748391109559)
        ·
          refine ⟨5488971640292622586664339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3659314426861748391109559 5488971640292622586664339)
          ·
            refine ⟨8233457460438933879996509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5488971640292622586664339 8233457460438933879996509)
            ·
              refine ⟨3087546547664600204998691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8233457460438933879996509 3087546547664600204998691)
              ·
                refine ⟨4631319821496900307498037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3087546547664600204998691 4631319821496900307498037)
                ·
                  refine ⟨434186233265334403827941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4631319821496900307498037 434186233265334403827941)
                  ·
                    rfl

theorem cell22_3805086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_3805086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805086 prefixEnd_3805086 := by exact prefixLift 3805086
  have htrace : WordTrace (prefixWord ++ tailWord_3805086) baseStart_3805086 baseEnd_3805086 := by
    simpa [prefixWord, tailWord_3805086, baseEnd_3805086] using wordTrace_append hprefix tailTrace_3805086
  have hstable : (prefixWord ++ tailWord_3805086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805086).length < 2 ^ (prefixWord ++ tailWord_3805086).sum := by decide
  have hdescent : baseEnd_3805086 < baseStart_3805086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805146 : List Nat := [3, 1, 1, 2, 5, 2, 2, 1, 2, 3]
def baseStart_3805146 : Nat := 118140960795 + 3805146 * 2 ^ 59
def prefixEnd_3805146 : Nat := 4983230072969 + 3 ^ 40 * 3805146 * 2
def baseEnd_3805146 : Nat := 1302579239022183054983639

theorem tailTrace_3805146 : CollatzResearch.WordTrace tailWord_3805146 prefixEnd_3805146 1302579239022183054983639 := by
  unfold tailWord_3805146
  simp only [CollatzResearch.WordTrace]
  refine ⟨34696269068153346010834823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92523384181742256028892861 34696269068153346010834823)
  ·
    refine ⟨52044403602230019016252235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34696269068153346010834823 52044403602230019016252235)
    ·
      refine ⟨78066605403345028524378353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52044403602230019016252235 78066605403345028524378353)
      ·
        refine ⟨58549954052508771393283765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78066605403345028524378353 58549954052508771393283765)
        ·
          refine ⟨5489058192422697318120353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58549954052508771393283765 5489058192422697318120353)
          ·
            refine ⟨4116793644317022988590265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5489058192422697318120353 4116793644317022988590265)
            ·
              refine ⟨3087595233237767241442699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4116793644317022988590265 3087595233237767241442699)
              ·
                refine ⟨4631392849856650862164049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3087595233237767241442699 4631392849856650862164049)
                ·
                  refine ⟨3473544637392488146623037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4631392849856650862164049 3473544637392488146623037)
                  ·
                    refine ⟨1302579239022183054983639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3473544637392488146623037 1302579239022183054983639)
                    ·
                      rfl

theorem cell22_3805146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 2, 3].length) (baseStart_3805146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805146 prefixEnd_3805146 := by exact prefixLift 3805146
  have htrace : WordTrace (prefixWord ++ tailWord_3805146) baseStart_3805146 baseEnd_3805146 := by
    simpa [prefixWord, tailWord_3805146, baseEnd_3805146] using wordTrace_append hprefix tailTrace_3805146
  have hstable : (prefixWord ++ tailWord_3805146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805146).length < 2 ^ (prefixWord ++ tailWord_3805146).sum := by decide
  have hdescent : baseEnd_3805146 < baseStart_3805146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805185 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 2, 5]
def baseStart_3805185 : Nat := 118140960795 + 3805185 * 2 ^ 59
def prefixEnd_3805185 : Nat := 4983230072969 + 3 ^ 40 * 3805185 * 2
def baseEnd_3805185 : Nat := 1302592589519199953258519

theorem tailTrace_3805185 : CollatzResearch.WordTrace tailWord_3805185 prefixEnd_3805185 1302592589519199953258519 := by
  unfold tailWord_3805185
  simp only [CollatzResearch.WordTrace]
  refine ⟨138786498719472093704009009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92524332479648062469339339 138786498719472093704009009)
  ·
    refine ⟨104089874039604070278006757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138786498719472093704009009 104089874039604070278006757)
    ·
      refine ⟨19516851382425763177126267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104089874039604070278006757 19516851382425763177126267)
      ·
        refine ⟨29275277073638644765689401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19516851382425763177126267 29275277073638644765689401)
        ·
          refine ⟨21956457805228983574267051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29275277073638644765689401 21956457805228983574267051)
          ·
            refine ⟨32934686707843475361400577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21956457805228983574267051 32934686707843475361400577)
            ·
              refine ⟨24701015030882606521050433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32934686707843475361400577 24701015030882606521050433)
              ·
                refine ⟨18525761273161954890787825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24701015030882606521050433 18525761273161954890787825)
                ·
                  refine ⟨13894320954871466168090869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18525761273161954890787825 13894320954871466168090869)
                  ·
                    refine ⟨1302592589519199953258519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13894320954871466168090869 1302592589519199953258519)
                    ·
                      rfl

theorem cell22_3805185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_3805185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805185 prefixEnd_3805185 := by exact prefixLift 3805185
  have htrace : WordTrace (prefixWord ++ tailWord_3805185) baseStart_3805185 baseEnd_3805185 := by
    simpa [prefixWord, tailWord_3805185, baseEnd_3805185] using wordTrace_append hprefix tailTrace_3805185
  have hstable : (prefixWord ++ tailWord_3805185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805185).length < 2 ^ (prefixWord ++ tailWord_3805185).sum := by decide
  have hdescent : baseEnd_3805185 < baseStart_3805185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805191 : List Nat := [1, 1, 4, 3, 1, 2, 4, 2, 1, 3]
def baseStart_3805191 : Nat := 118140960795 + 3805191 * 2 ^ 59
def prefixEnd_3805191 : Nat := 4983230072969 + 3 ^ 40 * 3805191 * 2
def baseEnd_3805191 : Nat := 1302594643441817937608501

theorem tailTrace_3805191 : CollatzResearch.WordTrace tailWord_3805191 prefixEnd_3805191 1302594643441817937608501 := by
  unfold tailWord_3805191
  simp only [CollatzResearch.WordTrace]
  refine ⟨138786717557450356728727427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92524478371633571152484951 138786717557450356728727427)
  ·
    refine ⟨208180076336175535093091141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138786717557450356728727427 208180076336175535093091141)
    ·
      refine ⟨39033764313032912829954589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208180076336175535093091141 39033764313032912829954589)
      ·
        refine ⟨14637661617387342311232971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39033764313032912829954589 14637661617387342311232971)
        ·
          refine ⟨21956492426081013466849457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14637661617387342311232971 21956492426081013466849457)
          ·
            refine ⟨16467369319560760100137093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21956492426081013466849457 16467369319560760100137093)
            ·
              refine ⟨3087631747417642518775705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16467369319560760100137093 3087631747417642518775705)
              ·
                refine ⟨2315723810563231889081779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3087631747417642518775705 2315723810563231889081779)
                ·
                  refine ⟨3473585715844847833622669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2315723810563231889081779 3473585715844847833622669)
                  ·
                    refine ⟨1302594643441817937608501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3473585715844847833622669 1302594643441817937608501)
                    ·
                      rfl

theorem cell22_3805191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_3805191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805191 prefixEnd_3805191 := by exact prefixLift 3805191
  have htrace : WordTrace (prefixWord ++ tailWord_3805191) baseStart_3805191 baseEnd_3805191 := by
    simpa [prefixWord, tailWord_3805191, baseEnd_3805191] using wordTrace_append hprefix tailTrace_3805191
  have hstable : (prefixWord ++ tailWord_3805191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805191).length < 2 ^ (prefixWord ++ tailWord_3805191).sum := by decide
  have hdescent : baseEnd_3805191 < baseStart_3805191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805215 : List Nat := [1, 1, 2, 4, 1, 2, 3, 2, 6]
def baseStart_3805215 : Nat := 118140960795 + 3805215 * 2 ^ 59
def prefixEnd_3805215 : Nat := 4983230072969 + 3 ^ 40 * 3805215 * 2
def baseEnd_3805215 : Nat := 434200953044096625002809

theorem tailTrace_3805215 : CollatzResearch.WordTrace tailWord_3805215 prefixEnd_3805215 434200953044096625002809 := by
  unfold tailWord_3805215
  simp only [CollatzResearch.WordTrace]
  refine ⟨138787592909363408827601099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92525061939575605885067399 138787592909363408827601099)
  ·
    refine ⟨208181389364045113241401649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138787592909363408827601099 208181389364045113241401649)
    ·
      refine ⟨156136042023033834931051237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208181389364045113241401649 156136042023033834931051237)
      ·
        refine ⟨29275507879318844049572107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156136042023033834931051237 29275507879318844049572107)
        ·
          refine ⟨43913261818978266074358161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29275507879318844049572107 43913261818978266074358161)
          ·
            refine ⟨32934946364233699555768621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43913261818978266074358161 32934946364233699555768621)
            ·
              refine ⟨12350604886587637333413233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32934946364233699555768621 12350604886587637333413233)
              ·
                refine ⟨9262953664940728000059925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12350604886587637333413233 9262953664940728000059925)
                ·
                  refine ⟨434200953044096625002809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9262953664940728000059925 434200953044096625002809)
                  ·
                    rfl

theorem cell22_3805215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 6].length) (baseStart_3805215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805215 prefixEnd_3805215 := by exact prefixLift 3805215
  have htrace : WordTrace (prefixWord ++ tailWord_3805215) baseStart_3805215 baseEnd_3805215 := by
    simpa [prefixWord, tailWord_3805215, baseEnd_3805215] using wordTrace_append hprefix tailTrace_3805215
  have hstable : (prefixWord ++ tailWord_3805215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805215).length < 2 ^ (prefixWord ++ tailWord_3805215).sum := by decide
  have hdescent : baseEnd_3805215 < baseStart_3805215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805232 : List Nat := [2, 1, 1, 1, 2, 5, 1, 5, 4]
def baseStart_3805232 : Nat := 118140960795 + 3805232 * 2 ^ 59
def prefixEnd_3805232 : Nat := 4983230072969 + 3 ^ 40 * 3805232 * 2
def baseEnd_3805232 : Nat := 434202892859902499111125

theorem tailTrace_3805232 : CollatzResearch.WordTrace tailWord_3805232 prefixEnd_3805232 434202892859902499111125 := by
  unfold tailWord_3805232
  simp only [CollatzResearch.WordTrace]
  refine ⟨69394106475150910365484975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92525475300201213820646633 69394106475150910365484975)
  ·
    refine ⟨104091159712726365548227463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69394106475150910365484975 104091159712726365548227463)
    ·
      refine ⟨156136739569089548322341195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104091159712726365548227463 156136739569089548322341195)
      ·
        refine ⟨234205109353634322483511793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156136739569089548322341195 234205109353634322483511793)
        ·
          refine ⟨175653832015225741862633845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234205109353634322483511793 175653832015225741862633845)
          ·
            refine ⟨16467546751427413299621923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175653832015225741862633845 16467546751427413299621923)
            ·
              refine ⟨24701320127141119949432885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16467546751427413299621923 24701320127141119949432885)
              ·
                refine ⟨2315748761919479995259333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24701320127141119949432885 2315748761919479995259333)
                ·
                  refine ⟨434202892859902499111125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2315748761919479995259333 434202892859902499111125)
                  ·
                    rfl

theorem cell22_3805232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 4].length) (baseStart_3805232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805232 prefixEnd_3805232 := by exact prefixLift 3805232
  have htrace : WordTrace (prefixWord ++ tailWord_3805232) baseStart_3805232 baseEnd_3805232 := by
    simpa [prefixWord, tailWord_3805232, baseEnd_3805232] using wordTrace_append hprefix tailTrace_3805232
  have hstable : (prefixWord ++ tailWord_3805232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805232).length < 2 ^ (prefixWord ++ tailWord_3805232).sum := by decide
  have hdescent : baseEnd_3805232 < baseStart_3805232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805234 : List Nat := [3, 2, 1, 1, 2, 3, 4, 1, 1, 4]
def baseStart_3805234 : Nat := 118140960795 + 3805234 * 2 ^ 59
def prefixEnd_3805234 : Nat := 4983230072969 + 3 ^ 40 * 3805234 * 2
def baseEnd_3805234 : Nat := 1302609363220580158783369

theorem tailTrace_3805234 : CollatzResearch.WordTrace tailWord_3805234 prefixEnd_3805234 1302609363220580158783369 := by
  unfold tailWord_3805234
  simp only [CollatzResearch.WordTrace]
  refine ⟨34697071474073643768135689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92525523930863050048361837 34697071474073643768135689)
  ·
    refine ⟨26022803605555232826101767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34697071474073643768135689 26022803605555232826101767)
    ·
      refine ⟨39034205408332849239152651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26022803605555232826101767 39034205408332849239152651)
      ·
        refine ⟨58551308112499273858728977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39034205408332849239152651 58551308112499273858728977)
        ·
          refine ⟨43913481084374455394046733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58551308112499273858728977 43913481084374455394046733)
          ·
            refine ⟨16467555406640420772767525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43913481084374455394046733 16467555406640420772767525)
            ·
              refine ⟨3087666638745078894893911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16467555406640420772767525 3087666638745078894893911)
              ·
                refine ⟨4631499958117618342340867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3087666638745078894893911 4631499958117618342340867)
                ·
                  refine ⟨6947249937176427513511301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4631499958117618342340867 6947249937176427513511301)
                  ·
                    refine ⟨1302609363220580158783369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6947249937176427513511301 1302609363220580158783369)
                    ·
                      rfl

theorem cell22_3805234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_3805234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805234 prefixEnd_3805234 := by exact prefixLift 3805234
  have htrace : WordTrace (prefixWord ++ tailWord_3805234) baseStart_3805234 baseEnd_3805234 := by
    simpa [prefixWord, tailWord_3805234, baseEnd_3805234] using wordTrace_append hprefix tailTrace_3805234
  have hstable : (prefixWord ++ tailWord_3805234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805234).length < 2 ^ (prefixWord ++ tailWord_3805234).sum := by decide
  have hdescent : baseEnd_3805234 < baseStart_3805234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805249 : List Nat := [1, 2, 5, 1, 2, 1, 2, 4, 4]
def baseStart_3805249 : Nat := 118140960795 + 3805249 * 2 ^ 59
def prefixEnd_3805249 : Nat := 4983230072969 + 3 ^ 40 * 3805249 * 2
def baseEnd_3805249 : Nat := 434204832675708373219441

theorem tailTrace_3805249 : CollatzResearch.WordTrace tailWord_3805249 prefixEnd_3805249 434204832675708373219441 := by
  unfold tailWord_3805249
  simp only [CollatzResearch.WordTrace]
  refine ⟨138788832991240232634338801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92525888660826821756225867 138788832991240232634338801)
  ·
    refine ⟨104091624743430174475754101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138788832991240232634338801 104091624743430174475754101)
    ·
      refine ⟨9758589819696578857101947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104091624743430174475754101 9758589819696578857101947)
      ·
        refine ⟨14637884729544868285652921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9758589819696578857101947 14637884729544868285652921)
        ·
          refine ⟨10978413547158651214239691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14637884729544868285652921 10978413547158651214239691)
          ·
            refine ⟨16467620320737976821359537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10978413547158651214239691 16467620320737976821359537)
            ·
              refine ⟨12350715240553482616019653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16467620320737976821359537 12350715240553482616019653)
              ·
                refine ⟨2315759107603777990503685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12350715240553482616019653 2315759107603777990503685)
                ·
                  refine ⟨434204832675708373219441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2315759107603777990503685 434204832675708373219441)
                  ·
                    rfl

theorem cell22_3805249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 4].length) (baseStart_3805249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805249 prefixEnd_3805249 := by exact prefixLift 3805249
  have htrace : WordTrace (prefixWord ++ tailWord_3805249) baseStart_3805249 baseEnd_3805249 := by
    simpa [prefixWord, tailWord_3805249, baseEnd_3805249] using wordTrace_append hprefix tailTrace_3805249
  have hstable : (prefixWord ++ tailWord_3805249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805249).length < 2 ^ (prefixWord ++ tailWord_3805249).sum := by decide
  have hdescent : baseEnd_3805249 < baseStart_3805249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805309 : List Nat := [1, 4, 1, 1, 3, 2, 3, 1, 3, 3]
def baseStart_3805309 : Nat := 118140960795 + 3805309 * 2 ^ 59
def prefixEnd_3805309 : Nat := 4983230072969 + 3 ^ 40 * 3805309 * 2
def baseEnd_3805309 : Nat := 1302635037253304963158139

theorem tailTrace_3805309 : CollatzResearch.WordTrace tailWord_3805309 prefixEnd_3805309 1302635037253304963158139 := by
  unfold tailWord_3805309
  simp only [CollatzResearch.WordTrace]
  refine ⟨138791021371022862881522981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92527347580681908587681987 138791021371022862881522981)
  ·
    refine ⟨26023316507066786790285559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138791021371022862881522981 26023316507066786790285559)
    ·
      refine ⟨39034974760600180185428339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26023316507066786790285559 39034974760600180185428339)
      ·
        refine ⟨58552462140900270278142509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39034974760600180185428339 58552462140900270278142509)
        ·
          refine ⟨21957173302837601354303441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58552462140900270278142509 21957173302837601354303441)
          ·
            refine ⟨16467879977128201015727581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21957173302837601354303441 16467879977128201015727581)
            ·
              refine ⟨6175454991423075380897843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16467879977128201015727581 6175454991423075380897843)
              ·
                refine ⟨9263182487134613071346765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6175454991423075380897843 9263182487134613071346765)
                ·
                  refine ⟨3473693432675479901755037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9263182487134613071346765 3473693432675479901755037)
                  ·
                    refine ⟨1302635037253304963158139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3473693432675479901755037 1302635037253304963158139)
                    ·
                      rfl

theorem cell22_3805309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_3805309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805309 prefixEnd_3805309 := by exact prefixLift 3805309
  have htrace : WordTrace (prefixWord ++ tailWord_3805309) baseStart_3805309 baseEnd_3805309 := by
    simpa [prefixWord, tailWord_3805309, baseEnd_3805309] using wordTrace_append hprefix tailTrace_3805309
  have hstable : (prefixWord ++ tailWord_3805309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805309).length < 2 ^ (prefixWord ++ tailWord_3805309).sum := by decide
  have hdescent : baseEnd_3805309 < baseStart_3805309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805416 : List Nat := [2, 1, 4, 1, 2, 2, 3, 2, 2, 3]
def baseStart_3805416 : Nat := 118140960795 + 3805416 * 2 ^ 59
def prefixEnd_3805416 : Nat := 4983230072969 + 3 ^ 40 * 3805416 * 2
def baseEnd_3805416 : Nat := 1302671665539992350732811

theorem tailTrace_3805416 : CollatzResearch.WordTrace tailWord_3805416 prefixEnd_3805416 1302671665539992350732811 := by
  unfold tailWord_3805416
  simp only [CollatzResearch.WordTrace]
  refine ⟨69397461990817610077834051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92529949321090146770445401 69397461990817610077834051)
  ·
    refine ⟨104096192986226415116751077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69397461990817610077834051 104096192986226415116751077)
    ·
      refine ⟨19518036184917452834390827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104096192986226415116751077 19518036184917452834390827)
      ·
        refine ⟨29277054277376179251586241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19518036184917452834390827 29277054277376179251586241)
        ·
          refine ⟨21957790708032134438689681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29277054277376179251586241 21957790708032134438689681)
          ·
            refine ⟨16468343031024100829017261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21957790708032134438689681 16468343031024100829017261)
            ·
              refine ⟨6175628636634037810881473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16468343031024100829017261 6175628636634037810881473)
              ·
                refine ⟨4631721477475528358161105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6175628636634037810881473 4631721477475528358161105)
                ·
                  refine ⟨3473791108106646268620829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4631721477475528358161105 3473791108106646268620829)
                  ·
                    refine ⟨1302671665539992350732811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3473791108106646268620829 1302671665539992350732811)
                    ·
                      rfl

theorem cell22_3805416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_3805416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805416 prefixEnd_3805416 := by exact prefixLift 3805416
  have htrace : WordTrace (prefixWord ++ tailWord_3805416) baseStart_3805416 baseEnd_3805416 := by
    simpa [prefixWord, tailWord_3805416, baseEnd_3805416] using wordTrace_append hprefix tailTrace_3805416
  have hstable : (prefixWord ++ tailWord_3805416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805416).length < 2 ^ (prefixWord ++ tailWord_3805416).sum := by decide
  have hdescent : baseEnd_3805416 < baseStart_3805416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805457 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 7]
def baseStart_3805457 : Nat := 118140960795 + 3805457 * 2 ^ 59
def prefixEnd_3805457 : Nat := 4983230072969 + 3 ^ 40 * 3805457 * 2
def baseEnd_3805457 : Nat := 434228566892627303485895

theorem tailTrace_3805457 : CollatzResearch.WordTrace tailWord_3805457 prefixEnd_3805457 434228566892627303485895 := by
  unfold tailWord_3805457
  simp only [CollatzResearch.WordTrace]
  refine ⟨138796419374486684157910625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92530946249657789438607083 138796419374486684157910625)
  ·
    refine ⟨104097314530865013118432969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138796419374486684157910625 104097314530865013118432969)
    ·
      refine ⟨78072985898148759838824727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104097314530865013118432969 78072985898148759838824727)
      ·
        refine ⟨117109478847223139758237091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78072985898148759838824727 117109478847223139758237091)
        ·
          refine ⟨175664218270834709637355637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117109478847223139758237091 175664218270834709637355637)
          ·
            refine ⟨16468520462890754028502091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175664218270834709637355637 16468520462890754028502091)
            ·
              refine ⟨24702780694336131042753137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16468520462890754028502091 24702780694336131042753137)
              ·
                refine ⟨18527085520752098282064853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24702780694336131042753137 18527085520752098282064853)
                ·
                  refine ⟨434228566892627303485895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18527085520752098282064853 434228566892627303485895)
                  ·
                    rfl

theorem cell22_3805457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 7].length) (baseStart_3805457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805457 prefixEnd_3805457 := by exact prefixLift 3805457
  have htrace : WordTrace (prefixWord ++ tailWord_3805457) baseStart_3805457 baseEnd_3805457 := by
    simpa [prefixWord, tailWord_3805457, baseEnd_3805457] using wordTrace_append hprefix tailTrace_3805457
  have hstable : (prefixWord ++ tailWord_3805457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805457).length < 2 ^ (prefixWord ++ tailWord_3805457).sum := by decide
  have hdescent : baseEnd_3805457 < baseStart_3805457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805474 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 7]
def baseStart_3805474 : Nat := 118140960795 + 3805474 * 2 ^ 59
def prefixEnd_3805474 : Nat := 4983230072969 + 3 ^ 40 * 3805474 * 2
def baseEnd_3805474 : Nat := 434230506708433177594211

theorem tailTrace_3805474 : CollatzResearch.WordTrace tailWord_3805474 prefixEnd_3805474 434230506708433177594211 := by
  unfold tailWord_3805474
  simp only [CollatzResearch.WordTrace]
  refine ⟨34699259853856274015319869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92531359610283397374186317 34699259853856274015319869)
  ·
    refine ⟨13012222445196102755744951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34699259853856274015319869 13012222445196102755744951)
    ·
      refine ⟨19518333667794154133617427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13012222445196102755744951 19518333667794154133617427)
      ·
        refine ⟨29277500501691231200426141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19518333667794154133617427 29277500501691231200426141)
        ·
          refine ⟨10979062688134211700159803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29277500501691231200426141 10979062688134211700159803)
          ·
            refine ⟨16468594032201317550239705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10979062688134211700159803 16468594032201317550239705)
            ·
              refine ⟨12351445524150988162679779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16468594032201317550239705 12351445524150988162679779)
              ·
                refine ⟨18527168286226482244019669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12351445524150988162679779 18527168286226482244019669)
                ·
                  refine ⟨434230506708433177594211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18527168286226482244019669 434230506708433177594211)
                  ·
                    rfl

theorem cell22_3805474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_3805474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805474 prefixEnd_3805474 := by exact prefixLift 3805474
  have htrace : WordTrace (prefixWord ++ tailWord_3805474) baseStart_3805474 baseEnd_3805474 := by
    simpa [prefixWord, tailWord_3805474, baseEnd_3805474] using wordTrace_append hprefix tailTrace_3805474
  have hstable : (prefixWord ++ tailWord_3805474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805474).length < 2 ^ (prefixWord ++ tailWord_3805474).sum := by decide
  have hdescent : baseEnd_3805474 < baseStart_3805474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805504 : List Nat := [2, 1, 1, 2, 2, 1, 2, 6, 1, 4]
def baseStart_3805504 : Nat := 118140960795 + 3805504 * 2 ^ 59
def prefixEnd_3805504 : Nat := 4983230072969 + 3 ^ 40 * 3805504 * 2
def baseEnd_3805504 : Nat := 1302701789738389454532541

theorem tailTrace_3805504 : CollatzResearch.WordTrace tailWord_3805504 prefixEnd_3805504 1302701789738389454532541 := by
  unfold tailWord_3805504
  simp only [CollatzResearch.WordTrace]
  refine ⟨69399066802658205592435783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92532089070210940789914377 69399066802658205592435783)
  ·
    refine ⟨104098600203987308388653675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69399066802658205592435783 104098600203987308388653675)
    ·
      refine ⟨156147900305980962582980513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104098600203987308388653675 156147900305980962582980513)
      ·
        refine ⟨117110925229485721937235385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156147900305980962582980513 117110925229485721937235385)
        ·
          refine ⟨87833193922114291452926539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117110925229485721937235385 87833193922114291452926539)
          ·
            refine ⟨131749790883171437179389809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87833193922114291452926539 131749790883171437179389809)
            ·
              refine ⟨98812343162378577884542357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131749790883171437179389809 98812343162378577884542357)
              ·
                refine ⟨4631828585736495838337923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98812343162378577884542357 4631828585736495838337923)
                ·
                  refine ⟨6947742878604743757506885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4631828585736495838337923 6947742878604743757506885)
                  ·
                    refine ⟨1302701789738389454532541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6947742878604743757506885 1302701789738389454532541)
                    ·
                      rfl

theorem cell22_3805504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 1, 4].length) (baseStart_3805504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805504 prefixEnd_3805504 := by exact prefixLift 3805504
  have htrace : WordTrace (prefixWord ++ tailWord_3805504) baseStart_3805504 baseEnd_3805504 := by
    simpa [prefixWord, tailWord_3805504, baseEnd_3805504] using wordTrace_append hprefix tailTrace_3805504
  have hstable : (prefixWord ++ tailWord_3805504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805504).length < 2 ^ (prefixWord ++ tailWord_3805504).sum := by decide
  have hdescent : baseEnd_3805504 < baseStart_3805504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805549 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_3805549 : Nat := 118140960795 + 3805549 * 2 ^ 59
def prefixEnd_3805549 : Nat := 4983230072969 + 3 ^ 40 * 3805549 * 2
def baseEnd_3805549 : Nat := 1302717194158024337157403

theorem tailTrace_3805549 : CollatzResearch.WordTrace tailWord_3805549 prefixEnd_3805549 1302717194158024337157403 := by
  unfold tailWord_3805549
  simp only [CollatzResearch.WordTrace]
  refine ⟨138799774890153383870259701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92533183260102255913506467 138799774890153383870259701)
  ·
    refine ⟨13012478895951879737836847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138799774890153383870259701 13012478895951879737836847)
    ·
      refine ⟨19518718343927819606755271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13012478895951879737836847 19518718343927819606755271)
      ·
        refine ⟨29278077515891729410132907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19518718343927819606755271 29278077515891729410132907)
        ·
          refine ⟨43917116273837594115199361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29278077515891729410132907 43917116273837594115199361)
          ·
            refine ⟨32937837205378195586399521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43917116273837594115199361 32937837205378195586399521)
            ·
              refine ⟨24703377904033646689799641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32937837205378195586399521 24703377904033646689799641)
              ·
                refine ⟨18527533428025235017349731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24703377904033646689799641 18527533428025235017349731)
                ·
                  refine ⟨27791300142037852526024597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18527533428025235017349731 27791300142037852526024597)
                  ·
                    refine ⟨1302717194158024337157403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27791300142037852526024597 1302717194158024337157403)
                    ·
                      rfl

theorem cell22_3805549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_3805549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805549 prefixEnd_3805549 := by exact prefixLift 3805549
  have htrace : WordTrace (prefixWord ++ tailWord_3805549) baseStart_3805549 baseEnd_3805549 := by
    simpa [prefixWord, tailWord_3805549, baseEnd_3805549] using wordTrace_append hprefix tailTrace_3805549
  have hstable : (prefixWord ++ tailWord_3805549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805549).length < 2 ^ (prefixWord ++ tailWord_3805549).sum := by decide
  have hdescent : baseEnd_3805549 < baseStart_3805549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805609 : List Nat := [1, 2, 1, 1, 1, 1, 3, 7, 5]
def baseStart_3805609 : Nat := 118140960795 + 3805609 * 2 ^ 59
def prefixEnd_3805609 : Nat := 4983230072969 + 3 ^ 40 * 3805609 * 2
def baseEnd_3805609 : Nat := 434245911128068060219073

theorem tailTrace_3805609 : CollatzResearch.WordTrace tailWord_3805609 prefixEnd_3805609 434245911128068060219073 := by
  unfold tailWord_3805609
  simp only [CollatzResearch.WordTrace]
  refine ⟨138801963269936014117443881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92534642179957342744962587 138801963269936014117443881)
  ·
    refine ⟨104101472452452010588082911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138801963269936014117443881 104101472452452010588082911)
    ·
      refine ⟨156152208678678015882124367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104101472452452010588082911 156152208678678015882124367)
      ·
        refine ⟨234228313018017023823186551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156152208678678015882124367 234228313018017023823186551)
        ·
          refine ⟨351342469527025535734779827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234228313018017023823186551 351342469527025535734779827)
          ·
            refine ⟨527013704290538303602169741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351342469527025535734779827 527013704290538303602169741)
            ·
              refine ⟨197630139108951863850813653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 527013704290538303602169741 197630139108951863850813653)
              ·
                refine ⟨4631956385366059309003445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 197630139108951863850813653 4631956385366059309003445)
                ·
                  refine ⟨434245911128068060219073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4631956385366059309003445 434245911128068060219073)
                  ·
                    rfl

theorem cell22_3805609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 5].length) (baseStart_3805609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805609 prefixEnd_3805609 := by exact prefixLift 3805609
  have htrace : WordTrace (prefixWord ++ tailWord_3805609) baseStart_3805609 baseEnd_3805609 := by
    simpa [prefixWord, tailWord_3805609, baseEnd_3805609] using wordTrace_append hprefix tailTrace_3805609
  have hstable : (prefixWord ++ tailWord_3805609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805609).length < 2 ^ (prefixWord ++ tailWord_3805609).sum := by decide
  have hdescent : baseEnd_3805609 < baseStart_3805609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805630 : List Nat := [4, 2, 1, 1, 1, 1, 5, 3, 1, 3]
def baseStart_3805630 : Nat := 118140960795 + 3805630 * 2 ^ 59
def prefixEnd_3805630 : Nat := 4983230072969 + 3 ^ 40 * 3805630 * 2
def baseEnd_3805630 : Nat := 1302744922113367125882155

theorem tailTrace_3805630 : CollatzResearch.WordTrace tailWord_3805630 prefixEnd_3805630 1302744922113367125882155 := by
  unfold tailWord_3805630
  simp only [CollatzResearch.WordTrace]
  refine ⟨17350341150357491837994793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92535152801906623135972229 17350341150357491837994793)
  ·
    refine ⟨13012755862768118878496095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17350341150357491837994793 13012755862768118878496095)
    ·
      refine ⟨19519133794152178317744143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13012755862768118878496095 19519133794152178317744143)
      ·
        refine ⟨29278700691228267476616215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19519133794152178317744143 29278700691228267476616215)
        ·
          refine ⟨43918051036842401214924323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29278700691228267476616215 43918051036842401214924323)
          ·
            refine ⟨65877076555263601822386485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43918051036842401214924323 65877076555263601822386485)
            ·
              refine ⟨6175975927055962670848733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65877076555263601822386485 6175975927055962670848733)
              ·
                refine ⟨2315990972645986001568275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6175975927055962670848733 2315990972645986001568275)
                ·
                  refine ⟨3473986458968979002352413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2315990972645986001568275 3473986458968979002352413)
                  ·
                    refine ⟨1302744922113367125882155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3473986458968979002352413 1302744922113367125882155)
                    ·
                      rfl

theorem cell22_3805630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_3805630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805630 prefixEnd_3805630 := by exact prefixLift 3805630
  have htrace : WordTrace (prefixWord ++ tailWord_3805630) baseStart_3805630 baseEnd_3805630 := by
    simpa [prefixWord, tailWord_3805630, baseEnd_3805630] using wordTrace_append hprefix tailTrace_3805630
  have hstable : (prefixWord ++ tailWord_3805630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805630).length < 2 ^ (prefixWord ++ tailWord_3805630).sum := by decide
  have hdescent : baseEnd_3805630 < baseStart_3805630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805701 : List Nat := [1, 3, 1, 1, 2, 2, 4, 2, 2, 4]
def baseStart_3805701 : Nat := 118140960795 + 3805701 * 2 ^ 59
def prefixEnd_3805701 : Nat := 4983230072969 + 3 ^ 40 * 3805701 * 2
def baseEnd_3805701 : Nat := 1302769226864346607356937

theorem tailTrace_3805701 : CollatzResearch.WordTrace tailWord_3805701 prefixEnd_3805701 1302769226864346607356937 := by
  unfold tailWord_3805701
  simp only [CollatzResearch.WordTrace]
  refine ⟨138805318785602713829792957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92536879190401809219861971 138805318785602713829792957)
  ·
    refine ⟨52051994544601017686172359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138805318785602713829792957 52051994544601017686172359)
    ·
      refine ⟨78077991816901526529258539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52051994544601017686172359 78077991816901526529258539)
      ·
        refine ⟨117116987725352289793887809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78077991816901526529258539 117116987725352289793887809)
        ·
          refine ⟨87837740794014217345415857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117116987725352289793887809 87837740794014217345415857)
          ·
            refine ⟨65878305595510663009061893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87837740794014217345415857 65878305595510663009061893)
            ·
              refine ⟨12352182299158249314199105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65878305595510663009061893 12352182299158249314199105)
              ·
                refine ⟨9264136724368686985649329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12352182299158249314199105 9264136724368686985649329)
                ·
                  refine ⟨6948102543276515239236997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9264136724368686985649329 6948102543276515239236997)
                  ·
                    refine ⟨1302769226864346607356937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6948102543276515239236997 1302769226864346607356937)
                    ·
                      rfl

theorem cell22_3805701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_3805701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805701 prefixEnd_3805701 := by exact prefixLift 3805701
  have htrace : WordTrace (prefixWord ++ tailWord_3805701) baseStart_3805701 baseEnd_3805701 := by
    simpa [prefixWord, tailWord_3805701, baseEnd_3805701] using wordTrace_append hprefix tailTrace_3805701
  have hstable : (prefixWord ++ tailWord_3805701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805701).length < 2 ^ (prefixWord ++ tailWord_3805701).sum := by decide
  have hdescent : baseEnd_3805701 < baseStart_3805701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805735 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 1, 6]
def baseStart_3805735 : Nat := 118140960795 + 3805735 * 2 ^ 59
def prefixEnd_3805735 : Nat := 4983230072969 + 3 ^ 40 * 3805735 * 2
def baseEnd_3805735 : Nat := 1302780865759181852006833

theorem tailTrace_3805735 : CollatzResearch.WordTrace tailWord_3805735 prefixEnd_3805735 1302780865759181852006833 := by
  unfold tailWord_3805735
  simp only [CollatzResearch.WordTrace]
  refine ⟨138806558867479537636530659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92537705911653025091020439 138806558867479537636530659)
  ·
    refine ⟨208209838301219306454795989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138806558867479537636530659 208209838301219306454795989)
    ·
      refine ⟨4879918085184827495034281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 208209838301219306454795989 4879918085184827495034281)
      ·
        refine ⟨3659938563888620621275711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4879918085184827495034281 3659938563888620621275711)
        ·
          refine ⟨5489907845832930931913567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3659938563888620621275711 5489907845832930931913567)
          ·
            refine ⟨8234861768749396397870351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5489907845832930931913567 8234861768749396397870351)
            ·
              refine ⟨12352292653124094596805527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8234861768749396397870351 12352292653124094596805527)
              ·
                refine ⟨18528438979686141895208291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12352292653124094596805527 18528438979686141895208291)
                ·
                  refine ⟨27792658469529212842812437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18528438979686141895208291 27792658469529212842812437)
                  ·
                    refine ⟨1302780865759181852006833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27792658469529212842812437 1302780865759181852006833)
                    ·
                      rfl

theorem cell22_3805735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_3805735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805735 prefixEnd_3805735 := by exact prefixLift 3805735
  have htrace : WordTrace (prefixWord ++ tailWord_3805735) baseStart_3805735 baseEnd_3805735 := by
    simpa [prefixWord, tailWord_3805735, baseEnd_3805735] using wordTrace_append hprefix tailTrace_3805735
  have hstable : (prefixWord ++ tailWord_3805735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805735).length < 2 ^ (prefixWord ++ tailWord_3805735).sum := by decide
  have hdescent : baseEnd_3805735 < baseStart_3805735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805741 : List Nat := [1, 5, 4, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3805741 : Nat := 118140960795 + 3805741 * 2 ^ 59
def prefixEnd_3805741 : Nat := 4983230072969 + 3 ^ 40 * 3805741 * 2
def baseEnd_3805741 : Nat := 1302782919681799836356815

theorem tailTrace_3805741 : CollatzResearch.WordTrace tailWord_3805741 prefixEnd_3805741 1302782919681799836356815 := by
  unfold tailWord_3805741
  simp only [CollatzResearch.WordTrace]
  refine ⟨138806777705457800661249077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92537851803638533774166051 138806777705457800661249077)
  ·
    refine ⟨13013135409886668811992101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138806777705457800661249077 13013135409886668811992101)
    ·
      refine ⟨2439962889353750402248519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13013135409886668811992101 2439962889353750402248519)
      ·
        refine ⟨3659944334030625603372779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2439962889353750402248519 3659944334030625603372779)
        ·
          refine ⟨5489916501045938405059169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3659944334030625603372779 5489916501045938405059169)
          ·
            refine ⟨4117437375784453803794377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5489916501045938405059169 4117437375784453803794377)
            ·
              refine ⟨3088078031838340352845783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4117437375784453803794377 3088078031838340352845783)
              ·
                refine ⟨4632117047757510529268675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3088078031838340352845783 4632117047757510529268675)
                ·
                  refine ⟨6948175571636265793903013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4632117047757510529268675 6948175571636265793903013)
                  ·
                    refine ⟨1302782919681799836356815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6948175571636265793903013 1302782919681799836356815)
                    ·
                      rfl

theorem cell22_3805741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3805741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805741 prefixEnd_3805741 := by exact prefixLift 3805741
  have htrace : WordTrace (prefixWord ++ tailWord_3805741) baseStart_3805741 baseEnd_3805741 := by
    simpa [prefixWord, tailWord_3805741, baseEnd_3805741] using wordTrace_append hprefix tailTrace_3805741
  have hstable : (prefixWord ++ tailWord_3805741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805741).length < 2 ^ (prefixWord ++ tailWord_3805741).sum := by decide
  have hdescent : baseEnd_3805741 < baseStart_3805741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805765 : List Nat := [1, 3, 1, 1, 1, 5, 2, 4, 1, 3]
def baseStart_3805765 : Nat := 118140960795 + 3805765 * 2 ^ 59
def prefixEnd_3805765 : Nat := 4983230072969 + 3 ^ 40 * 3805765 * 2
def baseEnd_3805765 : Nat := 1302791135372271773756741

theorem tailTrace_3805765 : CollatzResearch.WordTrace tailWord_3805765 prefixEnd_3805765 1302791135372271773756741 := by
  unfold tailWord_3805765
  simp only [CollatzResearch.WordTrace]
  refine ⟨138807653057370852760122749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92538435371580568506748499 138807653057370852760122749)
  ·
    refine ⟨52052869896514069785046031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138807653057370852760122749 52052869896514069785046031)
    ·
      refine ⟨78079304844771104677569047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52052869896514069785046031 78079304844771104677569047)
      ·
        refine ⟨117118957267156657016353571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78079304844771104677569047 117118957267156657016353571)
        ·
          refine ⟨175678435900734985524530357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117118957267156657016353571 175678435900734985524530357)
          ·
            refine ⟨16469853365693904892924721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175678435900734985524530357 16469853365693904892924721)
            ·
              refine ⟨12352390024270428669693541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16469853365693904892924721 12352390024270428669693541)
              ·
                refine ⟨2316073129550705375567539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12352390024270428669693541 2316073129550705375567539)
                ·
                  refine ⟨3474109694326058063351309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2316073129550705375567539 3474109694326058063351309)
                  ·
                    refine ⟨1302791135372271773756741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3474109694326058063351309 1302791135372271773756741)
                    ·
                      rfl

theorem cell22_3805765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 1, 3].length) (baseStart_3805765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805765 prefixEnd_3805765 := by exact prefixLift 3805765
  have htrace : WordTrace (prefixWord ++ tailWord_3805765) baseStart_3805765 baseEnd_3805765 := by
    simpa [prefixWord, tailWord_3805765, baseEnd_3805765] using wordTrace_append hprefix tailTrace_3805765
  have hstable : (prefixWord ++ tailWord_3805765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805765).length < 2 ^ (prefixWord ++ tailWord_3805765).sum := by decide
  have hdescent : baseEnd_3805765 < baseStart_3805765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805791 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 3, 4]
def baseStart_3805791 : Nat := 118140960795 + 3805791 * 2 ^ 59
def prefixEnd_3805791 : Nat := 4983230072969 + 3 ^ 40 * 3805791 * 2
def baseEnd_3805791 : Nat := 1302800035703616372606661

theorem tailTrace_3805791 : CollatzResearch.WordTrace tailWord_3805791 prefixEnd_3805791 1302800035703616372606661 := by
  unfold tailWord_3805791
  simp only [CollatzResearch.WordTrace]
  refine ⟨138808601355276659200569227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92539067570184439467046151 138808601355276659200569227)
  ·
    refine ⟨208212902032914988800853841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138808601355276659200569227 208212902032914988800853841)
    ·
      refine ⟨156159676524686241600640381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208212902032914988800853841 156159676524686241600640381)
      ·
        refine ⟨58559878696757340600240143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156159676524686241600640381 58559878696757340600240143)
        ·
          refine ⟨87839818045136010900360215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58559878696757340600240143 87839818045136010900360215)
          ·
            refine ⟨131759727067704016350540323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87839818045136010900360215 131759727067704016350540323)
            ·
              refine ⟨197639590601556024525810485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131759727067704016350540323 197639590601556024525810485)
              ·
                refine ⟨18528711618895877299294733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197639590601556024525810485 18528711618895877299294733)
                ·
                  refine ⟨6948266857085953987235525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18528711618895877299294733 6948266857085953987235525)
                  ·
                    refine ⟨1302800035703616372606661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6948266857085953987235525 1302800035703616372606661)
                    ·
                      rfl

theorem cell22_3805791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 4].length) (baseStart_3805791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805791 prefixEnd_3805791 := by exact prefixLift 3805791
  have htrace : WordTrace (prefixWord ++ tailWord_3805791) baseStart_3805791 baseEnd_3805791 := by
    simpa [prefixWord, tailWord_3805791, baseEnd_3805791] using wordTrace_append hprefix tailTrace_3805791
  have hstable : (prefixWord ++ tailWord_3805791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805791).length < 2 ^ (prefixWord ++ tailWord_3805791).sum := by decide
  have hdescent : baseEnd_3805791 < baseStart_3805791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805836 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 1, 6]
def baseStart_3805836 : Nat := 118140960795 + 3805836 * 2 ^ 59
def prefixEnd_3805836 : Nat := 4983230072969 + 3 ^ 40 * 3805836 * 2
def baseEnd_3805836 : Nat := 1302815440123251255231523

theorem tailTrace_3805836 : CollatzResearch.WordTrace tailWord_3805836 prefixEnd_3805836 1302815440123251255231523 := by
  unfold tailWord_3805836
  simp only [CollatzResearch.WordTrace]
  refine ⟨69405121320056815942978681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92540161760075754590638241 69405121320056815942978681)
  ·
    refine ⟨52053840990042611957234011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69405121320056815942978681 52053840990042611957234011)
    ·
      refine ⟨78080761485063917935851017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52053840990042611957234011 78080761485063917935851017)
      ·
        refine ⟨58560571113797938451888263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78080761485063917935851017 58560571113797938451888263)
        ·
          refine ⟨87840856670696907677832395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58560571113797938451888263 87840856670696907677832395)
          ·
            refine ⟨131761285006045361516748593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87840856670696907677832395 131761285006045361516748593)
            ·
              refine ⟨98820963754534021137561445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131761285006045361516748593 98820963754534021137561445)
              ·
                refine ⟨18528930703975128963292771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98820963754534021137561445 18528930703975128963292771)
                ·
                  refine ⟨27793396055962693444939157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18528930703975128963292771 27793396055962693444939157)
                  ·
                    refine ⟨1302815440123251255231523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27793396055962693444939157 1302815440123251255231523)
                    ·
                      rfl

theorem cell22_3805836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_3805836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805836 prefixEnd_3805836 := by exact prefixLift 3805836
  have htrace : WordTrace (prefixWord ++ tailWord_3805836) baseStart_3805836 baseEnd_3805836 := by
    simpa [prefixWord, tailWord_3805836, baseEnd_3805836] using wordTrace_append hprefix tailTrace_3805836
  have hstable : (prefixWord ++ tailWord_3805836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805836).length < 2 ^ (prefixWord ++ tailWord_3805836).sum := by decide
  have hdescent : baseEnd_3805836 < baseStart_3805836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805838 : List Nat := [4, 1, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_3805838 : Nat := 118140960795 + 3805838 * 2 ^ 59
def prefixEnd_3805838 : Nat := 4983230072969 + 3 ^ 40 * 3805838 * 2
def baseEnd_3805838 : Nat := 1302816124764123916681517

theorem tailTrace_3805838 : CollatzResearch.WordTrace tailWord_3805838 prefixEnd_3805838 1302816124764123916681517 := by
  unfold tailWord_3805838
  simp only [CollatzResearch.WordTrace]
  refine ⟨17351289448263298278441271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92540210390737590818353445 17351289448263298278441271)
  ·
    refine ⟨26026934172394947417661907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17351289448263298278441271 26026934172394947417661907)
    ·
      refine ⟨39040401258592421126492861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26026934172394947417661907 39040401258592421126492861)
      ·
        refine ⟨14640150471972157922434823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39040401258592421126492861 14640150471972157922434823)
        ·
          refine ⟨21960225707958236883652235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14640150471972157922434823 21960225707958236883652235)
          ·
            refine ⟨32940338561937355325478353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21960225707958236883652235 32940338561937355325478353)
            ·
              refine ⟨24705253921453016494108765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32940338561937355325478353 24705253921453016494108765)
              ·
                refine ⟨9264470220544881185290787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24705253921453016494108765 9264470220544881185290787)
                ·
                  refine ⟨13896705330817321777936181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9264470220544881185290787 13896705330817321777936181)
                  ·
                    refine ⟨1302816124764123916681517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13896705330817321777936181 1302816124764123916681517)
                    ·
                      rfl

theorem cell22_3805838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_3805838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805838 prefixEnd_3805838 := by exact prefixLift 3805838
  have htrace : WordTrace (prefixWord ++ tailWord_3805838) baseStart_3805838 baseEnd_3805838 := by
    simpa [prefixWord, tailWord_3805838, baseEnd_3805838] using wordTrace_append hprefix tailTrace_3805838
  have hstable : (prefixWord ++ tailWord_3805838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805838).length < 2 ^ (prefixWord ++ tailWord_3805838).sum := by decide
  have hdescent : baseEnd_3805838 < baseStart_3805838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805842 : List Nat := [3, 2, 3, 1, 2, 3, 1, 2, 1, 4]
def baseStart_3805842 : Nat := 118140960795 + 3805842 * 2 ^ 59
def prefixEnd_3805842 : Nat := 4983230072969 + 3 ^ 40 * 3805842 * 2
def baseEnd_3805842 : Nat := 1302817494045869239581505

theorem tailTrace_3805842 : CollatzResearch.WordTrace tailWord_3805842 prefixEnd_3805842 1302817494045869239581505 := by
  unfold tailWord_3805842
  simp only [CollatzResearch.WordTrace]
  refine ⟨34702615369522973727668945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92540307652061263273783853 34702615369522973727668945)
  ·
    refine ⟨26026961527142230295751709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34702615369522973727668945 26026961527142230295751709)
    ·
      refine ⟨9760110572678336360906891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26026961527142230295751709 9760110572678336360906891)
      ·
        refine ⟨14640165859017504541360337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9760110572678336360906891 14640165859017504541360337)
        ·
          refine ⟨10980124394263128406020253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14640165859017504541360337 10980124394263128406020253)
          ·
            refine ⟨4117546647848673152257595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10980124394263128406020253 4117546647848673152257595)
            ·
              refine ⟨6176319971773009728386393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4117546647848673152257595 6176319971773009728386393)
              ·
                refine ⟨4632239978829757296289795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6176319971773009728386393 4632239978829757296289795)
                ·
                  refine ⟨6948359968244635944434693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4632239978829757296289795 6948359968244635944434693)
                  ·
                    refine ⟨1302817494045869239581505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6948359968244635944434693 1302817494045869239581505)
                    ·
                      rfl

theorem cell22_3805842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_3805842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805842 prefixEnd_3805842 := by exact prefixLift 3805842
  have htrace : WordTrace (prefixWord ++ tailWord_3805842) baseStart_3805842 baseEnd_3805842 := by
    simpa [prefixWord, tailWord_3805842, baseEnd_3805842] using wordTrace_append hprefix tailTrace_3805842
  have hstable : (prefixWord ++ tailWord_3805842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805842).length < 2 ^ (prefixWord ++ tailWord_3805842).sum := by decide
  have hdescent : baseEnd_3805842 < baseStart_3805842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805853 : List Nat := [1, 4, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_3805853 : Nat := 118140960795 + 3805853 * 2 ^ 59
def prefixEnd_3805853 : Nat := 4983230072969 + 3 ^ 40 * 3805853 * 2
def baseEnd_3805853 : Nat := 1302821259570668877556471

theorem tailTrace_3805853 : CollatzResearch.WordTrace tailWord_3805853 prefixEnd_3805853 1302821259570668877556471 := by
  unfold tailWord_3805853
  simp only [CollatzResearch.WordTrace]
  refine ⟨138810862681052043789326213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92540575120701362526217475 138810862681052043789326213)
  ·
    refine ⟨26027036752697258210498665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138810862681052043789326213 26027036752697258210498665)
    ·
      refine ⟨19520277564522943657873999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26027036752697258210498665 19520277564522943657873999)
      ·
        refine ⟨29280416346784415486810999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19520277564522943657873999 29280416346784415486810999)
        ·
          refine ⟨43920624520176623230216499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29280416346784415486810999 43920624520176623230216499)
          ·
            refine ⟨65880936780264934845324749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43920624520176623230216499 65880936780264934845324749)
            ·
              refine ⟨24705351292599350566996781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65880936780264934845324749 24705351292599350566996781)
              ·
                refine ⟨9264506734724756462623793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24705351292599350566996781 9264506734724756462623793)
                ·
                  refine ⟨6948380051043567346967845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9264506734724756462623793 6948380051043567346967845)
                  ·
                    refine ⟨1302821259570668877556471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6948380051043567346967845 1302821259570668877556471)
                    ·
                      rfl

theorem cell22_3805853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_3805853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805853 prefixEnd_3805853 := by exact prefixLift 3805853
  have htrace : WordTrace (prefixWord ++ tailWord_3805853) baseStart_3805853 baseEnd_3805853 := by
    simpa [prefixWord, tailWord_3805853, baseEnd_3805853] using wordTrace_append hprefix tailTrace_3805853
  have hstable : (prefixWord ++ tailWord_3805853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805853).length < 2 ^ (prefixWord ++ tailWord_3805853).sum := by decide
  have hdescent : baseEnd_3805853 < baseStart_3805853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805900 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 5, 3]
def baseStart_3805900 : Nat := 118140960795 + 3805900 * 2 ^ 59
def prefixEnd_3805900 : Nat := 4983230072969 + 3 ^ 40 * 3805900 * 2
def baseEnd_3805900 : Nat := 1302837348631176421631327

theorem tailTrace_3805900 : CollatzResearch.WordTrace tailWord_3805900 prefixEnd_3805900 1302837348631176421631327 := by
  unfold tailWord_3805900
  simp only [CollatzResearch.WordTrace]
  refine ⟨69406288455940885408143577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92541717941254513877524769 69406288455940885408143577)
  ·
    refine ⟨52054716341955664056107683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69406288455940885408143577 52054716341955664056107683)
    ·
      refine ⟨78082074512933496084161525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52054716341955664056107683 78082074512933496084161525)
      ·
        refine ⟨7320194485587515257890143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78082074512933496084161525 7320194485587515257890143)
        ·
          refine ⟨10980291728381272886835215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7320194485587515257890143 10980291728381272886835215)
          ·
            refine ⟨16470437592571909330252823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10980291728381272886835215 16470437592571909330252823)
            ·
              refine ⟨24705656388857863995379235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16470437592571909330252823 24705656388857863995379235)
              ·
                refine ⟨37058484583286795993068853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24705656388857863995379235 37058484583286795993068853)
                ·
                  refine ⟨3474232929683137124350205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37058484583286795993068853 3474232929683137124350205)
                  ·
                    refine ⟨1302837348631176421631327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3474232929683137124350205 1302837348631176421631327)
                    ·
                      rfl

theorem cell22_3805900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_3805900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805900 prefixEnd_3805900 := by exact prefixLift 3805900
  have htrace : WordTrace (prefixWord ++ tailWord_3805900) baseStart_3805900 baseEnd_3805900 := by
    simpa [prefixWord, tailWord_3805900, baseEnd_3805900] using wordTrace_append hprefix tailTrace_3805900
  have hstable : (prefixWord ++ tailWord_3805900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805900).length < 2 ^ (prefixWord ++ tailWord_3805900).sum := by decide
  have hdescent : baseEnd_3805900 < baseStart_3805900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805960 : List Nat := [2, 1, 3, 2, 2, 2, 1, 4, 1, 4]
def baseStart_3805960 : Nat := 118140960795 + 3805960 * 2 ^ 59
def prefixEnd_3805960 : Nat := 4983230072969 + 3 ^ 40 * 3805960 * 2
def baseEnd_3805960 : Nat := 1302857887857356265131143

theorem tailTrace_3805960 : CollatzResearch.WordTrace tailWord_3805960 prefixEnd_3805960 1302857887857356265131143 := by
  unfold tailWord_3805960
  simp only [CollatzResearch.WordTrace]
  refine ⟨69407382645832200531735667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92543176861109600708980889 69407382645832200531735667)
  ·
    refine ⟨104111073968748300797603501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69407382645832200531735667 104111073968748300797603501)
    ·
      refine ⟨39041652738280612799101313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104111073968748300797603501 39041652738280612799101313)
      ·
        refine ⟨29281239553710459599325985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39041652738280612799101313 29281239553710459599325985)
        ·
          refine ⟨21960929665282844699494489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29281239553710459599325985 21960929665282844699494489)
          ·
            refine ⟨16470697248962133524620867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21960929665282844699494489 16470697248962133524620867)
            ·
              refine ⟨24706045873443200286931301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16470697248962133524620867 24706045873443200286931301)
              ·
                refine ⟨4632383601270600053799619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24706045873443200286931301 4632383601270600053799619)
                ·
                  refine ⟨6948575401905900080699429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4632383601270600053799619 6948575401905900080699429)
                  ·
                    refine ⟨1302857887857356265131143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6948575401905900080699429 1302857887857356265131143)
                    ·
                      rfl

theorem cell22_3805960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_3805960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805960 prefixEnd_3805960 := by exact prefixLift 3805960
  have htrace : WordTrace (prefixWord ++ tailWord_3805960) baseStart_3805960 baseEnd_3805960 := by
    simpa [prefixWord, tailWord_3805960, baseEnd_3805960] using wordTrace_append hprefix tailTrace_3805960
  have hstable : (prefixWord ++ tailWord_3805960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805960).length < 2 ^ (prefixWord ++ tailWord_3805960).sum := by decide
  have hdescent : baseEnd_3805960 < baseStart_3805960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3805973 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 3, 5]
def baseStart_3805973 : Nat := 118140960795 + 3805973 * 2 ^ 59
def prefixEnd_3805973 : Nat := 4983230072969 + 3 ^ 40 * 3805973 * 2
def baseEnd_3805973 : Nat := 1302862338023028564556103

theorem tailTrace_3805973 : CollatzResearch.WordTrace tailWord_3805973 prefixEnd_3805973 1302862338023028564556103 := by
  unfold tailWord_3805973
  simp only [CollatzResearch.WordTrace]
  refine ⟨138815239440617304283694573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92543492960411536189129715 138815239440617304283694573)
  ·
    refine ⟨52055714790231489106385465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138815239440617304283694573 52055714790231489106385465)
    ·
      refine ⟨39041786092673616829789099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52055714790231489106385465 39041786092673616829789099)
      ·
        refine ⟨58562679139010425244683649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39041786092673616829789099 58562679139010425244683649)
        ·
          refine ⟨43922009354257818933512737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58562679139010425244683649 43922009354257818933512737)
          ·
            refine ⟨32941507015693364200134553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43922009354257818933512737 32941507015693364200134553)
            ·
              refine ⟨24706130261770023150100915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32941507015693364200134553 24706130261770023150100915)
              ·
                refine ⟨37059195392655034725151373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24706130261770023150100915 37059195392655034725151373)
                ·
                  refine ⟨13897198272245638021931765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37059195392655034725151373 13897198272245638021931765)
                  ·
                    refine ⟨1302862338023028564556103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13897198272245638021931765 1302862338023028564556103)
                    ·
                      rfl

theorem cell22_3805973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_3805973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3805973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3805973 prefixEnd_3805973 := by exact prefixLift 3805973
  have htrace : WordTrace (prefixWord ++ tailWord_3805973) baseStart_3805973 baseEnd_3805973 := by
    simpa [prefixWord, tailWord_3805973, baseEnd_3805973] using wordTrace_append hprefix tailTrace_3805973
  have hstable : (prefixWord ++ tailWord_3805973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3805973).length < 2 ^ (prefixWord ++ tailWord_3805973).sum := by decide
  have hdescent : baseEnd_3805973 < baseStart_3805973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3805973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806003 : List Nat := [1, 1, 1, 2, 6, 1, 1, 9]
def baseStart_3806003 : Nat := 118140960795 + 3806003 * 2 ^ 59
def prefixEnd_3806003 : Nat := 4983230072969 + 3 ^ 40 * 3806003 * 2
def baseEnd_3806003 : Nat := 144763623070679831811779

theorem tailTrace_3806003 : CollatzResearch.WordTrace tailWord_3806003 prefixEnd_3806003 144763623070679831811779 := by
  unfold tailWord_3806003
  simp only [CollatzResearch.WordTrace]
  refine ⟨138816333630508619407286663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92544222420339079604857775 138816333630508619407286663)
  ·
    refine ⟨208224500445762929110929995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138816333630508619407286663 208224500445762929110929995)
    ·
      refine ⟨312336750668644393666394993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208224500445762929110929995 312336750668644393666394993)
      ·
        refine ⟨234252563001483295249796245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312336750668644393666394993 234252563001483295249796245)
        ·
          refine ⟨10980588890694529464834199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 234252563001483295249796245 10980588890694529464834199)
          ·
            refine ⟨16470883336041794197251299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10980588890694529464834199 16470883336041794197251299)
            ·
              refine ⟨24706325004062691295876949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16470883336041794197251299 24706325004062691295876949)
              ·
                refine ⟨144763623070679831811779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24706325004062691295876949 144763623070679831811779)
                ·
                  rfl

theorem cell22_3806003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 9].length) (baseStart_3806003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806003 prefixEnd_3806003 := by exact prefixLift 3806003
  have htrace : WordTrace (prefixWord ++ tailWord_3806003) baseStart_3806003 baseEnd_3806003 := by
    simpa [prefixWord, tailWord_3806003, baseEnd_3806003] using wordTrace_append hprefix tailTrace_3806003
  have hstable : (prefixWord ++ tailWord_3806003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806003).length < 2 ^ (prefixWord ++ tailWord_3806003).sum := by decide
  have hdescent : baseEnd_3806003 < baseStart_3806003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806065 : List Nat := [1, 2, 2, 2, 1, 4, 2, 3, 5]
def baseStart_3806065 : Nat := 118140960795 + 3806065 * 2 ^ 59
def prefixEnd_3806065 : Nat := 4983230072969 + 3 ^ 40 * 3806065 * 2
def baseEnd_3806065 : Nat := 434297943834390330418607

theorem tailTrace_3806065 : CollatzResearch.WordTrace tailWord_3806065 prefixEnd_3806065 434297943834390330418607 := by
  unfold tailWord_3806065
  simp only [CollatzResearch.WordTrace]
  refine ⟨138818594956284003996043649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92545729970856002664029099 138818594956284003996043649)
  ·
    refine ⟨104113946217213002997032737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138818594956284003996043649 104113946217213002997032737)
    ·
      refine ⟨78085459662909752247774553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104113946217213002997032737 78085459662909752247774553)
      ·
        refine ⟨58564094747182314185830915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78085459662909752247774553 58564094747182314185830915)
        ·
          refine ⟨87846142120773471278746373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58564094747182314185830915 87846142120773471278746373)
          ·
            refine ⟨16471151647645025864764945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87846142120773471278746373 16471151647645025864764945)
            ·
              refine ⟨12353363735733769398573709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16471151647645025864764945 12353363735733769398573709)
              ·
                refine ⟨4632511400900163524465141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12353363735733769398573709 4632511400900163524465141)
                ·
                  refine ⟨434297943834390330418607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4632511400900163524465141 434297943834390330418607)
                  ·
                    rfl

theorem cell22_3806065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 5].length) (baseStart_3806065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806065 prefixEnd_3806065 := by exact prefixLift 3806065
  have htrace : WordTrace (prefixWord ++ tailWord_3806065) baseStart_3806065 baseEnd_3806065 := by
    simpa [prefixWord, tailWord_3806065, baseEnd_3806065] using wordTrace_append hprefix tailTrace_3806065
  have hstable : (prefixWord ++ tailWord_3806065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806065).length < 2 ^ (prefixWord ++ tailWord_3806065).sum := by decide
  have hdescent : baseEnd_3806065 < baseStart_3806065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806129 : List Nat := [1, 2, 2, 4, 3, 1, 2, 2, 1, 4]
def baseStart_3806129 : Nat := 118140960795 + 3806129 * 2 ^ 59
def prefixEnd_3806129 : Nat := 4983230072969 + 3 ^ 40 * 3806129 * 2
def baseEnd_3806129 : Nat := 1302915740011096157655625

theorem tailTrace_3806129 : CollatzResearch.WordTrace tailWord_3806129 prefixEnd_3806129 1302915740011096157655625 := by
  unfold tailWord_3806129
  simp only [CollatzResearch.WordTrace]
  refine ⟨138820929228052142926373441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92547286152034761950915627 138820929228052142926373441)
  ·
    refine ⟨104115696921039107194780081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138820929228052142926373441 104115696921039107194780081)
    ·
      refine ⟨78086772690779330396085061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104115696921039107194780081 78086772690779330396085061)
      ·
        refine ⟨14641269879521124449265949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78086772690779330396085061 14641269879521124449265949)
        ·
          refine ⟨5490476204820421668474731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14641269879521124449265949 5490476204820421668474731)
          ·
            refine ⟨8235714307230632502712097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5490476204820421668474731 8235714307230632502712097)
            ·
              refine ⟨6176785730422974377034073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8235714307230632502712097 6176785730422974377034073)
              ·
                refine ⟨4632589297817230782775555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6176785730422974377034073 4632589297817230782775555)
                ·
                  refine ⟨6948883946725846174163333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4632589297817230782775555 6948883946725846174163333)
                  ·
                    refine ⟨1302915740011096157655625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6948883946725846174163333 1302915740011096157655625)
                    ·
                      rfl

theorem cell22_3806129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_3806129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806129 prefixEnd_3806129 := by exact prefixLift 3806129
  have htrace : WordTrace (prefixWord ++ tailWord_3806129) baseStart_3806129 baseEnd_3806129 := by
    simpa [prefixWord, tailWord_3806129, baseEnd_3806129] using wordTrace_append hprefix tailTrace_3806129
  have hstable : (prefixWord ++ tailWord_3806129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806129).length < 2 ^ (prefixWord ++ tailWord_3806129).sum := by decide
  have hdescent : baseEnd_3806129 < baseStart_3806129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806142 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_3806142 : Nat := 118140960795 + 3806142 * 2 ^ 59
def prefixEnd_3806142 : Nat := 4983230072969 + 3 ^ 40 * 3806142 * 2
def baseEnd_3806142 : Nat := 1302920190176768457080585

theorem tailTrace_3806142 : CollatzResearch.WordTrace tailWord_3806142 prefixEnd_3806142 1302920190176768457080585 := by
  unfold tailWord_3806142
  simp only [CollatzResearch.WordTrace]
  refine ⟨17352675422125630768324585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92547602251336697431064453 17352675422125630768324585)
  ·
    refine ⟨13014506566594223076243439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17352675422125630768324585 13014506566594223076243439)
    ·
      refine ⟨19521759849891334614365159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13014506566594223076243439 19521759849891334614365159)
      ·
        refine ⟨29282639774837001921547739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19521759849891334614365159 29282639774837001921547739)
        ·
          refine ⟨43923959662255502882321609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29282639774837001921547739 43923959662255502882321609)
          ·
            refine ⟨32942969746691627161741207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43923959662255502882321609 32942969746691627161741207)
            ·
              refine ⟨49414454620037440742611811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32942969746691627161741207 49414454620037440742611811)
              ·
                refine ⟨74121681930056161113917717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49414454620037440742611811 74121681930056161113917717)
                ·
                  refine ⟨3474453840471382552214893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74121681930056161113917717 3474453840471382552214893)
                  ·
                    refine ⟨1302920190176768457080585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3474453840471382552214893 1302920190176768457080585)
                    ·
                      rfl

theorem cell22_3806142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_3806142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806142 prefixEnd_3806142 := by exact prefixLift 3806142
  have htrace : WordTrace (prefixWord ++ tailWord_3806142) baseStart_3806142 baseEnd_3806142 := by
    simpa [prefixWord, tailWord_3806142, baseEnd_3806142] using wordTrace_append hprefix tailTrace_3806142
  have hstable : (prefixWord ++ tailWord_3806142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806142).length < 2 ^ (prefixWord ++ tailWord_3806142).sum := by decide
  have hdescent : baseEnd_3806142 < baseStart_3806142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806144 : List Nat := [2, 1, 1, 2, 3, 5, 1, 3, 4]
def baseStart_3806144 : Nat := 118140960795 + 3806144 * 2 ^ 59
def prefixEnd_3806144 : Nat := 4983230072969 + 3 ^ 40 * 3806144 * 2
def baseEnd_3806144 : Nat := 434306958272547039510193

theorem tailTrace_3806144 : CollatzResearch.WordTrace tailWord_3806144 prefixEnd_3806144 434306958272547039510193 := by
  unfold tailWord_3806144
  simp only [CollatzResearch.WordTrace]
  refine ⟨69410738161498900244084743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92547650881998533658779657 69410738161498900244084743)
  ·
    refine ⟨104116107242248350366127115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69410738161498900244084743 104116107242248350366127115)
    ·
      refine ⟨156174160863372525549190673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104116107242248350366127115 156174160863372525549190673)
      ·
        refine ⟨117130620647529394161893005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156174160863372525549190673 117130620647529394161893005)
        ·
          refine ⟨43923982742823522810709877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117130620647529394161893005 43923982742823522810709877)
          ·
            refine ⟨4117873382139705263504051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43923982742823522810709877 4117873382139705263504051)
            ·
              refine ⟨6176810073209557895256077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4117873382139705263504051 6176810073209557895256077)
              ·
                refine ⟨2316303777453584210721029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6176810073209557895256077 2316303777453584210721029)
                ·
                  refine ⟨434306958272547039510193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2316303777453584210721029 434306958272547039510193)
                  ·
                    rfl

theorem cell22_3806144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 4].length) (baseStart_3806144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806144 prefixEnd_3806144 := by exact prefixLift 3806144
  have htrace : WordTrace (prefixWord ++ tailWord_3806144) baseStart_3806144 baseEnd_3806144 := by
    simpa [prefixWord, tailWord_3806144, baseEnd_3806144] using wordTrace_append hprefix tailTrace_3806144
  have hstable : (prefixWord ++ tailWord_3806144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806144).length < 2 ^ (prefixWord ++ tailWord_3806144).sum := by decide
  have hdescent : baseEnd_3806144 < baseStart_3806144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806155 : List Nat := [1, 1, 1, 1, 3, 7, 8]
def baseStart_3806155 : Nat := 118140960795 + 3806155 * 2 ^ 59
def prefixEnd_3806155 : Nat := 4983230072969 + 3 ^ 40 * 3806155 * 2
def baseEnd_3806155 : Nat := 48256468160831139129835

theorem tailTrace_3806155 : CollatzResearch.WordTrace tailWord_3806155 prefixEnd_3806155 48256468160831139129835 := by
  unfold tailWord_3806155
  simp only [CollatzResearch.WordTrace]
  refine ⟨138821877525957949366819919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92547918350638632911213279 138821877525957949366819919)
  ·
    refine ⟨208232816288936924050229879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138821877525957949366819919 208232816288936924050229879)
    ·
      refine ⟨312349224433405386075344819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208232816288936924050229879 312349224433405386075344819)
      ·
        refine ⟨468523836650108079113017229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312349224433405386075344819 468523836650108079113017229)
        ·
          refine ⟨175696438743790529667381461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 468523836650108079113017229 175696438743790529667381461)
          ·
            refine ⟨4117885283057590539079253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 175696438743790529667381461 4117885283057590539079253)
            ·
              refine ⟨48256468160831139129835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4117885283057590539079253 48256468160831139129835)
              ·
                rfl

theorem cell22_3806155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 8].length) (baseStart_3806155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806155 prefixEnd_3806155 := by exact prefixLift 3806155
  have htrace : WordTrace (prefixWord ++ tailWord_3806155) baseStart_3806155 baseEnd_3806155 := by
    simpa [prefixWord, tailWord_3806155, baseEnd_3806155] using wordTrace_append hprefix tailTrace_3806155
  have hstable : (prefixWord ++ tailWord_3806155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806155).length < 2 ^ (prefixWord ++ tailWord_3806155).sum := by decide
  have hdescent : baseEnd_3806155 < baseStart_3806155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806232 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 2, 5]
def baseStart_3806232 : Nat := 118140960795 + 3806232 * 2 ^ 59
def prefixEnd_3806232 : Nat := 4983230072969 + 3 ^ 40 * 3806232 * 2
def baseEnd_3806232 : Nat := 1302950999016038222330309

theorem tailTrace_3806232 : CollatzResearch.WordTrace tailWord_3806232 prefixEnd_3806232 1302950999016038222330309 := by
  unfold tailWord_3806232
  simp only [CollatzResearch.WordTrace]
  refine ⟨69412342973339495758686475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92549790631119327678248633 69412342973339495758686475)
  ·
    refine ⟨104118514460009243638029713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69412342973339495758686475 104118514460009243638029713)
    ·
      refine ⟨78088885845006932728522285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104118514460009243638029713 78088885845006932728522285)
      ·
        refine ⟨29283332191877599773195857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78088885845006932728522285 29283332191877599773195857)
        ·
          refine ⟨21962499143908199829896893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29283332191877599773195857 21962499143908199829896893)
          ·
            refine ⟨8235937178965574936211335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21962499143908199829896893 8235937178965574936211335)
            ·
              refine ⟨12353905768448362404317003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8235937178965574936211335 12353905768448362404317003)
              ·
                refine ⟨18530858652672543606475505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12353905768448362404317003 18530858652672543606475505)
                ·
                  refine ⟨13898143989504407704856629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18530858652672543606475505 13898143989504407704856629)
                  ·
                    refine ⟨1302950999016038222330309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13898143989504407704856629 1302950999016038222330309)
                    ·
                      rfl

theorem cell22_3806232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_3806232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806232 prefixEnd_3806232 := by exact prefixLift 3806232
  have htrace : WordTrace (prefixWord ++ tailWord_3806232) baseStart_3806232 baseEnd_3806232 := by
    simpa [prefixWord, tailWord_3806232, baseEnd_3806232] using wordTrace_append hprefix tailTrace_3806232
  have hstable : (prefixWord ++ tailWord_3806232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806232).length < 2 ^ (prefixWord ++ tailWord_3806232).sum := by decide
  have hdescent : baseEnd_3806232 < baseStart_3806232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806264 : List Nat := [2, 1, 2, 1, 5, 2, 1, 3, 1, 4]
def baseStart_3806264 : Nat := 118140960795 + 3806264 * 2 ^ 59
def prefixEnd_3806264 : Nat := 4983230072969 + 3 ^ 40 * 3806264 * 2
def baseEnd_3806264 : Nat := 1302961953270000805530211

theorem tailTrace_3806264 : CollatzResearch.WordTrace tailWord_3806264 prefixEnd_3806264 1302961953270000805530211 := by
  unfold tailWord_3806264
  simp only [CollatzResearch.WordTrace]
  refine ⟨69412926541281530491268923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92550568721708707321691897 69412926541281530491268923)
  ·
    refine ⟨104119389811922295736903385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69412926541281530491268923 104119389811922295736903385)
    ·
      refine ⟨78089542358941721802677539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104119389811922295736903385 78089542358941721802677539)
      ·
        refine ⟨117134313538412582704016309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78089542358941721802677539 117134313538412582704016309)
        ·
          refine ⟨10981341894226179628501529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117134313538412582704016309 10981341894226179628501529)
          ·
            refine ⟨8236006420669634721376147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10981341894226179628501529 8236006420669634721376147)
            ·
              refine ⟨12354009631004452082064221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8236006420669634721376147 12354009631004452082064221)
              ·
                refine ⟨4632753611626669530774083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12354009631004452082064221 4632753611626669530774083)
                ·
                  refine ⟨6949130417440004296161125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4632753611626669530774083 6949130417440004296161125)
                  ·
                    refine ⟨1302961953270000805530211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6949130417440004296161125 1302961953270000805530211)
                    ·
                      rfl

theorem cell22_3806264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_3806264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806264 prefixEnd_3806264 := by exact prefixLift 3806264
  have htrace : WordTrace (prefixWord ++ tailWord_3806264) baseStart_3806264 baseEnd_3806264 := by
    simpa [prefixWord, tailWord_3806264, baseEnd_3806264] using wordTrace_append hprefix tailTrace_3806264
  have hstable : (prefixWord ++ tailWord_3806264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806264).length < 2 ^ (prefixWord ++ tailWord_3806264).sum := by decide
  have hdescent : baseEnd_3806264 < baseStart_3806264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806279 : List Nat := [1, 1, 4, 1, 3, 2, 2, 4, 4]
def baseStart_3806279 : Nat := 118140960795 + 3806279 * 2 ^ 59
def prefixEnd_3806279 : Nat := 4983230072969 + 3 ^ 40 * 3806279 * 2
def baseEnd_3806279 : Nat := 434322362692181922135055

theorem tailTrace_3806279 : CollatzResearch.WordTrace tailWord_3806279 prefixEnd_3806279 434322362692181922135055 := by
  unfold tailWord_3806279
  simp only [CollatzResearch.WordTrace]
  refine ⟨138826400177508718544333891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92550933451672479029555927 138826400177508718544333891)
  ·
    refine ⟨208239600266263077816500837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138826400177508718544333891 208239600266263077816500837)
    ·
      refine ⟨39044925049924327090593907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208239600266263077816500837 39044925049924327090593907)
      ·
        refine ⟨58567387574886490635890861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39044925049924327090593907 58567387574886490635890861)
        ·
          refine ⟨21962770340582433988459073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58567387574886490635890861 21962770340582433988459073)
          ·
            refine ⟨16472077755436825491344305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21962770340582433988459073 16472077755436825491344305)
            ·
              refine ⟨12354058316577619118508229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16472077755436825491344305 12354058316577619118508229)
              ·
                refine ⟨2316385934358303584720293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12354058316577619118508229 2316385934358303584720293)
                ·
                  refine ⟨434322362692181922135055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2316385934358303584720293 434322362692181922135055)
                  ·
                    rfl

theorem cell22_3806279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 4].length) (baseStart_3806279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806279 prefixEnd_3806279 := by exact prefixLift 3806279
  have htrace : WordTrace (prefixWord ++ tailWord_3806279) baseStart_3806279 baseEnd_3806279 := by
    simpa [prefixWord, tailWord_3806279, baseEnd_3806279] using wordTrace_append hprefix tailTrace_3806279
  have hstable : (prefixWord ++ tailWord_3806279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806279).length < 2 ^ (prefixWord ++ tailWord_3806279).sum := by decide
  have hdescent : baseEnd_3806279 < baseStart_3806279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806292 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_3806292 : Nat := 118140960795 + 3806292 * 2 ^ 59
def prefixEnd_3806292 : Nat := 4983230072969 + 3 ^ 40 * 3806292 * 2
def baseEnd_3806292 : Nat := 1302971538242218065830125

theorem tailTrace_3806292 : CollatzResearch.WordTrace tailWord_3806292 prefixEnd_3806292 1302971538242218065830125 := by
  unfold tailWord_3806292
  simp only [CollatzResearch.WordTrace]
  refine ⟨69413437163230810882278565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92551249550974414509704753 69413437163230810882278565)
  ·
    refine ⟨13015019468105777040427231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69413437163230810882278565 13015019468105777040427231)
    ·
      refine ⟨19522529202158665560640847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13015019468105777040427231 19522529202158665560640847)
      ·
        refine ⟨29283793803237998340961271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19522529202158665560640847 29283793803237998340961271)
        ·
          refine ⟨43925690704856997511441907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29283793803237998340961271 43925690704856997511441907)
          ·
            refine ⟨65888536057285496267162861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43925690704856997511441907 65888536057285496267162861)
            ·
              refine ⟨24708201021482061100186073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65888536057285496267162861 24708201021482061100186073)
              ·
                refine ⟨18531150766111545825139555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24708201021482061100186073 18531150766111545825139555)
                ·
                  refine ⟨27796726149167318737709333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18531150766111545825139555 27796726149167318737709333)
                  ·
                    refine ⟨1302971538242218065830125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27796726149167318737709333 1302971538242218065830125)
                    ·
                      rfl

theorem cell22_3806292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_3806292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806292 prefixEnd_3806292 := by exact prefixLift 3806292
  have htrace : WordTrace (prefixWord ++ tailWord_3806292) baseStart_3806292 baseEnd_3806292 := by
    simpa [prefixWord, tailWord_3806292, baseEnd_3806292] using wordTrace_append hprefix tailTrace_3806292
  have hstable : (prefixWord ++ tailWord_3806292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806292).length < 2 ^ (prefixWord ++ tailWord_3806292).sum := by decide
  have hdescent : baseEnd_3806292 < baseStart_3806292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806401 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3806401 : Nat := 118140960795 + 3806401 * 2 ^ 59
def prefixEnd_3806401 : Nat := 4983230072969 + 3 ^ 40 * 3806401 * 2
def baseEnd_3806401 : Nat := 1303008851169778114854791

theorem tailTrace_3806401 : CollatzResearch.WordTrace tailWord_3806401 prefixEnd_3806401 1303008851169778114854791 := by
  unfold tailWord_3806401
  simp only [CollatzResearch.WordTrace]
  refine ⟨138830849883066733380275057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92553899922044488920183371 138830849883066733380275057)
  ·
    refine ⟨104123137412300050035206293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138830849883066733380275057 104123137412300050035206293)
    ·
      refine ⟨4880772066201564845400295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104123137412300050035206293 4880772066201564845400295)
      ·
        refine ⟨7321158099302347268100443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4880772066201564845400295 7321158099302347268100443)
        ·
          refine ⟨10981737148953520902150665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7321158099302347268100443 10981737148953520902150665)
          ·
            refine ⟨8236302861715140676612999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10981737148953520902150665 8236302861715140676612999)
            ·
              refine ⟨12354454292572711014919499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8236302861715140676612999 12354454292572711014919499)
              ·
                refine ⟨18531681438859066522379249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12354454292572711014919499 18531681438859066522379249)
                ·
                  refine ⟨13898761079144299891784437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18531681438859066522379249 13898761079144299891784437)
                  ·
                    refine ⟨1303008851169778114854791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13898761079144299891784437 1303008851169778114854791)
                    ·
                      rfl

theorem cell22_3806401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3806401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806401 prefixEnd_3806401 := by exact prefixLift 3806401
  have htrace : WordTrace (prefixWord ++ tailWord_3806401) baseStart_3806401 baseEnd_3806401 := by
    simpa [prefixWord, tailWord_3806401, baseEnd_3806401] using wordTrace_append hprefix tailTrace_3806401
  have hstable : (prefixWord ++ tailWord_3806401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806401).length < 2 ^ (prefixWord ++ tailWord_3806401).sum := by decide
  have hdescent : baseEnd_3806401 < baseStart_3806401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806433 : List Nat := [1, 2, 3, 1, 3, 4, 2, 1, 1, 4]
def baseStart_3806433 : Nat := 118140960795 + 3806433 * 2 ^ 59
def prefixEnd_3806433 : Nat := 4983230072969 + 3 ^ 40 * 3806433 * 2
def baseEnd_3806433 : Nat := 1303019805423740698054693

theorem tailTrace_3806433 : CollatzResearch.WordTrace tailWord_3806433 prefixEnd_3806433 1303019805423740698054693 := by
  unfold tailWord_3806433
  simp only [CollatzResearch.WordTrace]
  refine ⟨138832017018950802845439953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92554678012633868563626635 138832017018950802845439953)
  ·
    refine ⟨104124012764213102134079965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138832017018950802845439953 104124012764213102134079965)
    ·
      refine ⟨39046504786579913300279987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104124012764213102134079965 39046504786579913300279987)
      ·
        refine ⟨58569757179869869950419981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39046504786579913300279987 58569757179869869950419981)
        ·
          refine ⟨21963658942451201231407493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58569757179869869950419981 21963658942451201231407493)
          ·
            refine ⟨4118186051709600230888905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21963658942451201231407493 4118186051709600230888905)
            ·
              refine ⟨3088639538782200173166679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4118186051709600230888905 3088639538782200173166679)
              ·
                refine ⟨4632959308173300259750019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3088639538782200173166679 4632959308173300259750019)
                ·
                  refine ⟨6949438962259950389625029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4632959308173300259750019 6949438962259950389625029)
                  ·
                    refine ⟨1303019805423740698054693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6949438962259950389625029 1303019805423740698054693)
                    ·
                      rfl

theorem cell22_3806433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_3806433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806433 prefixEnd_3806433 := by exact prefixLift 3806433
  have htrace : WordTrace (prefixWord ++ tailWord_3806433) baseStart_3806433 baseEnd_3806433 := by
    simpa [prefixWord, tailWord_3806433, baseEnd_3806433] using wordTrace_append hprefix tailTrace_3806433
  have hstable : (prefixWord ++ tailWord_3806433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806433).length < 2 ^ (prefixWord ++ tailWord_3806433).sum := by decide
  have hdescent : baseEnd_3806433 < baseStart_3806433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806463 : List Nat := [1, 1, 2, 2, 1, 6, 3, 1, 2, 3]
def baseStart_3806463 : Nat := 118140960795 + 3806463 * 2 ^ 59
def prefixEnd_3806463 : Nat := 4983230072969 + 3 ^ 40 * 3806463 * 2
def baseEnd_3806463 : Nat := 1303030075036830619804601

theorem tailTrace_3806463 : CollatzResearch.WordTrace tailWord_3806463 prefixEnd_3806463 1303030075036830619804601 := by
  unfold tailWord_3806463
  simp only [CollatzResearch.WordTrace]
  refine ⟨138833111208842117969032043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92555407472561411979354695 138833111208842117969032043)
  ·
    refine ⟨208249666813263176953548065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138833111208842117969032043 208249666813263176953548065)
    ·
      refine ⟨156187250109947382715161049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208249666813263176953548065 156187250109947382715161049)
      ·
        refine ⟨117140437582460537036370787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156187250109947382715161049 117140437582460537036370787)
        ·
          refine ⟨175710656373690805554556181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117140437582460537036370787 175710656373690805554556181)
          ·
            refine ⟨8236437017516756510369821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 175710656373690805554556181 8236437017516756510369821)
            ·
              refine ⟨3088663881568783691388683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8236437017516756510369821 3088663881568783691388683)
              ·
                refine ⟨4632995822353175537083025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3088663881568783691388683 4632995822353175537083025)
                ·
                  refine ⟨3474746866764881652812269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4632995822353175537083025 3474746866764881652812269)
                  ·
                    refine ⟨1303030075036830619804601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3474746866764881652812269 1303030075036830619804601)
                    ·
                      rfl

theorem cell22_3806463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 2, 3].length) (baseStart_3806463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806463 prefixEnd_3806463 := by exact prefixLift 3806463
  have htrace : WordTrace (prefixWord ++ tailWord_3806463) baseStart_3806463 baseEnd_3806463 := by
    simpa [prefixWord, tailWord_3806463, baseEnd_3806463] using wordTrace_append hprefix tailTrace_3806463
  have hstable : (prefixWord ++ tailWord_3806463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806463).length < 2 ^ (prefixWord ++ tailWord_3806463).sum := by decide
  have hdescent : baseEnd_3806463 < baseStart_3806463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806476 : List Nat := [2, 2, 1, 2, 2, 5, 2, 6]
def baseStart_3806476 : Nat := 118140960795 + 3806476 * 2 ^ 59
def prefixEnd_3806476 : Nat := 4983230072969 + 3 ^ 40 * 3806476 * 2
def baseEnd_3806476 : Nat := 144781613911389213247729

theorem tailTrace_3806476 : CollatzResearch.WordTrace tailWord_3806476 prefixEnd_3806476 144781613911389213247729 := by
  unfold tailWord_3806476
  simp only [CollatzResearch.WordTrace]
  refine ⟨69416792678897510594627641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92555723571863347459503521 69416792678897510594627641)
  ·
    refine ⟨52062594509173132945970731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69416792678897510594627641 52062594509173132945970731)
    ·
      refine ⟨78093891763759699418956097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52062594509173132945970731 78093891763759699418956097)
      ·
        refine ⟨58570418822819774564217073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78093891763759699418956097 58570418822819774564217073)
        ·
          refine ⟨43927814117114830923162805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58570418822819774564217073 43927814117114830923162805)
          ·
            refine ⟨4118232573479515399046513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43927814117114830923162805 4118232573479515399046513)
            ·
              refine ⟨3088674430109636549284885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4118232573479515399046513 3088674430109636549284885)
              ·
                refine ⟨144781613911389213247729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3088674430109636549284885 144781613911389213247729)
                ·
                  rfl

theorem cell22_3806476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 6].length) (baseStart_3806476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806476 prefixEnd_3806476 := by exact prefixLift 3806476
  have htrace : WordTrace (prefixWord ++ tailWord_3806476) baseStart_3806476 baseEnd_3806476 := by
    simpa [prefixWord, tailWord_3806476, baseEnd_3806476] using wordTrace_append hprefix tailTrace_3806476
  have hstable : (prefixWord ++ tailWord_3806476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806476).length < 2 ^ (prefixWord ++ tailWord_3806476).sum := by decide
  have hdescent : baseEnd_3806476 < baseStart_3806476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806482 : List Nat := [3, 2, 4, 2, 1, 2, 1, 3, 4]
def baseStart_3806482 : Nat := 118140960795 + 3806482 * 2 ^ 59
def prefixEnd_3806482 : Nat := 4983230072969 + 3 ^ 40 * 3806482 * 2
def baseEnd_3806482 : Nat := 434345526375040301193181

theorem tailTrace_3806482 : CollatzResearch.WordTrace tailWord_3806482 prefixEnd_3806482 434345526375040301193181 := by
  unfold tailWord_3806482
  simp only [CollatzResearch.WordTrace]
  refine ⟨34708451048943321053493425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92555869463848856142649133 34708451048943321053493425)
  ·
    refine ⟨26031338286707490790120069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34708451048943321053493425 26031338286707490790120069)
    ·
      refine ⟨4880875928757654523147513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26031338286707490790120069 4880875928757654523147513)
      ·
        refine ⟨3660656946568240892360635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4880875928757654523147513 3660656946568240892360635)
        ·
          refine ⟨5490985419852361338540953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3660656946568240892360635 5490985419852361338540953)
          ·
            refine ⟨4118239064889271003905715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5490985419852361338540953 4118239064889271003905715)
            ·
              refine ⟨6177358597333906505858573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4118239064889271003905715 6177358597333906505858573)
              ·
                refine ⟨2316509474000214939696965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6177358597333906505858573 2316509474000214939696965)
                ·
                  refine ⟨434345526375040301193181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2316509474000214939696965 434345526375040301193181)
                  ·
                    rfl

theorem cell22_3806482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_3806482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806482 prefixEnd_3806482 := by exact prefixLift 3806482
  have htrace : WordTrace (prefixWord ++ tailWord_3806482) baseStart_3806482 baseEnd_3806482 := by
    simpa [prefixWord, tailWord_3806482, baseEnd_3806482] using wordTrace_append hprefix tailTrace_3806482
  have hstable : (prefixWord ++ tailWord_3806482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806482).length < 2 ^ (prefixWord ++ tailWord_3806482).sum := by decide
  have hdescent : baseEnd_3806482 < baseStart_3806482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806596 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_3806596 : Nat := 118140960795 + 3806596 * 2 ^ 59
def prefixEnd_3806596 : Nat := 4983230072969 + 3 ^ 40 * 3806596 * 2
def baseEnd_3806596 : Nat := 1303075603654862606229193

theorem tailTrace_3806596 : CollatzResearch.WordTrace tailWord_3806596 prefixEnd_3806596 1303075603654862606229193 := by
  unfold tailWord_3806596
  simp only [CollatzResearch.WordTrace]
  refine ⟨69418981058680140841811821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92558641411573521122415761 69418981058680140841811821)
  ·
    refine ⟨26032117897005052815679433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69418981058680140841811821 26032117897005052815679433)
    ·
      refine ⟨19524088422753789611759575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26032117897005052815679433 19524088422753789611759575)
      ·
        refine ⟨29286132634130684417639363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19524088422753789611759575 29286132634130684417639363)
        ·
          refine ⟨43929198951196026626459045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29286132634130684417639363 43929198951196026626459045)
          ·
            refine ⟨8236724803349254992461071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43929198951196026626459045 8236724803349254992461071)
            ·
              refine ⟨12355087205023882488691607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8236724803349254992461071 12355087205023882488691607)
              ·
                refine ⟨18532630807535823733037411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12355087205023882488691607 18532630807535823733037411)
                ·
                  refine ⟨27798946211303735599556117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18532630807535823733037411 27798946211303735599556117)
                  ·
                    refine ⟨1303075603654862606229193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27798946211303735599556117 1303075603654862606229193)
                    ·
                      rfl

theorem cell22_3806596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_3806596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806596 prefixEnd_3806596 := by exact prefixLift 3806596
  have htrace : WordTrace (prefixWord ++ tailWord_3806596) baseStart_3806596 baseEnd_3806596 := by
    simpa [prefixWord, tailWord_3806596, baseEnd_3806596] using wordTrace_append hprefix tailTrace_3806596
  have hstable : (prefixWord ++ tailWord_3806596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806596).length < 2 ^ (prefixWord ++ tailWord_3806596).sum := by decide
  have hdescent : baseEnd_3806596 < baseStart_3806596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806632 : List Nat := [2, 1, 6, 1, 3, 1, 1, 1, 1, 5]
def baseStart_3806632 : Nat := 118140960795 + 3806632 * 2 ^ 59
def prefixEnd_3806632 : Nat := 4983230072969 + 3 ^ 40 * 3806632 * 2
def baseEnd_3806632 : Nat := 1303087927190570512329083

theorem tailTrace_3806632 : CollatzResearch.WordTrace tailWord_3806632 prefixEnd_3806632 1303087927190570512329083 := by
  unfold tailWord_3806632
  simp only [CollatzResearch.WordTrace]
  refine ⟨69419637572614929915967075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92559516763486573221289433 69419637572614929915967075)
  ·
    refine ⟨104129456358922394873950613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69419637572614929915967075 104129456358922394873950613)
    ·
      refine ⟨4881068266824487259716435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104129456358922394873950613 4881068266824487259716435)
      ·
        refine ⟨7321602400236730889574653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4881068266824487259716435 7321602400236730889574653)
        ·
          refine ⟨2745600900088774083590495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7321602400236730889574653 2745600900088774083590495)
          ·
            refine ⟨4118401350133161125385743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2745600900088774083590495 4118401350133161125385743)
            ·
              refine ⟨6177602025199741688078615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4118401350133161125385743 6177602025199741688078615)
              ·
                refine ⟨9266403037799612532117923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6177602025199741688078615 9266403037799612532117923)
                ·
                  refine ⟨13899604556699418798176885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9266403037799612532117923 13899604556699418798176885)
                  ·
                    refine ⟨1303087927190570512329083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13899604556699418798176885 1303087927190570512329083)
                    ·
                      rfl

theorem cell22_3806632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_3806632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806632 prefixEnd_3806632 := by exact prefixLift 3806632
  have htrace : WordTrace (prefixWord ++ tailWord_3806632) baseStart_3806632 baseEnd_3806632 := by
    simpa [prefixWord, tailWord_3806632, baseEnd_3806632] using wordTrace_append hprefix tailTrace_3806632
  have hstable : (prefixWord ++ tailWord_3806632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806632).length < 2 ^ (prefixWord ++ tailWord_3806632).sum := by decide
  have hdescent : baseEnd_3806632 < baseStart_3806632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806677 : List Nat := [1, 3, 2, 3, 1, 1, 5, 2, 1, 3]
def baseStart_3806677 : Nat := 118140960795 + 3806677 * 2 ^ 59
def prefixEnd_3806677 : Nat := 4983230072969 + 3 ^ 40 * 3806677 * 2
def baseEnd_3806677 : Nat := 1303103331610205394953945

theorem tailTrace_3806677 : CollatzResearch.WordTrace tailWord_3806677 prefixEnd_3806677 1303103331610205394953945 := by
  unfold tailWord_3806677
  simp only [CollatzResearch.WordTrace]
  refine ⟨138840916430066832517322285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92560610953377888344881523 138840916430066832517322285)
  ·
    refine ⟨52065343661275062193995857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138840916430066832517322285 52065343661275062193995857)
    ·
      refine ⟨39049007745956296645496893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52065343661275062193995857 39049007745956296645496893)
      ·
        refine ⟨14643377904733611242061335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39049007745956296645496893 14643377904733611242061335)
        ·
          refine ⟨21965066857100416863092003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14643377904733611242061335 21965066857100416863092003)
          ·
            refine ⟨32947600285650625294638005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21965066857100416863092003 32947600285650625294638005)
            ·
              refine ⟨3088837526779746121372313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32947600285650625294638005 3088837526779746121372313)
              ·
                refine ⟨2316628145084809591029235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3088837526779746121372313 2316628145084809591029235)
                ·
                  refine ⟨3474942217627214386543853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2316628145084809591029235 3474942217627214386543853)
                  ·
                    refine ⟨1303103331610205394953945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3474942217627214386543853 1303103331610205394953945)
                    ·
                      rfl

theorem cell22_3806677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_3806677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806677 prefixEnd_3806677 := by exact prefixLift 3806677
  have htrace : WordTrace (prefixWord ++ tailWord_3806677) baseStart_3806677 baseEnd_3806677 := by
    simpa [prefixWord, tailWord_3806677, baseEnd_3806677] using wordTrace_append hprefix tailTrace_3806677
  have hstable : (prefixWord ++ tailWord_3806677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806677).length < 2 ^ (prefixWord ++ tailWord_3806677).sum := by decide
  have hdescent : baseEnd_3806677 < baseStart_3806677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806703 : List Nat := [1, 1, 2, 1, 4, 1, 5, 2, 1, 4]
def baseStart_3806703 : Nat := 118140960795 + 3806703 * 2 ^ 59
def prefixEnd_3806703 : Nat := 4983230072969 + 3 ^ 40 * 3806703 * 2
def baseEnd_3806703 : Nat := 1303112231941549993803865

theorem tailTrace_3806703 : CollatzResearch.WordTrace tailWord_3806703 prefixEnd_3806703 1303112231941549993803865 := by
  unfold tailWord_3806703
  simp only [CollatzResearch.WordTrace]
  refine ⟨138841864727972638957768763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92561243151981759305179175 138841864727972638957768763)
  ·
    refine ⟨208262797091958958436653145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138841864727972638957768763 208262797091958958436653145)
    ·
      refine ⟨156197097818969218827489859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208262797091958958436653145 156197097818969218827489859)
      ·
        refine ⟨234295646728453828241234789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156197097818969218827489859 234295646728453828241234789)
        ·
          refine ⟨43930433761585092795231523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234295646728453828241234789 43930433761585092795231523)
          ·
            refine ⟨65895650642377639192847285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43930433761585092795231523 65895650642377639192847285)
            ·
              refine ⟨6177717247722903674329433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65895650642377639192847285 6177717247722903674329433)
              ·
                refine ⟨4633287935792177755747075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6177717247722903674329433 4633287935792177755747075)
                ·
                  refine ⟨6949931903688266633620613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4633287935792177755747075 6949931903688266633620613)
                  ·
                    refine ⟨1303112231941549993803865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6949931903688266633620613 1303112231941549993803865)
                    ·
                      rfl

theorem cell22_3806703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 4].length) (baseStart_3806703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806703 prefixEnd_3806703 := by exact prefixLift 3806703
  have htrace : WordTrace (prefixWord ++ tailWord_3806703) baseStart_3806703 baseEnd_3806703 := by
    simpa [prefixWord, tailWord_3806703, baseEnd_3806703] using wordTrace_append hprefix tailTrace_3806703
  have hstable : (prefixWord ++ tailWord_3806703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806703).length < 2 ^ (prefixWord ++ tailWord_3806703).sum := by decide
  have hdescent : baseEnd_3806703 < baseStart_3806703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806716 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 3, 5]
def baseStart_3806716 : Nat := 118140960795 + 3806716 * 2 ^ 59
def prefixEnd_3806716 : Nat := 4983230072969 + 3 ^ 40 * 3806716 * 2
def baseEnd_3806716 : Nat := 1303116682107222293228825

theorem tailTrace_3806716 : CollatzResearch.WordTrace tailWord_3806716 prefixEnd_3806716 1303116682107222293228825 := by
  unfold tailWord_3806716
  simp only [CollatzResearch.WordTrace]
  refine ⟨69421169438462771088996001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92561559251283694785328001 69421169438462771088996001)
  ·
    refine ⟨52065877078847078316747001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69421169438462771088996001 52065877078847078316747001)
    ·
      refine ⟨39049407809135308737560251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52065877078847078316747001 39049407809135308737560251)
      ·
        refine ⟨58574111713702963106340377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39049407809135308737560251 58574111713702963106340377)
        ·
          refine ⟨43930583785277222329755283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58574111713702963106340377 43930583785277222329755283)
          ·
            refine ⟨65895875677915833494632925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43930583785277222329755283 65895875677915833494632925)
            ·
              refine ⟨24710953379218437560487347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65895875677915833494632925 24710953379218437560487347)
              ·
                refine ⟨37066430068827656340731021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24710953379218437560487347 37066430068827656340731021)
                ·
                  refine ⟨13899911275810371127774133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37066430068827656340731021 13899911275810371127774133)
                  ·
                    refine ⟨1303116682107222293228825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13899911275810371127774133 1303116682107222293228825)
                    ·
                      rfl

theorem cell22_3806716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_3806716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806716 prefixEnd_3806716 := by exact prefixLift 3806716
  have htrace : WordTrace (prefixWord ++ tailWord_3806716) baseStart_3806716 baseEnd_3806716 := by
    simpa [prefixWord, tailWord_3806716, baseEnd_3806716] using wordTrace_append hprefix tailTrace_3806716
  have hstable : (prefixWord ++ tailWord_3806716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806716).length < 2 ^ (prefixWord ++ tailWord_3806716).sum := by decide
  have hdescent : baseEnd_3806716 < baseStart_3806716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806778 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 5, 3]
def baseStart_3806778 : Nat := 118140960795 + 3806778 * 2 ^ 59
def prefixEnd_3806778 : Nat := 4983230072969 + 3 ^ 40 * 3806778 * 2
def baseEnd_3806778 : Nat := 1303137905974274798178635

theorem tailTrace_3806778 : CollatzResearch.WordTrace tailWord_3806778 prefixEnd_3806778 1303137905974274798178635 := by
  unfold tailWord_3806778
  simp only [CollatzResearch.WordTrace]
  refine ⟨34711150050675231691687247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92563066801800617844499325 34711150050675231691687247)
  ·
    refine ⟨52066725076012847537530871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34711150050675231691687247 52066725076012847537530871)
    ·
      refine ⟨78100087614019271306296307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52066725076012847537530871 78100087614019271306296307)
      ·
        refine ⟨117150131421028906959444461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78100087614019271306296307 117150131421028906959444461)
        ·
          refine ⟨43931299282885840109791673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117150131421028906959444461 43931299282885840109791673)
          ·
            refine ⟨32948474462164380082343755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43931299282885840109791673 32948474462164380082343755)
            ·
              refine ⟨49422711693246570123515633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32948474462164380082343755 49422711693246570123515633)
              ·
                refine ⟨37067033769934927592636725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49422711693246570123515633 37067033769934927592636725)
                ·
                  refine ⟨3475034415931399461809693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37067033769934927592636725 3475034415931399461809693)
                  ·
                    refine ⟨1303137905974274798178635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3475034415931399461809693 1303137905974274798178635)
                    ·
                      rfl

theorem cell22_3806778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_3806778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806778 prefixEnd_3806778 := by exact prefixLift 3806778
  have htrace : WordTrace (prefixWord ++ tailWord_3806778) baseStart_3806778 baseEnd_3806778 := by
    simpa [prefixWord, tailWord_3806778, baseEnd_3806778] using wordTrace_append hprefix tailTrace_3806778
  have hstable : (prefixWord ++ tailWord_3806778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806778).length < 2 ^ (prefixWord ++ tailWord_3806778).sum := by decide
  have hdescent : baseEnd_3806778 < baseStart_3806778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806872 : List Nat := [2, 1, 2, 4, 1, 4, 1, 2, 1, 4]
def baseStart_3806872 : Nat := 118140960795 + 3806872 * 2 ^ 59
def prefixEnd_3806872 : Nat := 4983230072969 + 3 ^ 40 * 3806872 * 2
def baseEnd_3806872 : Nat := 1303170084095289886328347

theorem tailTrace_3806872 : CollatzResearch.WordTrace tailWord_3806872 prefixEnd_3806872 1303170084095289886328347 := by
  unfold tailWord_3806872
  simp only [CollatzResearch.WordTrace]
  refine ⟨69424014332180190410335435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92565352442906920547113913 69424014332180190410335435)
  ·
    refine ⟨104136021498270285615503153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69424014332180190410335435 104136021498270285615503153)
    ·
      refine ⟨78102016123702714211627365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104136021498270285615503153 78102016123702714211627365)
      ·
        refine ⟨14644128023194258914680131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78102016123702714211627365 14644128023194258914680131)
        ·
          refine ⟨21966192034791388372020197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14644128023194258914680131 21966192034791388372020197)
          ·
            refine ⟨4118661006523385319753787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21966192034791388372020197 4118661006523385319753787)
            ·
              refine ⟨6177991509785077979630681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4118661006523385319753787 6177991509785077979630681)
              ·
                refine ⟨4633493632338808484723011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6177991509785077979630681 4633493632338808484723011)
                ·
                  refine ⟨6950240448508212727084517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4633493632338808484723011 6950240448508212727084517)
                  ·
                    refine ⟨1303170084095289886328347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6950240448508212727084517 1303170084095289886328347)
                    ·
                      rfl

theorem cell22_3806872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_3806872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806872 prefixEnd_3806872 := by exact prefixLift 3806872
  have htrace : WordTrace (prefixWord ++ tailWord_3806872) baseStart_3806872 baseEnd_3806872 := by
    simpa [prefixWord, tailWord_3806872, baseEnd_3806872] using wordTrace_append hprefix tailTrace_3806872
  have hstable : (prefixWord ++ tailWord_3806872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806872).length < 2 ^ (prefixWord ++ tailWord_3806872).sum := by decide
  have hdescent : baseEnd_3806872 < baseStart_3806872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806932 : List Nat := [2, 4, 1, 3, 1, 2, 3, 6]
def baseStart_3806932 : Nat := 118140960795 + 3806932 * 2 ^ 59
def prefixEnd_3806932 : Nat := 4983230072969 + 3 ^ 40 * 3806932 * 2
def baseEnd_3806932 : Nat := 144798958146829969980907

theorem tailTrace_3806932 : CollatzResearch.WordTrace tailWord_3806932 prefixEnd_3806932 144798958146829969980907 := by
  unfold tailWord_3806932
  simp only [CollatzResearch.WordTrace]
  refine ⟨69425108522071505533927525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92566811362762007378570033 69425108522071505533927525)
  ·
    refine ⟨13017207847888407287611411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69425108522071505533927525 13017207847888407287611411)
    ·
      refine ⟨19525811771832610931417117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13017207847888407287611411 19525811771832610931417117)
      ·
        refine ⟨7322179414437229099281419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19525811771832610931417117 7322179414437229099281419)
        ·
          refine ⟨10983269121655843648922129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7322179414437229099281419 10983269121655843648922129)
          ·
            refine ⟨8237451841241882736691597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10983269121655843648922129 8237451841241882736691597)
            ·
              refine ⟨3089044440465706026259349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8237451841241882736691597 3089044440465706026259349)
              ·
                refine ⟨144798958146829969980907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3089044440465706026259349 144798958146829969980907)
                ·
                  rfl

theorem cell22_3806932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 6].length) (baseStart_3806932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806932 prefixEnd_3806932 := by exact prefixLift 3806932
  have htrace : WordTrace (prefixWord ++ tailWord_3806932) baseStart_3806932 baseEnd_3806932 := by
    simpa [prefixWord, tailWord_3806932, baseEnd_3806932] using wordTrace_append hprefix tailTrace_3806932
  have hstable : (prefixWord ++ tailWord_3806932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806932).length < 2 ^ (prefixWord ++ tailWord_3806932).sum := by decide
  have hdescent : baseEnd_3806932 < baseStart_3806932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806934 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_3806934 : Nat := 118140960795 + 3806934 * 2 ^ 59
def prefixEnd_3806934 : Nat := 4983230072969 + 3 ^ 40 * 3806934 * 2
def baseEnd_3806934 : Nat := 1303191307962342391278157

theorem tailTrace_3806934 : CollatzResearch.WordTrace tailWord_3806934 prefixEnd_3806934 1303191307962342391278157 := by
  unfold tailWord_3806934
  simp only [CollatzResearch.WordTrace]
  refine ⟨8678143124383485338089241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92566859993423843606285237 8678143124383485338089241)
  ·
    refine ⟨6508607343287614003566931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8678143124383485338089241 6508607343287614003566931)
    ·
      refine ⟨9762911014931421005350397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6508607343287614003566931 9762911014931421005350397)
      ·
        refine ⟨3661091630599282877006399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9762911014931421005350397 3661091630599282877006399)
        ·
          refine ⟨5491637445898924315509599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3661091630599282877006399 5491637445898924315509599)
          ·
            refine ⟨8237456168848386473264399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5491637445898924315509599 8237456168848386473264399)
            ·
              refine ⟨12356184253272579709896599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8237456168848386473264399 12356184253272579709896599)
              ·
                refine ⟨18534276379908869564844899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12356184253272579709896599 18534276379908869564844899)
                ·
                  refine ⟨27801414569863304347267349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18534276379908869564844899 27801414569863304347267349)
                  ·
                    refine ⟨1303191307962342391278157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27801414569863304347267349 1303191307962342391278157)
                    ·
                      rfl

theorem cell22_3806934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_3806934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806934 prefixEnd_3806934 := by exact prefixLift 3806934
  have htrace : WordTrace (prefixWord ++ tailWord_3806934) baseStart_3806934 baseEnd_3806934 := by
    simpa [prefixWord, tailWord_3806934, baseEnd_3806934] using wordTrace_append hprefix tailTrace_3806934
  have hstable : (prefixWord ++ tailWord_3806934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806934).length < 2 ^ (prefixWord ++ tailWord_3806934).sum := by decide
  have hdescent : baseEnd_3806934 < baseStart_3806934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806943 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 7]
def baseStart_3806943 : Nat := 118140960795 + 3806943 * 2 ^ 59
def prefixEnd_3806943 : Nat := 4983230072969 + 3 ^ 40 * 3806943 * 2
def baseEnd_3806943 : Nat := 434398129615423122601043

theorem tailTrace_3806943 : CollatzResearch.WordTrace tailWord_3806943 prefixEnd_3806943 434398129615423122601043 := by
  unfold tailWord_3806943
  simp only [CollatzResearch.WordTrace]
  refine ⟨138850618247103159946505483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92567078831402106631003655 138850618247103159946505483)
  ·
    refine ⟨208275927370654739919758225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138850618247103159946505483 208275927370654739919758225)
    ·
      refine ⟨156206945527991054939818669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208275927370654739919758225 156206945527991054939818669)
      ·
        refine ⟨58577604572996645602432001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156206945527991054939818669 58577604572996645602432001)
        ·
          refine ⟨43933203429747484201824001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58577604572996645602432001 43933203429747484201824001)
          ·
            refine ⟨32949902572310613151368001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43933203429747484201824001 32949902572310613151368001)
            ·
              refine ⟨24712426929232959863526001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32949902572310613151368001 24712426929232959863526001)
              ·
                refine ⟨18534320196924719897644501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24712426929232959863526001 18534320196924719897644501)
                ·
                  refine ⟨434398129615423122601043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18534320196924719897644501 434398129615423122601043)
                  ·
                    rfl

theorem cell22_3806943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 7].length) (baseStart_3806943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806943 prefixEnd_3806943 := by exact prefixLift 3806943
  have htrace : WordTrace (prefixWord ++ tailWord_3806943) baseStart_3806943 baseEnd_3806943 := by
    simpa [prefixWord, tailWord_3806943, baseEnd_3806943] using wordTrace_append hprefix tailTrace_3806943
  have hstable : (prefixWord ++ tailWord_3806943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806943).length < 2 ^ (prefixWord ++ tailWord_3806943).sum := by decide
  have hdescent : baseEnd_3806943 < baseStart_3806943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806973 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_3806973 : Nat := 118140960795 + 3806973 * 2 ^ 59
def prefixEnd_3806973 : Nat := 4983230072969 + 3 ^ 40 * 3806973 * 2
def baseEnd_3806973 : Nat := 1303204658459359289553037

theorem tailTrace_3806973 : CollatzResearch.WordTrace tailWord_3806973 prefixEnd_3806973 1303204658459359289553037 := by
  unfold tailWord_3806973
  simp only [CollatzResearch.WordTrace]
  refine ⟨138851712436994475070097573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92567808291329650046731715 138851712436994475070097573)
  ·
    refine ⟨26034696081936464075643295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138851712436994475070097573 26034696081936464075643295)
    ·
      refine ⟨39052044122904696113464943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26034696081936464075643295 39052044122904696113464943)
      ·
        refine ⟨58578066184357044170197415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39052044122904696113464943 58578066184357044170197415)
        ·
          refine ⟨87867099276535566255296123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58578066184357044170197415 87867099276535566255296123)
          ·
            refine ⟨131800648914803349382944185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87867099276535566255296123 131800648914803349382944185)
            ·
              refine ⟨98850486686102512037208139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131800648914803349382944185 98850486686102512037208139)
              ·
                refine ⟨148275730029153768055812209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98850486686102512037208139 148275730029153768055812209)
                ·
                  refine ⟨111206797521865326041859157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148275730029153768055812209 111206797521865326041859157)
                  ·
                    refine ⟨1303204658459359289553037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111206797521865326041859157 1303204658459359289553037)
                    ·
                      rfl

theorem cell22_3806973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_3806973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806973 prefixEnd_3806973 := by exact prefixLift 3806973
  have htrace : WordTrace (prefixWord ++ tailWord_3806973) baseStart_3806973 baseEnd_3806973 := by
    simpa [prefixWord, tailWord_3806973, baseEnd_3806973] using wordTrace_append hprefix tailTrace_3806973
  have hstable : (prefixWord ++ tailWord_3806973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806973).length < 2 ^ (prefixWord ++ tailWord_3806973).sum := by decide
  have hdescent : baseEnd_3806973 < baseStart_3806973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3806990 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_3806990 : Nat := 118140960795 + 3806990 * 2 ^ 59
def prefixEnd_3806990 : Nat := 4983230072969 + 3 ^ 40 * 3806990 * 2
def baseEnd_3806990 : Nat := 1303210477906776911877985

theorem tailTrace_3806990 : CollatzResearch.WordTrace tailWord_3806990 prefixEnd_3806990 1303210477906776911877985 := by
  unfold tailWord_3806990
  simp only [CollatzResearch.WordTrace]
  refine ⟨17356541559741610871683303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92568221651955257982310949 17356541559741610871683303)
  ·
    refine ⟨26034812339612416307524955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17356541559741610871683303 26034812339612416307524955)
    ·
      refine ⟨39052218509418624461287433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26034812339612416307524955 39052218509418624461287433)
      ·
        refine ⟨29289163882063968345965575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39052218509418624461287433 29289163882063968345965575)
        ·
          refine ⟨43933745823095952518948363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29289163882063968345965575 43933745823095952518948363)
          ·
            refine ⟨65900618734643928778422545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43933745823095952518948363 65900618734643928778422545)
            ·
              refine ⟨49425464050982946583816909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65900618734643928778422545 49425464050982946583816909)
              ·
                refine ⟨18534549019118604968931341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49425464050982946583816909 18534549019118604968931341)
                ·
                  refine ⟨6950455882169476863349253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18534549019118604968931341 6950455882169476863349253)
                  ·
                    refine ⟨1303210477906776911877985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6950455882169476863349253 1303210477906776911877985)
                    ·
                      rfl

theorem cell22_3806990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_3806990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3806990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3806990 prefixEnd_3806990 := by exact prefixLift 3806990
  have htrace : WordTrace (prefixWord ++ tailWord_3806990) baseStart_3806990 baseEnd_3806990 := by
    simpa [prefixWord, tailWord_3806990, baseEnd_3806990] using wordTrace_append hprefix tailTrace_3806990
  have hstable : (prefixWord ++ tailWord_3806990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3806990).length < 2 ^ (prefixWord ++ tailWord_3806990).sum := by decide
  have hdescent : baseEnd_3806990 < baseStart_3806990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3806990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807080 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 1, 8]
def baseStart_3807080 : Nat := 118140960795 + 3807080 * 2 ^ 59
def prefixEnd_3807080 : Nat := 4983230072969 + 3 ^ 40 * 3807080 * 2
def baseEnd_3807080 : Nat := 1303241286746046677127709

theorem tailTrace_3807080 : CollatzResearch.WordTrace tailWord_3807080 prefixEnd_3807080 1303241286746046677127709 := by
  unfold tailWord_3807080
  simp only [CollatzResearch.WordTrace]
  refine ⟨69427807523803416172121347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92570410031737888229495129 69427807523803416172121347)
  ·
    refine ⟨104141711285705124258182021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69427807523803416172121347 104141711285705124258182021)
    ·
      refine ⟨19526570866069710798409129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104141711285705124258182021 19526570866069710798409129)
      ·
        refine ⟨14644928149552283098806847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19526570866069710798409129 14644928149552283098806847)
        ·
          refine ⟨21967392224328424648210271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14644928149552283098806847 21967392224328424648210271)
          ·
            refine ⟨32951088336492636972315407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21967392224328424648210271 32951088336492636972315407)
            ·
              refine ⟨49426632504738955458473111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32951088336492636972315407 49426632504738955458473111)
              ·
                refine ⟨74139948757108433187709667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49426632504738955458473111 74139948757108433187709667)
                ·
                  refine ⟨111209923135662649781564501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74139948757108433187709667 111209923135662649781564501)
                  ·
                    refine ⟨1303241286746046677127709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111209923135662649781564501 1303241286746046677127709)
                    ·
                      rfl

theorem cell22_3807080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_3807080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807080 prefixEnd_3807080 := by exact prefixLift 3807080
  have htrace : WordTrace (prefixWord ++ tailWord_3807080) baseStart_3807080 baseEnd_3807080 := by
    simpa [prefixWord, tailWord_3807080, baseEnd_3807080] using wordTrace_append hprefix tailTrace_3807080
  have hstable : (prefixWord ++ tailWord_3807080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807080).length < 2 ^ (prefixWord ++ tailWord_3807080).sum := by decide
  have hdescent : baseEnd_3807080 < baseStart_3807080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807157 : List Nat := [1, 3, 3, 2, 1, 2, 2, 2, 6]
def baseStart_3807157 : Nat := 118140960795 + 3807157 * 2 ^ 59
def prefixEnd_3807157 : Nat := 4983230072969 + 3 ^ 40 * 3807157 * 2
def baseEnd_3807157 : Nat := 434422548473214714317491

theorem tailTrace_3807157 : CollatzResearch.WordTrace tailWord_3807157 prefixEnd_3807157 434422548473214714317491 := by
  unfold tailWord_3807157
  simp only [CollatzResearch.WordTrace]
  refine ⟨138858423468327874494795725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92572282312218582996530483 138858423468327874494795725)
  ·
    refine ⟨52071908800622952935548397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138858423468327874494795725 52071908800622952935548397)
    ·
      refine ⟨19526965800233607350830649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52071908800622952935548397 19526965800233607350830649)
      ·
        refine ⟨14645224350175205513122987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19526965800233607350830649 14645224350175205513122987)
        ·
          refine ⟨21967836525262808269684481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14645224350175205513122987 21967836525262808269684481)
          ·
            refine ⟨16475877393947106202263361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21967836525262808269684481 16475877393947106202263361)
            ·
              refine ⟨12356908045460329651697521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16475877393947106202263361 12356908045460329651697521)
              ·
                refine ⟨9267681034095247238773141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12356908045460329651697521 9267681034095247238773141)
                ·
                  refine ⟨434422548473214714317491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9267681034095247238773141 434422548473214714317491)
                  ·
                    rfl

theorem cell22_3807157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_3807157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807157 prefixEnd_3807157 := by exact prefixLift 3807157
  have htrace : WordTrace (prefixWord ++ tailWord_3807157) baseStart_3807157 baseEnd_3807157 := by
    simpa [prefixWord, tailWord_3807157, baseEnd_3807157] using wordTrace_append hprefix tailTrace_3807157
  have hstable : (prefixWord ++ tailWord_3807157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807157).length < 2 ^ (prefixWord ++ tailWord_3807157).sum := by decide
  have hdescent : baseEnd_3807157 < baseStart_3807157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807189 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 4, 3]
def baseStart_3807189 : Nat := 118140960795 + 3807189 * 2 ^ 59
def prefixEnd_3807189 : Nat := 4983230072969 + 3 ^ 40 * 3807189 * 2
def baseEnd_3807189 : Nat := 1303278599673606726152375

theorem tailTrace_3807189 : CollatzResearch.WordTrace tailWord_3807189 prefixEnd_3807189 1303278599673606726152375 := by
  unfold tailWord_3807189
  simp only [CollatzResearch.WordTrace]
  refine ⟨138859590604211943959960621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92573060402807962639973747 138859590604211943959960621)
  ·
    refine ⟨52072346476579478984985233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138859590604211943959960621 52072346476579478984985233)
    ·
      refine ⟨39054259857434609238738925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52072346476579478984985233 39054259857434609238738925)
      ·
        refine ⟨14645347446537978464527097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39054259857434609238738925 14645347446537978464527097)
        ·
          refine ⟨10984010584903483848395323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14645347446537978464527097 10984010584903483848395323)
          ·
            refine ⟨16476015877355225772592985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10984010584903483848395323 16476015877355225772592985)
            ·
              refine ⟨12357011908016419329444739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16476015877355225772592985 12357011908016419329444739)
              ·
                refine ⟨18535517862024628994167109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12357011908016419329444739 18535517862024628994167109)
                ·
                  refine ⟨3475409599129617936406333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18535517862024628994167109 3475409599129617936406333)
                  ·
                    refine ⟨1303278599673606726152375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3475409599129617936406333 1303278599673606726152375)
                    ·
                      rfl

theorem cell22_3807189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_3807189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807189 prefixEnd_3807189 := by exact prefixLift 3807189
  have htrace : WordTrace (prefixWord ++ tailWord_3807189) baseStart_3807189 baseEnd_3807189 := by
    simpa [prefixWord, tailWord_3807189, baseEnd_3807189] using wordTrace_append hprefix tailTrace_3807189
  have hstable : (prefixWord ++ tailWord_3807189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807189).length < 2 ^ (prefixWord ++ tailWord_3807189).sum := by decide
  have hdescent : baseEnd_3807189 < baseStart_3807189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807292 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 8]
def baseStart_3807292 : Nat := 118140960795 + 3807292 * 2 ^ 59
def prefixEnd_3807292 : Nat := 4983230072969 + 3 ^ 40 * 3807292 * 2
def baseEnd_3807292 : Nat := 434437952892849596942353

theorem tailTrace_3807292 : CollatzResearch.WordTrace tailWord_3807292 prefixEnd_3807292 434437952892849596942353 := by
  unfold tailWord_3807292
  simp only [CollatzResearch.WordTrace]
  refine ⟨69431673661419396275480065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92575564881892528367306753 69431673661419396275480065)
  ·
    refine ⟨52073755246064547206610049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69431673661419396275480065 52073755246064547206610049)
    ·
      refine ⟨39055316434548410404957537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52073755246064547206610049 39055316434548410404957537)
      ·
        refine ⟨29291487325911307803718153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39055316434548410404957537 29291487325911307803718153)
        ·
          refine ⟨21968615494433480852788615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29291487325911307803718153 21968615494433480852788615)
          ·
            refine ⟨32952923241650221279182923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21968615494433480852788615 32952923241650221279182923)
            ·
              refine ⟨49429384862475331918774385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32952923241650221279182923 49429384862475331918774385)
              ·
                refine ⟨37072038646856498939080789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49429384862475331918774385 37072038646856498939080789)
                ·
                  refine ⟨434437952892849596942353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37072038646856498939080789 434437952892849596942353)
                  ·
                    rfl

theorem cell22_3807292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_3807292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807292 prefixEnd_3807292 := by exact prefixLift 3807292
  have htrace : WordTrace (prefixWord ++ tailWord_3807292) baseStart_3807292 baseEnd_3807292 := by
    simpa [prefixWord, tailWord_3807292, baseEnd_3807292] using wordTrace_append hprefix tailTrace_3807292
  have hstable : (prefixWord ++ tailWord_3807292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807292).length < 2 ^ (prefixWord ++ tailWord_3807292).sum := by decide
  have hdescent : baseEnd_3807292 < baseStart_3807292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807322 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 3, 6]
def baseStart_3807322 : Nat := 118140960795 + 3807322 * 2 ^ 59
def prefixEnd_3807322 : Nat := 4983230072969 + 3 ^ 40 * 3807322 * 2
def baseEnd_3807322 : Nat := 1303324128291638712576967

theorem tailTrace_3807322 : CollatzResearch.WordTrace tailWord_3807322 prefixEnd_3807322 1303324128291638712576967 := by
  unfold tailWord_3807322
  simp only [CollatzResearch.WordTrace]
  refine ⟨34716110378182526918638055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92576294341820071783034813 34716110378182526918638055)
  ·
    refine ⟨52074165567273790377957083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34716110378182526918638055 52074165567273790377957083)
    ·
      refine ⟨78111248350910685566935625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52074165567273790377957083 78111248350910685566935625)
      ·
        refine ⟨58583436263183014175201719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78111248350910685566935625 58583436263183014175201719)
        ·
          refine ⟨87875154394774521262802579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58583436263183014175201719 87875154394774521262802579)
          ·
            refine ⟨131812731592161781894203869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87875154394774521262802579 131812731592161781894203869)
            ·
              refine ⟨49429774347060668210326451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131812731592161781894203869 49429774347060668210326451)
              ·
                refine ⟨74144661520591002315489677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49429774347060668210326451 74144661520591002315489677)
                ·
                  refine ⟨27804248070221625868308629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74144661520591002315489677 27804248070221625868308629)
                  ·
                    refine ⟨1303324128291638712576967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27804248070221625868308629 1303324128291638712576967)
                    ·
                      rfl

theorem cell22_3807322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_3807322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807322 prefixEnd_3807322 := by exact prefixLift 3807322
  have htrace : WordTrace (prefixWord ++ tailWord_3807322) baseStart_3807322 baseEnd_3807322 := by
    simpa [prefixWord, tailWord_3807322, baseEnd_3807322] using wordTrace_append hprefix tailTrace_3807322
  have hstable : (prefixWord ++ tailWord_3807322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807322).length < 2 ^ (prefixWord ++ tailWord_3807322).sum := by decide
  have hdescent : baseEnd_3807322 < baseStart_3807322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807337 : List Nat := [1, 2, 1, 1, 1, 5, 3, 8]
def baseStart_3807337 : Nat := 118140960795 + 3807337 * 2 ^ 59
def prefixEnd_3807337 : Nat := 4983230072969 + 3 ^ 40 * 3807337 * 2
def baseEnd_3807337 : Nat := 144814362566464852605769

theorem tailTrace_3807337 : CollatzResearch.WordTrace tailWord_3807337 prefixEnd_3807337 144814362566464852605769 := by
  unfold tailWord_3807337
  simp only [CollatzResearch.WordTrace]
  refine ⟨138864988607675765236348265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92576659071783843490898843 138864988607675765236348265)
  ·
    refine ⟨104148741455756823927261199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138864988607675765236348265 104148741455756823927261199)
    ·
      refine ⟨156223112183635235890891799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104148741455756823927261199 156223112183635235890891799)
      ·
        refine ⟨234334668275452853836337699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156223112183635235890891799 234334668275452853836337699)
        ·
          refine ⟨351502002413179280754506549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234334668275452853836337699 351502002413179280754506549)
          ·
            refine ⟨32953312726235557570734989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 351502002413179280754506549 32953312726235557570734989)
            ·
              refine ⟨12357492272338334089025621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32953312726235557570734989 12357492272338334089025621)
              ·
                refine ⟨144814362566464852605769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12357492272338334089025621 144814362566464852605769)
                ·
                  rfl

theorem cell22_3807337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 8].length) (baseStart_3807337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807337 prefixEnd_3807337 := by exact prefixLift 3807337
  have htrace : WordTrace (prefixWord ++ tailWord_3807337) baseStart_3807337 baseEnd_3807337 := by
    simpa [prefixWord, tailWord_3807337, baseEnd_3807337] using wordTrace_append hprefix tailTrace_3807337
  have hstable : (prefixWord ++ tailWord_3807337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807337).length < 2 ^ (prefixWord ++ tailWord_3807337).sum := by decide
  have hdescent : baseEnd_3807337 < baseStart_3807337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807420 : List Nat := [2, 2, 2, 3, 3, 1, 1, 4, 1, 3]
def baseStart_3807420 : Nat := 118140960795 + 3807420 * 2 ^ 59
def prefixEnd_3807420 : Nat := 4983230072969 + 3 ^ 40 * 3807420 * 2
def baseEnd_3807420 : Nat := 1303357675694399123626667

theorem tailTrace_3807420 : CollatzResearch.WordTrace tailWord_3807420 prefixEnd_3807420 1303357675694399123626667 := by
  unfold tailWord_3807420
  simp only [CollatzResearch.WordTrace]
  refine ⟨69434007933187535205809857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92578677244250046941079809 69434007933187535205809857)
  ·
    refine ⟨52075505949890651404357393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69434007933187535205809857 52075505949890651404357393)
    ·
      refine ⟨39056629462417988553268045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52075505949890651404357393 39056629462417988553268045)
      ·
        refine ⟨14646236048406745707475517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39056629462417988553268045 14646236048406745707475517)
        ·
          refine ⟨5492338518152529640303319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14646236048406745707475517 5492338518152529640303319)
          ·
            refine ⟨8238507777228794460454979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5492338518152529640303319 8238507777228794460454979)
            ·
              refine ⟨12357761665843191690682469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8238507777228794460454979 12357761665843191690682469)
              ·
                refine ⟨2317080312345598442002963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12357761665843191690682469 2317080312345598442002963)
                ·
                  refine ⟨3475620468518397663004445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2317080312345598442002963 3475620468518397663004445)
                  ·
                    refine ⟨1303357675694399123626667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3475620468518397663004445 1303357675694399123626667)
                    ·
                      rfl

theorem cell22_3807420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_3807420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807420 prefixEnd_3807420 := by exact prefixLift 3807420
  have htrace : WordTrace (prefixWord ++ tailWord_3807420) baseStart_3807420 baseEnd_3807420 := by
    simpa [prefixWord, tailWord_3807420, baseEnd_3807420] using wordTrace_append hprefix tailTrace_3807420
  have hstable : (prefixWord ++ tailWord_3807420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807420).length < 2 ^ (prefixWord ++ tailWord_3807420).sum := by decide
  have hdescent : baseEnd_3807420 < baseStart_3807420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807429 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 3, 4]
def baseStart_3807429 : Nat := 118140960795 + 3807429 * 2 ^ 59
def prefixEnd_3807429 : Nat := 4983230072969 + 3 ^ 40 * 3807429 * 2
def baseEnd_3807429 : Nat := 1303360756578326100151639

theorem tailTrace_3807429 : CollatzResearch.WordTrace tailWord_3807429 prefixEnd_3807429 1303360756578326100151639 := by
  unfold tailWord_3807429
  simp only [CollatzResearch.WordTrace]
  refine ⟨138868344123342464948697341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92578896082228309965798227 138868344123342464948697341)
  ·
    refine ⟨52075629046253424355761503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138868344123342464948697341 52075629046253424355761503)
    ·
      refine ⟨78113443569380136533642255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52075629046253424355761503 78113443569380136533642255)
      ·
        refine ⟨117170165354070204800463383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78113443569380136533642255 117170165354070204800463383)
        ·
          refine ⟨175755248031105307200695075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117170165354070204800463383 175755248031105307200695075)
          ·
            refine ⟨263632872046657960801042613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175755248031105307200695075 263632872046657960801042613)
            ·
              refine ⟨24715581754374183825097745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263632872046657960801042613 24715581754374183825097745)
              ·
                refine ⟨18536686315780637868823309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24715581754374183825097745 18536686315780637868823309)
                ·
                  refine ⟨6951257368417739200808741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18536686315780637868823309 6951257368417739200808741)
                  ·
                    refine ⟨1303360756578326100151639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6951257368417739200808741 1303360756578326100151639)
                    ·
                      rfl

theorem cell22_3807429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_3807429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807429 prefixEnd_3807429 := by exact prefixLift 3807429
  have htrace : WordTrace (prefixWord ++ tailWord_3807429) baseStart_3807429 baseEnd_3807429 := by
    simpa [prefixWord, tailWord_3807429, baseEnd_3807429] using wordTrace_append hprefix tailTrace_3807429
  have hstable : (prefixWord ++ tailWord_3807429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807429).length < 2 ^ (prefixWord ++ tailWord_3807429).sum := by decide
  have hdescent : baseEnd_3807429 < baseStart_3807429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807463 : List Nat := [1, 1, 5, 3, 1, 2, 1, 3, 1, 4]
def baseStart_3807463 : Nat := 118140960795 + 3807463 * 2 ^ 59
def prefixEnd_3807463 : Nat := 4983230072969 + 3 ^ 40 * 3807463 * 2
def baseEnd_3807463 : Nat := 1303372395473161344801535

theorem tailTrace_3807463 : CollatzResearch.WordTrace tailWord_3807463 prefixEnd_3807463 1303372395473161344801535 := by
  unfold tailWord_3807463
  simp only [CollatzResearch.WordTrace]
  refine ⟨138869584205219288755435043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92579722803479525836956695 138869584205219288755435043)
  ·
    refine ⟨208304376307828933133152565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138869584205219288755435043 208304376307828933133152565)
    ·
      refine ⟨19528535278858962481233053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208304376307828933133152565 19528535278858962481233053)
      ·
        refine ⟨7323200729572110930462395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19528535278858962481233053 7323200729572110930462395)
        ·
          refine ⟨10984801094358166395693593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7323200729572110930462395 10984801094358166395693593)
          ·
            refine ⟨8238600820768624796770195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10984801094358166395693593 8238600820768624796770195)
            ·
              refine ⟨12357901231152937195155293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8238600820768624796770195 12357901231152937195155293)
              ·
                refine ⟨4634212961682351448183235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12357901231152937195155293 4634212961682351448183235)
                ·
                  refine ⟨6951319442523527172274853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4634212961682351448183235 6951319442523527172274853)
                  ·
                    refine ⟨1303372395473161344801535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6951319442523527172274853 1303372395473161344801535)
                    ·
                      rfl

theorem cell22_3807463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_3807463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807463 prefixEnd_3807463 := by exact prefixLift 3807463
  have htrace : WordTrace (prefixWord ++ tailWord_3807463) baseStart_3807463 baseEnd_3807463 := by
    simpa [prefixWord, tailWord_3807463, baseEnd_3807463] using wordTrace_append hprefix tailTrace_3807463
  have hstable : (prefixWord ++ tailWord_3807463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807463).length < 2 ^ (prefixWord ++ tailWord_3807463).sum := by decide
  have hdescent : baseEnd_3807463 < baseStart_3807463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807478 : List Nat := [5, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_3807478 : Nat := 118140960795 + 3807478 * 2 ^ 59
def prefixEnd_3807478 : Nat := 4983230072969 + 3 ^ 40 * 3807478 * 2
def baseEnd_3807478 : Nat := 434459176759902101892163

theorem tailTrace_3807478 : CollatzResearch.WordTrace tailWord_3807478 prefixEnd_3807478 434459176759902101892163 := by
  unfold tailWord_3807478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8679383206260309144826943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92580087533443297544820725 8679383206260309144826943)
  ·
    refine ⟨13019074809390463717240415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8679383206260309144826943 13019074809390463717240415)
    ·
      refine ⟨19528612214085695575860623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13019074809390463717240415 19528612214085695575860623)
      ·
        refine ⟨29292918321128543363790935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19528612214085695575860623 29292918321128543363790935)
        ·
          refine ⟨43939377481692815045686403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29292918321128543363790935 43939377481692815045686403)
          ·
            refine ⟨65909066222539222568529605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43939377481692815045686403 65909066222539222568529605)
            ·
              refine ⟨12357949916726104231599301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65909066222539222568529605 12357949916726104231599301)
              ·
                refine ⟨2317115609386144543424869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12357949916726104231599301 2317115609386144543424869)
                ·
                  refine ⟨434459176759902101892163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2317115609386144543424869 434459176759902101892163)
                  ·
                    rfl

theorem cell22_3807478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_3807478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807478 prefixEnd_3807478 := by exact prefixLift 3807478
  have htrace : WordTrace (prefixWord ++ tailWord_3807478) baseStart_3807478 baseEnd_3807478 := by
    simpa [prefixWord, tailWord_3807478, baseEnd_3807478] using wordTrace_append hprefix tailTrace_3807478
  have hstable : (prefixWord ++ tailWord_3807478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807478).length < 2 ^ (prefixWord ++ tailWord_3807478).sum := by decide
  have hdescent : baseEnd_3807478 < baseStart_3807478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807489 : List Nat := [1, 2, 4, 1, 1, 2, 2, 9]
def baseStart_3807489 : Nat := 118140960795 + 3807489 * 2 ^ 59
def prefixEnd_3807489 : Nat := 4983230072969 + 3 ^ 40 * 3807489 * 2
def baseEnd_3807489 : Nat := 144820143978278438183495

theorem tailTrace_3807489 : CollatzResearch.WordTrace tailWord_3807489 prefixEnd_3807489 144820143978278438183495 := by
  unfold tailWord_3807489
  simp only [CollatzResearch.WordTrace]
  refine ⟨138870532503125095195881521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92580355002083396797254347 138870532503125095195881521)
  ·
    refine ⟨104152899377343821396911141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138870532503125095195881521 104152899377343821396911141)
    ·
      refine ⟨19528668633251966511920839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104152899377343821396911141 19528668633251966511920839)
      ·
        refine ⟨29293002949877949767881259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19528668633251966511920839 29293002949877949767881259)
        ·
          refine ⟨43939504424816924651821889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29293002949877949767881259 43939504424816924651821889)
          ·
            refine ⟨32954628318612693488866417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43939504424816924651821889 32954628318612693488866417)
            ·
              refine ⟨24715971238959520116649813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32954628318612693488866417 24715971238959520116649813)
              ·
                refine ⟨144820143978278438183495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24715971238959520116649813 144820143978278438183495)
                ·
                  rfl

theorem cell22_3807489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 9].length) (baseStart_3807489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807489 prefixEnd_3807489 := by exact prefixLift 3807489
  have htrace : WordTrace (prefixWord ++ tailWord_3807489) baseStart_3807489 baseEnd_3807489 := by
    simpa [prefixWord, tailWord_3807489, baseEnd_3807489] using wordTrace_append hprefix tailTrace_3807489
  have hstable : (prefixWord ++ tailWord_3807489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807489).length < 2 ^ (prefixWord ++ tailWord_3807489).sum := by decide
  have hdescent : baseEnd_3807489 < baseStart_3807489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807521 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 5, 3]
def baseStart_3807521 : Nat := 118140960795 + 3807521 * 2 ^ 59
def prefixEnd_3807521 : Nat := 4983230072969 + 3 ^ 40 * 3807521 * 2
def baseEnd_3807521 : Nat := 1303392250058468526851357

theorem tailTrace_3807521 : CollatzResearch.WordTrace tailWord_3807521 prefixEnd_3807521 1303392250058468526851357 := by
  unfold tailWord_3807521
  simp only [CollatzResearch.WordTrace]
  refine ⟨138871699639009164661046417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92581133092672776440697611 138871699639009164661046417)
  ·
    refine ⟨104153774729256873495784813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138871699639009164661046417 104153774729256873495784813)
    ·
      refine ⟨39057665523471327560919305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104153774729256873495784813 39057665523471327560919305)
      ·
        refine ⟨29293249142603495670689479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39057665523471327560919305 29293249142603495670689479)
        ·
          refine ⟨43939873713905243506034219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29293249142603495670689479 43939873713905243506034219)
          ·
            refine ⟨65909810570857865259051329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43939873713905243506034219 65909810570857865259051329)
            ·
              refine ⟨49432357928143398944288497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65909810570857865259051329 49432357928143398944288497)
              ·
                refine ⟨37074268446107549208216373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49432357928143398944288497 37074268446107549208216373)
                ·
                  refine ⟨3475712666822582738270285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37074268446107549208216373 3475712666822582738270285)
                  ·
                    refine ⟨1303392250058468526851357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3475712666822582738270285 1303392250058468526851357)
                    ·
                      rfl

theorem cell22_3807521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_3807521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807521 prefixEnd_3807521 := by exact prefixLift 3807521
  have htrace : WordTrace (prefixWord ++ tailWord_3807521) baseStart_3807521 baseEnd_3807521 := by
    simpa [prefixWord, tailWord_3807521, baseEnd_3807521] using wordTrace_append hprefix tailTrace_3807521
  have hstable : (prefixWord ++ tailWord_3807521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807521).length < 2 ^ (prefixWord ++ tailWord_3807521).sum := by decide
  have hdescent : baseEnd_3807521 < baseStart_3807521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807551 : List Nat := [1, 1, 2, 2, 4, 1, 3, 3, 5]
def baseStart_3807551 : Nat := 118140960795 + 3807551 * 2 ^ 59
def prefixEnd_3807551 : Nat := 4983230072969 + 3 ^ 40 * 3807551 * 2
def baseEnd_3807551 : Nat := 434467506557186149533755

theorem tailTrace_3807551 : CollatzResearch.WordTrace tailWord_3807551 prefixEnd_3807551 434467506557186149533755 := by
  unfold tailWord_3807551
  simp only [CollatzResearch.WordTrace]
  refine ⟨138872793828900479784638507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92581862552600319856425671 138872793828900479784638507)
  ·
    refine ⟨208309190743350719676957761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138872793828900479784638507 208309190743350719676957761)
    ·
      refine ⟨156231893057513039757718321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208309190743350719676957761 156231893057513039757718321)
      ·
        refine ⟨117173919793134779818288741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156231893057513039757718321 117173919793134779818288741)
        ·
          refine ⟨21970109961212771215929139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117173919793134779818288741 21970109961212771215929139)
          ·
            refine ⟨32955164941819156823893709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21970109961212771215929139 32955164941819156823893709)
            ·
              refine ⟨12358186853182183808960141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32955164941819156823893709 12358186853182183808960141)
              ·
                refine ⟨4634320069943318928360053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12358186853182183808960141 4634320069943318928360053)
                ·
                  refine ⟨434467506557186149533755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4634320069943318928360053 434467506557186149533755)
                  ·
                    rfl

theorem cell22_3807551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 5].length) (baseStart_3807551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807551 prefixEnd_3807551 := by exact prefixLift 3807551
  have htrace : WordTrace (prefixWord ++ tailWord_3807551) baseStart_3807551 baseEnd_3807551 := by
    simpa [prefixWord, tailWord_3807551, baseEnd_3807551] using wordTrace_append hprefix tailTrace_3807551
  have hstable : (prefixWord ++ tailWord_3807551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807551).length < 2 ^ (prefixWord ++ tailWord_3807551).sum := by decide
  have hdescent : baseEnd_3807551 < baseStart_3807551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807611 : List Nat := [1, 1, 1, 1, 1, 7, 1, 3, 1, 5]
def baseStart_3807611 : Nat := 118140960795 + 3807611 * 2 ^ 59
def prefixEnd_3807611 : Nat := 4983230072969 + 3 ^ 40 * 3807611 * 2
def baseEnd_3807611 : Nat := 1303423058897738292101081

theorem tailTrace_3807611 : CollatzResearch.WordTrace tailWord_3807611 prefixEnd_3807611 1303423058897738292101081 := by
  unfold tailWord_3807611
  simp only [CollatzResearch.WordTrace]
  refine ⟨138874982208683110031822687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92583321472455406687881791 138874982208683110031822687)
  ·
    refine ⟨208312473313024665047734031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138874982208683110031822687 208312473313024665047734031)
    ·
      refine ⟨312468709969536997571601047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208312473313024665047734031 312468709969536997571601047)
      ·
        refine ⟨468703064954305496357401571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312468709969536997571601047 468703064954305496357401571)
        ·
          refine ⟨703054597431458244536102357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468703064954305496357401571 703054597431458244536102357)
          ·
            refine ⟨16477842127299802606314899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 703054597431458244536102357 16477842127299802606314899)
            ·
              refine ⟨24716763190949703909472349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16477842127299802606314899 24716763190949703909472349)
              ·
                refine ⟨9268786196606138966052131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24716763190949703909472349 9268786196606138966052131)
                ·
                  refine ⟨13903179294909208449078197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9268786196606138966052131 13903179294909208449078197)
                  ·
                    refine ⟨1303423058897738292101081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13903179294909208449078197 1303423058897738292101081)
                    ·
                      rfl

theorem cell22_3807611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 5].length) (baseStart_3807611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807611 prefixEnd_3807611 := by exact prefixLift 3807611
  have htrace : WordTrace (prefixWord ++ tailWord_3807611) baseStart_3807611 baseEnd_3807611 := by
    simpa [prefixWord, tailWord_3807611, baseEnd_3807611] using wordTrace_append hprefix tailTrace_3807611
  have hstable : (prefixWord ++ tailWord_3807611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807611).length < 2 ^ (prefixWord ++ tailWord_3807611).sum := by decide
  have hdescent : baseEnd_3807611 < baseStart_3807611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807630 : List Nat := [4, 1, 1, 4, 1, 1, 1, 5, 4]
def baseStart_3807630 : Nat := 118140960795 + 3807630 * 2 ^ 59
def prefixEnd_3807630 : Nat := 4983230072969 + 3 ^ 40 * 3807630 * 2
def baseEnd_3807630 : Nat := 434476520995342858625341

theorem tailTrace_3807630 : CollatzResearch.WordTrace tailWord_3807630 prefixEnd_3807630 434476520995342858625341 := by
  unfold tailWord_3807630
  simp only [CollatzResearch.WordTrace]
  refine ⟨17359459399451784534595543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92583783463742850851176229 17359459399451784534595543)
  ·
    refine ⟨26039189099177676801893315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17359459399451784534595543 26039189099177676801893315)
    ·
      refine ⟨39058783648766515202839973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26039189099177676801893315 39058783648766515202839973)
      ·
        refine ⟨7323521934143721600532495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39058783648766515202839973 7323521934143721600532495)
        ·
          refine ⟨10985282901215582400798743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7323521934143721600532495 10985282901215582400798743)
          ·
            refine ⟨16477924351823373601198115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10985282901215582400798743 16477924351823373601198115)
            ·
              refine ⟨24716886527735060401797173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16477924351823373601198115 24716886527735060401797173)
              ·
                refine ⟨2317208111975161912668485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24716886527735060401797173 2317208111975161912668485)
                ·
                  refine ⟨434476520995342858625341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2317208111975161912668485 434476520995342858625341)
                  ·
                    rfl

theorem cell22_3807630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_3807630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807630 prefixEnd_3807630 := by exact prefixLift 3807630
  have htrace : WordTrace (prefixWord ++ tailWord_3807630) baseStart_3807630 baseEnd_3807630 := by
    simpa [prefixWord, tailWord_3807630, baseEnd_3807630] using wordTrace_append hprefix tailTrace_3807630
  have hstable : (prefixWord ++ tailWord_3807630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807630).length < 2 ^ (prefixWord ++ tailWord_3807630).sum := by decide
  have hdescent : baseEnd_3807630 < baseStart_3807630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807645 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 4, 3]
def baseStart_3807645 : Nat := 118140960795 + 3807645 * 2 ^ 59
def prefixEnd_3807645 : Nat := 4983230072969 + 3 ^ 40 * 3807645 * 2
def baseEnd_3807645 : Nat := 1303434697792573536750977

theorem tailTrace_3807645 : CollatzResearch.WordTrace tailWord_3807645 prefixEnd_3807645 1303434697792573536750977 := by
  unfold tailWord_3807645
  simp only [CollatzResearch.WordTrace]
  refine ⟨138876222290559933838560389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92584148193706622559040259 138876222290559933838560389)
  ·
    refine ⟨26039291679479987594730073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138876222290559933838560389 26039291679479987594730073)
    ·
      refine ⟨19529468759609990696047555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26039291679479987594730073 19529468759609990696047555)
      ·
        refine ⟨29294203139414986044071333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19529468759609990696047555 29294203139414986044071333)
        ·
          refine ⟨5492663088640309883263375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29294203139414986044071333 5492663088640309883263375)
          ·
            refine ⟨8238994632960464824895063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5492663088640309883263375 8238994632960464824895063)
            ·
              refine ⟨12358491949440697237342595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8238994632960464824895063 12358491949440697237342595)
              ·
                refine ⟨18537737924161045856013893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12358491949440697237342595 18537737924161045856013893)
                ·
                  refine ⟨3475825860780196098002605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18537737924161045856013893 3475825860780196098002605)
                  ·
                    refine ⟨1303434697792573536750977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3475825860780196098002605 1303434697792573536750977)
                    ·
                      rfl

theorem cell22_3807645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_3807645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807645 prefixEnd_3807645 := by exact prefixLift 3807645
  have htrace : WordTrace (prefixWord ++ tailWord_3807645) baseStart_3807645 baseEnd_3807645 := by
    simpa [prefixWord, tailWord_3807645, baseEnd_3807645] using wordTrace_append hprefix tailTrace_3807645
  have hstable : (prefixWord ++ tailWord_3807645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807645).length < 2 ^ (prefixWord ++ tailWord_3807645).sum := by decide
  have hdescent : baseEnd_3807645 < baseStart_3807645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807681 : List Nat := [1, 2, 7, 1, 1, 2, 1, 3, 4]
def baseStart_3807681 : Nat := 118140960795 + 3807681 * 2 ^ 59
def prefixEnd_3807681 : Nat := 4983230072969 + 3 ^ 40 * 3807681 * 2
def baseEnd_3807681 : Nat := 434482340442760480950289

theorem tailTrace_3807681 : CollatzResearch.WordTrace tailWord_3807681 prefixEnd_3807681 434482340442760480950289 := by
  unfold tailWord_3807681
  simp only [CollatzResearch.WordTrace]
  refine ⟨138877535318429511986870897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92585023545619674657913931 138877535318429511986870897)
  ·
    refine ⟨104158151488822133990153173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138877535318429511986870897 104158151488822133990153173)
    ·
      refine ⟨2441206675519268765394215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 104158151488822133990153173 2441206675519268765394215)
      ·
        refine ⟨3661810013278903148091323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2441206675519268765394215 3661810013278903148091323)
        ·
          refine ⟨5492715019918354722136985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3661810013278903148091323 5492715019918354722136985)
          ·
            refine ⟨4119536264938766041602739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5492715019918354722136985 4119536264938766041602739)
            ·
              refine ⟨6179304397408149062404109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4119536264938766041602739 6179304397408149062404109)
              ·
                refine ⟨2317239149028055898401541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6179304397408149062404109 2317239149028055898401541)
                ·
                  refine ⟨434482340442760480950289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2317239149028055898401541 434482340442760480950289)
                  ·
                    rfl

theorem cell22_3807681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 4].length) (baseStart_3807681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807681 prefixEnd_3807681 := by exact prefixLift 3807681
  have htrace : WordTrace (prefixWord ++ tailWord_3807681) baseStart_3807681 baseEnd_3807681 := by
    simpa [prefixWord, tailWord_3807681, baseEnd_3807681] using wordTrace_append hprefix tailTrace_3807681
  have hstable : (prefixWord ++ tailWord_3807681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807681).length < 2 ^ (prefixWord ++ tailWord_3807681).sum := by decide
  have hdescent : baseEnd_3807681 < baseStart_3807681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807716 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_3807716 : Nat := 118140960795 + 3807716 * 2 ^ 59
def prefixEnd_3807716 : Nat := 4983230072969 + 3 ^ 40 * 3807716 * 2
def baseEnd_3807716 : Nat := 1303459002543553018225759

theorem tailTrace_3807716 : CollatzResearch.WordTrace tailWord_3807716 prefixEnd_3807716 1303459002543553018225759 := by
  unfold tailWord_3807716
  simp only [CollatzResearch.WordTrace]
  refine ⟨69439405936651356482197501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92585874582201808642930001 69439405936651356482197501)
  ·
    refine ⟨26039777226244258680824063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69439405936651356482197501 26039777226244258680824063)
    ·
      refine ⟨39059665839366388021236095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26039777226244258680824063 39059665839366388021236095)
      ·
        refine ⟨58589498759049582031854143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39059665839366388021236095 58589498759049582031854143)
        ·
          refine ⟨87884248138574373047781215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58589498759049582031854143 87884248138574373047781215)
          ·
            refine ⟨131826372207861559571671823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87884248138574373047781215 131826372207861559571671823)
            ·
              refine ⟨197739558311792339357507735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131826372207861559571671823 197739558311792339357507735)
              ·
                refine ⟨296609337467688509036261603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197739558311792339357507735 296609337467688509036261603)
                ·
                  refine ⟨444914006201532763554392405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296609337467688509036261603 444914006201532763554392405)
                  ·
                    refine ⟨1303459002543553018225759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 444914006201532763554392405 1303459002543553018225759)
                    ·
                      rfl

theorem cell22_3807716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_3807716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807716 prefixEnd_3807716 := by exact prefixLift 3807716
  have htrace : WordTrace (prefixWord ++ tailWord_3807716) baseStart_3807716 baseEnd_3807716 := by
    simpa [prefixWord, tailWord_3807716, baseEnd_3807716] using wordTrace_append hprefix tailTrace_3807716
  have hstable : (prefixWord ++ tailWord_3807716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807716).length < 2 ^ (prefixWord ++ tailWord_3807716).sum := by decide
  have hdescent : baseEnd_3807716 < baseStart_3807716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807720 : List Nat := [2, 1, 4, 1, 1, 3, 4, 1, 5]
def baseStart_3807720 : Nat := 118140960795 + 3807720 * 2 ^ 59
def prefixEnd_3807720 : Nat := 4983230072969 + 3 ^ 40 * 3807720 * 2
def baseEnd_3807720 : Nat := 434486790608432780375249

theorem tailTrace_3807720 : CollatzResearch.WordTrace tailWord_3807720 prefixEnd_3807720 434486790608432780375249 := by
  unfold tailWord_3807720
  simp only [CollatzResearch.WordTrace]
  refine ⟨69439478882644110823770307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92585971843525481098360409 69439478882644110823770307)
  ·
    refine ⟨104159218323966166235655461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69439478882644110823770307 104159218323966166235655461)
    ·
      refine ⟨19529853435743656169185399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104159218323966166235655461 19529853435743656169185399)
      ·
        refine ⟨29294780153615484253778099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19529853435743656169185399 29294780153615484253778099)
        ·
          refine ⟨43942170230423226380667149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29294780153615484253778099 43942170230423226380667149)
          ·
            refine ⟨16478313836408709892750181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43942170230423226380667149 16478313836408709892750181)
            ·
              refine ⟨3089683844326633104890659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16478313836408709892750181 3089683844326633104890659)
              ·
                refine ⟨4634525766489949657335989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3089683844326633104890659 4634525766489949657335989)
                ·
                  refine ⟨434486790608432780375249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4634525766489949657335989 434486790608432780375249)
                  ·
                    rfl

theorem cell22_3807720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 5].length) (baseStart_3807720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807720 prefixEnd_3807720 := by exact prefixLift 3807720
  have htrace : WordTrace (prefixWord ++ tailWord_3807720) baseStart_3807720 baseEnd_3807720 := by
    simpa [prefixWord, tailWord_3807720, baseEnd_3807720] using wordTrace_append hprefix tailTrace_3807720
  have hstable : (prefixWord ++ tailWord_3807720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807720).length < 2 ^ (prefixWord ++ tailWord_3807720).sum := by decide
  have hdescent : baseEnd_3807720 < baseStart_3807720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807731 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 8]
def baseStart_3807731 : Nat := 118140960795 + 3807731 * 2 ^ 59
def prefixEnd_3807731 : Nat := 4983230072969 + 3 ^ 40 * 3807731 * 2
def baseEnd_3807731 : Nat := 434488045783365993033571

theorem tailTrace_3807731 : CollatzResearch.WordTrace tailWord_3807731 prefixEnd_3807731 434488045783365993033571 := by
  unfold tailWord_3807731
  simp only [CollatzResearch.WordTrace]
  refine ⟨138879358968248370526191047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92586239312165580350794031 138879358968248370526191047)
  ·
    refine ⟨208319038452372555789286571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138879358968248370526191047 208319038452372555789286571)
    ·
      refine ⟨312478557678558833683929857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208319038452372555789286571 312478557678558833683929857)
      ·
        refine ⟨234358918258919125262947393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312478557678558833683929857 234358918258919125262947393)
        ·
          refine ⟨175769188694189343947210545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234358918258919125262947393 175769188694189343947210545)
          ·
            refine ⟨131826891520642007960407909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175769188694189343947210545 131826891520642007960407909)
            ·
              refine ⟨24717542160120376492576483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131826891520642007960407909 24717542160120376492576483)
              ·
                refine ⟨37076313240180564738864725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24717542160120376492576483 37076313240180564738864725)
                ·
                  refine ⟨434488045783365993033571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37076313240180564738864725 434488045783365993033571)
                  ·
                    rfl

theorem cell22_3807731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 8].length) (baseStart_3807731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807731 prefixEnd_3807731 := by exact prefixLift 3807731
  have htrace : WordTrace (prefixWord ++ tailWord_3807731) baseStart_3807731 baseEnd_3807731 := by
    simpa [prefixWord, tailWord_3807731, baseEnd_3807731] using wordTrace_append hprefix tailTrace_3807731
  have hstable : (prefixWord ++ tailWord_3807731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807731).length < 2 ^ (prefixWord ++ tailWord_3807731).sum := by decide
  have hdescent : baseEnd_3807731 < baseStart_3807731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807765 : List Nat := [1, 3, 2, 1, 3, 1, 3, 4, 4]
def baseStart_3807765 : Nat := 118140960795 + 3807765 * 2 ^ 59
def prefixEnd_3807765 : Nat := 4983230072969 + 3 ^ 40 * 3807765 * 2
def baseEnd_3807765 : Nat := 434491925414977741250203

theorem tailTrace_3807765 : CollatzResearch.WordTrace tailWord_3807765 prefixEnd_3807765 434491925414977741250203 := by
  unfold tailWord_3807765
  simp only [CollatzResearch.WordTrace]
  refine ⟨138880599050125194332928749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92587066033416796221952499 138880599050125194332928749)
  ·
    refine ⟨52080224643796947874848281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138880599050125194332928749 52080224643796947874848281)
    ·
      refine ⟨39060168482847710906136211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52080224643796947874848281 39060168482847710906136211)
      ·
        refine ⟨58590252724271566359204317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39060168482847710906136211 58590252724271566359204317)
        ·
          refine ⟨21971344771601837384701619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58590252724271566359204317 21971344771601837384701619)
          ·
            refine ⟨32957017157402756077052429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21971344771601837384701619 32957017157402756077052429)
            ·
              refine ⟨12358881434026033528894661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32957017157402756077052429 12358881434026033528894661)
              ·
                refine ⟨2317290268879881286667749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12358881434026033528894661 2317290268879881286667749)
                ·
                  refine ⟨434491925414977741250203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2317290268879881286667749 434491925414977741250203)
                  ·
                    rfl

theorem cell22_3807765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 4].length) (baseStart_3807765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807765 prefixEnd_3807765 := by exact prefixLift 3807765
  have htrace : WordTrace (prefixWord ++ tailWord_3807765) baseStart_3807765 baseEnd_3807765 := by
    simpa [prefixWord, tailWord_3807765, baseEnd_3807765] using wordTrace_append hprefix tailTrace_3807765
  have hstable : (prefixWord ++ tailWord_3807765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807765).length < 2 ^ (prefixWord ++ tailWord_3807765).sum := by decide
  have hdescent : baseEnd_3807765 < baseStart_3807765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807778 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_3807778 : Nat := 118140960795 + 3807778 * 2 ^ 59
def prefixEnd_3807778 : Nat := 4983230072969 + 3 ^ 40 * 3807778 * 2
def baseEnd_3807778 : Nat := 1303480226410605523175569

theorem tailTrace_3807778 : CollatzResearch.WordTrace tailWord_3807778 prefixEnd_3807778 1303480226410605523175569 := by
  unfold tailWord_3807778
  simp only [CollatzResearch.WordTrace]
  refine ⟨34720268299769524388287997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92587382132718731702101325 34720268299769524388287997)
  ·
    refine ⟨13020100612413571645607999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34720268299769524388287997 13020100612413571645607999)
    ·
      refine ⟨19530150918620357468411999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13020100612413571645607999 19530150918620357468411999)
      ·
        refine ⟨29295226377930536202617999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19530150918620357468411999 29295226377930536202617999)
        ·
          refine ⟨43942839566895804303926999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29295226377930536202617999 43942839566895804303926999)
          ·
            refine ⟨65914259350343706455890499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43942839566895804303926999 65914259350343706455890499)
            ·
              refine ⟨98871389025515559683835749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65914259350343706455890499 98871389025515559683835749)
              ·
                refine ⟨18538385442284167440719203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98871389025515559683835749 18538385442284167440719203)
                ·
                  refine ⟨27807578163426251161078805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18538385442284167440719203 27807578163426251161078805)
                  ·
                    refine ⟨1303480226410605523175569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27807578163426251161078805 1303480226410605523175569)
                    ·
                      rfl

theorem cell22_3807778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_3807778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807778 prefixEnd_3807778 := by exact prefixLift 3807778
  have htrace : WordTrace (prefixWord ++ tailWord_3807778) baseStart_3807778 baseEnd_3807778 := by
    simpa [prefixWord, tailWord_3807778, baseEnd_3807778] using wordTrace_append hprefix tailTrace_3807778
  have hstable : (prefixWord ++ tailWord_3807778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807778).length < 2 ^ (prefixWord ++ tailWord_3807778).sum := by decide
  have hdescent : baseEnd_3807778 < baseStart_3807778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807814 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_3807814 : Nat := 118140960795 + 3807814 * 2 ^ 59
def prefixEnd_3807814 : Nat := 4983230072969 + 3 ^ 40 * 3807814 * 2
def baseEnd_3807814 : Nat := 1303492549946313429275459

theorem tailTrace_3807814 : CollatzResearch.WordTrace tailWord_3807814 prefixEnd_3807814 1303492549946313429275459 := by
  unfold tailWord_3807814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4340074569592114865670703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92588257484631783800974997 4340074569592114865670703)
  ·
    refine ⟨6510111854388172298506055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4340074569592114865670703 6510111854388172298506055)
    ·
      refine ⟨9765167781582258447759083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6510111854388172298506055 9765167781582258447759083)
      ·
        refine ⟨14647751672373387671638625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9765167781582258447759083 14647751672373387671638625)
        ·
          refine ⟨10985813754280040753728969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14647751672373387671638625 10985813754280040753728969)
          ·
            refine ⟨8239360315710030565296727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10985813754280040753728969 8239360315710030565296727)
            ·
              refine ⟨12359040473565045847945091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8239360315710030565296727 12359040473565045847945091)
              ·
                refine ⟨18538560710347568771917637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12359040473565045847945091 18538560710347568771917637)
                ·
                  refine ⟨3475980133190169144734557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18538560710347568771917637 3475980133190169144734557)
                  ·
                    refine ⟨1303492549946313429275459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3475980133190169144734557 1303492549946313429275459)
                    ·
                      rfl

theorem cell22_3807814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_3807814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807814 prefixEnd_3807814 := by exact prefixLift 3807814
  have htrace : WordTrace (prefixWord ++ tailWord_3807814) baseStart_3807814 baseEnd_3807814 := by
    simpa [prefixWord, tailWord_3807814, baseEnd_3807814] using wordTrace_append hprefix tailTrace_3807814
  have hstable : (prefixWord ++ tailWord_3807814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807814).length < 2 ^ (prefixWord ++ tailWord_3807814).sum := by decide
  have hdescent : baseEnd_3807814 < baseStart_3807814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807825 : List Nat := [1, 2, 2, 1, 3, 3, 1, 3, 3, 3]
def baseStart_3807825 : Nat := 118140960795 + 3807825 * 2 ^ 59
def prefixEnd_3807825 : Nat := 4983230072969 + 3 ^ 40 * 3807825 * 2
def baseEnd_3807825 : Nat := 1303496315471113067250425

theorem tailTrace_3807825 : CollatzResearch.WordTrace tailWord_3807825 prefixEnd_3807825 1303496315471113067250425 := by
  unfold tailWord_3807825
  simp only [CollatzResearch.WordTrace]
  refine ⟨138882787429907824580112929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92588524953271883053408619 138882787429907824580112929)
  ·
    refine ⟨104162090572430868435084697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138882787429907824580112929 104162090572430868435084697)
    ·
      refine ⟨78121567929323151326313523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104162090572430868435084697 78121567929323151326313523)
      ·
        refine ⟨117182351893984726989470285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78121567929323151326313523 117182351893984726989470285)
        ·
          refine ⟨43943381960244272621051357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117182351893984726989470285 43943381960244272621051357)
          ·
            refine ⟨16478768235091602232894259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43943381960244272621051357 16478768235091602232894259)
            ·
              refine ⟨24718152352637403349341389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16478768235091602232894259 24718152352637403349341389)
              ·
                refine ⟨9269307132239026256003021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24718152352637403349341389 9269307132239026256003021)
                ·
                  refine ⟨3475990174589634846001133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9269307132239026256003021 3475990174589634846001133)
                  ·
                    refine ⟨1303496315471113067250425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3475990174589634846001133 1303496315471113067250425)
                    ·
                      rfl

theorem cell22_3807825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_3807825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807825 prefixEnd_3807825 := by exact prefixLift 3807825
  have htrace : WordTrace (prefixWord ++ tailWord_3807825) baseStart_3807825 baseEnd_3807825 := by
    simpa [prefixWord, tailWord_3807825, baseEnd_3807825] using wordTrace_append hprefix tailTrace_3807825
  have hstable : (prefixWord ++ tailWord_3807825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807825).length < 2 ^ (prefixWord ++ tailWord_3807825).sum := by decide
  have hdescent : baseEnd_3807825 < baseStart_3807825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807876 : List Nat := [2, 3, 2, 1, 3, 2, 3, 2, 1, 3]
def baseStart_3807876 : Nat := 118140960795 + 3807876 * 2 ^ 59
def prefixEnd_3807876 : Nat := 4983230072969 + 3 ^ 40 * 3807876 * 2
def baseEnd_3807876 : Nat := 1303513773813365934225269

theorem tailTrace_3807876 : CollatzResearch.WordTrace tailWord_3807876 prefixEnd_3807876 1303513773813365934225269 := by
  unfold tailWord_3807876
  simp only [CollatzResearch.WordTrace]
  refine ⟨69442323776361530145109741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92589765035148706860146321 69442323776361530145109741)
  ·
    refine ⟨26040871416135573804416153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69442323776361530145109741 26040871416135573804416153)
    ·
      refine ⟨19530653562101680353312115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26040871416135573804416153 19530653562101680353312115)
      ·
        refine ⟨29295980343152520529968173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19530653562101680353312115 29295980343152520529968173)
        ·
          refine ⟨10985992628682195198738065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29295980343152520529968173 10985992628682195198738065)
          ·
            refine ⟨8239494471511646399053549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10985992628682195198738065 8239494471511646399053549)
            ·
              refine ⟨3089810426816867399645081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8239494471511646399053549 3089810426816867399645081)
              ·
                refine ⟨2317357820112650549733811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3089810426816867399645081 2317357820112650549733811)
                ·
                  refine ⟨3476036730168975824600717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2317357820112650549733811 3476036730168975824600717)
                  ·
                    refine ⟨1303513773813365934225269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3476036730168975824600717 1303513773813365934225269)
                    ·
                      rfl

theorem cell22_3807876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_3807876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807876 prefixEnd_3807876 := by exact prefixLift 3807876
  have htrace : WordTrace (prefixWord ++ tailWord_3807876) baseStart_3807876 baseEnd_3807876 := by
    simpa [prefixWord, tailWord_3807876, baseEnd_3807876] using wordTrace_append hprefix tailTrace_3807876
  have hstable : (prefixWord ++ tailWord_3807876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807876).length < 2 ^ (prefixWord ++ tailWord_3807876).sum := by decide
  have hdescent : baseEnd_3807876 < baseStart_3807876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
