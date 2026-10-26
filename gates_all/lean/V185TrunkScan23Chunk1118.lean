import V185TrunkScan23Chunk1117

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6621639 : List Nat := [1, 1, 4, 1, 1, 5, 3, 1, 2, 2, 2]
def baseStart_6621639 : Nat := 118140960795 + 6621639 * 2 ^ 59
def prefixEnd_6621639 : Nat := 4983230072969 + 3 ^ 40 * 6621639 * 2
def baseEnd_6621639 : Nat := 3400083527556923540660143

theorem tailTrace_6621639 : CollatzResearch.WordTrace tailWord_6621639 prefixEnd_6621639 3400083527556923540660143 := by
  unfold tailWord_6621639
  simp only [CollatzResearch.WordTrace]
  refine ⟨241511015257940263751883971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161007343505293509167922647 241511015257940263751883971)
  ·
    refine ⟨362266522886910395627825957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241511015257940263751883971 362266522886910395627825957)
    ·
      refine ⟨67924973041295699180217367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 362266522886910395627825957 67924973041295699180217367)
      ·
        refine ⟨101887459561943548770326051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67924973041295699180217367 101887459561943548770326051)
        ·
          refine ⟨152831189342915323155489077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101887459561943548770326051 152831189342915323155489077)
          ·
            refine ⟨14327924000898311545827101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152831189342915323155489077 14327924000898311545827101)
            ·
              refine ⟨5372971500336866829685163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14327924000898311545827101 5372971500336866829685163)
              ·
                refine ⟨8059457250505300244527745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5372971500336866829685163 8059457250505300244527745)
                ·
                  refine ⟨6044592937878975183395809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8059457250505300244527745 6044592937878975183395809)
                  ·
                    refine ⟨4533444703409231387546857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6044592937878975183395809 4533444703409231387546857)
                    ·
                      refine ⟨3400083527556923540660143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4533444703409231387546857 3400083527556923540660143)
                      ·
                        rfl

theorem cell23_6621639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_6621639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621639 prefixEnd_6621639 := by exact prefixLift 6621639
  have htrace : WordTrace (prefixWord ++ tailWord_6621639) baseStart_6621639 baseEnd_6621639 := by
    simpa [prefixWord, tailWord_6621639, baseEnd_6621639] using wordTrace_append hprefix tailTrace_6621639
  have hstable : (prefixWord ++ tailWord_6621639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621639).length < 2 ^ (prefixWord ++ tailWord_6621639).sum := by decide
  have hdescent : baseEnd_6621639 < baseStart_6621639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621641 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 1, 7]
def baseStart_6621641 : Nat := 118140960795 + 6621641 * 2 ^ 59
def prefixEnd_6621641 : Nat := 4983230072969 + 3 ^ 40 * 6621641 * 2
def baseEnd_6621641 : Nat := 1133361518172744177611711

theorem tailTrace_6621641 : CollatzResearch.WordTrace tailWord_6621641 prefixEnd_6621641 1133361518172744177611711 := by
  unfold tailWord_6621641
  simp only [CollatzResearch.WordTrace]
  refine ⟨241511088203933018093456777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161007392135955345395637851 241511088203933018093456777)
  ·
    refine ⟨181133316152949763570092583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241511088203933018093456777 181133316152949763570092583)
    ·
      refine ⟨271699974229424645355138875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181133316152949763570092583 271699974229424645355138875)
      ·
        refine ⟨407549961344136968032708313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271699974229424645355138875 407549961344136968032708313)
        ·
          refine ⟨305662471008102726024531235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407549961344136968032708313 305662471008102726024531235)
          ·
            refine ⟨458493706512154089036796853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305662471008102726024531235 458493706512154089036796853)
            ·
              refine ⟨42983784985514445847199705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 458493706512154089036796853 42983784985514445847199705)
              ·
                refine ⟨32237838739135834385399779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42983784985514445847199705 32237838739135834385399779)
                ·
                  refine ⟨48356758108703751578099669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32237838739135834385399779 48356758108703751578099669)
                  ·
                    refine ⟨1133361518172744177611711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48356758108703751578099669 1133361518172744177611711)
                    ·
                      rfl

theorem cell23_6621641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 7].length) (baseStart_6621641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621641 prefixEnd_6621641 := by exact prefixLift 6621641
  have htrace : WordTrace (prefixWord ++ tailWord_6621641) baseStart_6621641 baseEnd_6621641 := by
    simpa [prefixWord, tailWord_6621641, baseEnd_6621641] using wordTrace_append hprefix tailTrace_6621641
  have hstable : (prefixWord ++ tailWord_6621641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621641).length < 2 ^ (prefixWord ++ tailWord_6621641).sum := by decide
  have hdescent : baseEnd_6621641 < baseStart_6621641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621658 : List Nat := [3, 1, 1, 2, 3, 1, 2, 3, 2, 5]
def baseStart_6621658 : Nat := 118140960795 + 6621658 * 2 ^ 59
def prefixEnd_6621658 : Nat := 4983230072969 + 3 ^ 40 * 6621658 * 2
def baseEnd_6621658 : Nat := 1133364427896452988774185

theorem tailTrace_6621658 : CollatzResearch.WordTrace tailWord_6621658 prefixEnd_6621658 1133364427896452988774185 := by
  unfold tailWord_6621658
  simp only [CollatzResearch.WordTrace]
  refine ⟨60377927061217857499206407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161007805496580953331217085 60377927061217857499206407)
  ·
    refine ⟨90566890591826786248809611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60377927061217857499206407 90566890591826786248809611)
    ·
      refine ⟨135850335887740179373214417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90566890591826786248809611 135850335887740179373214417)
      ·
        refine ⟨101887751915805134529910813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135850335887740179373214417 101887751915805134529910813)
        ·
          refine ⟨38207906968426925448716555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101887751915805134529910813 38207906968426925448716555)
          ·
            refine ⟨57311860452640388173074833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38207906968426925448716555 57311860452640388173074833)
            ·
              refine ⟨42983895339480291129806125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57311860452640388173074833 42983895339480291129806125)
              ·
                refine ⟨16118960752305109173677297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42983895339480291129806125 16118960752305109173677297)
                ·
                  refine ⟨12089220564228831880257973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16118960752305109173677297 12089220564228831880257973)
                  ·
                    refine ⟨1133364427896452988774185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12089220564228831880257973 1133364427896452988774185)
                    ·
                      rfl

theorem cell23_6621658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_6621658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621658 prefixEnd_6621658 := by exact prefixLift 6621658
  have htrace : WordTrace (prefixWord ++ tailWord_6621658) baseStart_6621658 baseEnd_6621658 := by
    simpa [prefixWord, tailWord_6621658, baseEnd_6621658] using wordTrace_append hprefix tailTrace_6621658
  have hstable : (prefixWord ++ tailWord_6621658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621658).length < 2 ^ (prefixWord ++ tailWord_6621658).sum := by decide
  have hdescent : baseEnd_6621658 < baseStart_6621658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621709 : List Nat := [1, 7, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_6621709 : Nat := 118140960795 + 6621709 * 2 ^ 59
def prefixEnd_6621709 : Nat := 4983230072969 + 3 ^ 40 * 6621709 * 2
def baseEnd_6621709 : Nat := 1133373157067579422261607

theorem tailTrace_6621709 : CollatzResearch.WordTrace tailWord_6621709 prefixEnd_6621709 1133373157067579422261607 := by
  unfold tailWord_6621709
  simp only [CollatzResearch.WordTrace]
  refine ⟨241513568367686665706932181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161009045578457777137954787 241513568367686665706932181)
  ·
    refine ⟨5660474258617656227506223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 241513568367686665706932181 5660474258617656227506223)
    ·
      refine ⟨8490711387926484341259335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5660474258617656227506223 8490711387926484341259335)
      ·
        refine ⟨12736067081889726511889003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8490711387926484341259335 12736067081889726511889003)
        ·
          refine ⟨19104100622834589767833505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12736067081889726511889003 19104100622834589767833505)
          ·
            refine ⟨14328075467125942325875129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19104100622834589767833505 14328075467125942325875129)
            ·
              refine ⟨10746056600344456744406347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14328075467125942325875129 10746056600344456744406347)
              ·
                refine ⟨16119084900516685116609521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10746056600344456744406347 16119084900516685116609521)
                ·
                  refine ⟨12089313675387513837457141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16119084900516685116609521 12089313675387513837457141)
                  ·
                    refine ⟨1133373157067579422261607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12089313675387513837457141 1133373157067579422261607)
                    ·
                      rfl

theorem cell23_6621709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_6621709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621709 prefixEnd_6621709 := by exact prefixLift 6621709
  have htrace : WordTrace (prefixWord ++ tailWord_6621709) baseStart_6621709 baseEnd_6621709 := by
    simpa [prefixWord, tailWord_6621709, baseEnd_6621709] using wordTrace_append hprefix tailTrace_6621709
  have hstable : (prefixWord ++ tailWord_6621709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621709).length < 2 ^ (prefixWord ++ tailWord_6621709).sum := by decide
  have hdescent : baseEnd_6621709 < baseStart_6621709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621715 : List Nat := [1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 3]
def baseStart_6621715 : Nat := 118140960795 + 6621715 * 2 ^ 59
def prefixEnd_6621715 : Nat := 4983230072969 + 3 ^ 40 * 6621715 * 2
def baseEnd_6621715 : Nat := 3400122552086665243309793

theorem tailTrace_6621715 : CollatzResearch.WordTrace tailWord_6621715 prefixEnd_6621715 3400122552086665243309793 := by
  unfold tailWord_6621715
  simp only [CollatzResearch.WordTrace]
  refine ⟨241513787205664928731650599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161009191470443285821100399 241513787205664928731650599)
  ·
    refine ⟨362270680808497393097475899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241513787205664928731650599 362270680808497393097475899)
    ·
      refine ⟨543406021212746089646213849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362270680808497393097475899 543406021212746089646213849)
      ·
        refine ⟨407554515909559567234660387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543406021212746089646213849 407554515909559567234660387)
        ·
          refine ⟨611331773864339350851990581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407554515909559567234660387 611331773864339350851990581)
          ·
            refine ⟨57312353799781814142374117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 611331773864339350851990581 57312353799781814142374117)
            ·
              refine ⟨10746066337459090151695147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57312353799781814142374117 10746066337459090151695147)
              ·
                refine ⟨16119099506188635227542721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10746066337459090151695147 16119099506188635227542721)
                ·
                  refine ⟨12089324629641476420657041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16119099506188635227542721 12089324629641476420657041)
                  ·
                    refine ⟨9066993472231107315492781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12089324629641476420657041 9066993472231107315492781)
                    ·
                      refine ⟨3400122552086665243309793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9066993472231107315492781 3400122552086665243309793)
                      ·
                        rfl

theorem cell23_6621715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 3].length) (baseStart_6621715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621715 prefixEnd_6621715 := by exact prefixLift 6621715
  have htrace : WordTrace (prefixWord ++ tailWord_6621715) baseStart_6621715 baseEnd_6621715 := by
    simpa [prefixWord, tailWord_6621715, baseEnd_6621715] using wordTrace_append hprefix tailTrace_6621715
  have hstable : (prefixWord ++ tailWord_6621715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621715).length < 2 ^ (prefixWord ++ tailWord_6621715).sum := by decide
  have hdescent : baseEnd_6621715 < baseStart_6621715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621766 : List Nat := [6, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_6621766 : Nat := 118140960795 + 6621766 * 2 ^ 59
def prefixEnd_6621766 : Nat := 4983230072969 + 3 ^ 40 * 6621766 * 2
def baseEnd_6621766 : Nat := 3400148739600044543772059

theorem tailTrace_6621766 : CollatzResearch.WordTrace tailWord_6621766 prefixEnd_6621766 3400148739600044543772059 := by
  unfold tailWord_6621766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7547363979015005138804911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 161010431552320109627838101 7547363979015005138804911)
  ·
    refine ⟨11321045968522507708207367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7547363979015005138804911 11321045968522507708207367)
    ·
      refine ⟨16981568952783761562311051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11321045968522507708207367 16981568952783761562311051)
      ·
        refine ⟨25472353429175642343466577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16981568952783761562311051 25472353429175642343466577)
        ·
          refine ⟨19104265071881731757599933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25472353429175642343466577 19104265071881731757599933)
          ·
            refine ⟨7164099401955649409099975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19104265071881731757599933 7164099401955649409099975)
            ·
              refine ⟨10746149102933474113649963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7164099401955649409099975 10746149102933474113649963)
              ·
                refine ⟨16119223654400211170474945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10746149102933474113649963 16119223654400211170474945)
                ·
                  refine ⟨12089417740800158377856209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16119223654400211170474945 12089417740800158377856209)
                  ·
                    refine ⟨9067063305600118783392157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12089417740800158377856209 9067063305600118783392157)
                    ·
                      refine ⟨3400148739600044543772059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9067063305600118783392157 3400148739600044543772059)
                      ·
                        rfl

theorem cell23_6621766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_6621766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621766 prefixEnd_6621766 := by exact prefixLift 6621766
  have htrace : WordTrace (prefixWord ++ tailWord_6621766) baseStart_6621766 baseEnd_6621766 := by
    simpa [prefixWord, tailWord_6621766, baseEnd_6621766] using wordTrace_append hprefix tailTrace_6621766
  have hstable : (prefixWord ++ tailWord_6621766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621766).length < 2 ^ (prefixWord ++ tailWord_6621766).sum := by decide
  have hdescent : baseEnd_6621766 < baseStart_6621766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621795 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 4, 4]
def baseStart_6621795 : Nat := 118140960795 + 6621795 * 2 ^ 59
def prefixEnd_6621795 : Nat := 4983230072969 + 3 ^ 40 * 6621795 * 2
def baseEnd_6621795 : Nat := 1133387876846341643436475

theorem tailTrace_6621795 : CollatzResearch.WordTrace tailWord_6621795 prefixEnd_6621795 1133387876846341643436475 := by
  unfold tailWord_6621795
  simp only [CollatzResearch.WordTrace]
  refine ⟨241516705045375102394562839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161011136696916734929708559 241516705045375102394562839)
  ·
    refine ⟨362275057568062653591844259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241516705045375102394562839 362275057568062653591844259)
    ·
      refine ⟨543412586352093980387766389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362275057568062653591844259 543412586352093980387766389)
      ·
        refine ⟨50944929970508810661353099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 543412586352093980387766389 50944929970508810661353099)
        ·
          refine ⟨76417394955763215992029649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50944929970508810661353099 76417394955763215992029649)
          ·
            refine ⟨57313046216822411994022237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76417394955763215992029649 57313046216822411994022237)
            ·
              refine ⟨21492392331308404497758339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57313046216822411994022237 21492392331308404497758339)
              ·
                refine ⟨32238588496962606746637509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21492392331308404497758339 32238588496962606746637509)
                ·
                  refine ⟨6044735343180488764994533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32238588496962606746637509 6044735343180488764994533)
                  ·
                    refine ⟨1133387876846341643436475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6044735343180488764994533 1133387876846341643436475)
                    ·
                      rfl

theorem cell23_6621795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 4].length) (baseStart_6621795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621795 prefixEnd_6621795 := by exact prefixLift 6621795
  have htrace : WordTrace (prefixWord ++ tailWord_6621795) baseStart_6621795 baseEnd_6621795 := by
    simpa [prefixWord, tailWord_6621795, baseEnd_6621795] using wordTrace_append hprefix tailTrace_6621795
  have hstable : (prefixWord ++ tailWord_6621795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621795).length < 2 ^ (prefixWord ++ tailWord_6621795).sum := by decide
  have hdescent : baseEnd_6621795 < baseStart_6621795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621805 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_6621805 : Nat := 118140960795 + 6621805 * 2 ^ 59
def prefixEnd_6621805 : Nat := 4983230072969 + 3 ^ 40 * 6621805 * 2
def baseEnd_6621805 : Nat := 3400168765345569891184379

theorem tailTrace_6621805 : CollatzResearch.WordTrace tailWord_6621805 prefixEnd_6621805 3400168765345569891184379 := by
  unfold tailWord_6621805
  simp only [CollatzResearch.WordTrace]
  refine ⟨241517069775338874102426869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161011379850225916068284579 241517069775338874102426869)
  ·
    refine ⟨22642225291438019447102519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 241517069775338874102426869 22642225291438019447102519)
    ·
      refine ⟨33963337937157029170653779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22642225291438019447102519 33963337937157029170653779)
      ·
        refine ⟨50945006905735543755980669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33963337937157029170653779 50945006905735543755980669)
        ·
          refine ⟨19104377589650828908492751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50945006905735543755980669 19104377589650828908492751)
          ·
            refine ⟨28656566384476243362739127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19104377589650828908492751 28656566384476243362739127)
            ·
              refine ⟨42984849576714365044108691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28656566384476243362739127 42984849576714365044108691)
              ·
                refine ⟨64477274365071547566163037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42984849576714365044108691 64477274365071547566163037)
                ·
                  refine ⟨24178977886901830337311139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64477274365071547566163037 24178977886901830337311139)
                  ·
                    refine ⟨36268466830352745505966709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24178977886901830337311139 36268466830352745505966709)
                    ·
                      refine ⟨3400168765345569891184379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36268466830352745505966709 3400168765345569891184379)
                      ·
                        rfl

theorem cell23_6621805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_6621805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621805 prefixEnd_6621805 := by exact prefixLift 6621805
  have htrace : WordTrace (prefixWord ++ tailWord_6621805) baseStart_6621805 baseEnd_6621805 := by
    simpa [prefixWord, tailWord_6621805, baseEnd_6621805] using wordTrace_append hprefix tailTrace_6621805
  have hstable : (prefixWord ++ tailWord_6621805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621805).length < 2 ^ (prefixWord ++ tailWord_6621805).sum := by decide
  have hdescent : baseEnd_6621805 < baseStart_6621805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621815 : List Nat := [1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 4]
def baseStart_6621815 : Nat := 118140960795 + 6621815 * 2 ^ 59
def prefixEnd_6621815 : Nat := 4983230072969 + 3 ^ 40 * 6621815 * 2
def baseEnd_6621815 : Nat := 3400173900152114852059333

theorem tailTrace_6621815 : CollatzResearch.WordTrace tailWord_6621815 prefixEnd_6621815 3400173900152114852059333 := by
  unfold tailWord_6621815
  simp only [CollatzResearch.WordTrace]
  refine ⟨241517434505302645810290899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161011623003535097206860599 241517434505302645810290899)
  ·
    refine ⟨362276151757953968715436349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241517434505302645810290899 362276151757953968715436349)
    ·
      refine ⟨135853556909232738268288631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362276151757953968715436349 135853556909232738268288631)
      ·
        refine ⟨203780335363849107402432947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135853556909232738268288631 203780335363849107402432947)
        ·
          refine ⟨305670503045773661103649421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203780335363849107402432947 305670503045773661103649421)
          ·
            refine ⟨114626438642165122913868533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305670503045773661103649421 114626438642165122913868533)
            ·
              refine ⟨10746228622702980273175175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114626438642165122913868533 10746228622702980273175175)
              ·
                refine ⟨16119342934054470409762763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10746228622702980273175175 16119342934054470409762763)
                ·
                  refine ⟨24179014401081705614644145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16119342934054470409762763 24179014401081705614644145)
                  ·
                    refine ⟨18134260800811279210983109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24179014401081705614644145 18134260800811279210983109)
                    ·
                      refine ⟨3400173900152114852059333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18134260800811279210983109 3400173900152114852059333)
                      ·
                        rfl

theorem cell23_6621815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_6621815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621815 prefixEnd_6621815 := by exact prefixLift 6621815
  have htrace : WordTrace (prefixWord ++ tailWord_6621815) baseStart_6621815 baseEnd_6621815 := by
    simpa [prefixWord, tailWord_6621815, baseEnd_6621815] using wordTrace_append hprefix tailTrace_6621815
  have hstable : (prefixWord ++ tailWord_6621815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621815).length < 2 ^ (prefixWord ++ tailWord_6621815).sum := by decide
  have hdescent : baseEnd_6621815 < baseStart_6621815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621863 : List Nat := [1, 1, 6, 3, 1, 2, 2, 1, 2, 4]
def baseStart_6621863 : Nat := 118140960795 + 6621863 * 2 ^ 59
def prefixEnd_6621863 : Nat := 4983230072969 + 3 ^ 40 * 6621863 * 2
def baseEnd_6621863 : Nat := 1133399515741176888086371

theorem tailTrace_6621863 : CollatzResearch.WordTrace tailWord_6621863 prefixEnd_6621863 1133399515741176888086371 := by
  unfold tailWord_6621863
  simp only [CollatzResearch.WordTrace]
  refine ⟨241519185209128750008038243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161012790139419166672025495 241519185209128750008038243)
  ·
    refine ⟨362278777813693125012057365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241519185209128750008038243 362278777813693125012057365)
    ·
      refine ⟨16981817710016865234940189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 362278777813693125012057365 16981817710016865234940189)
      ·
        refine ⟨6368181641256324463102571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16981817710016865234940189 6368181641256324463102571)
        ·
          refine ⟨9552272461884486694653857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6368181641256324463102571 9552272461884486694653857)
          ·
            refine ⟨7164204346413365020990393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9552272461884486694653857 7164204346413365020990393)
            ·
              refine ⟨5373153259810023765742795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7164204346413365020990393 5373153259810023765742795)
              ·
                refine ⟨8059729889715035648614193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5373153259810023765742795 8059729889715035648614193)
                ·
                  refine ⟨6044797417286276736460645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8059729889715035648614193 6044797417286276736460645)
                  ·
                    refine ⟨1133399515741176888086371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6044797417286276736460645 1133399515741176888086371)
                    ·
                      rfl

theorem cell23_6621863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_6621863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621863 prefixEnd_6621863 := by exact prefixLift 6621863
  have htrace : WordTrace (prefixWord ++ tailWord_6621863) baseStart_6621863 baseEnd_6621863 := by
    simpa [prefixWord, tailWord_6621863, baseEnd_6621863] using wordTrace_append hprefix tailTrace_6621863
  have hstable : (prefixWord ++ tailWord_6621863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621863).length < 2 ^ (prefixWord ++ tailWord_6621863).sum := by decide
  have hdescent : baseEnd_6621863 < baseStart_6621863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621873 : List Nat := [1, 2, 2, 6, 2, 1, 1, 2, 1, 2, 3]
def baseStart_6621873 : Nat := 118140960795 + 6621873 * 2 ^ 59
def prefixEnd_6621873 : Nat := 4983230072969 + 3 ^ 40 * 6621873 * 2
def baseEnd_6621873 : Nat := 3400203682030075625134067

theorem tailTrace_6621873 : CollatzResearch.WordTrace tailWord_6621873 prefixEnd_6621873 3400203682030075625134067 := by
  unfold tailWord_6621873
  simp only [CollatzResearch.WordTrace]
  refine ⟨241519549939092521715902273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161013033292728347810601515 241519549939092521715902273)
  ·
    refine ⟨181139662454319391286926705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241519549939092521715902273 181139662454319391286926705)
    ·
      refine ⟨135854746840739543465195029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181139662454319391286926705 135854746840739543465195029)
      ·
        refine ⟨6368191258159666099931017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 135854746840739543465195029 6368191258159666099931017)
        ·
          refine ⟨4776143443619749574948263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6368191258159666099931017 4776143443619749574948263)
          ·
            refine ⟨7164215165429624362422395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4776143443619749574948263 7164215165429624362422395)
            ·
              refine ⟨10746322748144436543633593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7164215165429624362422395 10746322748144436543633593)
              ·
                refine ⟨8059742061108327407725195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10746322748144436543633593 8059742061108327407725195)
                ·
                  refine ⟨12089613091662491111587793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8059742061108327407725195 12089613091662491111587793)
                  ·
                    refine ⟨9067209818746868333690845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12089613091662491111587793 9067209818746868333690845)
                    ·
                      refine ⟨3400203682030075625134067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9067209818746868333690845 3400203682030075625134067)
                      ·
                        rfl

theorem cell23_6621873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_6621873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621873 prefixEnd_6621873 := by exact prefixLift 6621873
  have htrace : WordTrace (prefixWord ++ tailWord_6621873) baseStart_6621873 baseEnd_6621873 := by
    simpa [prefixWord, tailWord_6621873, baseEnd_6621873] using wordTrace_append hprefix tailTrace_6621873
  have hstable : (prefixWord ++ tailWord_6621873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621873).length < 2 ^ (prefixWord ++ tailWord_6621873).sum := by decide
  have hdescent : baseEnd_6621873 < baseStart_6621873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621879 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 3, 3, 2]
def baseStart_6621879 : Nat := 118140960795 + 6621879 * 2 ^ 59
def prefixEnd_6621879 : Nat := 4983230072969 + 3 ^ 40 * 6621879 * 2
def baseEnd_6621879 : Nat := 3400206762914002601659039

theorem tailTrace_6621879 : CollatzResearch.WordTrace tailWord_6621879 prefixEnd_6621879 3400206762914002601659039 := by
  unfold tailWord_6621879
  simp only [CollatzResearch.WordTrace]
  refine ⟨241519768777070784740620691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161013179184713856493747127 241519768777070784740620691)
  ·
    refine ⟨362279653165606177110931037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241519768777070784740620691 362279653165606177110931037)
    ·
      refine ⟨135854869937102316416599139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362279653165606177110931037 135854869937102316416599139)
      ·
        refine ⟨203782304905653474624898709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135854869937102316416599139 203782304905653474624898709)
        ·
          refine ⟨9552295542452506623042127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 203782304905653474624898709 9552295542452506623042127)
          ·
            refine ⟨14328443313678759934563191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9552295542452506623042127 14328443313678759934563191)
            ·
              refine ⟨21492664970518139901844787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14328443313678759934563191 21492664970518139901844787)
              ·
                refine ⟨32238997455777209852767181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21492664970518139901844787 32238997455777209852767181)
                ·
                  refine ⟨12089624045916453694787693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32238997455777209852767181 12089624045916453694787693)
                  ·
                    refine ⟨4533609017218670135545385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12089624045916453694787693 4533609017218670135545385)
                    ·
                      refine ⟨3400206762914002601659039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4533609017218670135545385 3400206762914002601659039)
                      ·
                        rfl

theorem cell23_6621879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 3, 2].length) (baseStart_6621879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621879 prefixEnd_6621879 := by exact prefixLift 6621879
  have htrace : WordTrace (prefixWord ++ tailWord_6621879) baseStart_6621879 baseEnd_6621879 := by
    simpa [prefixWord, tailWord_6621879, baseEnd_6621879] using wordTrace_append hprefix tailTrace_6621879
  have hstable : (prefixWord ++ tailWord_6621879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621879).length < 2 ^ (prefixWord ++ tailWord_6621879).sum := by decide
  have hdescent : baseEnd_6621879 < baseStart_6621879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621896 : List Nat := [2, 1, 3, 1, 2, 4, 3, 1, 1, 3, 2]
def baseStart_6621896 : Nat := 118140960795 + 6621896 * 2 ^ 59
def prefixEnd_6621896 : Nat := 4983230072969 + 3 ^ 40 * 6621896 * 2
def baseEnd_6621896 : Nat := 3400215492085129035146461

theorem tailTrace_6621896 : CollatzResearch.WordTrace tailWord_6621896 prefixEnd_6621896 3400215492085129035146461 := by
  unfold tailWord_6621896
  simp only [CollatzResearch.WordTrace]
  refine ⟨120760194409004598321994771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161013592545339464429326361 120760194409004598321994771)
  ·
    refine ⟨181140291613506897482992157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120760194409004598321994771 181140291613506897482992157)
    ·
      refine ⟨67927609355065086556122059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181140291613506897482992157 67927609355065086556122059)
      ·
        refine ⟨101891414032597629834183089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67927609355065086556122059 101891414032597629834183089)
        ·
          refine ⟨76418560524448222375637317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101891414032597629834183089 76418560524448222375637317)
          ·
            refine ⟨14328480098334041695431997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76418560524448222375637317 14328480098334041695431997)
            ·
              refine ⟨5373180036875265635786999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14328480098334041695431997 5373180036875265635786999)
              ·
                refine ⟨8059770055312898453680499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5373180036875265635786999 8059770055312898453680499)
                ·
                  refine ⟨12089655082969347680520749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8059770055312898453680499 12089655082969347680520749)
                  ·
                    refine ⟨4533620656113505380195281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12089655082969347680520749 4533620656113505380195281)
                    ·
                      refine ⟨3400215492085129035146461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4533620656113505380195281 3400215492085129035146461)
                      ·
                        rfl

theorem cell23_6621896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_6621896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621896 prefixEnd_6621896 := by exact prefixLift 6621896
  have htrace : WordTrace (prefixWord ++ tailWord_6621896) baseStart_6621896 baseEnd_6621896 := by
    simpa [prefixWord, tailWord_6621896, baseEnd_6621896] using wordTrace_append hprefix tailTrace_6621896
  have hstable : (prefixWord ++ tailWord_6621896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621896).length < 2 ^ (prefixWord ++ tailWord_6621896).sum := by decide
  have hdescent : baseEnd_6621896 < baseStart_6621896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621905 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 2, 2, 4]
def baseStart_6621905 : Nat := 118140960795 + 6621905 * 2 ^ 59
def prefixEnd_6621905 : Nat := 4983230072969 + 3 ^ 40 * 6621905 * 2
def baseEnd_6621905 : Nat := 3400220113411019499933919

theorem tailTrace_6621905 : CollatzResearch.WordTrace tailWord_6621905 prefixEnd_6621905 3400220113411019499933919 := by
  unfold tailWord_6621905
  simp only [CollatzResearch.WordTrace]
  refine ⟨241520717074976591181067169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161013811383317727454044779 241520717074976591181067169)
  ·
    refine ⟨181140537806232443385800377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241520717074976591181067169 181140537806232443385800377)
    ·
      refine ⟨135855403354674332539350283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181140537806232443385800377 135855403354674332539350283)
      ·
        refine ⟨203783105032011498809025425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135855403354674332539350283 203783105032011498809025425)
        ·
          refine ⟨152837328774008624106769069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203783105032011498809025425 152837328774008624106769069)
          ·
            refine ⟨57313998290253234040038401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152837328774008624106769069 57313998290253234040038401)
            ·
              refine ⟨42985498717689925530028801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57313998290253234040038401 42985498717689925530028801)
              ·
                refine ⟨32239124038267444147521601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42985498717689925530028801 32239124038267444147521601)
                ·
                  refine ⟨24179343028700583110641201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32239124038267444147521601 24179343028700583110641201)
                  ·
                    refine ⟨18134507271525437332980901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24179343028700583110641201 18134507271525437332980901)
                    ·
                      refine ⟨3400220113411019499933919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18134507271525437332980901 3400220113411019499933919)
                      ·
                        rfl

theorem cell23_6621905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_6621905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621905 prefixEnd_6621905 := by exact prefixLift 6621905
  have htrace : WordTrace (prefixWord ++ tailWord_6621905) baseStart_6621905 baseEnd_6621905 := by
    simpa [prefixWord, tailWord_6621905, baseEnd_6621905] using wordTrace_append hprefix tailTrace_6621905
  have hstable : (prefixWord ++ tailWord_6621905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621905).length < 2 ^ (prefixWord ++ tailWord_6621905).sum := by decide
  have hdescent : baseEnd_6621905 < baseStart_6621905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621942 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_6621942 : Nat := 118140960795 + 6621942 * 2 ^ 59
def prefixEnd_6621942 : Nat := 4983230072969 + 3 ^ 40 * 6621942 * 2
def baseEnd_6621942 : Nat := 3400239112195235855171249

theorem tailTrace_6621942 : CollatzResearch.WordTrace tailWord_6621942 prefixEnd_6621942 3400239112195235855171249 := by
  unfold tailWord_6621942
  simp only [CollatzResearch.WordTrace]
  refine ⟨15095129160990159156260255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161014711050561697666776053 15095129160990159156260255)
  ·
    refine ⟨22642693741485238734390383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15095129160990159156260255 22642693741485238734390383)
    ·
      refine ⟨33964040612227858101585575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22642693741485238734390383 33964040612227858101585575)
      ·
        refine ⟨50946060918341787152378363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33964040612227858101585575 50946060918341787152378363)
        ·
          refine ⟨76419091377512680728567545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50946060918341787152378363 76419091377512680728567545)
          ·
            refine ⟨57314318533134510546425659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76419091377512680728567545 57314318533134510546425659)
            ·
              refine ⟨85971477799701765819638489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57314318533134510546425659 85971477799701765819638489)
              ·
                refine ⟨64478608349776324364728867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85971477799701765819638489 64478608349776324364728867)
                ·
                  refine ⟨96717912524664486547093301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64478608349776324364728867 96717912524664486547093301)
                  ·
                    refine ⟨9067304299187295613789997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96717912524664486547093301 9067304299187295613789997)
                    ·
                      refine ⟨3400239112195235855171249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9067304299187295613789997 3400239112195235855171249)
                      ·
                        rfl

theorem cell23_6621942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_6621942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621942 prefixEnd_6621942 := by exact prefixLift 6621942
  have htrace : WordTrace (prefixWord ++ tailWord_6621942) baseStart_6621942 baseEnd_6621942 := by
    simpa [prefixWord, tailWord_6621942, baseEnd_6621942] using wordTrace_append hprefix tailTrace_6621942
  have hstable : (prefixWord ++ tailWord_6621942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621942).length < 2 ^ (prefixWord ++ tailWord_6621942).sum := by decide
  have hdescent : baseEnd_6621942 < baseStart_6621942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622002 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3]
def baseStart_6622002 : Nat := 118140960795 + 6622002 * 2 ^ 59
def prefixEnd_6622002 : Nat := 4983230072969 + 3 ^ 40 * 6622002 * 2
def baseEnd_6622002 : Nat := 3400269921034505620420973

theorem tailTrace_6622002 : CollatzResearch.WordTrace tailWord_6622002 prefixEnd_6622002 3400269921034505620420973 := by
  unfold tailWord_6622002
  simp only [CollatzResearch.WordTrace]
  refine ⟨60381063738906294186837065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161016169970416784498232173 60381063738906294186837065)
  ·
    refine ⟨45285797804179720640127799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60381063738906294186837065 45285797804179720640127799)
    ·
      refine ⟨67928696706269580960191699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45285797804179720640127799 67928696706269580960191699)
      ·
        refine ⟨101893045059404371440287549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67928696706269580960191699 101893045059404371440287549)
        ·
          refine ⟨38209891897276639290107831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101893045059404371440287549 38209891897276639290107831)
          ·
            refine ⟨57314837845914958935161747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38209891897276639290107831 57314837845914958935161747)
            ·
              refine ⟨85972256768872438402742621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57314837845914958935161747 85972256768872438402742621)
              ·
                refine ⟨32239596288327164401028483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85972256768872438402742621 32239596288327164401028483)
                ·
                  refine ⟨48359394432490746601542725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32239596288327164401028483 48359394432490746601542725)
                  ·
                    refine ⟨9067386456092014987789261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48359394432490746601542725 9067386456092014987789261)
                    ·
                      refine ⟨3400269921034505620420973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9067386456092014987789261 3400269921034505620420973)
                      ·
                        rfl

theorem cell23_6622002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_6622002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622002 prefixEnd_6622002 := by exact prefixLift 6622002
  have htrace : WordTrace (prefixWord ++ tailWord_6622002) baseStart_6622002 baseEnd_6622002 := by
    simpa [prefixWord, tailWord_6622002, baseEnd_6622002] using wordTrace_append hprefix tailTrace_6622002
  have hstable : (prefixWord ++ tailWord_6622002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622002).length < 2 ^ (prefixWord ++ tailWord_6622002).sum := by decide
  have hdescent : baseEnd_6622002 < baseStart_6622002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622039 : List Nat := [1, 1, 3, 2, 4, 1, 4, 1, 6]
def baseStart_6622039 : Nat := 118140960795 + 6622039 * 2 ^ 59
def prefixEnd_6622039 : Nat := 4983230072969 + 3 ^ 40 * 6622039 * 2
def baseEnd_6622039 : Nat := 377809879979857997295367

theorem tailTrace_6622039 : CollatzResearch.WordTrace tailWord_6622039 prefixEnd_6622039 377809879979857997295367 := by
  unfold tailWord_6622039
  simp only [CollatzResearch.WordTrace]
  refine ⟨241525604456491132066445171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161017069637660754710963447 241525604456491132066445171)
  ·
    refine ⟨362288406684736698099667757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241525604456491132066445171 362288406684736698099667757)
    ·
      refine ⟨135858152506776261787375409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362288406684736698099667757 135858152506776261787375409)
      ·
        refine ⟨101893614380082196340531557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135858152506776261787375409 101893614380082196340531557)
        ·
          refine ⟨19105052696265411813849667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101893614380082196340531557 19105052696265411813849667)
          ·
            refine ⟨28657579044398117720774501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19105052696265411813849667 28657579044398117720774501)
            ·
              refine ⟨5373296070824647072645219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28657579044398117720774501 5373296070824647072645219)
              ·
                refine ⟨8059944106236970608967829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5373296070824647072645219 8059944106236970608967829)
                ·
                  refine ⟨377809879979857997295367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8059944106236970608967829 377809879979857997295367)
                  ·
                    rfl

theorem cell23_6622039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 6].length) (baseStart_6622039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622039 prefixEnd_6622039 := by exact prefixLift 6622039
  have htrace : WordTrace (prefixWord ++ tailWord_6622039) baseStart_6622039 baseEnd_6622039 := by
    simpa [prefixWord, tailWord_6622039, baseEnd_6622039] using wordTrace_append hprefix tailTrace_6622039
  have hstable : (prefixWord ++ tailWord_6622039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622039).length < 2 ^ (prefixWord ++ tailWord_6622039).sum := by decide
  have hdescent : baseEnd_6622039 < baseStart_6622039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622059 : List Nat := [1, 1, 1, 1, 2, 2, 5, 3, 2, 3, 2]
def baseStart_6622059 : Nat := 118140960795 + 6622059 * 2 ^ 59
def prefixEnd_6622059 : Nat := 4983230072969 + 3 ^ 40 * 6622059 * 2
def baseEnd_6622059 : Nat := 3400299189431811897408211

theorem tailTrace_6622059 : CollatzResearch.WordTrace tailWord_6622059 prefixEnd_6622059 3400299189431811897408211 := by
  unfold tailWord_6622059
  simp only [CollatzResearch.WordTrace]
  refine ⟨241526333916418675482173231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161017555944279116988115487 241526333916418675482173231)
  ·
    refine ⟨362289500874628013223259847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241526333916418675482173231 362289500874628013223259847)
    ·
      refine ⟨543434251311942019834889771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362289500874628013223259847 543434251311942019834889771)
      ·
        refine ⟨815151376967913029752334657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543434251311942019834889771 815151376967913029752334657)
        ·
          refine ⟨611363532725934772314250993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 815151376967913029752334657 611363532725934772314250993)
          ·
            refine ⟨458522649544451079235688245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 611363532725934772314250993 458522649544451079235688245)
            ·
              refine ⟨42986498394792288678345773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 458522649544451079235688245 42986498394792288678345773)
              ·
                refine ⟨16119936898047108254379665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42986498394792288678345773 16119936898047108254379665)
                ·
                  refine ⟨12089952673535331190784749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16119936898047108254379665 12089952673535331190784749)
                  ·
                    refine ⟨4533732252575749196544281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12089952673535331190784749 4533732252575749196544281)
                    ·
                      refine ⟨3400299189431811897408211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4533732252575749196544281 3400299189431811897408211)
                      ·
                        rfl

theorem cell23_6622059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 3, 2].length) (baseStart_6622059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622059 prefixEnd_6622059 := by exact prefixLift 6622059
  have htrace : WordTrace (prefixWord ++ tailWord_6622059) baseStart_6622059 baseEnd_6622059 := by
    simpa [prefixWord, tailWord_6622059, baseEnd_6622059] using wordTrace_append hprefix tailTrace_6622059
  have hstable : (prefixWord ++ tailWord_6622059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622059).length < 2 ^ (prefixWord ++ tailWord_6622059).sum := by decide
  have hdescent : baseEnd_6622059 < baseStart_6622059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622092 : List Nat := [2, 2, 1, 2, 1, 2, 2, 4, 1, 1, 5]
def baseStart_6622092 : Nat := 118140960795 + 6622092 * 2 ^ 59
def prefixEnd_6622092 : Nat := 4983230072969 + 3 ^ 40 * 6622092 * 2
def baseEnd_6622092 : Nat := 3400316134293410268295559

theorem tailTrace_6622092 : CollatzResearch.WordTrace tailWord_6622092 prefixEnd_6622092 3400316134293410268295559 := by
  unfold tailWord_6622092
  simp only [CollatzResearch.WordTrace]
  refine ⟨120763768762649561059062265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161018358350199414745416353 120763768762649561059062265)
  ·
    refine ⟨90572826571987170794296699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120763768762649561059062265 90572826571987170794296699)
    ·
      refine ⟨135859239857980756191445049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90572826571987170794296699 135859239857980756191445049)
      ·
        refine ⟨101894429893485567143583787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135859239857980756191445049 101894429893485567143583787)
        ·
          refine ⟨152841644840228350715375681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101894429893485567143583787 152841644840228350715375681)
          ·
            refine ⟨114631233630171263036531761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152841644840228350715375681 114631233630171263036531761)
            ·
              refine ⟨85973425222628447277398821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114631233630171263036531761 85973425222628447277398821)
              ·
                refine ⟨16120017229242833864512279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85973425222628447277398821 16120017229242833864512279)
                ·
                  refine ⟨24180025843864250796768419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16120017229242833864512279 24180025843864250796768419)
                  ·
                    refine ⟨36270038765796376195152629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24180025843864250796768419 36270038765796376195152629)
                    ·
                      refine ⟨3400316134293410268295559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36270038765796376195152629 3400316134293410268295559)
                      ·
                        rfl

theorem cell23_6622092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_6622092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622092 prefixEnd_6622092 := by exact prefixLift 6622092
  have htrace : WordTrace (prefixWord ++ tailWord_6622092) baseStart_6622092 baseEnd_6622092 := by
    simpa [prefixWord, tailWord_6622092, baseEnd_6622092] using wordTrace_append hprefix tailTrace_6622092
  have hstable : (prefixWord ++ tailWord_6622092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622092).length < 2 ^ (prefixWord ++ tailWord_6622092).sum := by decide
  have hdescent : baseEnd_6622092 < baseStart_6622092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622109 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_6622109 : Nat := 118140960795 + 6622109 * 2 ^ 59
def prefixEnd_6622109 : Nat := 4983230072969 + 3 ^ 40 * 6622109 * 2
def baseEnd_6622109 : Nat := 3400324863464536701782981

theorem tailTrace_6622109 : CollatzResearch.WordTrace tailWord_6622109 prefixEnd_6622109 3400324863464536701782981 := by
  unfold tailWord_6622109
  simp only [CollatzResearch.WordTrace]
  refine ⟨241528157566237534021493381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161018771710825022680995587 241528157566237534021493381)
  ·
    refine ⟨45286529543669537629030009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241528157566237534021493381 45286529543669537629030009)
    ·
      refine ⟨33964897157752153221772507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45286529543669537629030009 33964897157752153221772507)
      ·
        refine ⟨50947345736628229832658761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33964897157752153221772507 50947345736628229832658761)
        ·
          refine ⟨38210509302471172374494071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50947345736628229832658761 38210509302471172374494071)
          ·
            refine ⟨57315763953706758561741107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38210509302471172374494071 57315763953706758561741107)
            ·
              refine ⟨85973645930560137842611661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57315763953706758561741107 85973645930560137842611661)
              ·
                refine ⟨32240117223960051690979373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85973645930560137842611661 32240117223960051690979373)
                ·
                  refine ⟨12090043958985019384117265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32240117223960051690979373 12090043958985019384117265)
                  ·
                    refine ⟨9067532969238764538087949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12090043958985019384117265 9067532969238764538087949)
                    ·
                      refine ⟨3400324863464536701782981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9067532969238764538087949 3400324863464536701782981)
                      ·
                        rfl

theorem cell23_6622109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_6622109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622109 prefixEnd_6622109 := by exact prefixLift 6622109
  have htrace : WordTrace (prefixWord ++ tailWord_6622109) baseStart_6622109 baseEnd_6622109 := by
    simpa [prefixWord, tailWord_6622109, baseEnd_6622109] using wordTrace_append hprefix tailTrace_6622109
  have hstable : (prefixWord ++ tailWord_6622109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622109).length < 2 ^ (prefixWord ++ tailWord_6622109).sum := by decide
  have hdescent : baseEnd_6622109 < baseStart_6622109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622157 : List Nat := [1, 6, 3, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_6622157 : Nat := 118140960795 + 6622157 * 2 ^ 59
def prefixEnd_6622157 : Nat := 4983230072969 + 3 ^ 40 * 6622157 * 2
def baseEnd_6622157 : Nat := 3400349510535952513982761

theorem tailTrace_6622157 : CollatzResearch.WordTrace tailWord_6622157 prefixEnd_6622157 3400349510535952513982761 := by
  unfold tailWord_6622157
  simp only [CollatzResearch.WordTrace]
  refine ⟨241529908270063638219240725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161019938846709092146160483 241529908270063638219240725)
  ·
    refine ⟨11321714450159233041526909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 241529908270063638219240725 11321714450159233041526909)
    ·
      refine ⟨4245642918809712390572591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11321714450159233041526909 4245642918809712390572591)
      ·
        refine ⟨6368464378214568585858887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4245642918809712390572591 6368464378214568585858887)
        ·
          refine ⟨9552696567321852878788331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6368464378214568585858887 9552696567321852878788331)
          ·
            refine ⟨14329044850982779318182497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9552696567321852878788331 14329044850982779318182497)
            ·
              refine ⟨10746783638237084488636873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14329044850982779318182497 10746783638237084488636873)
              ·
                refine ⟨8060087728677813366477655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10746783638237084488636873 8060087728677813366477655)
                ·
                  refine ⟨12090131593016720049716483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8060087728677813366477655 12090131593016720049716483)
                  ·
                    refine ⟨18135197389525080074574725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12090131593016720049716483 18135197389525080074574725)
                    ·
                      refine ⟨3400349510535952513982761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18135197389525080074574725 3400349510535952513982761)
                      ·
                        rfl

theorem cell23_6622157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_6622157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622157 prefixEnd_6622157 := by exact prefixLift 6622157
  have htrace : WordTrace (prefixWord ++ tailWord_6622157) baseStart_6622157 baseEnd_6622157 := by
    simpa [prefixWord, tailWord_6622157, baseEnd_6622157] using wordTrace_append hprefix tailTrace_6622157
  have hstable : (prefixWord ++ tailWord_6622157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622157).length < 2 ^ (prefixWord ++ tailWord_6622157).sum := by decide
  have hdescent : baseEnd_6622157 < baseStart_6622157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622183 : List Nat := [1, 1, 5, 2, 2, 1, 2, 3, 1, 3, 2]
def baseStart_6622183 : Nat := 118140960795 + 6622183 * 2 ^ 59
def prefixEnd_6622183 : Nat := 4983230072969 + 3 ^ 40 * 6622183 * 2
def baseEnd_6622183 : Nat := 3400362861032969412257641

theorem tailTrace_6622183 : CollatzResearch.WordTrace tailWord_6622183 prefixEnd_6622183 3400362861032969412257641 := by
  unfold tailWord_6622183
  simp only [CollatzResearch.WordTrace]
  refine ⟨241530856567969444659687203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161020571045312963106458135 241530856567969444659687203)
  ·
    refine ⟨362296284851954166989530805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241530856567969444659687203 362296284851954166989530805)
    ·
      refine ⟨33965276704870703155268513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 362296284851954166989530805 33965276704870703155268513)
      ·
        refine ⟨25473957528653027366451385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33965276704870703155268513 25473957528653027366451385)
        ·
          refine ⟨19105468146489770524838539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25473957528653027366451385 19105468146489770524838539)
          ·
            refine ⟨28658202219734655787257809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19105468146489770524838539 28658202219734655787257809)
            ·
              refine ⟨21493651664800991840443357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28658202219734655787257809 21493651664800991840443357)
              ·
                refine ⟨8060119374300371940166259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21493651664800991840443357 8060119374300371940166259)
                ·
                  refine ⟨12090179061450557910249389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8060119374300371940166259 12090179061450557910249389)
                  ·
                    refine ⟨4533817148043959216343521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12090179061450557910249389 4533817148043959216343521)
                    ·
                      refine ⟨3400362861032969412257641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4533817148043959216343521 3400362861032969412257641)
                      ·
                        rfl

theorem cell23_6622183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_6622183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622183 prefixEnd_6622183 := by exact prefixLift 6622183
  have htrace : WordTrace (prefixWord ++ tailWord_6622183) baseStart_6622183 baseEnd_6622183 := by
    simpa [prefixWord, tailWord_6622183, baseEnd_6622183] using wordTrace_append hprefix tailTrace_6622183
  have hstable : (prefixWord ++ tailWord_6622183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622183).length < 2 ^ (prefixWord ++ tailWord_6622183).sum := by decide
  have hdescent : baseEnd_6622183 < baseStart_6622183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622213 : List Nat := [1, 3, 1, 1, 2, 3, 3, 3, 2, 2, 2]
def baseStart_6622213 : Nat := 118140960795 + 6622213 * 2 ^ 59
def prefixEnd_6622213 : Nat := 4983230072969 + 3 ^ 40 * 6622213 * 2
def baseEnd_6622213 : Nat := 3400378265452604294882503

theorem tailTrace_6622213 : CollatzResearch.WordTrace tailWord_6622213 prefixEnd_6622213 3400378265452604294882503 := by
  unfold tailWord_6622213
  simp only [CollatzResearch.WordTrace]
  refine ⟨241531950757860759783279293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161021300505240506522186195 241531950757860759783279293)
  ·
    refine ⟨90574481534197784918729735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241531950757860759783279293 90574481534197784918729735)
    ·
      refine ⟨135861722301296677378094603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90574481534197784918729735 135861722301296677378094603)
      ·
        refine ⟨203792583451945016067141905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135861722301296677378094603 203792583451945016067141905)
        ·
          refine ⟨152844437588958762050356429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203792583451945016067141905 152844437588958762050356429)
          ·
            refine ⟨57316664095859535768883661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152844437588958762050356429 57316664095859535768883661)
            ·
              refine ⟨21493749035947325913331373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57316664095859535768883661 21493749035947325913331373)
              ·
                refine ⟨8060155888480247217499265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21493749035947325913331373 8060155888480247217499265)
                ·
                  refine ⟨6045116916360185413124449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8060155888480247217499265 6045116916360185413124449)
                  ·
                    refine ⟨4533837687270139059843337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6045116916360185413124449 4533837687270139059843337)
                    ·
                      refine ⟨3400378265452604294882503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4533837687270139059843337 3400378265452604294882503)
                      ·
                        rfl

theorem cell23_6622213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 2, 2].length) (baseStart_6622213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622213 prefixEnd_6622213 := by exact prefixLift 6622213
  have htrace : WordTrace (prefixWord ++ tailWord_6622213) baseStart_6622213 baseEnd_6622213 := by
    simpa [prefixWord, tailWord_6622213, baseEnd_6622213] using wordTrace_append hprefix tailTrace_6622213
  have hstable : (prefixWord ++ tailWord_6622213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622213).length < 2 ^ (prefixWord ++ tailWord_6622213).sum := by decide
  have hdescent : baseEnd_6622213 < baseStart_6622213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622247 : List Nat := [1, 1, 7, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_6622247 : Nat := 118140960795 + 6622247 * 2 ^ 59
def prefixEnd_6622247 : Nat := 4983230072969 + 3 ^ 40 * 6622247 * 2
def baseEnd_6622247 : Nat := 3400395723794857161857347

theorem tailTrace_6622247 : CollatzResearch.WordTrace tailWord_6622247 prefixEnd_6622247 3400395723794857161857347 := by
  unfold tailWord_6622247
  simp only [CollatzResearch.WordTrace]
  refine ⟨241533190839737583590016995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161022127226491722393344663 241533190839737583590016995)
  ·
    refine ⟨362299786259606375385025493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241533190839737583590016995 362299786259606375385025493)
    ·
      refine ⟨8491401240459524423086535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 362299786259606375385025493 8491401240459524423086535)
      ·
        refine ⟨12737101860689286634629803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8491401240459524423086535 12737101860689286634629803)
        ·
          refine ⟨19105652791033929951944705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12737101860689286634629803 19105652791033929951944705)
          ·
            refine ⟨14329239593275447463958529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19105652791033929951944705 14329239593275447463958529)
            ·
              refine ⟨10746929694956585597968897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14329239593275447463958529 10746929694956585597968897)
              ·
                refine ⟨8060197271217439198476673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10746929694956585597968897 8060197271217439198476673)
                ·
                  refine ⟨6045147953413079398857505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8060197271217439198476673 6045147953413079398857505)
                  ·
                    refine ⟨4533860965059809549143129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6045147953413079398857505 4533860965059809549143129)
                    ·
                      refine ⟨3400395723794857161857347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4533860965059809549143129 3400395723794857161857347)
                      ·
                        rfl

theorem cell23_6622247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_6622247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622247 prefixEnd_6622247 := by exact prefixLift 6622247
  have htrace : WordTrace (prefixWord ++ tailWord_6622247) baseStart_6622247 baseEnd_6622247 := by
    simpa [prefixWord, tailWord_6622247, baseEnd_6622247] using wordTrace_append hprefix tailTrace_6622247
  have hstable : (prefixWord ++ tailWord_6622247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622247).length < 2 ^ (prefixWord ++ tailWord_6622247).sum := by decide
  have hdescent : baseEnd_6622247 < baseStart_6622247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622286 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2]
def baseStart_6622286 : Nat := 118140960795 + 6622286 * 2 ^ 59
def prefixEnd_6622286 : Nat := 4983230072969 + 3 ^ 40 * 6622286 * 2
def baseEnd_6622286 : Nat := 3400415749540382509269667

theorem tailTrace_6622286 : CollatzResearch.WordTrace tailWord_6622286 prefixEnd_6622286 3400415749540382509269667 := by
  unfold tailWord_6622286
  simp only [CollatzResearch.WordTrace]
  refine ⟨30191826660824536656335839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161023075524397528833791141 30191826660824536656335839)
  ·
    refine ⟨45287739991236804984503759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30191826660824536656335839 45287739991236804984503759)
    ·
      refine ⟨67931609986855207476755639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45287739991236804984503759 67931609986855207476755639)
      ·
        refine ⟨101897414980282811215133459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67931609986855207476755639 101897414980282811215133459)
        ·
          refine ⟨152846122470424216822700189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101897414980282811215133459 152846122470424216822700189)
          ·
            refine ⟨57317295926409081308512571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152846122470424216822700189 57317295926409081308512571)
            ·
              refine ⟨85975943889613621962768857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57317295926409081308512571 85975943889613621962768857)
              ·
                refine ⟨64481957917210216472076643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85975943889613621962768857 64481957917210216472076643)
                ·
                  refine ⟨96722936875815324708114965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64481957917210216472076643 96722936875815324708114965)
                  ·
                    refine ⟨4533887666053843345692889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96722936875815324708114965 4533887666053843345692889)
                    ·
                      refine ⟨3400415749540382509269667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4533887666053843345692889 3400415749540382509269667)
                      ·
                        rfl

theorem cell23_6622286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_6622286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622286 prefixEnd_6622286 := by exact prefixLift 6622286
  have htrace : WordTrace (prefixWord ++ tailWord_6622286) baseStart_6622286 baseEnd_6622286 := by
    simpa [prefixWord, tailWord_6622286, baseEnd_6622286] using wordTrace_append hprefix tailTrace_6622286
  have hstable : (prefixWord ++ tailWord_6622286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622286).length < 2 ^ (prefixWord ++ tailWord_6622286).sum := by decide
  have hdescent : baseEnd_6622286 < baseStart_6622286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622309 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 8]
def baseStart_6622309 : Nat := 118140960795 + 6622309 * 2 ^ 59
def prefixEnd_6622309 : Nat := 4983230072969 + 3 ^ 40 * 6622309 * 2
def baseEnd_6622309 : Nat := 377825284399492879920229

theorem tailTrace_6622309 : CollatzResearch.WordTrace tailWord_6622309 prefixEnd_6622309 377825284399492879920229 := by
  unfold tailWord_6622309
  simp only [CollatzResearch.WordTrace]
  refine ⟨241535452165512968178773981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161023634777008645452515987 241535452165512968178773981)
  ·
    refine ⟨90575794562067363067040243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241535452165512968178773981 90575794562067363067040243)
    ·
      refine ⟨135863691843101044600560365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90575794562067363067040243 135863691843101044600560365)
      ·
        refine ⟨50948884441162891725210137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135863691843101044600560365 50948884441162891725210137)
        ·
          refine ⟨38211663330872168793907603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50948884441162891725210137 38211663330872168793907603)
          ·
            refine ⟨57317494996308253190861405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38211663330872168793907603 57317494996308253190861405)
            ·
              refine ⟨21494060623615594946573027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57317494996308253190861405 21494060623615594946573027)
              ·
                refine ⟨32241090935423392419859541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21494060623615594946573027 32241090935423392419859541)
                ·
                  refine ⟨377825284399492879920229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32241090935423392419859541 377825284399492879920229)
                  ·
                    rfl

theorem cell23_6622309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 8].length) (baseStart_6622309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622309 prefixEnd_6622309 := by exact prefixLift 6622309
  have htrace : WordTrace (prefixWord ++ tailWord_6622309) baseStart_6622309 baseEnd_6622309 := by
    simpa [prefixWord, tailWord_6622309, baseEnd_6622309] using wordTrace_append hprefix tailTrace_6622309
  have hstable : (prefixWord ++ tailWord_6622309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622309).length < 2 ^ (prefixWord ++ tailWord_6622309).sum := by decide
  have hdescent : baseEnd_6622309 < baseStart_6622309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622313 : List Nat := [1, 2, 1, 1, 1, 6, 2, 4, 1, 4]
def baseStart_6622313 : Nat := 118140960795 + 6622313 * 2 ^ 59
def prefixEnd_6622313 : Nat := 4983230072969 + 3 ^ 40 * 6622313 * 2
def baseEnd_6622313 : Nat := 1133476537839351301210681

theorem tailTrace_6622313 : CollatzResearch.WordTrace tailWord_6622313 prefixEnd_6622313 1133476537839351301210681 := by
  unfold tailWord_6622313
  simp only [CollatzResearch.WordTrace]
  refine ⟨241535598057498476861919593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161023732038332317907946395 241535598057498476861919593)
  ·
    refine ⟨181151698543123857646439695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241535598057498476861919593 181151698543123857646439695)
    ·
      refine ⟨271727547814685786469659543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181151698543123857646439695 271727547814685786469659543)
      ·
        refine ⟨407591321722028679704489315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271727547814685786469659543 407591321722028679704489315)
        ·
          refine ⟨611386982583043019556733973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407591321722028679704489315 611386982583043019556733973)
          ·
            refine ⟨28658764808580141541721905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 611386982583043019556733973 28658764808580141541721905)
            ·
              refine ⟨21494073606435106156291429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28658764808580141541721905 21494073606435106156291429)
              ·
                refine ⟨4030138801206582404304643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21494073606435106156291429 4030138801206582404304643)
                ·
                  refine ⟨6045208201809873606456965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4030138801206582404304643 6045208201809873606456965)
                  ·
                    refine ⟨1133476537839351301210681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6045208201809873606456965 1133476537839351301210681)
                    ·
                      rfl

theorem cell23_6622313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 1, 4].length) (baseStart_6622313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622313 prefixEnd_6622313 := by exact prefixLift 6622313
  have htrace : WordTrace (prefixWord ++ tailWord_6622313) baseStart_6622313 baseEnd_6622313 := by
    simpa [prefixWord, tailWord_6622313, baseEnd_6622313] using wordTrace_append hprefix tailTrace_6622313
  have hstable : (prefixWord ++ tailWord_6622313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622313).length < 2 ^ (prefixWord ++ tailWord_6622313).sum := by decide
  have hdescent : baseEnd_6622313 < baseStart_6622313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622393 : List Nat := [1, 2, 1, 4, 1, 3, 3, 2, 1, 1, 4]
def baseStart_6622393 : Nat := 118140960795 + 6622393 * 2 ^ 59
def prefixEnd_6622393 : Nat := 4983230072969 + 3 ^ 40 * 6622393 * 2
def baseEnd_6622393 : Nat := 3400470691970413590631675

theorem tailTrace_6622393 : CollatzResearch.WordTrace tailWord_6622393 prefixEnd_6622393 3400470691970413590631675 := by
  unfold tailWord_6622393
  simp only [CollatzResearch.WordTrace]
  refine ⟨241538515897208650524831833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161025677264805767016554555 241538515897208650524831833)
  ·
    refine ⟨181153886922906487893623875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241538515897208650524831833 181153886922906487893623875)
    ·
      refine ⟨271730830384359731840435813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181153886922906487893623875 271730830384359731840435813)
      ·
        refine ⟨50949530697067449720081715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271730830384359731840435813 50949530697067449720081715)
        ·
          refine ⟨76424296045601174580122573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50949530697067449720081715 76424296045601174580122573)
          ·
            refine ⟨28659111017100440467545965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76424296045601174580122573 28659111017100440467545965)
            ·
              refine ⟨10747166631412665175329737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28659111017100440467545965 10747166631412665175329737)
              ·
                refine ⟨8060374973559498881497303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10747166631412665175329737 8060374973559498881497303)
                ·
                  refine ⟨12090562460339248322245955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8060374973559498881497303 12090562460339248322245955)
                  ·
                    refine ⟨18135843690508872483368933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12090562460339248322245955 18135843690508872483368933)
                    ·
                      refine ⟨3400470691970413590631675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18135843690508872483368933 3400470691970413590631675)
                      ·
                        rfl

theorem cell23_6622393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_6622393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622393 prefixEnd_6622393 := by exact prefixLift 6622393
  have htrace : WordTrace (prefixWord ++ tailWord_6622393) baseStart_6622393 baseEnd_6622393 := by
    simpa [prefixWord, tailWord_6622393, baseEnd_6622393] using wordTrace_append hprefix tailTrace_6622393
  have hstable : (prefixWord ++ tailWord_6622393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622393).length < 2 ^ (prefixWord ++ tailWord_6622393).sum := by decide
  have hdescent : baseEnd_6622393 < baseStart_6622393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622399 : List Nat := [1, 1, 2, 2, 2, 2, 4, 9]
def baseStart_6622399 : Nat := 118140960795 + 6622399 * 2 ^ 59
def prefixEnd_6622399 : Nat := 4983230072969 + 3 ^ 40 * 6622399 * 2
def baseEnd_6622399 : Nat := 125943473068679280265061

theorem tailTrace_6622399 : CollatzResearch.WordTrace tailWord_6622399 prefixEnd_6622399 125943473068679280265061 := by
  unfold tailWord_6622399
  simp only [CollatzResearch.WordTrace]
  refine ⟨241538734735186913549550251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161025823156791275699700167 241538734735186913549550251)
  ·
    refine ⟨362308102102780370324325377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241538734735186913549550251 362308102102780370324325377)
    ·
      refine ⟨271731076577085277743244033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362308102102780370324325377 271731076577085277743244033)
      ·
        refine ⟨203798307432813958307433025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271731076577085277743244033 203798307432813958307433025)
        ·
          refine ⟨152848730574610468730574769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203798307432813958307433025 152848730574610468730574769)
          ·
            refine ⟨114636547930957851547931077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152848730574610468730574769 114636547930957851547931077)
            ·
              refine ⟨21494352737054597165237077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114636547930957851547931077 21494352737054597165237077)
              ·
                refine ⟨125943473068679280265061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21494352737054597165237077 125943473068679280265061)
                ·
                  rfl

theorem cell23_6622399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 9].length) (baseStart_6622399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622399 prefixEnd_6622399 := by exact prefixLift 6622399
  have htrace : WordTrace (prefixWord ++ tailWord_6622399) baseStart_6622399 baseEnd_6622399 := by
    simpa [prefixWord, tailWord_6622399, baseEnd_6622399] using wordTrace_append hprefix tailTrace_6622399
  have hstable : (prefixWord ++ tailWord_6622399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622399).length < 2 ^ (prefixWord ++ tailWord_6622399).sum := by decide
  have hdescent : baseEnd_6622399 < baseStart_6622399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622410 : List Nat := [3, 1, 2, 1, 3, 3, 3, 1, 1, 1, 4]
def baseStart_6622410 : Nat := 118140960795 + 6622410 * 2 ^ 59
def prefixEnd_6622410 : Nat := 4983230072969 + 3 ^ 40 * 6622410 * 2
def baseEnd_6622410 : Nat := 3400479421141540024119097

theorem tailTrace_6622410 : CollatzResearch.WordTrace tailWord_6622410 prefixEnd_6622410 3400479421141540024119097 := by
  unfold tailWord_6622410
  simp only [CollatzResearch.WordTrace]
  refine ⟨60384783984536765607050171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161026090625431374952133789 60384783984536765607050171)
  ·
    refine ⟨90577175976805148410575257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60384783984536765607050171 90577175976805148410575257)
    ·
      refine ⟨67932881982603861307931443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90577175976805148410575257 67932881982603861307931443)
      ·
        refine ⟨101899322973905791961897165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67932881982603861307931443 101899322973905791961897165)
        ·
          refine ⟨38212246115214671985711437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101899322973905791961897165 38212246115214671985711437)
          ·
            refine ⟨14329592293205501994641789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38212246115214671985711437 14329592293205501994641789)
            ·
              refine ⟨5373597109952063247990671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14329592293205501994641789 5373597109952063247990671)
              ·
                refine ⟨8060395664928094871986007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5373597109952063247990671 8060395664928094871986007)
                ·
                  refine ⟨12090593497392142307979011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8060395664928094871986007 12090593497392142307979011)
                  ·
                    refine ⟨18135890246088213461968517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12090593497392142307979011 18135890246088213461968517)
                    ·
                      refine ⟨3400479421141540024119097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18135890246088213461968517 3400479421141540024119097)
                      ·
                        rfl

theorem cell23_6622410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_6622410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622410 prefixEnd_6622410 := by exact prefixLift 6622410
  have htrace : WordTrace (prefixWord ++ tailWord_6622410) baseStart_6622410 baseEnd_6622410 := by
    simpa [prefixWord, tailWord_6622410, baseEnd_6622410] using wordTrace_append hprefix tailTrace_6622410
  have hstable : (prefixWord ++ tailWord_6622410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622410).length < 2 ^ (prefixWord ++ tailWord_6622410).sum := by decide
  have hdescent : baseEnd_6622410 < baseStart_6622410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622426 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3]
def baseStart_6622426 : Nat := 118140960795 + 6622426 * 2 ^ 59
def prefixEnd_6622426 : Nat := 4983230072969 + 3 ^ 40 * 6622426 * 2
def baseEnd_6622426 : Nat := 3400487636832011961519023

theorem tailTrace_6622426 : CollatzResearch.WordTrace tailWord_6622426 prefixEnd_6622426 3400487636832011961519023 := by
  unfold tailWord_6622426
  simp only [CollatzResearch.WordTrace]
  refine ⟨60384929876522274290195783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161026479670726064773855421 60384929876522274290195783)
  ·
    refine ⟨90577394814783411435293675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60384929876522274290195783 90577394814783411435293675)
    ·
      refine ⟨135866092222175117152940513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90577394814783411435293675 135866092222175117152940513)
      ·
        refine ⟨101899569166631337864705385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135866092222175117152940513 101899569166631337864705385)
        ·
          refine ⟨76424676874973503398529039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101899569166631337864705385 76424676874973503398529039)
          ·
            refine ⟨114637015312460255097793559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76424676874973503398529039 114637015312460255097793559)
            ·
              refine ⟨171955522968690382646690339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114637015312460255097793559 171955522968690382646690339)
              ·
                refine ⟨257933284453035573970035509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171955522968690382646690339 257933284453035573970035509)
                ·
                  refine ⟨24181245417472085059690829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 257933284453035573970035509 24181245417472085059690829)
                  ·
                    refine ⟨9067967031552031897384061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24181245417472085059690829 9067967031552031897384061)
                    ·
                      refine ⟨3400487636832011961519023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9067967031552031897384061 3400487636832011961519023)
                      ·
                        rfl

theorem cell23_6622426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_6622426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622426 prefixEnd_6622426 := by exact prefixLift 6622426
  have htrace : WordTrace (prefixWord ++ tailWord_6622426) baseStart_6622426 baseEnd_6622426 := by
    simpa [prefixWord, tailWord_6622426, baseEnd_6622426] using wordTrace_append hprefix tailTrace_6622426
  have hstable : (prefixWord ++ tailWord_6622426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622426).length < 2 ^ (prefixWord ++ tailWord_6622426).sum := by decide
  have hdescent : baseEnd_6622426 < baseStart_6622426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622443 : List Nat := [1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 3]
def baseStart_6622443 : Nat := 118140960795 + 6622443 * 2 ^ 59
def prefixEnd_6622443 : Nat := 4983230072969 + 3 ^ 40 * 6622443 * 2
def baseEnd_6622443 : Nat := 3400496366003138395006445

theorem tailTrace_6622443 : CollatzResearch.WordTrace tailWord_6622443 prefixEnd_6622443 3400496366003138395006445 := by
  unfold tailWord_6622443
  simp only [CollatzResearch.WordTrace]
  refine ⟨241540339547027509064151983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161026893031351672709434655 241540339547027509064151983)
  ·
    refine ⟨362310509320541263596227975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241540339547027509064151983 362310509320541263596227975)
    ·
      refine ⟨543465763980811895394341963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362310509320541263596227975 543465763980811895394341963)
      ·
        refine ⟨815198645971217843091512945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543465763980811895394341963 815198645971217843091512945)
        ·
          refine ⟨611398984478413382318634709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 815198645971217843091512945 611398984478413382318634709)
          ·
            refine ⟨14329663698712813648093001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 611398984478413382318634709 14329663698712813648093001)
            ·
              refine ⟨10747247774034610236069751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14329663698712813648093001 10747247774034610236069751)
              ·
                refine ⟨16120871661051915354104627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10747247774034610236069751 16120871661051915354104627)
                ·
                  refine ⟨24181307491577873031156941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16120871661051915354104627 24181307491577873031156941)
                  ·
                    refine ⟨9067990309341702386683853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24181307491577873031156941 9067990309341702386683853)
                    ·
                      refine ⟨3400496366003138395006445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9067990309341702386683853 3400496366003138395006445)
                      ·
                        rfl

theorem cell23_6622443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 3].length) (baseStart_6622443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622443 prefixEnd_6622443 := by exact prefixLift 6622443
  have htrace : WordTrace (prefixWord ++ tailWord_6622443) baseStart_6622443 baseEnd_6622443 := by
    simpa [prefixWord, tailWord_6622443, baseEnd_6622443] using wordTrace_append hprefix tailTrace_6622443
  have hstable : (prefixWord ++ tailWord_6622443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622443).length < 2 ^ (prefixWord ++ tailWord_6622443).sum := by decide
  have hdescent : baseEnd_6622443 < baseStart_6622443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622476 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 2, 6]
def baseStart_6622476 : Nat := 118140960795 + 6622476 * 2 ^ 59
def prefixEnd_6622476 : Nat := 4983230072969 + 3 ^ 40 * 6622476 * 2
def baseEnd_6622476 : Nat := 1133504436954912255297931

theorem tailTrace_6622476 : CollatzResearch.WordTrace tailWord_6622476 prefixEnd_6622476 1133504436954912255297931 := by
  unfold tailWord_6622476
  simp only [CollatzResearch.WordTrace]
  refine ⟨120770771577953977850051641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161027695437271970466735521 120770771577953977850051641)
  ·
    refine ⟨90578078683465483387538731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120770771577953977850051641 90578078683465483387538731)
    ·
      refine ⟨135867118025198225081308097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90578078683465483387538731 135867118025198225081308097)
      ·
        refine ⟨101900338518898668810981073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135867118025198225081308097 101900338518898668810981073)
        ·
          refine ⟨76425253889174001608235805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101900338518898668810981073 76425253889174001608235805)
          ·
            refine ⟨28659470208440250603088427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76425253889174001608235805 28659470208440250603088427)
            ·
              refine ⟨42989205312660375904632641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28659470208440250603088427 42989205312660375904632641)
              ·
                refine ⟨32241903984495281928474481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42989205312660375904632641 32241903984495281928474481)
                ·
                  refine ⟨24181427988371461446355861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32241903984495281928474481 24181427988371461446355861)
                  ·
                    refine ⟨1133504436954912255297931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24181427988371461446355861 1133504436954912255297931)
                    ·
                      rfl

theorem cell23_6622476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_6622476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622476 prefixEnd_6622476 := by exact prefixLift 6622476
  have htrace : WordTrace (prefixWord ++ tailWord_6622476) baseStart_6622476 baseEnd_6622476 := by
    simpa [prefixWord, tailWord_6622476, baseEnd_6622476] using wordTrace_append hprefix tailTrace_6622476
  have hstable : (prefixWord ++ tailWord_6622476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622476).length < 2 ^ (prefixWord ++ tailWord_6622476).sum := by decide
  have hdescent : baseEnd_6622476 < baseStart_6622476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622493 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 2, 6]
def baseStart_6622493 : Nat := 118140960795 + 6622493 * 2 ^ 59
def prefixEnd_6622493 : Nat := 4983230072969 + 3 ^ 40 * 6622493 * 2
def baseEnd_6622493 : Nat := 1133507346678621066460405

theorem tailTrace_6622493 : CollatzResearch.WordTrace tailWord_6622493 prefixEnd_6622493 1133507346678621066460405 := by
  unfold tailWord_6622493
  simp only [CollatzResearch.WordTrace]
  refine ⟨241542163196846367603472133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161028108797897578402314755 241542163196846367603472133)
  ·
    refine ⟨45289155599408693925651025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241542163196846367603472133 45289155599408693925651025)
    ·
      refine ⟨33966866699556520444238269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45289155599408693925651025 33966866699556520444238269)
      ·
        refine ⟨12737575012333695166589351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33966866699556520444238269 12737575012333695166589351)
        ·
          refine ⟨19106362518500542749884027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12737575012333695166589351 19106362518500542749884027)
          ·
            refine ⟨28659543777750814124826041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19106362518500542749884027 28659543777750814124826041)
            ·
              refine ⟨21494657833313110593619531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28659543777750814124826041 21494657833313110593619531)
              ·
                refine ⟨32241986749969665890429297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21494657833313110593619531 32241986749969665890429297)
                ·
                  refine ⟨24181490062477249417821973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32241986749969665890429297 24181490062477249417821973)
                  ·
                    refine ⟨1133507346678621066460405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24181490062477249417821973 1133507346678621066460405)
                    ·
                      rfl

theorem cell23_6622493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_6622493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622493 prefixEnd_6622493 := by exact prefixLift 6622493
  have htrace : WordTrace (prefixWord ++ tailWord_6622493) baseStart_6622493 baseEnd_6622493 := by
    simpa [prefixWord, tailWord_6622493, baseEnd_6622493] using wordTrace_append hprefix tailTrace_6622493
  have hstable : (prefixWord ++ tailWord_6622493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622493).length < 2 ^ (prefixWord ++ tailWord_6622493).sum := by decide
  have hdescent : baseEnd_6622493 < baseStart_6622493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622494 : List Nat := [4, 3, 2, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_6622494 : Nat := 118140960795 + 6622494 * 2 ^ 59
def prefixEnd_6622494 : Nat := 4983230072969 + 3 ^ 40 * 6622494 * 2
def baseEnd_6622494 : Nat := 3400522553516517695468711

theorem tailTrace_6622494 : CollatzResearch.WordTrace tailWord_6622494 prefixEnd_6622494 3400522553516517695468711 := by
  unfold tailWord_6622494
  simp only [CollatzResearch.WordTrace]
  refine ⟨30192774958730343096782317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161028133113228496516172357 30192774958730343096782317)
  ·
    refine ⟨11322290609523878661293369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30192774958730343096782317 11322290609523878661293369)
    ·
      refine ⟨8491717957142908995970027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11322290609523878661293369 8491717957142908995970027)
      ·
        refine ⟨12737576935714363493955041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8491717957142908995970027 12737576935714363493955041)
        ·
          refine ⟨9553182701785772620466281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12737576935714363493955041 9553182701785772620466281)
          ·
            refine ⟨7164887026339329465349711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9553182701785772620466281 7164887026339329465349711)
            ·
              refine ⟨10747330539508994198024567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7164887026339329465349711 10747330539508994198024567)
              ·
                refine ⟨16120995809263491297036851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10747330539508994198024567 16120995809263491297036851)
                ·
                  refine ⟨24181493713895236945555277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16120995809263491297036851 24181493713895236945555277)
                  ·
                    refine ⟨9068060142710713854583229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24181493713895236945555277 9068060142710713854583229)
                    ·
                      refine ⟨3400522553516517695468711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9068060142710713854583229 3400522553516517695468711)
                      ·
                        rfl

theorem cell23_6622494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_6622494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622494 prefixEnd_6622494 := by exact prefixLift 6622494
  have htrace : WordTrace (prefixWord ++ tailWord_6622494) baseStart_6622494 baseEnd_6622494 := by
    simpa [prefixWord, tailWord_6622494, baseEnd_6622494] using wordTrace_append hprefix tailTrace_6622494
  have hstable : (prefixWord ++ tailWord_6622494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622494).length < 2 ^ (prefixWord ++ tailWord_6622494).sum := by decide
  have hdescent : baseEnd_6622494 < baseStart_6622494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622586 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6]
def baseStart_6622586 : Nat := 118140960795 + 6622586 * 2 ^ 59
def prefixEnd_6622586 : Nat := 4983230072969 + 3 ^ 40 * 6622586 * 2
def baseEnd_6622586 : Nat := 3400569793736731335518287

theorem tailTrace_6622586 : CollatzResearch.WordTrace tailWord_6622586 prefixEnd_6622586 3400569793736731335518287 := by
  unfold tailWord_6622586
  simp only [CollatzResearch.WordTrace]
  refine ⟨60386388796377361121651903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161030370123672962991071741 60386388796377361121651903)
  ·
    refine ⟨90579583194566041682477855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60386388796377361121651903 90579583194566041682477855)
    ·
      refine ⟨135869374791849062523716783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90579583194566041682477855 135869374791849062523716783)
      ·
        refine ⟨203804062187773593785575175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135869374791849062523716783 203804062187773593785575175)
        ·
          refine ⟨305706093281660390678362763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203804062187773593785575175 305706093281660390678362763)
          ·
            refine ⟨458559139922490586017544145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305706093281660390678362763 458559139922490586017544145)
            ·
              refine ⟨343919354941867939513158109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458559139922490586017544145 343919354941867939513158109)
              ·
                refine ⟨128969758103200477317434291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 343919354941867939513158109 128969758103200477317434291)
                ·
                  refine ⟨193454637154800715976151437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128969758103200477317434291 193454637154800715976151437)
                  ·
                    refine ⟨72545488933050268491056789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193454637154800715976151437 72545488933050268491056789)
                    ·
                      refine ⟨3400569793736731335518287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72545488933050268491056789 3400569793736731335518287)
                      ·
                        rfl

theorem cell23_6622586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_6622586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622586 prefixEnd_6622586 := by exact prefixLift 6622586
  have htrace : WordTrace (prefixWord ++ tailWord_6622586) baseStart_6622586 baseEnd_6622586 := by
    simpa [prefixWord, tailWord_6622586, baseEnd_6622586] using wordTrace_append hprefix tailTrace_6622586
  have hstable : (prefixWord ++ tailWord_6622586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622586).length < 2 ^ (prefixWord ++ tailWord_6622586).sum := by decide
  have hdescent : baseEnd_6622586 < baseStart_6622586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622613 : List Nat := [1, 3, 2, 1, 1, 2, 4, 3, 6]
def baseStart_6622613 : Nat := 118140960795 + 6622613 * 2 ^ 59
def prefixEnd_6622613 : Nat := 4983230072969 + 3 ^ 40 * 6622613 * 2
def baseEnd_6622613 : Nat := 377842628634933636653407

theorem tailTrace_6622613 : CollatzResearch.WordTrace tailWord_6622613 prefixEnd_6622613 377842628634933636653407 := by
  unfold tailWord_6622613
  simp only [CollatzResearch.WordTrace]
  refine ⟨241546539956411628097840493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161031026637607752065226995 241546539956411628097840493)
  ·
    refine ⟨90579952483654360536690185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241546539956411628097840493 90579952483654360536690185)
    ·
      refine ⟨67934964362740770402517639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90579952483654360536690185 67934964362740770402517639)
      ·
        refine ⟨101902446544111155603776459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67934964362740770402517639 101902446544111155603776459)
        ·
          refine ⟨152853669816166733405664689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101902446544111155603776459 152853669816166733405664689)
          ·
            refine ⟨114640252362125050054248517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152853669816166733405664689 114640252362125050054248517)
            ·
              refine ⟨21495047317898446885171597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114640252362125050054248517 21495047317898446885171597)
              ·
                refine ⟨8060642744211917581939349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21495047317898446885171597 8060642744211917581939349)
                ·
                  refine ⟨377842628634933636653407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8060642744211917581939349 377842628634933636653407)
                  ·
                    rfl

theorem cell23_6622613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 6].length) (baseStart_6622613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622613 prefixEnd_6622613 := by exact prefixLift 6622613
  have htrace : WordTrace (prefixWord ++ tailWord_6622613) baseStart_6622613 baseEnd_6622613 := by
    simpa [prefixWord, tailWord_6622613, baseEnd_6622613] using wordTrace_append hprefix tailTrace_6622613
  have hstable : (prefixWord ++ tailWord_6622613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622613).length < 2 ^ (prefixWord ++ tailWord_6622613).sum := by decide
  have hdescent : baseEnd_6622613 < baseStart_6622613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622680 : List Nat := [2, 1, 2, 2, 2, 1, 3, 4, 1, 1, 4]
def baseStart_6622680 : Nat := 118140960795 + 6622680 * 2 ^ 59
def prefixEnd_6622680 : Nat := 4983230072969 + 3 ^ 40 * 6622680 * 2
def baseEnd_6622680 : Nat := 3400618060918253967742855

theorem tailTrace_6622680 : CollatzResearch.WordTrace tailWord_6622680 prefixEnd_6622680 3400618060918253967742855 := by
  unfold tailWord_6622680
  simp only [CollatzResearch.WordTrace]
  refine ⟨120774491823584449270264747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161032655764779265693686329 120774491823584449270264747)
  ·
    refine ⟨181161737735376673905397121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120774491823584449270264747 181161737735376673905397121)
    ·
      refine ⟨135871303301532505429047841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181161737735376673905397121 135871303301532505429047841)
      ·
        refine ⟨101903477476149379071785881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135871303301532505429047841 101903477476149379071785881)
        ·
          refine ⟨76427608107112034303839411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101903477476149379071785881 76427608107112034303839411)
          ·
            refine ⟨114641412160668051455759117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76427608107112034303839411 114641412160668051455759117)
            ·
              refine ⟨42990529560250519295909669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114641412160668051455759117 42990529560250519295909669)
              ·
                refine ⟨8060724292546972367983063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42990529560250519295909669 8060724292546972367983063)
                ·
                  refine ⟨12091086438820458551974595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8060724292546972367983063 12091086438820458551974595)
                  ·
                    refine ⟨18136629658230687827961893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12091086438820458551974595 18136629658230687827961893)
                    ·
                      refine ⟨3400618060918253967742855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18136629658230687827961893 3400618060918253967742855)
                      ·
                        rfl

theorem cell23_6622680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_6622680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622680 prefixEnd_6622680 := by exact prefixLift 6622680
  have htrace : WordTrace (prefixWord ++ tailWord_6622680) baseStart_6622680 baseEnd_6622680 := by
    simpa [prefixWord, tailWord_6622680, baseEnd_6622680] using wordTrace_append hprefix tailTrace_6622680
  have hstable : (prefixWord ++ tailWord_6622680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622680).length < 2 ^ (prefixWord ++ tailWord_6622680).sum := by decide
  have hdescent : baseEnd_6622680 < baseStart_6622680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622691 : List Nat := [1, 1, 1, 6, 2, 3, 1, 3, 1, 1, 3]
def baseStart_6622691 : Nat := 118140960795 + 6622691 * 2 ^ 59
def prefixEnd_6622691 : Nat := 4983230072969 + 3 ^ 40 * 6622691 * 2
def baseEnd_6622691 : Nat := 3400623709205453424705305

theorem tailTrace_6622691 : CollatzResearch.WordTrace tailWord_6622691 prefixEnd_6622691 3400623709205453424705305 := by
  unfold tailWord_6622691
  simp only [CollatzResearch.WordTrace]
  refine ⟨241549384850129047419179927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161032923233419364946119951 241549384850129047419179927)
  ·
    refine ⟨362324077275193571128769891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241549384850129047419179927 362324077275193571128769891)
    ·
      refine ⟨543486115912790356693154837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362324077275193571128769891 543486115912790356693154837)
      ·
        refine ⟨25475911683412047969991633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 543486115912790356693154837 25475911683412047969991633)
        ·
          refine ⟨19106933762559035977493725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25475911683412047969991633 19106933762559035977493725)
          ·
            refine ⟨7165100160959638491560147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19106933762559035977493725 7165100160959638491560147)
            ·
              refine ⟨10747650241439457737340221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7165100160959638491560147 10747650241439457737340221)
              ·
                refine ⟨4030368840539796651502583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10747650241439457737340221 4030368840539796651502583)
                ·
                  refine ⟨6045553260809694977253875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4030368840539796651502583 6045553260809694977253875)
                  ·
                    refine ⟨9068329891214542465880813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6045553260809694977253875 9068329891214542465880813)
                    ·
                      refine ⟨3400623709205453424705305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9068329891214542465880813 3400623709205453424705305)
                      ·
                        rfl

theorem cell23_6622691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_6622691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622691 prefixEnd_6622691 := by exact prefixLift 6622691
  have htrace : WordTrace (prefixWord ++ tailWord_6622691) baseStart_6622691 baseEnd_6622691 := by
    simpa [prefixWord, tailWord_6622691, baseEnd_6622691] using wordTrace_append hprefix tailTrace_6622691
  have hstable : (prefixWord ++ tailWord_6622691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622691).length < 2 ^ (prefixWord ++ tailWord_6622691).sum := by decide
  have hdescent : baseEnd_6622691 < baseStart_6622691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622710 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_6622710 : Nat := 118140960795 + 6622710 * 2 ^ 59
def prefixEnd_6622710 : Nat := 4983230072969 + 3 ^ 40 * 6622710 * 2
def baseEnd_6622710 : Nat := 3400633465337888850367717

theorem tailTrace_6622710 : CollatzResearch.WordTrace tailWord_6622710 prefixEnd_6622710 3400633465337888850367717 := by
  unfold tailWord_6622710
  simp only [CollatzResearch.WordTrace]
  refine ⟨15096879864816263354007599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161033385224706809109414389 15096879864816263354007599)
  ·
    refine ⟨22645319797224395031011399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15096879864816263354007599 22645319797224395031011399)
    ·
      refine ⟨33967979695836592546517099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22645319797224395031011399 33967979695836592546517099)
      ·
        refine ⟨50951969543754888819775649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33967979695836592546517099 50951969543754888819775649)
        ·
          refine ⟨38213977157816166614831737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50951969543754888819775649 38213977157816166614831737)
          ·
            refine ⟨28660482868362124961123803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38213977157816166614831737 28660482868362124961123803)
            ·
              refine ⟨42990724302543187441685705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28660482868362124961123803 42990724302543187441685705)
              ·
                refine ⟨32243043226907390581264279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42990724302543187441685705 32243043226907390581264279)
                ·
                  refine ⟨48364564840361085871896419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32243043226907390581264279 48364564840361085871896419)
                  ·
                    refine ⟨72546847260541628807844629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48364564840361085871896419 72546847260541628807844629)
                    ·
                      refine ⟨3400633465337888850367717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72546847260541628807844629 3400633465337888850367717)
                      ·
                        rfl

theorem cell23_6622710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_6622710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622710 prefixEnd_6622710 := by exact prefixLift 6622710
  have htrace : WordTrace (prefixWord ++ tailWord_6622710) baseStart_6622710 baseEnd_6622710 := by
    simpa [prefixWord, tailWord_6622710, baseEnd_6622710] using wordTrace_append hprefix tailTrace_6622710
  have hstable : (prefixWord ++ tailWord_6622710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622710).length < 2 ^ (prefixWord ++ tailWord_6622710).sum := by decide
  have hdescent : baseEnd_6622710 < baseStart_6622710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622724 : List Nat := [2, 3, 2, 3, 2, 1, 1, 3, 2, 4]
def baseStart_6622724 : Nat := 118140960795 + 6622724 * 2 ^ 59
def prefixEnd_6622724 : Nat := 4983230072969 + 3 ^ 40 * 6622724 * 2
def baseEnd_6622724 : Nat := 1133546884689017265197551

theorem tailTrace_6622724 : CollatzResearch.WordTrace tailWord_6622724 prefixEnd_6622724 1133546884689017265197551 := by
  unfold tailWord_6622724
  simp only [CollatzResearch.WordTrace]
  refine ⟨120775294229504747027565613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161033725639339662703420817 120775294229504747027565613)
  ·
    refine ⟨45290735336064280135337105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120775294229504747027565613 45290735336064280135337105)
    ·
      refine ⟨33968051502048210101502829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45290735336064280135337105 33968051502048210101502829)
      ·
        refine ⟨12738019313268078788063561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33968051502048210101502829 12738019313268078788063561)
        ·
          refine ⟨9553514484951059091047671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12738019313268078788063561 9553514484951059091047671)
          ·
            refine ⟨14330271727426588636571507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9553514484951059091047671 14330271727426588636571507)
            ·
              refine ⟨21495407591139882954857261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14330271727426588636571507 21495407591139882954857261)
              ·
                refine ⟨8060777846677456108071473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21495407591139882954857261 8060777846677456108071473)
                ·
                  refine ⟨6045583385008092081053605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8060777846677456108071473 6045583385008092081053605)
                  ·
                    refine ⟨1133546884689017265197551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6045583385008092081053605 1133546884689017265197551)
                    ·
                      rfl

theorem cell23_6622724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_6622724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622724 prefixEnd_6622724 := by exact prefixLift 6622724
  have htrace : WordTrace (prefixWord ++ tailWord_6622724) baseStart_6622724 baseEnd_6622724 := by
    simpa [prefixWord, tailWord_6622724, baseEnd_6622724] using wordTrace_append hprefix tailTrace_6622724
  have hstable : (prefixWord ++ tailWord_6622724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622724).length < 2 ^ (prefixWord ++ tailWord_6622724).sum := by decide
  have hdescent : baseEnd_6622724 < baseStart_6622724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622787 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 8, 2, 2]
def baseStart_6622787 : Nat := 118140960795 + 6622787 * 2 ^ 59
def prefixEnd_6622787 : Nat := 4983230072969 + 3 ^ 40 * 6622787 * 2
def baseEnd_6622787 : Nat := 3400673003348285049104863

theorem tailTrace_6622787 : CollatzResearch.WordTrace tailWord_6622787 prefixEnd_6622787 3400673003348285049104863 := by
  unfold tailWord_6622787
  simp only [CollatzResearch.WordTrace]
  refine ⟨241552886257781255814674615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161035257505187503876449743 241552886257781255814674615)
  ·
    refine ⟨362329329386671883722011923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241552886257781255814674615 362329329386671883722011923)
    ·
      refine ⟨543493994080007825583017885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362329329386671883722011923 543493994080007825583017885)
      ·
        refine ⟨203810247780002934593631707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 543493994080007825583017885 203810247780002934593631707)
        ·
          refine ⟨305715371670004401890447561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203810247780002934593631707 305715371670004401890447561)
          ·
            refine ⟨229286528752503301417835671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305715371670004401890447561 229286528752503301417835671)
            ·
              refine ⟨343929793128754952126753507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229286528752503301417835671 343929793128754952126753507)
              ·
                refine ⟨515894689693132428190130261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343929793128754952126753507 515894689693132428190130261)
                ·
                  refine ⟨6045640894841395642853089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 515894689693132428190130261 6045640894841395642853089)
                  ·
                    refine ⟨4534230671131046732139817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6045640894841395642853089 4534230671131046732139817)
                    ·
                      refine ⟨3400673003348285049104863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4534230671131046732139817 3400673003348285049104863)
                      ·
                        rfl

theorem cell23_6622787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 2, 2].length) (baseStart_6622787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622787 prefixEnd_6622787 := by exact prefixLift 6622787
  have htrace : WordTrace (prefixWord ++ tailWord_6622787) baseStart_6622787 baseEnd_6622787 := by
    simpa [prefixWord, tailWord_6622787, baseEnd_6622787] using wordTrace_append hprefix tailTrace_6622787
  have hstable : (prefixWord ++ tailWord_6622787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622787).length < 2 ^ (prefixWord ++ tailWord_6622787).sum := by decide
  have hdescent : baseEnd_6622787 < baseStart_6622787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622804 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 4, 2, 2]
def baseStart_6622804 : Nat := 118140960795 + 6622804 * 2 ^ 59
def prefixEnd_6622804 : Nat := 4983230072969 + 3 ^ 40 * 6622804 * 2
def baseEnd_6622804 : Nat := 3400681732519411482592285

theorem tailTrace_6622804 : CollatzResearch.WordTrace tailWord_6622804 prefixEnd_6622804 3400681732519411482592285 := by
  unfold tailWord_6622804
  simp only [CollatzResearch.WordTrace]
  refine ⟨120776753149359833859021733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161035670865813111812028977 120776753149359833859021733)
  ·
    refine ⟨22645641215504968848566575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120776753149359833859021733 22645641215504968848566575)
    ·
      refine ⟨33968461823257453272849863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22645641215504968848566575 33968461823257453272849863)
      ·
        refine ⟨50952692734886179909274795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33968461823257453272849863 50952692734886179909274795)
        ·
          refine ⟨76429039102329269863912193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50952692734886179909274795 76429039102329269863912193)
          ·
            refine ⟨57321779326746952397934145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76429039102329269863912193 57321779326746952397934145)
            ·
              refine ⟨42991334495060214298450609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57321779326746952397934145 42991334495060214298450609)
              ·
                refine ⟨32243500871295160723837957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42991334495060214298450609 32243500871295160723837957)
                ·
                  refine ⟨6045656413367842635719617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32243500871295160723837957 6045656413367842635719617)
                  ·
                    refine ⟨4534242310025881976789713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6045656413367842635719617 4534242310025881976789713)
                    ·
                      refine ⟨3400681732519411482592285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4534242310025881976789713 3400681732519411482592285)
                      ·
                        rfl

theorem cell23_6622804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_6622804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622804 prefixEnd_6622804 := by exact prefixLift 6622804
  have htrace : WordTrace (prefixWord ++ tailWord_6622804) baseStart_6622804 baseEnd_6622804 := by
    simpa [prefixWord, tailWord_6622804, baseEnd_6622804] using wordTrace_append hprefix tailTrace_6622804
  have hstable : (prefixWord ++ tailWord_6622804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622804).length < 2 ^ (prefixWord ++ tailWord_6622804).sum := by decide
  have hdescent : baseEnd_6622804 < baseStart_6622804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622821 : List Nat := [1, 3, 1, 3, 3, 1, 3, 2, 2, 2, 2]
def baseStart_6622821 : Nat := 118140960795 + 6622821 * 2 ^ 59
def prefixEnd_6622821 : Nat := 4983230072969 + 3 ^ 40 * 6622821 * 2
def baseEnd_6622821 : Nat := 3400690461690537916079707

theorem tailTrace_6622821 : CollatzResearch.WordTrace tailWord_6622821 prefixEnd_6622821 3400690461690537916079707 := by
  unfold tailWord_6622821
  simp only [CollatzResearch.WordTrace]
  refine ⟨241554126339658079621412317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161036084226438719747608211 241554126339658079621412317)
  ·
    refine ⟨90582797377371779858029619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241554126339658079621412317 90582797377371779858029619)
    ·
      refine ⟨135874196066057669787044429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90582797377371779858029619 135874196066057669787044429)
      ·
        refine ⟨50952823524771626170141661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135874196066057669787044429 50952823524771626170141661)
        ·
          refine ⟨19107308821789359813803123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50952823524771626170141661 19107308821789359813803123)
          ·
            refine ⟨28660963232684039720704685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19107308821789359813803123 28660963232684039720704685)
            ·
              refine ⟨10747861212256514895264257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28660963232684039720704685 10747861212256514895264257)
              ·
                refine ⟨8060895909192386171448193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10747861212256514895264257 8060895909192386171448193)
                ·
                  refine ⟨6045671931894289628586145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8060895909192386171448193 6045671931894289628586145)
                  ·
                    refine ⟨4534253948920717221439609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6045671931894289628586145 4534253948920717221439609)
                    ·
                      refine ⟨3400690461690537916079707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4534253948920717221439609 3400690461690537916079707)
                      ·
                        rfl

theorem cell23_6622821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_6622821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622821 prefixEnd_6622821 := by exact prefixLift 6622821
  have htrace : WordTrace (prefixWord ++ tailWord_6622821) baseStart_6622821 baseEnd_6622821 := by
    simpa [prefixWord, tailWord_6622821, baseEnd_6622821] using wordTrace_append hprefix tailTrace_6622821
  have hstable : (prefixWord ++ tailWord_6622821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622821).length < 2 ^ (prefixWord ++ tailWord_6622821).sum := by decide
  have hdescent : baseEnd_6622821 < baseStart_6622821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622860 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 1, 3, 4]
def baseStart_6622860 : Nat := 118140960795 + 6622860 * 2 ^ 59
def prefixEnd_6622860 : Nat := 4983230072969 + 3 ^ 40 * 6622860 * 2
def baseEnd_6622860 : Nat := 3400710487436063263492027

theorem tailTrace_6622860 : CollatzResearch.WordTrace tailWord_6622860 prefixEnd_6622860 3400710487436063263492027 := by
  unfold tailWord_6622860
  simp only [CollatzResearch.WordTrace]
  refine ⟨120777774393258394641041017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161037032524344526188054689 120777774393258394641041017)
  ·
    refine ⟨90583330794943795980780763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120777774393258394641041017 90583330794943795980780763)
    ·
      refine ⟨135874996192415693971171145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90583330794943795980780763 135874996192415693971171145)
      ·
        refine ⟨101906247144311770478378359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135874996192415693971171145 101906247144311770478378359)
        ·
          refine ⟨152859370716467655717567539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101906247144311770478378359 152859370716467655717567539)
          ·
            refine ⟨229289056074701483576351309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152859370716467655717567539 229289056074701483576351309)
            ·
              refine ⟨85983396028013056341131741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229289056074701483576351309 85983396028013056341131741)
              ·
                refine ⟨32243773510504896127924403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85983396028013056341131741 32243773510504896127924403)
                ·
                  refine ⟨48365660265757344191886605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32243773510504896127924403 48365660265757344191886605)
                  ·
                    refine ⟨18137122599659004071957477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48365660265757344191886605 18137122599659004071957477)
                    ·
                      refine ⟨3400710487436063263492027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18137122599659004071957477 3400710487436063263492027)
                      ·
                        rfl

theorem cell23_6622860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_6622860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622860 prefixEnd_6622860 := by exact prefixLift 6622860
  have htrace : WordTrace (prefixWord ++ tailWord_6622860) baseStart_6622860 baseEnd_6622860 := by
    simpa [prefixWord, tailWord_6622860, baseEnd_6622860] using wordTrace_append hprefix tailTrace_6622860
  have hstable : (prefixWord ++ tailWord_6622860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622860).length < 2 ^ (prefixWord ++ tailWord_6622860).sum := by decide
  have hdescent : baseEnd_6622860 < baseStart_6622860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622938 : List Nat := [3, 1, 1, 2, 2, 5, 2, 2, 1, 4]
def baseStart_6622938 : Nat := 118140960795 + 6622938 * 2 ^ 59
def prefixEnd_6622938 : Nat := 4983230072969 + 3 ^ 40 * 6622938 * 2
def baseEnd_6622938 : Nat := 1133583512975704652772223

theorem tailTrace_6622938 : CollatzResearch.WordTrace tailWord_6622938 prefixEnd_6622938 1133583512975704652772223 := by
  unfold tailWord_6622938
  simp only [CollatzResearch.WordTrace]
  refine ⟨60389598420058552150855367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161038929120156139068947645 60389598420058552150855367)
  ·
    refine ⟨90584397630087828226283051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60389598420058552150855367 90584397630087828226283051)
    ·
      refine ⟨135876596445131742339424577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90584397630087828226283051 135876596445131742339424577)
      ·
        refine ⟨101907447333848806754568433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135876596445131742339424577 101907447333848806754568433)
        ·
          refine ⟨76430585500386605065926325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101907447333848806754568433 76430585500386605065926325)
          ·
            refine ⟨7165367390661244224930593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76430585500386605065926325 7165367390661244224930593)
            ·
              refine ⟨5374025542995933168697945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7165367390661244224930593 5374025542995933168697945)
              ·
                refine ⟨4030519157246949876523459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5374025542995933168697945 4030519157246949876523459)
                ·
                  refine ⟨6045778735870424814785189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4030519157246949876523459 6045778735870424814785189)
                  ·
                    refine ⟨1133583512975704652772223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6045778735870424814785189 1133583512975704652772223)
                    ·
                      rfl

theorem cell23_6622938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 1, 4].length) (baseStart_6622938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622938 prefixEnd_6622938 := by exact prefixLift 6622938
  have htrace : WordTrace (prefixWord ++ tailWord_6622938) baseStart_6622938 baseEnd_6622938 := by
    simpa [prefixWord, tailWord_6622938, baseEnd_6622938] using wordTrace_append hprefix tailTrace_6622938
  have hstable : (prefixWord ++ tailWord_6622938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622938).length < 2 ^ (prefixWord ++ tailWord_6622938).sum := by decide
  have hdescent : baseEnd_6622938 < baseStart_6622938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622954 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 4, 3, 2]
def baseStart_6622954 : Nat := 118140960795 + 6622954 * 2 ^ 59
def prefixEnd_6622954 : Nat := 4983230072969 + 3 ^ 40 * 6622954 * 2
def baseEnd_6622954 : Nat := 3400758754617585895716595

theorem tailTrace_6622954 : CollatzResearch.WordTrace tailWord_6622954 prefixEnd_6622954 3400758754617585895716595 := by
  unfold tailWord_6622954
  simp only [CollatzResearch.WordTrace]
  refine ⟨60389744312044060834000979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161039318165450828890669277 60389744312044060834000979)
  ·
    refine ⟨90584616468066091251001469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60389744312044060834000979 90584616468066091251001469)
    ·
      refine ⟨33969231175524784219125551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90584616468066091251001469 33969231175524784219125551)
      ·
        refine ⟨50953846763287176328688327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33969231175524784219125551 50953846763287176328688327)
        ·
          refine ⟨76430770144930764493032491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50953846763287176328688327 76430770144930764493032491)
          ·
            refine ⟨114646155217396146739548737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76430770144930764493032491 114646155217396146739548737)
            ·
              refine ⟨85984616413047110054661553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114646155217396146739548737 85984616413047110054661553)
              ·
                refine ⟨64488462309785332540996165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85984616413047110054661553 64488462309785332540996165)
                ·
                  refine ⟨12091586683084749851436781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64488462309785332540996165 12091586683084749851436781)
                  ·
                    refine ⟨4534345006156781194288793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12091586683084749851436781 4534345006156781194288793)
                    ·
                      refine ⟨3400758754617585895716595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4534345006156781194288793 3400758754617585895716595)
                      ·
                        rfl

theorem cell23_6622954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_6622954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622954 prefixEnd_6622954 := by exact prefixLift 6622954
  have htrace : WordTrace (prefixWord ++ tailWord_6622954) baseStart_6622954 baseEnd_6622954 := by
    simpa [prefixWord, tailWord_6622954, baseEnd_6622954] using wordTrace_append hprefix tailTrace_6622954
  have hstable : (prefixWord ++ tailWord_6622954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622954).length < 2 ^ (prefixWord ++ tailWord_6622954).sum := by decide
  have hdescent : baseEnd_6622954 < baseStart_6622954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622967 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 4]
def baseStart_6622967 : Nat := 118140960795 + 6622967 * 2 ^ 59
def prefixEnd_6622967 : Nat := 4983230072969 + 3 ^ 40 * 6622967 * 2
def baseEnd_6622967 : Nat := 3400765429866094344854035

theorem tailTrace_6622967 : CollatzResearch.WordTrace tailWord_6622967 prefixEnd_6622967 3400765429866094344854035 := by
  unfold tailWord_6622967
  simp only [CollatzResearch.WordTrace]
  refine ⟨241559451397129146556227155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161039634264752764370818103 241559451397129146556227155)
  ·
    refine ⟨362339177095693719834340733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241559451397129146556227155 362339177095693719834340733)
    ·
      refine ⟨135877191410885144937877775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362339177095693719834340733 135877191410885144937877775)
      ·
        refine ⟨203815787116327717406816663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135877191410885144937877775 203815787116327717406816663)
        ·
          refine ⟨305723680674491576110224995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203815787116327717406816663 305723680674491576110224995)
          ·
            refine ⟨458585521011737364165337493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305723680674491576110224995 458585521011737364165337493)
            ·
              refine ⟨21496196297425188945250195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 458585521011737364165337493 21496196297425188945250195)
              ·
                refine ⟨32244294446137783417875293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21496196297425188945250195 32244294446137783417875293)
                ·
                  refine ⟨12091610417301668781703235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32244294446137783417875293 12091610417301668781703235)
                  ·
                    refine ⟨18137415625952503172554853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12091610417301668781703235 18137415625952503172554853)
                    ·
                      refine ⟨3400765429866094344854035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18137415625952503172554853 3400765429866094344854035)
                      ·
                        rfl

theorem cell23_6622967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_6622967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622967 prefixEnd_6622967 := by exact prefixLift 6622967
  have htrace : WordTrace (prefixWord ++ tailWord_6622967) baseStart_6622967 baseEnd_6622967 := by
    simpa [prefixWord, tailWord_6622967, baseEnd_6622967] using wordTrace_append hprefix tailTrace_6622967
  have hstable : (prefixWord ++ tailWord_6622967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622967).length < 2 ^ (prefixWord ++ tailWord_6622967).sum := by decide
  have hdescent : baseEnd_6622967 < baseStart_6622967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622977 : List Nat := [1, 2, 4, 1, 1, 1, 4, 2, 1, 6]
def baseStart_6622977 : Nat := 118140960795 + 6622977 * 2 ^ 59
def prefixEnd_6622977 : Nat := 4983230072969 + 3 ^ 40 * 6622977 * 2
def baseEnd_6622977 : Nat := 1133590188224213101909663

theorem tailTrace_6622977 : CollatzResearch.WordTrace tailWord_6622977 prefixEnd_6622977 1133590188224213101909663 := by
  unfold tailWord_6622977
  simp only [CollatzResearch.WordTrace]
  refine ⟨241559816127092918264091185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161039877418061945509394123 241559816127092918264091185)
  ·
    refine ⟨181169862095319688698068389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241559816127092918264091185 181169862095319688698068389)
    ·
      refine ⟨33969349142872441630887823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181169862095319688698068389 33969349142872441630887823)
      ·
        refine ⟨50954023714308662446331735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33969349142872441630887823 50954023714308662446331735)
        ·
          refine ⟨76431035571462993669497603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50954023714308662446331735 76431035571462993669497603)
          ·
            refine ⟨114646553357194490504246405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76431035571462993669497603 114646553357194490504246405)
            ·
              refine ⟨21496228754473966969546201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114646553357194490504246405 21496228754473966969546201)
              ·
                refine ⟨16122171565855475227159651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21496228754473966969546201 16122171565855475227159651)
                ·
                  refine ⟨24183257348783212840739477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16122171565855475227159651 24183257348783212840739477)
                  ·
                    refine ⟨1133590188224213101909663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24183257348783212840739477 1133590188224213101909663)
                    ·
                      rfl

theorem cell23_6622977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_6622977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622977 prefixEnd_6622977 := by exact prefixLift 6622977
  have htrace : WordTrace (prefixWord ++ tailWord_6622977) baseStart_6622977 baseEnd_6622977 := by
    simpa [prefixWord, tailWord_6622977, baseEnd_6622977] using wordTrace_append hprefix tailTrace_6622977
  have hstable : (prefixWord ++ tailWord_6622977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622977).length < 2 ^ (prefixWord ++ tailWord_6622977).sum := by decide
  have hdescent : baseEnd_6622977 < baseStart_6622977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6622984 : List Nat := [2, 1, 3, 2, 2, 1, 3, 3, 1, 1, 4]
def baseStart_6622984 : Nat := 118140960795 + 6622984 * 2 ^ 59
def prefixEnd_6622984 : Nat := 4983230072969 + 3 ^ 40 * 6622984 * 2
def baseEnd_6622984 : Nat := 3400774159037220778341457

theorem tailTrace_6622984 : CollatzResearch.WordTrace tailWord_6622984 prefixEnd_6622984 3400774159037220778341457 := by
  unfold tailWord_6622984
  simp only [CollatzResearch.WordTrace]
  refine ⟨120780035719033779229798003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161040047625378372306397337 120780035719033779229798003)
  ·
    refine ⟨181170053578550668844697005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120780035719033779229798003 181170053578550668844697005)
    ·
      refine ⟨67938770091956500816761377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181170053578550668844697005 67938770091956500816761377)
      ·
        refine ⟨50954077568967375612571033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67938770091956500816761377 50954077568967375612571033)
        ·
          refine ⟨38215558176725531709428275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50954077568967375612571033 38215558176725531709428275)
          ·
            refine ⟨57323337265088297564142413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38215558176725531709428275 57323337265088297564142413)
            ·
              refine ⟨21496251474408111586553405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57323337265088297564142413 21496251474408111586553405)
              ·
                refine ⟨8061094302903041844957527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21496251474408111586553405 8061094302903041844957527)
                ·
                  refine ⟨12091641454354562767436291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8061094302903041844957527 12091641454354562767436291)
                  ·
                    refine ⟨18137462181531844151154437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12091641454354562767436291 18137462181531844151154437)
                    ·
                      refine ⟨3400774159037220778341457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18137462181531844151154437 3400774159037220778341457)
                      ·
                        rfl

theorem cell23_6622984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_6622984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6622984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6622984 prefixEnd_6622984 := by exact prefixLift 6622984
  have htrace : WordTrace (prefixWord ++ tailWord_6622984) baseStart_6622984 baseEnd_6622984 := by
    simpa [prefixWord, tailWord_6622984, baseEnd_6622984] using wordTrace_append hprefix tailTrace_6622984
  have hstable : (prefixWord ++ tailWord_6622984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6622984).length < 2 ^ (prefixWord ++ tailWord_6622984).sum := by decide
  have hdescent : baseEnd_6622984 < baseStart_6622984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6622984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623052 : List Nat := [2, 2, 1, 3, 4, 1, 3, 2, 1, 2, 2]
def baseStart_6623052 : Nat := 118140960795 + 6623052 * 2 ^ 59
def prefixEnd_6623052 : Nat := 4983230072969 + 3 ^ 40 * 6623052 * 2
def baseEnd_6623052 : Nat := 3400809075721726512291145

theorem tailTrace_6623052 : CollatzResearch.WordTrace tailWord_6623052 prefixEnd_6623052 3400809075721726512291145 := by
  unfold tailWord_6623052
  simp only [CollatzResearch.WordTrace]
  refine ⟨120781275800910603036535705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161041701067880804048714273 120781275800910603036535705)
  ·
    refine ⟨90585956850682952277401779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120781275800910603036535705 90585956850682952277401779)
    ·
      refine ⟨135878935276024428416102669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90585956850682952277401779 135878935276024428416102669)
      ·
        refine ⟨50954600728509160656038501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135878935276024428416102669 50954600728509160656038501)
        ·
          refine ⟨9553987636595467623007219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50954600728509160656038501 9553987636595467623007219)
          ·
            refine ⟨14330981454893201434510829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9553987636595467623007219 14330981454893201434510829)
            ·
              refine ⟨5374118045584950537941561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14330981454893201434510829 5374118045584950537941561)
              ·
                refine ⟨4030588534188712903456171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5374118045584950537941561 4030588534188712903456171)
                ·
                  refine ⟨6045882801283069355184257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4030588534188712903456171 6045882801283069355184257)
                  ·
                    refine ⟨4534412100962302016388193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6045882801283069355184257 4534412100962302016388193)
                    ·
                      refine ⟨3400809075721726512291145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4534412100962302016388193 3400809075721726512291145)
                      ·
                        rfl

theorem cell23_6623052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_6623052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623052 prefixEnd_6623052 := by exact prefixLift 6623052
  have htrace : WordTrace (prefixWord ++ tailWord_6623052) baseStart_6623052 baseEnd_6623052 := by
    simpa [prefixWord, tailWord_6623052, baseEnd_6623052] using wordTrace_append hprefix tailTrace_6623052
  have hstable : (prefixWord ++ tailWord_6623052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623052).length < 2 ^ (prefixWord ++ tailWord_6623052).sum := by decide
  have hdescent : baseEnd_6623052 < baseStart_6623052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623087 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 4]
def baseStart_6623087 : Nat := 118140960795 + 6623087 * 2 ^ 59
def prefixEnd_6623087 : Nat := 4983230072969 + 3 ^ 40 * 6623087 * 2
def baseEnd_6623087 : Nat := 3400827047544633875353483

theorem tailTrace_6623087 : CollatzResearch.WordTrace tailWord_6623087 prefixEnd_6623087 3400827047544633875353483 := by
  unfold tailWord_6623087
  simp only [CollatzResearch.WordTrace]
  refine ⟨241563828156694407050595515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161042552104462938033730343 241563828156694407050595515)
  ·
    refine ⟨362345742235041610575893273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241563828156694407050595515 362345742235041610575893273)
    ·
      refine ⟨271759306676281207931919955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362345742235041610575893273 271759306676281207931919955)
      ·
        refine ⟨407638960014421811897879933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271759306676281207931919955 407638960014421811897879933)
        ·
          refine ⟨152864610005408179461704975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407638960014421811897879933 152864610005408179461704975)
          ·
            refine ⟨229296915008112269192557463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152864610005408179461704975 229296915008112269192557463)
            ·
              refine ⟨343945372512168403788836195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229296915008112269192557463 343945372512168403788836195)
              ·
                refine ⟨515918058768252605683254293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343945372512168403788836195 515918058768252605683254293)
                ·
                  refine ⟨24183659004761840891402545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 515918058768252605683254293 24183659004761840891402545)
                  ·
                    refine ⟨18137744253571380668551909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24183659004761840891402545 18137744253571380668551909)
                    ·
                      refine ⟨3400827047544633875353483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18137744253571380668551909 3400827047544633875353483)
                      ·
                        rfl

theorem cell23_6623087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 4].length) (baseStart_6623087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623087 prefixEnd_6623087 := by exact prefixLift 6623087
  have htrace : WordTrace (prefixWord ++ tailWord_6623087) baseStart_6623087 baseEnd_6623087 := by
    simpa [prefixWord, tailWord_6623087, baseEnd_6623087] using wordTrace_append hprefix tailTrace_6623087
  have hstable : (prefixWord ++ tailWord_6623087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623087).length < 2 ^ (prefixWord ++ tailWord_6623087).sum := by decide
  have hdescent : baseEnd_6623087 < baseStart_6623087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623108 : List Nat := [2, 3, 2, 1, 1, 1, 3, 4, 2, 2, 2]
def baseStart_6623108 : Nat := 118140960795 + 6623108 * 2 ^ 59
def prefixEnd_6623108 : Nat := 4983230072969 + 3 ^ 40 * 6623108 * 2
def baseEnd_6623108 : Nat := 3400837830638378293190887

theorem tailTrace_6623108 : CollatzResearch.WordTrace tailWord_6623108 prefixEnd_6623108 3400837830638378293190887 := by
  unfold tailWord_6623108
  simp only [CollatzResearch.WordTrace]
  refine ⟨120782297044809163818554989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161043062726412218424739985 120782297044809163818554989)
  ·
    refine ⟨45293361391803436431958121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120782297044809163818554989 45293361391803436431958121)
    ·
      refine ⟨33970021043852577323968591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45293361391803436431958121 33970021043852577323968591)
      ·
        refine ⟨50955031565778865985952887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33970021043852577323968591 50955031565778865985952887)
        ·
          refine ⟨76432547348668298978929331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50955031565778865985952887 76432547348668298978929331)
          ·
            refine ⟨114648821023002448468393997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76432547348668298978929331 114648821023002448468393997)
            ·
              refine ⟨42993307883625918175647749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114648821023002448468393997 42993307883625918175647749)
              ·
                refine ⟨8061245228179859657933953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42993307883625918175647749 8061245228179859657933953)
                ·
                  refine ⟨6045933921134894743450465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8061245228179859657933953 6045933921134894743450465)
                  ·
                    refine ⟨4534450440851171057587849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6045933921134894743450465 4534450440851171057587849)
                    ·
                      refine ⟨3400837830638378293190887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4534450440851171057587849 3400837830638378293190887)
                      ·
                        rfl

theorem cell23_6623108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_6623108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623108 prefixEnd_6623108 := by exact prefixLift 6623108
  have htrace : WordTrace (prefixWord ++ tailWord_6623108) baseStart_6623108 baseEnd_6623108 := by
    simpa [prefixWord, tailWord_6623108, baseEnd_6623108] using wordTrace_append hprefix tailTrace_6623108
  have hstable : (prefixWord ++ tailWord_6623108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623108).length < 2 ^ (prefixWord ++ tailWord_6623108).sum := by decide
  have hdescent : baseEnd_6623108 < baseStart_6623108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623184 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 3]
def baseStart_6623184 : Nat := 118140960795 + 6623184 * 2 ^ 59
def prefixEnd_6623184 : Nat := 4983230072969 + 3 ^ 40 * 6623184 * 2
def baseEnd_6623184 : Nat := 3400876855168119995840537

theorem tailTrace_6623184 : CollatzResearch.WordTrace tailWord_6623184 prefixEnd_6623184 3400876855168119995840537 := by
  unfold tailWord_6623184
  simp only [CollatzResearch.WordTrace]
  refine ⟨120783683018671496308438303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161044910691561995077917737 120783683018671496308438303)
  ·
    refine ⟨181175524528007244462657455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120783683018671496308438303 181175524528007244462657455)
    ·
      refine ⟨271763286792010866693986183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181175524528007244462657455 271763286792010866693986183)
      ·
        refine ⟨407644930188016300040979275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271763286792010866693986183 407644930188016300040979275)
        ·
          refine ⟨611467395282024450061468913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407644930188016300040979275 611467395282024450061468913)
          ·
            refine ⟨458600546461518337546101685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 611467395282024450061468913 458600546461518337546101685)
            ·
              refine ⟨42993801230767344144947033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 458600546461518337546101685 42993801230767344144947033)
              ·
                refine ⟨32245350923075508108710275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42993801230767344144947033 32245350923075508108710275)
                ·
                  refine ⟨48368026384613262163065413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32245350923075508108710275 48368026384613262163065413)
                  ·
                    refine ⟨9069004947114986655574765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48368026384613262163065413 9069004947114986655574765)
                    ·
                      refine ⟨3400876855168119995840537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9069004947114986655574765 3400876855168119995840537)
                      ·
                        rfl

theorem cell23_6623184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 3].length) (baseStart_6623184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623184 prefixEnd_6623184 := by exact prefixLift 6623184
  have htrace : WordTrace (prefixWord ++ tailWord_6623184) baseStart_6623184 baseEnd_6623184 := by
    simpa [prefixWord, tailWord_6623184, baseEnd_6623184] using wordTrace_append hprefix tailTrace_6623184
  have hstable : (prefixWord ++ tailWord_6623184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623184).length < 2 ^ (prefixWord ++ tailWord_6623184).sum := by decide
  have hdescent : baseEnd_6623184 < baseStart_6623184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623225 : List Nat := [1, 2, 1, 3, 1, 5, 3, 2, 1, 4]
def baseStart_6623225 : Nat := 118140960795 + 6623225 * 2 ^ 59
def prefixEnd_6623225 : Nat := 4983230072969 + 3 ^ 40 * 6623225 * 2
def baseEnd_6623225 : Nat := 1133632635958318111809283

theorem tailTrace_6623225 : CollatzResearch.WordTrace tailWord_6623225 prefixEnd_6623225 1133632635958318111809283 := by
  unfold tailWord_6623225
  simp only [CollatzResearch.WordTrace]
  refine ⟨241568861430194456619119129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161045907620129637746079419 241568861430194456619119129)
  ·
    refine ⟨181176646072645842464339347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241568861430194456619119129 181176646072645842464339347)
    ·
      refine ⟨271764969108968763696509021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181176646072645842464339347 271764969108968763696509021)
      ·
        refine ⟨101911863415863286386190883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271764969108968763696509021 101911863415863286386190883)
        ·
          refine ⟨152867795123794929579286325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101911863415863286386190883 152867795123794929579286325)
          ·
            refine ⟨14331355792855774648058093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152867795123794929579286325 14331355792855774648058093)
            ·
              refine ⟨5374258422320915493021785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14331355792855774648058093 5374258422320915493021785)
              ·
                refine ⟨4030693816740686619766339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5374258422320915493021785 4030693816740686619766339)
                ·
                  refine ⟨6046040725111029929649509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4030693816740686619766339 6046040725111029929649509)
                  ·
                    refine ⟨1133632635958318111809283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6046040725111029929649509 1133632635958318111809283)
                    ·
                      rfl

theorem cell23_6623225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 1, 4].length) (baseStart_6623225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623225 prefixEnd_6623225 := by exact prefixLift 6623225
  have htrace : WordTrace (prefixWord ++ tailWord_6623225) baseStart_6623225 baseEnd_6623225 := by
    simpa [prefixWord, tailWord_6623225, baseEnd_6623225] using wordTrace_append hprefix tailTrace_6623225
  have hstable : (prefixWord ++ tailWord_6623225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623225).length < 2 ^ (prefixWord ++ tailWord_6623225).sum := by decide
  have hdescent : baseEnd_6623225 < baseStart_6623225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623251 : List Nat := [1, 1, 1, 2, 1, 4, 5, 2, 1, 5]
def baseStart_6623251 : Nat := 118140960795 + 6623251 * 2 ^ 59
def prefixEnd_6623251 : Nat := 4983230072969 + 3 ^ 40 * 6623251 * 2
def baseEnd_6623251 : Nat := 1133637086123990411234243

theorem tailTrace_6623251 : CollatzResearch.WordTrace tailWord_6623251 prefixEnd_6623251 1133637086123990411234243 := by
  unfold tailWord_6623251
  simp only [CollatzResearch.WordTrace]
  refine ⟨241569809728100263059565607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161046539818733508706377071 241569809728100263059565607)
  ·
    refine ⟨362354714592150394589348411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241569809728100263059565607 362354714592150394589348411)
    ·
      refine ⟨543532071888225591884022617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362354714592150394589348411 543532071888225591884022617)
      ·
        refine ⟨407649053916169193913016963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543532071888225591884022617 407649053916169193913016963)
        ·
          refine ⟨611473580874253790869525445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407649053916169193913016963 611473580874253790869525445)
          ·
            refine ⟨114651296413922585788036021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 611473580874253790869525445 114651296413922585788036021)
            ·
              refine ⟨10748559038805242417628377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114651296413922585788036021 10748559038805242417628377)
              ·
                refine ⟨8061419279103931813221283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10748559038805242417628377 8061419279103931813221283)
                ·
                  refine ⟨12092128918655897719831925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8061419279103931813221283 12092128918655897719831925)
                  ·
                    refine ⟨1133637086123990411234243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12092128918655897719831925 1133637086123990411234243)
                    ·
                      rfl

theorem cell23_6623251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 5].length) (baseStart_6623251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623251 prefixEnd_6623251 := by exact prefixLift 6623251
  have htrace : WordTrace (prefixWord ++ tailWord_6623251) baseStart_6623251 baseEnd_6623251 := by
    simpa [prefixWord, tailWord_6623251, baseEnd_6623251] using wordTrace_append hprefix tailTrace_6623251
  have hstable : (prefixWord ++ tailWord_6623251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623251).length < 2 ^ (prefixWord ++ tailWord_6623251).sum := by decide
  have hdescent : baseEnd_6623251 < baseStart_6623251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623252 : List Nat := [2, 4, 3, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_6623252 : Nat := 118140960795 + 6623252 * 2 ^ 59
def prefixEnd_6623252 : Nat := 4983230072969 + 3 ^ 40 * 6623252 * 2
def baseEnd_6623252 : Nat := 3400911771852625729790225

theorem tailTrace_6623252 : CollatzResearch.WordTrace tailWord_6623252 prefixEnd_6623252 3400911771852625729790225 := by
  unfold tailWord_6623252
  simp only [CollatzResearch.WordTrace]
  refine ⟨120784923100548320115176005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161046564134064426820234673 120784923100548320115176005)
  ·
    refine ⟨22647173081352810021595501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120784923100548320115176005 22647173081352810021595501)
    ·
      refine ⟨8492689905507303758098313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22647173081352810021595501 8492689905507303758098313)
      ·
        refine ⟨6369517429130477818573735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8492689905507303758098313 6369517429130477818573735)
        ·
          refine ⟨9554276143695716727860603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6369517429130477818573735 9554276143695716727860603)
          ·
            refine ⟨14331414215543575091790905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9554276143695716727860603 14331414215543575091790905)
            ·
              refine ⟨10748560661657681318843179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14331414215543575091790905 10748560661657681318843179)
              ·
                refine ⟨16122840992486521978264769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10748560661657681318843179 16122840992486521978264769)
                ·
                  refine ⟨12092130744364891483698577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16122840992486521978264769 12092130744364891483698577)
                  ·
                    refine ⟨9069098058273668612773933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12092130744364891483698577 9069098058273668612773933)
                    ·
                      refine ⟨3400911771852625729790225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9069098058273668612773933 3400911771852625729790225)
                      ·
                        rfl

theorem cell23_6623252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_6623252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623252 prefixEnd_6623252 := by exact prefixLift 6623252
  have htrace : WordTrace (prefixWord ++ tailWord_6623252) baseStart_6623252 baseEnd_6623252 := by
    simpa [prefixWord, tailWord_6623252, baseEnd_6623252] using wordTrace_append hprefix tailTrace_6623252
  have hstable : (prefixWord ++ tailWord_6623252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623252).length < 2 ^ (prefixWord ++ tailWord_6623252).sum := by decide
  have hdescent : baseEnd_6623252 < baseStart_6623252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623258 : List Nat := [3, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2]
def baseStart_6623258 : Nat := 118140960795 + 6623258 * 2 ^ 59
def prefixEnd_6623258 : Nat := 4983230072969 + 3 ^ 40 * 6623258 * 2
def baseEnd_6623258 : Nat := 3400914852736552706315197

theorem tailTrace_6623258 : CollatzResearch.WordTrace tailWord_6623258 prefixEnd_6623258 3400914852736552706315197 := by
  unfold tailWord_6623258
  simp only [CollatzResearch.WordTrace]
  refine ⟨60392516259768725813767607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161046710026049935503380285 60392516259768725813767607)
  ·
    refine ⟨90588774389653088720651411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60392516259768725813767607 90588774389653088720651411)
    ·
      refine ⟨135883161584479633080977117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90588774389653088720651411 135883161584479633080977117)
      ·
        refine ⟨50956185594179862405366419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135883161584479633080977117 50956185594179862405366419)
        ·
          refine ⟨76434278391269793608049629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50956185594179862405366419 76434278391269793608049629)
          ·
            refine ⟨28662854396726172603018611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76434278391269793608049629 28662854396726172603018611)
            ·
              refine ⟨42994281595089258904527917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28662854396726172603018611 42994281595089258904527917)
              ·
                refine ⟨16122855598158472089197969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42994281595089258904527917 16122855598158472089197969)
                ·
                  refine ⟨12092141698618854066898477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16122855598158472089197969 12092141698618854066898477)
                  ·
                    refine ⟨4534553136982070275086929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12092141698618854066898477 4534553136982070275086929)
                    ·
                      refine ⟨3400914852736552706315197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4534553136982070275086929 3400914852736552706315197)
                      ·
                        rfl

theorem cell23_6623258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_6623258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623258 prefixEnd_6623258 := by exact prefixLift 6623258
  have htrace : WordTrace (prefixWord ++ tailWord_6623258) baseStart_6623258 baseEnd_6623258 := by
    simpa [prefixWord, tailWord_6623258, baseEnd_6623258] using wordTrace_append hprefix tailTrace_6623258
  have hstable : (prefixWord ++ tailWord_6623258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623258).length < 2 ^ (prefixWord ++ tailWord_6623258).sum := by decide
  have hdescent : baseEnd_6623258 < baseStart_6623258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623282 : List Nat := [3, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3]
def baseStart_6623282 : Nat := 118140960795 + 6623282 * 2 ^ 59
def prefixEnd_6623282 : Nat := 4983230072969 + 3 ^ 40 * 6623282 * 2
def baseEnd_6623282 : Nat := 3400927176272260612415087

theorem tailTrace_6623282 : CollatzResearch.WordTrace tailWord_6623282 prefixEnd_6623282 3400927176272260612415087 := by
  unfold tailWord_6623282
  simp only [CollatzResearch.WordTrace]
  refine ⟨60392735097746988838486025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161047293593991970235962733 60392735097746988838486025)
  ·
    refine ⟨45294551323310241628864519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60392735097746988838486025 45294551323310241628864519)
    ·
      refine ⟨67941826984965362443296779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45294551323310241628864519 67941826984965362443296779)
      ·
        refine ⟨101912740477448043664945169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67941826984965362443296779 101912740477448043664945169)
        ·
          refine ⟨76434555358086032748708877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101912740477448043664945169 76434555358086032748708877)
          ·
            refine ⟨28662958259282262280765829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76434555358086032748708877 28662958259282262280765829)
            ·
              refine ⟨5374304673615424177643593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28662958259282262280765829 5374304673615424177643593)
              ·
                refine ⟨4030728505211568133232695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5374304673615424177643593 4030728505211568133232695)
                ·
                  refine ⟨6046092757817352199849043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4030728505211568133232695 6046092757817352199849043)
                  ·
                    refine ⟨9069139136726028299773565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6046092757817352199849043 9069139136726028299773565)
                    ·
                      refine ⟨3400927176272260612415087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9069139136726028299773565 3400927176272260612415087)
                      ·
                        rfl

theorem cell23_6623282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3].length) (baseStart_6623282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623282 prefixEnd_6623282 := by exact prefixLift 6623282
  have htrace : WordTrace (prefixWord ++ tailWord_6623282) baseStart_6623282 baseEnd_6623282 := by
    simpa [prefixWord, tailWord_6623282, baseEnd_6623282] using wordTrace_append hprefix tailTrace_6623282
  have hstable : (prefixWord ++ tailWord_6623282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623282).length < 2 ^ (prefixWord ++ tailWord_6623282).sum := by decide
  have hdescent : baseEnd_6623282 < baseStart_6623282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623321 : List Nat := [1, 2, 1, 2, 2, 1, 3, 4, 1, 3, 3]
def baseStart_6623321 : Nat := 118140960795 + 6623321 * 2 ^ 59
def prefixEnd_6623321 : Nat := 4983230072969 + 3 ^ 40 * 6623321 * 2
def baseEnd_6623321 : Nat := 3400947202017785959827407

theorem tailTrace_6623321 : CollatzResearch.WordTrace tailWord_6623321 prefixEnd_6623321 3400947202017785959827407 := by
  unfold tailWord_6623321
  simp only [CollatzResearch.WordTrace]
  refine ⟨241572362837846665014613817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161048241891897776676409211 241572362837846665014613817)
  ·
    refine ⟨181179272128384998760960363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241572362837846665014613817 181179272128384998760960363)
    ·
      refine ⟨271768908192577498141440545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181179272128384998760960363 271768908192577498141440545)
      ·
        refine ⟨203826681144433123606080409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271768908192577498141440545 203826681144433123606080409)
        ·
          refine ⟨152870010858324842704560307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203826681144433123606080409 152870010858324842704560307)
          ·
            refine ⟨229305016287487264056840461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152870010858324842704560307 229305016287487264056840461)
            ·
              refine ⟨85989381107807724021315173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229305016287487264056840461 85989381107807724021315173)
              ·
                refine ⟨16123008957713948253996595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85989381107807724021315173 16123008957713948253996595)
                ·
                  refine ⟨24184513436570922380994893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16123008957713948253996595 24184513436570922380994893)
                  ·
                    refine ⟨9069192538714095892873085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24184513436570922380994893 9069192538714095892873085)
                    ·
                      refine ⟨3400947202017785959827407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9069192538714095892873085 3400947202017785959827407)
                      ·
                        rfl

theorem cell23_6623321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_6623321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623321 prefixEnd_6623321 := by exact prefixLift 6623321
  have htrace : WordTrace (prefixWord ++ tailWord_6623321) baseStart_6623321 baseEnd_6623321 := by
    simpa [prefixWord, tailWord_6623321, baseEnd_6623321] using wordTrace_append hprefix tailTrace_6623321
  have hstable : (prefixWord ++ tailWord_6623321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623321).length < 2 ^ (prefixWord ++ tailWord_6623321).sum := by decide
  have hdescent : baseEnd_6623321 < baseStart_6623321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623322 : List Nat := [3, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2]
def baseStart_6623322 : Nat := 118140960795 + 6623322 * 2 ^ 59
def prefixEnd_6623322 : Nat := 4983230072969 + 3 ^ 40 * 6623322 * 2
def baseEnd_6623322 : Nat := 3400947715498440455914903

theorem tailTrace_6623322 : CollatzResearch.WordTrace tailWord_6623322 prefixEnd_6623322 3400947715498440455914903 := by
  unfold tailWord_6623322
  simp only [CollatzResearch.WordTrace]
  refine ⟨60393099827710760546350055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161048266207228694790266813 60393099827710760546350055)
  ·
    refine ⟨90589649741566140819525083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60393099827710760546350055 90589649741566140819525083)
    ·
      refine ⟨135884474612349211229287625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90589649741566140819525083 135884474612349211229287625)
      ·
        refine ⟨101913355959261908421965719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135884474612349211229287625 101913355959261908421965719)
        ·
          refine ⟨152870033938892862632948579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101913355959261908421965719 152870033938892862632948579)
          ·
            refine ⟨229305050908339293949422869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152870033938892862632948579 229305050908339293949422869)
            ·
              refine ⟨10748674261328404403879197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 229305050908339293949422869 10748674261328404403879197)
              ·
                refine ⟨4030752847998151651454699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10748674261328404403879197 4030752847998151651454699)
                ·
                  refine ⟨6046129271997227477182049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4030752847998151651454699 6046129271997227477182049)
                  ·
                    refine ⟨4534596953997920607886537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6046129271997227477182049 4534596953997920607886537)
                    ·
                      refine ⟨3400947715498440455914903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4534596953997920607886537 3400947715498440455914903)
                      ·
                        rfl

theorem cell23_6623322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2].length) (baseStart_6623322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623322 prefixEnd_6623322 := by exact prefixLift 6623322
  have htrace : WordTrace (prefixWord ++ tailWord_6623322) baseStart_6623322 baseEnd_6623322 := by
    simpa [prefixWord, tailWord_6623322, baseEnd_6623322] using wordTrace_append hprefix tailTrace_6623322
  have hstable : (prefixWord ++ tailWord_6623322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623322).length < 2 ^ (prefixWord ++ tailWord_6623322).sum := by decide
  have hdescent : baseEnd_6623322 < baseStart_6623322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623365 : List Nat := [1, 3, 1, 1, 5, 1, 1, 4, 1, 3, 2]
def baseStart_6623365 : Nat := 118140960795 + 6623365 * 2 ^ 59
def prefixEnd_6623365 : Nat := 4983230072969 + 3 ^ 40 * 6623365 * 2
def baseEnd_6623365 : Nat := 3400969795166583787677205

theorem tailTrace_6623365 : CollatzResearch.WordTrace tailWord_6623365 prefixEnd_6623365 3400969795166583787677205 := by
  unfold tailWord_6623365
  simp only [CollatzResearch.WordTrace]
  refine ⟨241573967649687260529215549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161049311766458173686143699 241573967649687260529215549)
  ·
    refine ⟨90590237868632722698455831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241573967649687260529215549 90590237868632722698455831)
    ·
      refine ⟨135885356802949084047683747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90590237868632722698455831 135885356802949084047683747)
      ·
        refine ⟨203828035204423626071525621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135885356802949084047683747 203828035204423626071525621)
        ·
          refine ⟨19108878300414714944205527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 203828035204423626071525621 19108878300414714944205527)
          ·
            refine ⟨28663317450622072416308291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19108878300414714944205527 28663317450622072416308291)
            ·
              refine ⟨42994976175933108624462437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28663317450622072416308291 42994976175933108624462437)
              ·
                refine ⟨8061558032987457867086707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42994976175933108624462437 8061558032987457867086707)
                ·
                  refine ⟨12092337049481186800630061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8061558032987457867086707 12092337049481186800630061)
                  ·
                    refine ⟨4534626393555445050236273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12092337049481186800630061 4534626393555445050236273)
                    ·
                      refine ⟨3400969795166583787677205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4534626393555445050236273 3400969795166583787677205)
                      ·
                        rfl

theorem cell23_6623365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 3, 2].length) (baseStart_6623365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623365 prefixEnd_6623365 := by exact prefixLift 6623365
  have htrace : WordTrace (prefixWord ++ tailWord_6623365) baseStart_6623365 baseEnd_6623365 := by
    simpa [prefixWord, tailWord_6623365, baseEnd_6623365] using wordTrace_append hprefix tailTrace_6623365
  have hstable : (prefixWord ++ tailWord_6623365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623365).length < 2 ^ (prefixWord ++ tailWord_6623365).sum := by decide
  have hdescent : baseEnd_6623365 < baseStart_6623365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623381 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_6623381 : Nat := 118140960795 + 6623381 * 2 ^ 59
def prefixEnd_6623381 : Nat := 4983230072969 + 3 ^ 40 * 6623381 * 2
def baseEnd_6623381 : Nat := 3400978010857055725077131

theorem tailTrace_6623381 : CollatzResearch.WordTrace tailWord_6623381 prefixEnd_6623381 3400978010857055725077131 := by
  unfold tailWord_6623381
  simp only [CollatzResearch.WordTrace]
  refine ⟨241574551217629295261797997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161049700811752863507865331 241574551217629295261797997)
  ·
    refine ⟨90590456706610985723174249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241574551217629295261797997 90590456706610985723174249)
    ·
      refine ⟨67942842529958239292380687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90590456706610985723174249 67942842529958239292380687)
      ·
        refine ⟨101914263794937358938571031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67942842529958239292380687 101914263794937358938571031)
        ·
          refine ⟨152871395692406038407856547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101914263794937358938571031 152871395692406038407856547)
          ·
            refine ⟨229307093538609057611784821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152871395692406038407856547 229307093538609057611784821)
            ·
              refine ⟨21497540019244599151104827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 229307093538609057611784821 21497540019244599151104827)
              ·
                refine ⟨32246310028866898726657241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21497540019244599151104827 32246310028866898726657241)
                ·
                  refine ⟨24184732521650174044992931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32246310028866898726657241 24184732521650174044992931)
                  ·
                    refine ⟨36277098782475261067489397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24184732521650174044992931 36277098782475261067489397)
                    ·
                      refine ⟨3400978010857055725077131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36277098782475261067489397 3400978010857055725077131)
                      ·
                        rfl

theorem cell23_6623381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_6623381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623381 prefixEnd_6623381 := by exact prefixLift 6623381
  have htrace : WordTrace (prefixWord ++ tailWord_6623381) baseStart_6623381 baseEnd_6623381 := by
    simpa [prefixWord, tailWord_6623381, baseEnd_6623381] using wordTrace_append hprefix tailTrace_6623381
  have hstable : (prefixWord ++ tailWord_6623381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623381).length < 2 ^ (prefixWord ++ tailWord_6623381).sum := by decide
  have hdescent : baseEnd_6623381 < baseStart_6623381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623411 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 3]
def baseStart_6623411 : Nat := 118140960795 + 6623411 * 2 ^ 59
def prefixEnd_6623411 : Nat := 4983230072969 + 3 ^ 40 * 6623411 * 2
def baseEnd_6623411 : Nat := 3400993415276690607701993

theorem tailTrace_6623411 : CollatzResearch.WordTrace tailWord_6623411 prefixEnd_6623411 3400993415276690607701993 := by
  unfold tailWord_6623411
  simp only [CollatzResearch.WordTrace]
  refine ⟨241575645407520610385390087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161050430271680406923593391 241575645407520610385390087)
  ·
    refine ⟨362363468111280915578085131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241575645407520610385390087 362363468111280915578085131)
    ·
      refine ⟨543545202166921373367127697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362363468111280915578085131 543545202166921373367127697)
      ·
        refine ⟨407658901625191030025345773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543545202166921373367127697 407658901625191030025345773)
        ·
          refine ⟨152872088109446636259504665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407658901625191030025345773 152872088109446636259504665)
          ·
            refine ⟨114654066082084977194628499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152872088109446636259504665 114654066082084977194628499)
            ·
              refine ⟨171981099123127465791942749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114654066082084977194628499 171981099123127465791942749)
              ·
                refine ⟨64492912171172799671978531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171981099123127465791942749 64492912171172799671978531)
                ·
                  refine ⟨96739368256759199507967797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64492912171172799671978531 96739368256759199507967797)
                  ·
                    refine ⟨9069315774071174953871981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96739368256759199507967797 9069315774071174953871981)
                    ·
                      refine ⟨3400993415276690607701993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9069315774071174953871981 3400993415276690607701993)
                      ·
                        rfl

theorem cell23_6623411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 3].length) (baseStart_6623411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623411 prefixEnd_6623411 := by exact prefixLift 6623411
  have htrace : WordTrace (prefixWord ++ tailWord_6623411) baseStart_6623411 baseEnd_6623411 := by
    simpa [prefixWord, tailWord_6623411, baseEnd_6623411] using wordTrace_append hprefix tailTrace_6623411
  have hstable : (prefixWord ++ tailWord_6623411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623411).length < 2 ^ (prefixWord ++ tailWord_6623411).sum := by decide
  have hdescent : baseEnd_6623411 < baseStart_6623411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623441 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 1, 2, 5]
def baseStart_6623441 : Nat := 118140960795 + 6623441 * 2 ^ 59
def prefixEnd_6623441 : Nat := 4983230072969 + 3 ^ 40 * 6623441 * 2
def baseEnd_6623441 : Nat := 3401008819696325490326855

theorem tailTrace_6623441 : CollatzResearch.WordTrace tailWord_6623441 prefixEnd_6623441 3401008819696325490326855 := by
  unfold tailWord_6623441
  simp only [CollatzResearch.WordTrace]
  refine ⟨241576739597411925508982177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161051159731607950339321451 241576739597411925508982177)
  ·
    refine ⟨181182554698058944131736633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241576739597411925508982177 181182554698058944131736633)
    ·
      refine ⟨135886916023544208098802475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181182554698058944131736633 135886916023544208098802475)
      ·
        refine ⟨203830374035316312148203713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135886916023544208098802475 203830374035316312148203713)
        ·
          refine ⟨152872780526487234111152785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203830374035316312148203713 152872780526487234111152785)
          ·
            refine ⟨114654585394865425583364589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152872780526487234111152785 114654585394865425583364589)
            ·
              refine ⟨42995469523074534593761721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114654585394865425583364589 42995469523074534593761721)
              ·
                refine ⟨32246602142305900945321291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42995469523074534593761721 32246602142305900945321291)
                ·
                  refine ⟨48369903213458851417981937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32246602142305900945321291 48369903213458851417981937)
                  ·
                    refine ⟨36277427410094138563486453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48369903213458851417981937 36277427410094138563486453)
                    ·
                      refine ⟨3401008819696325490326855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36277427410094138563486453 3401008819696325490326855)
                      ·
                        rfl

theorem cell23_6623441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_6623441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623441 prefixEnd_6623441 := by exact prefixLift 6623441
  have htrace : WordTrace (prefixWord ++ tailWord_6623441) baseStart_6623441 baseEnd_6623441 := by
    simpa [prefixWord, tailWord_6623441, baseEnd_6623441] using wordTrace_append hprefix tailTrace_6623441
  have hstable : (prefixWord ++ tailWord_6623441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623441).length < 2 ^ (prefixWord ++ tailWord_6623441).sum := by decide
  have hdescent : baseEnd_6623441 < baseStart_6623441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623446 : List Nat := [5, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_6623446 : Nat := 118140960795 + 6623446 * 2 ^ 59
def prefixEnd_6623446 : Nat := 4983230072969 + 3 ^ 40 * 6623446 * 2
def baseEnd_6623446 : Nat := 3401011387099597970764333

theorem tailTrace_6623446 : CollatzResearch.WordTrace tailWord_6623446 prefixEnd_6623446 3401011387099597970764333 := by
  unfold tailWord_6623446
  simp only [CollatzResearch.WordTrace]
  refine ⟨15098557622649613210182137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161051281308262540908609461 15098557622649613210182137)
  ·
    refine ⟨11323918216987209907636603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15098557622649613210182137 11323918216987209907636603)
    ·
      refine ⟨16985877325480814861454905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11323918216987209907636603 16985877325480814861454905)
      ·
        refine ⟨12739407994110611146091179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16985877325480814861454905 12739407994110611146091179)
        ·
          refine ⟨19109111991165916719136769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12739407994110611146091179 19109111991165916719136769)
          ·
            refine ⟨14331833993374437539352577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19109111991165916719136769 14331833993374437539352577)
            ·
              refine ⟨10748875495030828154514433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14331833993374437539352577 10748875495030828154514433)
              ·
                refine ⟨8061656621273121115885825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10748875495030828154514433 8061656621273121115885825)
                ·
                  refine ⟨6046242465954840836914369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8061656621273121115885825 6046242465954840836914369)
                  ·
                    refine ⟨4534681849466130627685777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6046242465954840836914369 4534681849466130627685777)
                    ·
                      refine ⟨3401011387099597970764333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4534681849466130627685777 3401011387099597970764333)
                      ·
                        rfl

theorem cell23_6623446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_6623446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623446 prefixEnd_6623446 := by exact prefixLift 6623446
  have htrace : WordTrace (prefixWord ++ tailWord_6623446) baseStart_6623446 baseEnd_6623446 := by
    simpa [prefixWord, tailWord_6623446, baseEnd_6623446] using wordTrace_append hprefix tailTrace_6623446
  have hstable : (prefixWord ++ tailWord_6623446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623446).length < 2 ^ (prefixWord ++ tailWord_6623446).sum := by decide
  have hdescent : baseEnd_6623446 < baseStart_6623446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623448 : List Nat := [2, 1, 2, 2, 4, 1, 2, 2, 2, 5]
def baseStart_6623448 : Nat := 118140960795 + 6623448 * 2 ^ 59
def prefixEnd_6623448 : Nat := 4983230072969 + 3 ^ 40 * 6623448 * 2
def baseEnd_6623448 : Nat := 1133670804686968987646441

theorem tailTrace_6623448 : CollatzResearch.WordTrace tailWord_6623448 prefixEnd_6623448 1133670804686968987646441 := by
  unfold tailWord_6623448
  simp only [CollatzResearch.WordTrace]
  refine ⟨120788497454193282852243499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161051329938924377136324665 120788497454193282852243499)
  ·
    refine ⟨181182746181289924278365249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120788497454193282852243499 181182746181289924278365249)
    ·
      refine ⟨135887059635967443208773937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181182746181289924278365249 135887059635967443208773937)
      ·
        refine ⟨101915294726975582406580453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135887059635967443208773937 101915294726975582406580453)
        ·
          refine ⟨19109117761307921701233835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101915294726975582406580453 19109117761307921701233835)
          ·
            refine ⟨28663676641961882551850753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19109117761307921701233835 28663676641961882551850753)
            ·
              refine ⟨21497757481471411913888065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28663676641961882551850753 21497757481471411913888065)
              ·
                refine ⟨16123318111103558935416049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21497757481471411913888065 16123318111103558935416049)
                ·
                  refine ⟨12092488583327669201562037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16123318111103558935416049 12092488583327669201562037)
                  ·
                    refine ⟨1133670804686968987646441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12092488583327669201562037 1133670804686968987646441)
                    ·
                      rfl

theorem cell23_6623448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_6623448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623448 prefixEnd_6623448 := by exact prefixLift 6623448
  have htrace : WordTrace (prefixWord ++ tailWord_6623448) baseStart_6623448 baseEnd_6623448 := by
    simpa [prefixWord, tailWord_6623448, baseEnd_6623448] using wordTrace_append hprefix tailTrace_6623448
  have hstable : (prefixWord ++ tailWord_6623448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623448).length < 2 ^ (prefixWord ++ tailWord_6623448).sum := by decide
  have hdescent : baseEnd_6623448 < baseStart_6623448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623481 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 1, 6, 4]
def baseStart_6623481 : Nat := 118140960795 + 6623481 * 2 ^ 59
def prefixEnd_6623481 : Nat := 4983230072969 + 3 ^ 40 * 6623481 * 2
def baseEnd_6623481 : Nat := 3401029358922505333826671

theorem tailTrace_6623481 : CollatzResearch.WordTrace tailWord_6623481 prefixEnd_6623481 3401029358922505333826671 := by
  unfold tailWord_6623481
  simp only [CollatzResearch.WordTrace]
  refine ⟨241578198517267012340438297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161052132344844674893625531 241578198517267012340438297)
  ·
    refine ⟨181183648887950259255328723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241578198517267012340438297 181183648887950259255328723)
    ·
      refine ⟨271775473331925388882993085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181183648887950259255328723 271775473331925388882993085)
      ·
        refine ⟨101915802499472020831122407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271775473331925388882993085 101915802499472020831122407)
        ·
          refine ⟨152873703749208031246683611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101915802499472020831122407 152873703749208031246683611)
          ·
            refine ⟨229310555623812046870025417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152873703749208031246683611 229310555623812046870025417)
            ·
              refine ⟨171982916717859035152519063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229310555623812046870025417 171982916717859035152519063)
              ·
                refine ⟨257974375076788552728778595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171982916717859035152519063 257974375076788552728778595)
                ·
                  refine ⟨386961562615182829093167893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257974375076788552728778595 386961562615182829093167893)
                  ·
                    refine ⟨18138823247586695113742245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 386961562615182829093167893 18138823247586695113742245)
                    ·
                      refine ⟨3401029358922505333826671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18138823247586695113742245 3401029358922505333826671)
                      ·
                        rfl

theorem cell23_6623481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_6623481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623481 prefixEnd_6623481 := by exact prefixLift 6623481
  have htrace : WordTrace (prefixWord ++ tailWord_6623481) baseStart_6623481 baseEnd_6623481 := by
    simpa [prefixWord, tailWord_6623481, baseEnd_6623481] using wordTrace_append hprefix tailTrace_6623481
  have hstable : (prefixWord ++ tailWord_6623481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623481).length < 2 ^ (prefixWord ++ tailWord_6623481).sum := by decide
  have hdescent : baseEnd_6623481 < baseStart_6623481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623491 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 8]
def baseStart_6623491 : Nat := 118140960795 + 6623491 * 2 ^ 59
def prefixEnd_6623491 : Nat := 4983230072969 + 3 ^ 40 * 6623491 * 2
def baseEnd_6623491 : Nat := 377892721525450032744625

theorem tailTrace_6623491 : CollatzResearch.WordTrace tailWord_6623491 prefixEnd_6623491 377892721525450032744625 := by
  unfold tailWord_6623491
  simp only [CollatzResearch.WordTrace]
  refine ⟨241578563247230784048302327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161052375498153856032201551 241578563247230784048302327)
  ·
    refine ⟨362367844870846176072453491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241578563247230784048302327 362367844870846176072453491)
    ·
      refine ⟨543551767306269264108680237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362367844870846176072453491 543551767306269264108680237)
      ·
        refine ⟨203831912739850974040755089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 543551767306269264108680237 203831912739850974040755089)
        ·
          refine ⟨152873934554888230530566317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203831912739850974040755089 152873934554888230530566317)
          ·
            refine ⟨57327725458083086448962369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152873934554888230530566317 57327725458083086448962369)
            ·
              refine ⟨42995794093562314836721777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57327725458083086448962369 42995794093562314836721777)
              ·
                refine ⟨32246845570171736127541333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42995794093562314836721777 32246845570171736127541333)
                ·
                  refine ⟨377892721525450032744625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32246845570171736127541333 377892721525450032744625)
                  ·
                    rfl

theorem cell23_6623491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 8].length) (baseStart_6623491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623491 prefixEnd_6623491 := by exact prefixLift 6623491
  have htrace : WordTrace (prefixWord ++ tailWord_6623491) baseStart_6623491 baseEnd_6623491 := by
    simpa [prefixWord, tailWord_6623491, baseEnd_6623491] using wordTrace_append hprefix tailTrace_6623491
  have hstable : (prefixWord ++ tailWord_6623491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623491).length < 2 ^ (prefixWord ++ tailWord_6623491).sum := by decide
  have hdescent : baseEnd_6623491 < baseStart_6623491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623535 : List Nat := [1, 1, 2, 1, 2, 1, 6, 2, 3, 1, 3]
def baseStart_6623535 : Nat := 118140960795 + 6623535 * 2 ^ 59
def prefixEnd_6623535 : Nat := 4983230072969 + 3 ^ 40 * 6623535 * 2
def baseEnd_6623535 : Nat := 3401057086877848122551423

theorem tailTrace_6623535 : CollatzResearch.WordTrace tailWord_6623535 prefixEnd_6623535 3401057086877848122551423 := by
  unfold tailWord_6623535
  simp only [CollatzResearch.WordTrace]
  refine ⟨241580168059071379562904059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161053445372714253041936039 241580168059071379562904059)
  ·
    refine ⟨362370252088607069344356089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241580168059071379562904059 362370252088607069344356089)
    ·
      refine ⟨271777689066455302008267067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362370252088607069344356089 271777689066455302008267067)
      ·
        refine ⟨407666533599682953012400601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271777689066455302008267067 407666533599682953012400601)
        ·
          refine ⟨305749900199762214759300451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407666533599682953012400601 305749900199762214759300451)
          ·
            refine ⟨458624850299643322138950677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305749900199762214759300451 458624850299643322138950677)
            ·
              refine ⟨21498039857795780725263313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 458624850299643322138950677 21498039857795780725263313)
              ·
                refine ⟨16123529893346835543947485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21498039857795780725263313 16123529893346835543947485)
                ·
                  refine ⟨6046323710005063328980307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16123529893346835543947485 6046323710005063328980307)
                  ·
                    refine ⟨9069485565007594993470461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6046323710005063328980307 9069485565007594993470461)
                    ·
                      refine ⟨3401057086877848122551423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9069485565007594993470461 3401057086877848122551423)
                      ·
                        rfl

theorem cell23_6623535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 1, 3].length) (baseStart_6623535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623535 prefixEnd_6623535 := by exact prefixLift 6623535
  have htrace : WordTrace (prefixWord ++ tailWord_6623535) baseStart_6623535 baseEnd_6623535 := by
    simpa [prefixWord, tailWord_6623535, baseEnd_6623535] using wordTrace_append hprefix tailTrace_6623535
  have hstable : (prefixWord ++ tailWord_6623535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623535).length < 2 ^ (prefixWord ++ tailWord_6623535).sum := by decide
  have hdescent : baseEnd_6623535 < baseStart_6623535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623552 : List Nat := [2, 1, 1, 2, 2, 1, 2, 7, 1, 1, 3]
def baseStart_6623552 : Nat := 118140960795 + 6623552 * 2 ^ 59
def prefixEnd_6623552 : Nat := 4983230072969 + 3 ^ 40 * 6623552 * 2
def baseEnd_6623552 : Nat := 3401065816048974556038845

theorem tailTrace_6623552 : CollatzResearch.WordTrace tailWord_6623552 prefixEnd_6623552 3401065816048974556038845 := by
  unfold tailWord_6623552
  simp only [CollatzResearch.WordTrace]
  refine ⟨120790394050004895733136455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161053858733339860977515273 120790394050004895733136455)
  ·
    refine ⟨181185591075007343599704683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120790394050004895733136455 181185591075007343599704683)
    ·
      refine ⟨271778386612511015399557025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181185591075007343599704683 271778386612511015399557025)
      ·
        refine ⟨203833789959383261549667769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271778386612511015399557025 203833789959383261549667769)
        ·
          refine ⟨152875342469537446162250827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203833789959383261549667769 152875342469537446162250827)
          ·
            refine ⟨229313013704306169243376241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152875342469537446162250827 229313013704306169243376241)
            ·
              refine ⟨171984760278229626932532181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229313013704306169243376241 171984760278229626932532181)
              ·
                refine ⟨4030892819021006881231223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 171984760278229626932532181 4030892819021006881231223)
                ·
                  refine ⟨6046339228531510321846835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4030892819021006881231223 6046339228531510321846835)
                  ·
                    refine ⟨9069508842797265482770253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6046339228531510321846835 9069508842797265482770253)
                    ·
                      refine ⟨3401065816048974556038845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9069508842797265482770253 3401065816048974556038845)
                      ·
                        rfl

theorem cell23_6623552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 1, 1, 3].length) (baseStart_6623552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623552 prefixEnd_6623552 := by exact prefixLift 6623552
  have htrace : WordTrace (prefixWord ++ tailWord_6623552) baseStart_6623552 baseEnd_6623552 := by
    simpa [prefixWord, tailWord_6623552, baseEnd_6623552] using wordTrace_append hprefix tailTrace_6623552
  have hstable : (prefixWord ++ tailWord_6623552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623552).length < 2 ^ (prefixWord ++ tailWord_6623552).sum := by decide
  have hdescent : baseEnd_6623552 < baseStart_6623552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623578 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3]
def baseStart_6623578 : Nat := 118140960795 + 6623578 * 2 ^ 59
def prefixEnd_6623578 : Nat := 4983230072969 + 3 ^ 40 * 6623578 * 2
def baseEnd_6623578 : Nat := 3401079166545991454313725

theorem tailTrace_6623578 : CollatzResearch.WordTrace tailWord_6623578 prefixEnd_6623578 3401079166545991454313725 := by
  unfold tailWord_6623578
  simp only [CollatzResearch.WordTrace]
  refine ⟨60395434099478899476679847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161054490931943731937812925 60395434099478899476679847)
  ·
    refine ⟨90593151149218349215019771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60395434099478899476679847 90593151149218349215019771)
    ·
      refine ⟨135889726723827523822529657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90593151149218349215019771 135889726723827523822529657)
      ·
        refine ⟨101917295042870642866897243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135889726723827523822529657 101917295042870642866897243)
        ·
          refine ⟨152875942564305964300345865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101917295042870642866897243 152875942564305964300345865)
          ·
            refine ⟨114656956923229473225259399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152875942564305964300345865 114656956923229473225259399)
            ·
              refine ⟨171985435384844209837889099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114656956923229473225259399 171985435384844209837889099)
              ·
                refine ⟨257978153077266314756833649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171985435384844209837889099 257978153077266314756833649)
                ·
                  refine ⟨193483614807949736067625237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257978153077266314756833649 193483614807949736067625237)
                  ·
                    refine ⟨9069544444122643878169933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 193483614807949736067625237 9069544444122643878169933)
                    ·
                      refine ⟨3401079166545991454313725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9069544444122643878169933 3401079166545991454313725)
                      ·
                        rfl

theorem cell23_6623578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_6623578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623578 prefixEnd_6623578 := by exact prefixLift 6623578
  have htrace : WordTrace (prefixWord ++ tailWord_6623578) baseStart_6623578 baseEnd_6623578 := by
    simpa [prefixWord, tailWord_6623578, baseEnd_6623578] using wordTrace_append hprefix tailTrace_6623578
  have hstable : (prefixWord ++ tailWord_6623578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623578).length < 2 ^ (prefixWord ++ tailWord_6623578).sum := by decide
  have hdescent : baseEnd_6623578 < baseStart_6623578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623588 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_6623588 : Nat := 118140960795 + 6623588 * 2 ^ 59
def prefixEnd_6623588 : Nat := 4983230072969 + 3 ^ 40 * 6623588 * 2
def baseEnd_6623588 : Nat := 3401084301352536415188679

theorem tailTrace_6623588 : CollatzResearch.WordTrace tailWord_6623588 prefixEnd_6623588 3401084301352536415188679 := by
  unfold tailWord_6623588
  simp only [CollatzResearch.WordTrace]
  refine ⟨120791050563939684807291709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161054734085252913076388945 120791050563939684807291709)
  ·
    refine ⟨45296643961477381802734391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120791050563939684807291709 45296643961477381802734391)
    ·
      refine ⟨67944965942216072704101587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45296643961477381802734391 67944965942216072704101587)
      ·
        refine ⟨101917448913324109056152381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67944965942216072704101587 101917448913324109056152381)
        ·
          refine ⟨38219043342496540896057143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101917448913324109056152381 38219043342496540896057143)
          ·
            refine ⟨57328565013744811344085715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38219043342496540896057143 57328565013744811344085715)
            ·
              refine ⟨85992847520617217016128573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57328565013744811344085715 85992847520617217016128573)
              ·
                refine ⟨32247317820231456381048215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85992847520617217016128573 32247317820231456381048215)
                ·
                  refine ⟨48370976730347184571572323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32247317820231456381048215 48370976730347184571572323)
                  ·
                    refine ⟨72556465095520776857358485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48370976730347184571572323 72556465095520776857358485)
                    ·
                      refine ⟨3401084301352536415188679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72556465095520776857358485 3401084301352536415188679)
                      ·
                        rfl

theorem cell23_6623588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_6623588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623588 prefixEnd_6623588 := by exact prefixLift 6623588
  have htrace : WordTrace (prefixWord ++ tailWord_6623588) baseStart_6623588 baseEnd_6623588 := by
    simpa [prefixWord, tailWord_6623588, baseEnd_6623588] using wordTrace_append hprefix tailTrace_6623588
  have hstable : (prefixWord ++ tailWord_6623588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623588).length < 2 ^ (prefixWord ++ tailWord_6623588).sum := by decide
  have hdescent : baseEnd_6623588 < baseStart_6623588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623592 : List Nat := [2, 1, 4, 2, 2, 1, 3, 2, 1, 1, 4]
def baseStart_6623592 : Nat := 118140960795 + 6623592 * 2 ^ 59
def prefixEnd_6623592 : Nat := 4983230072969 + 3 ^ 40 * 6623592 * 2
def baseEnd_6623592 : Nat := 3401086355275154399538661

theorem tailTrace_6623592 : CollatzResearch.WordTrace tailWord_6623592 prefixEnd_6623592 3401086355275154399538661 := by
  unfold tailWord_6623592
  simp only [CollatzResearch.WordTrace]
  refine ⟨120791123509932439148864515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161054831346576585531819353 120791123509932439148864515)
  ·
    refine ⟨181186685264898658723296773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120791123509932439148864515 181186685264898658723296773)
    ·
      refine ⟨33972503487168498510618145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181186685264898658723296773 33972503487168498510618145)
      ·
        refine ⟨25479377615376373882963609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33972503487168498510618145 25479377615376373882963609)
        ·
          refine ⟨19109533211532280412222707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25479377615376373882963609 19109533211532280412222707)
          ·
            refine ⟨28664299817298420618334061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19109533211532280412222707 28664299817298420618334061)
            ·
              refine ⟨10749112431486907731875273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28664299817298420618334061 10749112431486907731875273)
              ·
                refine ⟨8061834323615180798906455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10749112431486907731875273 8061834323615180798906455)
                ·
                  refine ⟨12092751485422771198359683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8061834323615180798906455 12092751485422771198359683)
                  ·
                    refine ⟨18139127228134156797539525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12092751485422771198359683 18139127228134156797539525)
                    ·
                      refine ⟨3401086355275154399538661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18139127228134156797539525 3401086355275154399538661)
                      ·
                        rfl

theorem cell23_6623592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_6623592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623592 prefixEnd_6623592 := by exact prefixLift 6623592
  have htrace : WordTrace (prefixWord ++ tailWord_6623592) baseStart_6623592 baseEnd_6623592 := by
    simpa [prefixWord, tailWord_6623592, baseEnd_6623592] using wordTrace_append hprefix tailTrace_6623592
  have hstable : (prefixWord ++ tailWord_6623592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623592).length < 2 ^ (prefixWord ++ tailWord_6623592).sum := by decide
  have hdescent : baseEnd_6623592 < baseStart_6623592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623605 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_6623605 : Nat := 118140960795 + 6623605 * 2 ^ 59
def prefixEnd_6623605 : Nat := 4983230072969 + 3 ^ 40 * 6623605 * 2
def baseEnd_6623605 : Nat := 3401093030523662848676101

theorem tailTrace_6623605 : CollatzResearch.WordTrace tailWord_6623605 prefixEnd_6623605 3401093030523662848676101 := by
  unfold tailWord_6623605
  simp only [CollatzResearch.WordTrace]
  refine ⟨241582721168817781517952269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161055147445878521011968179 241582721168817781517952269)
  ·
    refine ⟨90593520438306668069232101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241582721168817781517952269 90593520438306668069232101)
    ·
      refine ⟨16986285082182500262981019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90593520438306668069232101 16986285082182500262981019)
      ·
        refine ⟨25479427623273750394471529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16986285082182500262981019 25479427623273750394471529)
        ·
          refine ⟨19109570717455312795853647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25479427623273750394471529 19109570717455312795853647)
          ·
            refine ⟨28664356076182969193780471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19109570717455312795853647 28664356076182969193780471)
            ·
              refine ⟨42996534114274453790670707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28664356076182969193780471 42996534114274453790670707)
              ·
                refine ⟨64494801171411680686006061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42996534114274453790670707 64494801171411680686006061)
                ·
                  refine ⟨24185550439279380257252273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64494801171411680686006061 24185550439279380257252273)
                  ·
                    refine ⟨18139162829459535192939205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24185550439279380257252273 18139162829459535192939205)
                    ·
                      refine ⟨3401093030523662848676101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18139162829459535192939205 3401093030523662848676101)
                      ·
                        rfl

theorem cell23_6623605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_6623605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623605 prefixEnd_6623605 := by exact prefixLift 6623605
  have htrace : WordTrace (prefixWord ++ tailWord_6623605) baseStart_6623605 baseEnd_6623605 := by
    simpa [prefixWord, tailWord_6623605, baseEnd_6623605] using wordTrace_append hprefix tailTrace_6623605
  have hstable : (prefixWord ++ tailWord_6623605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623605).length < 2 ^ (prefixWord ++ tailWord_6623605).sum := by decide
  have hdescent : baseEnd_6623605 < baseStart_6623605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623606 : List Nat := [5, 1, 1, 4, 1, 1, 3, 1, 1, 5]
def baseStart_6623606 : Nat := 118140960795 + 6623606 * 2 ^ 59
def prefixEnd_6623606 : Nat := 4983230072969 + 3 ^ 40 * 6623606 * 2
def baseEnd_6623606 : Nat := 1133697848001439114921199

theorem tailTrace_6623606 : CollatzResearch.WordTrace tailWord_6623606 prefixEnd_6623606 1133697848001439114921199 := by
  unfold tailWord_6623606
  simp only [CollatzResearch.WordTrace]
  refine ⟨15098922352613384918046167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161055171761209439125825781 15098922352613384918046167)
  ·
    refine ⟨22648383528920077377069251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15098922352613384918046167 22648383528920077377069251)
    ·
      refine ⟨33972575293380116065603877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22648383528920077377069251 33972575293380116065603877)
      ·
        refine ⟨6369857867508771762300727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33972575293380116065603877 6369857867508771762300727)
        ·
          refine ⟨9554786801263157643451091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6369857867508771762300727 9554786801263157643451091)
          ·
            refine ⟨14332180201894736465176637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9554786801263157643451091 14332180201894736465176637)
            ·
              refine ⟨5374567575710526174441239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14332180201894736465176637 5374567575710526174441239)
              ·
                refine ⟨8061851363565789261661859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5374567575710526174441239 8061851363565789261661859)
                ·
                  refine ⟨12092777045348683892492789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8061851363565789261661859 12092777045348683892492789)
                  ·
                    refine ⟨1133697848001439114921199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12092777045348683892492789 1133697848001439114921199)
                    ·
                      rfl

theorem cell23_6623606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_6623606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623606 prefixEnd_6623606 := by exact prefixLift 6623606
  have htrace : WordTrace (prefixWord ++ tailWord_6623606) baseStart_6623606 baseEnd_6623606 := by
    simpa [prefixWord, tailWord_6623606, baseEnd_6623606] using wordTrace_append hprefix tailTrace_6623606
  have hstable : (prefixWord ++ tailWord_6623606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623606).length < 2 ^ (prefixWord ++ tailWord_6623606).sum := by decide
  have hdescent : baseEnd_6623606 < baseStart_6623606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623609 : List Nat := [1, 2, 1, 3, 2, 1, 1, 7, 1, 2, 2]
def baseStart_6623609 : Nat := 118140960795 + 6623609 * 2 ^ 59
def prefixEnd_6623609 : Nat := 4983230072969 + 3 ^ 40 * 6623609 * 2
def baseEnd_6623609 : Nat := 3401095084446280833026083

theorem tailTrace_6623609 : CollatzResearch.WordTrace tailWord_6623609 prefixEnd_6623609 3401095084446280833026083 := by
  unfold tailWord_6623609
  simp only [CollatzResearch.WordTrace]
  refine ⟨241582867060803290201097881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161055244707202193467398587 241582867060803290201097881)
  ·
    refine ⟨181187150295602467650823411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241582867060803290201097881 181187150295602467650823411)
    ·
      refine ⟨271780725443403701476235117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181187150295602467650823411 271780725443403701476235117)
      ·
        refine ⟨101917772041276388053588169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271780725443403701476235117 101917772041276388053588169)
        ·
          refine ⟨76438329030957291040191127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101917772041276388053588169 76438329030957291040191127)
          ·
            refine ⟨114657493546435936560286691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76438329030957291040191127 114657493546435936560286691)
            ·
              refine ⟨171986240319653904840430037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114657493546435936560286691 171986240319653904840430037)
              ·
                refine ⟨4030927507491888394697579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 171986240319653904840430037 4030927507491888394697579)
                ·
                  refine ⟨6046391261237832592046369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4030927507491888394697579 6046391261237832592046369)
                  ·
                    refine ⟨4534793445928374444034777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6046391261237832592046369 4534793445928374444034777)
                    ·
                      refine ⟨3401095084446280833026083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4534793445928374444034777 3401095084446280833026083)
                      ·
                        rfl

theorem cell23_6623609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 1, 2, 2].length) (baseStart_6623609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623609 prefixEnd_6623609 := by exact prefixLift 6623609
  have htrace : WordTrace (prefixWord ++ tailWord_6623609) baseStart_6623609 baseEnd_6623609 := by
    simpa [prefixWord, tailWord_6623609, baseEnd_6623609] using wordTrace_append hprefix tailTrace_6623609
  have hstable : (prefixWord ++ tailWord_6623609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623609).length < 2 ^ (prefixWord ++ tailWord_6623609).sum := by decide
  have hdescent : baseEnd_6623609 < baseStart_6623609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623628 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 2, 7]
def baseStart_6623628 : Nat := 118140960795 + 6623628 * 2 ^ 59
def prefixEnd_6623628 : Nat := 4983230072969 + 3 ^ 40 * 6623628 * 2
def baseEnd_6623628 : Nat := 1133701613526238752896165

theorem tailTrace_6623628 : CollatzResearch.WordTrace tailWord_6623628 prefixEnd_6623628 1133701613526238752896165 := by
  unfold tailWord_6623628
  simp only [CollatzResearch.WordTrace]
  refine ⟨120791780023867228223019769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161055706698489637630693025 120791780023867228223019769)
  ·
    refine ⟨90593835017900421167264827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120791780023867228223019769 90593835017900421167264827)
    ·
      refine ⟨135890752526850631750897241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90593835017900421167264827 135890752526850631750897241)
      ·
        refine ⟨101918064395137973813172931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135890752526850631750897241 101918064395137973813172931)
        ·
          refine ⟨152877096592706960719759397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101918064395137973813172931 152877096592706960719759397)
          ·
            refine ⟨28664455611132555134954887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152877096592706960719759397 28664455611132555134954887)
            ·
              refine ⟨42996683416698832702432331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28664455611132555134954887 42996683416698832702432331)
              ·
                refine ⟨64495025125048249053648497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42996683416698832702432331 64495025125048249053648497)
                ·
                  refine ⟨48371268843786186790236373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64495025125048249053648497 48371268843786186790236373)
                  ·
                    refine ⟨1133701613526238752896165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48371268843786186790236373 1133701613526238752896165)
                    ·
                      rfl

theorem cell23_6623628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_6623628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623628 prefixEnd_6623628 := by exact prefixLift 6623628
  have htrace : WordTrace (prefixWord ++ tailWord_6623628) baseStart_6623628 baseEnd_6623628 := by
    simpa [prefixWord, tailWord_6623628, baseEnd_6623628] using wordTrace_append hprefix tailTrace_6623628
  have hstable : (prefixWord ++ tailWord_6623628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623628).length < 2 ^ (prefixWord ++ tailWord_6623628).sum := by decide
  have hdescent : baseEnd_6623628 < baseStart_6623628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623642 : List Nat := [3, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3]
def baseStart_6623642 : Nat := 118140960795 + 6623642 * 2 ^ 59
def prefixEnd_6623642 : Nat := 4983230072969 + 3 ^ 40 * 6623642 * 2
def baseEnd_6623642 : Nat := 3401112029307879203913431

theorem tailTrace_6623642 : CollatzResearch.WordTrace tailWord_6623642 prefixEnd_6623642 3401112029307879203913431 := by
  unfold tailWord_6623642
  simp only [CollatzResearch.WordTrace]
  refine ⟨60396017667420934209262295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161056047113122491224699453 60396017667420934209262295)
  ·
    refine ⟨90594026501131401313893443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60396017667420934209262295 90594026501131401313893443)
    ·
      refine ⟨135891039751697101970840165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90594026501131401313893443 135891039751697101970840165)
      ·
        refine ⟨25479569953443206619532531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135891039751697101970840165 25479569953443206619532531)
        ·
          refine ⟨38219354930164809929298797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25479569953443206619532531 38219354930164809929298797)
          ·
            refine ⟨14332258098811803723487049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38219354930164809929298797 14332258098811803723487049)
            ·
              refine ⟨10749193574108852792615287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14332258098811803723487049 10749193574108852792615287)
              ·
                refine ⟨16123790361163279188922931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10749193574108852792615287 16123790361163279188922931)
                ·
                  refine ⟨24185685541744918783384397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16123790361163279188922931 24185685541744918783384397)
                  ·
                    refine ⟨9069632078154344543769149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24185685541744918783384397 9069632078154344543769149)
                    ·
                      refine ⟨3401112029307879203913431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9069632078154344543769149 3401112029307879203913431)
                      ·
                        rfl

theorem cell23_6623642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_6623642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623642 prefixEnd_6623642 := by exact prefixLift 6623642
  have htrace : WordTrace (prefixWord ++ tailWord_6623642) baseStart_6623642 baseEnd_6623642 := by
    simpa [prefixWord, tailWord_6623642, baseEnd_6623642] using wordTrace_append hprefix tailTrace_6623642
  have hstable : (prefixWord ++ tailWord_6623642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623642).length < 2 ^ (prefixWord ++ tailWord_6623642).sum := by decide
  have hdescent : baseEnd_6623642 < baseStart_6623642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623652 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 3, 3, 2]
def baseStart_6623652 : Nat := 118140960795 + 6623652 * 2 ^ 59
def prefixEnd_6623652 : Nat := 4983230072969 + 3 ^ 40 * 6623652 * 2
def baseEnd_6623652 : Nat := 3401117164114424164788385

theorem tailTrace_6623652 : CollatzResearch.WordTrace tailWord_6623652 prefixEnd_6623652 3401117164114424164788385 := by
  unfold tailWord_6623652
  simp only [CollatzResearch.WordTrace]
  refine ⟨120792217699823754272456605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161056290266431672363275473 120792217699823754272456605)
  ·
    refine ⟨45297081637433907852171227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120792217699823754272456605 45297081637433907852171227)
    ·
      refine ⟨67945622456150861778256841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45297081637433907852171227 67945622456150861778256841)
      ·
        refine ⟨50959216842113146333692631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67945622456150861778256841 50959216842113146333692631)
        ·
          refine ⟨76438825263169719500538947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50959216842113146333692631 76438825263169719500538947)
          ·
            refine ⟨114658237894754579250808421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76438825263169719500538947 114658237894754579250808421)
            ·
              refine ⟨21498419605266483609526579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114658237894754579250808421 21498419605266483609526579)
              ·
                refine ⟨32247629407899725414289869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21498419605266483609526579 32247629407899725414289869)
                ·
                  refine ⟨12092861027962397030358701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32247629407899725414289869 12092861027962397030358701)
                  ·
                    refine ⟨4534822885485898886384513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12092861027962397030358701 4534822885485898886384513)
                    ·
                      refine ⟨3401117164114424164788385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4534822885485898886384513 3401117164114424164788385)
                      ·
                        rfl

theorem cell23_6623652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_6623652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623652 prefixEnd_6623652 := by exact prefixLift 6623652
  have htrace : WordTrace (prefixWord ++ tailWord_6623652) baseStart_6623652 baseEnd_6623652 := by
    simpa [prefixWord, tailWord_6623652, baseEnd_6623652] using wordTrace_append hprefix tailTrace_6623652
  have hstable : (prefixWord ++ tailWord_6623652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623652).length < 2 ^ (prefixWord ++ tailWord_6623652).sum := by decide
  have hdescent : baseEnd_6623652 < baseStart_6623652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623676 : List Nat := [2, 2, 2, 4, 1, 3, 1, 2, 2, 1, 3]
def baseStart_6623676 : Nat := 118140960795 + 6623676 * 2 ^ 59
def prefixEnd_6623676 : Nat := 4983230072969 + 3 ^ 40 * 6623676 * 2
def baseEnd_6623676 : Nat := 3401129487650132070888275

theorem tailTrace_6623676 : CollatzResearch.WordTrace tailWord_6623676 prefixEnd_6623676 3401129487650132070888275 := by
  unfold tailWord_6623676
  simp only [CollatzResearch.WordTrace]
  refine ⟨120792655375780280321893441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161056873834373707095857921 120792655375780280321893441)
  ·
    refine ⟨90594491531835210241420081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120792655375780280321893441 90594491531835210241420081)
    ·
      refine ⟨67945868648876407681065061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90594491531835210241420081 67945868648876407681065061)
      ·
        refine ⟨12739850371664326440199699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67945868648876407681065061 12739850371664326440199699)
        ·
          refine ⟨19109775557496489660299549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12739850371664326440199699 19109775557496489660299549)
          ·
            refine ⟨7166165834061183622612331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19109775557496489660299549 7166165834061183622612331)
            ·
              refine ⟨10749248751091775433918497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7166165834061183622612331 10749248751091775433918497)
              ·
                refine ⟨8061936563318831575438873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10749248751091775433918497 8061936563318831575438873)
                ·
                  refine ⟨6046452422489123681579155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8061936563318831575438873 6046452422489123681579155)
                  ·
                    refine ⟨9069678633733685522368733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6046452422489123681579155 9069678633733685522368733)
                    ·
                      refine ⟨3401129487650132070888275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9069678633733685522368733 3401129487650132070888275)
                      ·
                        rfl

theorem cell23_6623676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_6623676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623676 prefixEnd_6623676 := by exact prefixLift 6623676
  have htrace : WordTrace (prefixWord ++ tailWord_6623676) baseStart_6623676 baseEnd_6623676 := by
    simpa [prefixWord, tailWord_6623676, baseEnd_6623676] using wordTrace_append hprefix tailTrace_6623676
  have hstable : (prefixWord ++ tailWord_6623676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623676).length < 2 ^ (prefixWord ++ tailWord_6623676).sum := by decide
  have hdescent : baseEnd_6623676 < baseStart_6623676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623702 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_6623702 : Nat := 118140960795 + 6623702 * 2 ^ 59
def prefixEnd_6623702 : Nat := 4983230072969 + 3 ^ 40 * 6623702 * 2
def baseEnd_6623702 : Nat := 3401142838147148969163155

theorem tailTrace_6623702 : CollatzResearch.WordTrace tailWord_6623702 prefixEnd_6623702 3401142838147148969163155 := by
  unfold tailWord_6623702
  simp only [CollatzResearch.WordTrace]
  refine ⟨15099141190591647942764585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161057506032977578056155573 15099141190591647942764585)
  ·
    refine ⟨11324355892943735957073439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15099141190591647942764585 11324355892943735957073439)
    ·
      refine ⟨16986533839415603935610159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11324355892943735957073439 16986533839415603935610159)
      ·
        refine ⟨25479800759123405903415239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16986533839415603935610159 25479800759123405903415239)
        ·
          refine ⟨38219701138685108855122859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25479800759123405903415239 38219701138685108855122859)
          ·
            refine ⟨57329551708027663282684289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38219701138685108855122859 57329551708027663282684289)
            ·
              refine ⟨42997163781020747462013217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57329551708027663282684289 42997163781020747462013217)
              ·
                refine ⟨32247872835765560596509913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42997163781020747462013217 32247872835765560596509913)
                ·
                  refine ⟨24185904626824170447382435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32247872835765560596509913 24185904626824170447382435)
                  ·
                    refine ⟨36278856940236255671073653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24185904626824170447382435 36278856940236255671073653)
                    ·
                      refine ⟨3401142838147148969163155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36278856940236255671073653 3401142838147148969163155)
                      ·
                        rfl

theorem cell23_6623702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_6623702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623702 prefixEnd_6623702 := by exact prefixLift 6623702
  have htrace : WordTrace (prefixWord ++ tailWord_6623702) baseStart_6623702 baseEnd_6623702 := by
    simpa [prefixWord, tailWord_6623702, baseEnd_6623702] using wordTrace_append hprefix tailTrace_6623702
  have hstable : (prefixWord ++ tailWord_6623702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623702).length < 2 ^ (prefixWord ++ tailWord_6623702).sum := by decide
  have hdescent : baseEnd_6623702 < baseStart_6623702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623745 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_6623745 : Nat := 118140960795 + 6623745 * 2 ^ 59
def prefixEnd_6623745 : Nat := 4983230072969 + 3 ^ 40 * 6623745 * 2
def baseEnd_6623745 : Nat := 3401164917815292300925457

theorem tailTrace_6623745 : CollatzResearch.WordTrace tailWord_6623745 prefixEnd_6623745 3401164917815292300925457 := by
  unfold tailWord_6623745
  simp only [CollatzResearch.WordTrace]
  refine ⟨241587827388310585428048689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161058551592207056952032459 241587827388310585428048689)
  ·
    refine ⟨181190870541232939071036517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241587827388310585428048689 181190870541232939071036517)
    ·
      refine ⟨33973288226481176075819347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181190870541232939071036517 33973288226481176075819347)
      ·
        refine ⟨50959932339721764113729021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33973288226481176075819347 50959932339721764113729021)
        ·
          refine ⟨19109974627395661542648383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50959932339721764113729021 19109974627395661542648383)
          ·
            refine ⟨28664961941093492313972575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19109974627395661542648383 28664961941093492313972575)
            ·
              refine ⟨42997442911640238470958863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28664961941093492313972575 42997442911640238470958863)
              ·
                refine ⟨64496164367460357706438295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42997442911640238470958863 64496164367460357706438295)
                ·
                  refine ⟨96744246551190536559657443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64496164367460357706438295 96744246551190536559657443)
                  ·
                    refine ⟨145116369826785804839486165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96744246551190536559657443 145116369826785804839486165)
                    ·
                      refine ⟨3401164917815292300925457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145116369826785804839486165 3401164917815292300925457)
                      ·
                        rfl

theorem cell23_6623745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_6623745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623745 prefixEnd_6623745 := by exact prefixLift 6623745
  have htrace : WordTrace (prefixWord ++ tailWord_6623745) baseStart_6623745 baseEnd_6623745 := by
    simpa [prefixWord, tailWord_6623745, baseEnd_6623745] using wordTrace_append hprefix tailTrace_6623745
  have hstable : (prefixWord ++ tailWord_6623745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623745).length < 2 ^ (prefixWord ++ tailWord_6623745).sum := by decide
  have hdescent : baseEnd_6623745 < baseStart_6623745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623772 : List Nat := [2, 2, 3, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_6623772 : Nat := 118140960795 + 6623772 * 2 ^ 59
def prefixEnd_6623772 : Nat := 4983230072969 + 3 ^ 40 * 6623772 * 2
def baseEnd_6623772 : Nat := 3401178781792963695287833

theorem tailTrace_6623772 : CollatzResearch.WordTrace tailWord_6623772 prefixEnd_6623772 3401178781792963695287833 := by
  unfold tailWord_6623772
  simp only [CollatzResearch.WordTrace]
  refine ⟨120794406079606384519640785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161059208106141846026187713 120794406079606384519640785)
  ·
    refine ⟨90595804559704788389730589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120794406079606384519640785 90595804559704788389730589)
    ·
      refine ⟨33973426709889295646148971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90595804559704788389730589 33973426709889295646148971)
      ·
        refine ⟨50960140064833943469223457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33973426709889295646148971 50960140064833943469223457)
        ·
          refine ⟨38220105048625457601917593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50960140064833943469223457 38220105048625457601917593)
          ·
            refine ⟨28665078786469093201438195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38220105048625457601917593 28665078786469093201438195)
            ·
              refine ⟨42997618179703639802157293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28665078786469093201438195 42997618179703639802157293)
              ·
                refine ⟨16124106817388864925808985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42997618179703639802157293 16124106817388864925808985)
                ·
                  refine ⟨12093080113041648694356739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16124106817388864925808985 12093080113041648694356739)
                  ·
                    refine ⟨18139620169562473041535109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12093080113041648694356739 18139620169562473041535109)
                    ·
                      refine ⟨3401178781792963695287833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18139620169562473041535109 3401178781792963695287833)
                      ·
                        rfl

theorem cell23_6623772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_6623772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623772 prefixEnd_6623772 := by exact prefixLift 6623772
  have htrace : WordTrace (prefixWord ++ tailWord_6623772) baseStart_6623772 baseEnd_6623772 := by
    simpa [prefixWord, tailWord_6623772, baseEnd_6623772] using wordTrace_append hprefix tailTrace_6623772
  have hstable : (prefixWord ++ tailWord_6623772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623772).length < 2 ^ (prefixWord ++ tailWord_6623772).sum := by decide
  have hdescent : baseEnd_6623772 < baseStart_6623772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623792 : List Nat := [2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 3]
def baseStart_6623792 : Nat := 118140960795 + 6623792 * 2 ^ 59
def prefixEnd_6623792 : Nat := 4983230072969 + 3 ^ 40 * 6623792 * 2
def baseEnd_6623792 : Nat := 3401189051406053617037741

theorem tailTrace_6623792 : CollatzResearch.WordTrace tailWord_6623792 prefixEnd_6623792 3401189051406053617037741 := by
  unfold tailWord_6623792
  simp only [CollatzResearch.WordTrace]
  refine ⟨120794770809570156227504815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161059694412760208303339753 120794770809570156227504815)
  ·
    refine ⟨181192156214355234341257223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120794770809570156227504815 181192156214355234341257223)
    ·
      refine ⟨271788234321532851511885835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181192156214355234341257223 271788234321532851511885835)
      ·
        refine ⟨407682351482299277267828753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271788234321532851511885835 407682351482299277267828753)
        ·
          refine ⟨305761763611724457950871565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407682351482299277267828753 305761763611724457950871565)
          ·
            refine ⟨114660661354396671731576837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305761763611724457950871565 114660661354396671731576837)
            ·
              refine ⟨21498874003949375949670657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114660661354396671731576837 21498874003949375949670657)
              ·
                refine ⟨16124155502962031962252993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21498874003949375949670657 16124155502962031962252993)
                ·
                  refine ⟨12093116627221523971689745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16124155502962031962252993 12093116627221523971689745)
                  ·
                    refine ⟨9069837470416142978767309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12093116627221523971689745 9069837470416142978767309)
                    ·
                      refine ⟨3401189051406053617037741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9069837470416142978767309 3401189051406053617037741)
                      ·
                        rfl

theorem cell23_6623792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 3].length) (baseStart_6623792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623792 prefixEnd_6623792 := by exact prefixLift 6623792
  have htrace : WordTrace (prefixWord ++ tailWord_6623792) baseStart_6623792 baseEnd_6623792 := by
    simpa [prefixWord, tailWord_6623792, baseEnd_6623792] using wordTrace_append hprefix tailTrace_6623792
  have hstable : (prefixWord ++ tailWord_6623792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623792).length < 2 ^ (prefixWord ++ tailWord_6623792).sum := by decide
  have hdescent : baseEnd_6623792 < baseStart_6623792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623799 : List Nat := [1, 1, 3, 1, 2, 3, 3, 4, 1, 4]
def baseStart_6623799 : Nat := 118140960795 + 6623799 * 2 ^ 59
def prefixEnd_6623799 : Nat := 4983230072969 + 3 ^ 40 * 6623799 * 2
def baseEnd_6623799 : Nat := 1133730881923545029883403

theorem tailTrace_6623799 : CollatzResearch.WordTrace tailWord_6623799 prefixEnd_6623799 1133730881923545029883403 := by
  unfold tailWord_6623799
  simp only [CollatzResearch.WordTrace]
  refine ⟨241589796930114952650514451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161059864620076635100342967 241589796930114952650514451)
  ·
    refine ⟨362384695395172428975771677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241589796930114952650514451 362384695395172428975771677)
    ·
      refine ⟨135894260773189660865914379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362384695395172428975771677 135894260773189660865914379)
      ·
        refine ⟨203841391159784491298871569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135894260773189660865914379 203841391159784491298871569)
        ·
          refine ⟨152881043369838368474153677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203841391159784491298871569 152881043369838368474153677)
          ·
            refine ⟨57330391263689388177807629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152881043369838368474153677 57330391263689388177807629)
            ·
              refine ⟨21498896723883520566677861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57330391263689388177807629 21498896723883520566677861)
              ·
                refine ⟨4031043135728160106252099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21498896723883520566677861 4031043135728160106252099)
                ·
                  refine ⟨6046564703592240159378149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4031043135728160106252099 6046564703592240159378149)
                  ·
                    refine ⟨1133730881923545029883403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6046564703592240159378149 1133730881923545029883403)
                    ·
                      rfl

theorem cell23_6623799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 1, 4].length) (baseStart_6623799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623799 prefixEnd_6623799 := by exact prefixLift 6623799
  have htrace : WordTrace (prefixWord ++ tailWord_6623799) baseStart_6623799 baseEnd_6623799 := by
    simpa [prefixWord, tailWord_6623799, baseEnd_6623799] using wordTrace_append hprefix tailTrace_6623799
  have hstable : (prefixWord ++ tailWord_6623799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623799).length < 2 ^ (prefixWord ++ tailWord_6623799).sum := by decide
  have hdescent : baseEnd_6623799 < baseStart_6623799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623855 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 3, 6]
def baseStart_6623855 : Nat := 118140960795 + 6623855 * 2 ^ 59
def prefixEnd_6623855 : Nat := 4983230072969 + 3 ^ 40 * 6623855 * 2
def baseEnd_6623855 : Nat := 1133740466895762290183317

theorem tailTrace_6623855 : CollatzResearch.WordTrace tailWord_6623855 prefixEnd_6623855 1133740466895762290183317 := by
  unfold tailWord_6623855
  simp only [CollatzResearch.WordTrace]
  refine ⟨241591839417912074214553019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161061226278608049476368679 241591839417912074214553019)
  ·
    refine ⟨362387759126868111321829529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241591839417912074214553019 362387759126868111321829529)
    ·
      refine ⟨271790819345151083491372147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362387759126868111321829529 271790819345151083491372147)
      ·
        refine ⟨407686229017726625237058221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271790819345151083491372147 407686229017726625237058221)
        ·
          refine ⟨152882335881647484463896833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407686229017726625237058221 152882335881647484463896833)
          ·
            refine ⟨114661751911235613347922625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152882335881647484463896833 114661751911235613347922625)
            ·
              refine ⟨85996313933426710010941969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114661751911235613347922625 85996313933426710010941969)
              ·
                refine ⟨64497235450070032508206477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85996313933426710010941969 64497235450070032508206477)
                ·
                  refine ⟨24186463293776262190577429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64497235450070032508206477 24186463293776262190577429)
                  ·
                    refine ⟨1133740466895762290183317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24186463293776262190577429 1133740466895762290183317)
                    ·
                      rfl

theorem cell23_6623855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 6].length) (baseStart_6623855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623855 prefixEnd_6623855 := by exact prefixLift 6623855
  have htrace : WordTrace (prefixWord ++ tailWord_6623855) baseStart_6623855 baseEnd_6623855 := by
    simpa [prefixWord, tailWord_6623855, baseEnd_6623855] using wordTrace_append hprefix tailTrace_6623855
  have hstable : (prefixWord ++ tailWord_6623855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623855).length < 2 ^ (prefixWord ++ tailWord_6623855).sum := by decide
  have hdescent : baseEnd_6623855 < baseStart_6623855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623856 : List Nat := [2, 1, 1, 1, 7, 1, 2, 1, 3, 1, 3]
def baseStart_6623856 : Nat := 118140960795 + 6623856 * 2 ^ 59
def prefixEnd_6623856 : Nat := 4983230072969 + 3 ^ 40 * 6623856 * 2
def baseEnd_6623856 : Nat := 3401221914167941366637447

theorem tailTrace_6623856 : CollatzResearch.WordTrace tailWord_6623856 prefixEnd_6623856 3401221914167941366637447 := by
  unfold tailWord_6623856
  simp only [CollatzResearch.WordTrace]
  refine ⟨120795937945454225692669711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161061250593938967590226281 120795937945454225692669711)
  ·
    refine ⟨181193906918181338539004567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120795937945454225692669711 181193906918181338539004567)
    ·
      refine ⟨271790860377272007808506851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181193906918181338539004567 271790860377272007808506851)
      ·
        refine ⟨407686290565908011712760277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271790860377272007808506851 407686290565908011712760277)
        ·
          refine ⟨9555147435138469024517819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 407686290565908011712760277 9555147435138469024517819)
          ·
            refine ⟨14332721152707703536776729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9555147435138469024517819 14332721152707703536776729)
            ·
              refine ⟨10749540864530777652582547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14332721152707703536776729 10749540864530777652582547)
              ·
                refine ⟨16124311296796166478873821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10749540864530777652582547 16124311296796166478873821)
                ·
                  refine ⟨6046616736298562429577683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16124311296796166478873821 6046616736298562429577683)
                  ·
                    refine ⟨9069925104447843644366525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6046616736298562429577683 9069925104447843644366525)
                    ·
                      refine ⟨3401221914167941366637447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9069925104447843644366525 3401221914167941366637447)
                      ·
                        rfl

theorem cell23_6623856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 3, 1, 3].length) (baseStart_6623856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623856 prefixEnd_6623856 := by exact prefixLift 6623856
  have htrace : WordTrace (prefixWord ++ tailWord_6623856) baseStart_6623856 baseEnd_6623856 := by
    simpa [prefixWord, tailWord_6623856, baseEnd_6623856] using wordTrace_append hprefix tailTrace_6623856
  have hstable : (prefixWord ++ tailWord_6623856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623856).length < 2 ^ (prefixWord ++ tailWord_6623856).sum := by decide
  have hdescent : baseEnd_6623856 < baseStart_6623856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623872 : List Nat := [2, 1, 1, 2, 1, 5, 3, 1, 1, 6]
def baseStart_6623872 : Nat := 118140960795 + 6623872 * 2 ^ 59
def prefixEnd_6623872 : Nat := 4983230072969 + 3 ^ 40 * 6623872 * 2
def baseEnd_6623872 : Nat := 1133743376619471101345791

theorem tailTrace_6623872 : CollatzResearch.WordTrace tailWord_6623872 prefixEnd_6623872 1133743376619471101345791 := by
  unfold tailWord_6623872
  simp only [CollatzResearch.WordTrace]
  refine ⟨120796229729425243058960935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161061639639233657411947913 120796229729425243058960935)
  ·
    refine ⟨181194344594137864588441403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120796229729425243058960935 181194344594137864588441403)
    ·
      refine ⟨271791516891206796882662105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181194344594137864588441403 271791516891206796882662105)
      ·
        refine ⟨203843637668405097661996579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271791516891206796882662105 203843637668405097661996579)
        ·
          refine ⟨305765456502607646492994869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203843637668405097661996579 305765456502607646492994869)
          ·
            refine ⟨28665511547119466858718269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 305765456502607646492994869 28665511547119466858718269)
            ·
              refine ⟨10749566830169800072019351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28665511547119466858718269 10749566830169800072019351)
              ·
                refine ⟨16124350245254700108029027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10749566830169800072019351 16124350245254700108029027)
                ·
                  refine ⟨24186525367882050162043541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16124350245254700108029027 24186525367882050162043541)
                  ·
                    refine ⟨1133743376619471101345791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24186525367882050162043541 1133743376619471101345791)
                    ·
                      rfl

theorem cell23_6623872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 1, 6].length) (baseStart_6623872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623872 prefixEnd_6623872 := by exact prefixLift 6623872
  have htrace : WordTrace (prefixWord ++ tailWord_6623872) baseStart_6623872 baseEnd_6623872 := by
    simpa [prefixWord, tailWord_6623872, baseEnd_6623872] using wordTrace_append hprefix tailTrace_6623872
  have hstable : (prefixWord ++ tailWord_6623872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623872).length < 2 ^ (prefixWord ++ tailWord_6623872).sum := by decide
  have hdescent : baseEnd_6623872 < baseStart_6623872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623879 : List Nat := [1, 1, 4, 2, 1, 2, 4, 2, 1, 1, 4]
def baseStart_6623879 : Nat := 118140960795 + 6623879 * 2 ^ 59
def prefixEnd_6623879 : Nat := 4983230072969 + 3 ^ 40 * 6623879 * 2
def baseEnd_6623879 : Nat := 3401233724222994776649841

theorem tailTrace_6623879 : CollatzResearch.WordTrace tailWord_6623879 prefixEnd_6623879 3401233724222994776649841 := by
  unfold tailWord_6623879
  simp only [CollatzResearch.WordTrace]
  refine ⟨241592714769825126313426691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161061809846550084208951127 241592714769825126313426691)
  ·
    refine ⟨362389072154737689470140037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241592714769825126313426691 362389072154737689470140037)
    ·
      refine ⟨67947951029013316775651257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 362389072154737689470140037 67947951029013316775651257)
      ·
        refine ⟨50960963271759987581738443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67947951029013316775651257 50960963271759987581738443)
        ·
          refine ⟨76441444907639981372607665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50960963271759987581738443 76441444907639981372607665)
          ·
            refine ⟨57331083680729986029455749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76441444907639981372607665 57331083680729986029455749)
            ·
              refine ⟨10749578190136872380522953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57331083680729986029455749 10749578190136872380522953)
              ·
                refine ⟨8062183642602654285392215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10749578190136872380522953 8062183642602654285392215)
                ·
                  refine ⟨12093275463903981428088323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8062183642602654285392215 12093275463903981428088323)
                  ·
                    refine ⟨18139913195855972142132485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12093275463903981428088323 18139913195855972142132485)
                    ·
                      refine ⟨3401233724222994776649841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18139913195855972142132485 3401233724222994776649841)
                      ·
                        rfl

theorem cell23_6623879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_6623879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623879 prefixEnd_6623879 := by exact prefixLift 6623879
  have htrace : WordTrace (prefixWord ++ tailWord_6623879) baseStart_6623879 baseEnd_6623879 := by
    simpa [prefixWord, tailWord_6623879, baseEnd_6623879] using wordTrace_append hprefix tailTrace_6623879
  have hstable : (prefixWord ++ tailWord_6623879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623879).length < 2 ^ (prefixWord ++ tailWord_6623879).sum := by decide
  have hdescent : baseEnd_6623879 < baseStart_6623879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623890 : List Nat := [3, 2, 3, 1, 2, 3, 1, 3, 1, 1, 3]
def baseStart_6623890 : Nat := 118140960795 + 6623890 * 2 ^ 59
def prefixEnd_6623890 : Nat := 4983230072969 + 3 ^ 40 * 6623890 * 2
def baseEnd_6623890 : Nat := 3401239372510194233612291

theorem tailTrace_6623890 : CollatzResearch.WordTrace tailWord_6623890 prefixEnd_6623890 3401239372510194233612291 := by
  unfold tailWord_6623890
  simp only [CollatzResearch.WordTrace]
  refine ⟨60398278993196318798019281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161062077315190183461384749 60398278993196318798019281)
  ·
    refine ⟨45298709244897239098514461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60398278993196318798019281 45298709244897239098514461)
    ·
      refine ⟨16987015966836464661942923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45298709244897239098514461 16987015966836464661942923)
      ·
        refine ⟨25480523950254696992914385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16987015966836464661942923 25480523950254696992914385)
        ·
          refine ⟨19110392962691022744685789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25480523950254696992914385 19110392962691022744685789)
          ·
            refine ⟨7166397361009133529257171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19110392962691022744685789 7166397361009133529257171)
            ·
              refine ⟨10749596041513700293885757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7166397361009133529257171 10749596041513700293885757)
              ·
                refine ⟨4031098515567637610207159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10749596041513700293885757 4031098515567637610207159)
                ·
                  refine ⟨6046647773351456415310739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4031098515567637610207159 6046647773351456415310739)
                  ·
                    refine ⟨9069971660027184622966109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6046647773351456415310739 9069971660027184622966109)
                    ·
                      refine ⟨3401239372510194233612291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9069971660027184622966109 3401239372510194233612291)
                      ·
                        rfl

theorem cell23_6623890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_6623890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623890 prefixEnd_6623890 := by exact prefixLift 6623890
  have htrace : WordTrace (prefixWord ++ tailWord_6623890) baseStart_6623890 baseEnd_6623890 := by
    simpa [prefixWord, tailWord_6623890, baseEnd_6623890] using wordTrace_append hprefix tailTrace_6623890
  have hstable : (prefixWord ++ tailWord_6623890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623890).length < 2 ^ (prefixWord ++ tailWord_6623890).sum := by decide
  have hdescent : baseEnd_6623890 < baseStart_6623890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623962 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 2, 6]
def baseStart_6623962 : Nat := 118140960795 + 6623962 * 2 ^ 59
def prefixEnd_6623962 : Nat := 4983230072969 + 3 ^ 40 * 6623962 * 2
def baseEnd_6623962 : Nat := 1133758781039105983970653

theorem tailTrace_6623962 : CollatzResearch.WordTrace tailWord_6623962 prefixEnd_6623962 1133758781039105983970653 := by
  unfold tailWord_6623962
  simp only [CollatzResearch.WordTrace]
  refine ⟨60398935507131107872174535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161063828019016287659132093 60398935507131107872174535)
  ·
    refine ⟨90598403260696661808261803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60398935507131107872174535 90598403260696661808261803)
    ·
      refine ⟨135897604891044992712392705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90598403260696661808261803 135897604891044992712392705)
      ·
        refine ⟨101923203668283744534294529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135897604891044992712392705 101923203668283744534294529)
        ·
          refine ⟨76442402751212808400720897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101923203668283744534294529 76442402751212808400720897)
          ·
            refine ⟨57331802063409606300540673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76442402751212808400720897 57331802063409606300540673)
            ·
              refine ⟨42998851547557204725405505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57331802063409606300540673 42998851547557204725405505)
              ·
                refine ⟨32249138660667903544054129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42998851547557204725405505 32249138660667903544054129)
                ·
                  refine ⟨24186853995500927658040597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32249138660667903544054129 24186853995500927658040597)
                  ·
                    refine ⟨1133758781039105983970653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24186853995500927658040597 1133758781039105983970653)
                    ·
                      rfl

theorem cell23_6623962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_6623962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623962 prefixEnd_6623962 := by exact prefixLift 6623962
  have htrace : WordTrace (prefixWord ++ tailWord_6623962) baseStart_6623962 baseEnd_6623962 := by
    simpa [prefixWord, tailWord_6623962, baseEnd_6623962] using wordTrace_append hprefix tailTrace_6623962
  have hstable : (prefixWord ++ tailWord_6623962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623962).length < 2 ^ (prefixWord ++ tailWord_6623962).sum := by decide
  have hdescent : baseEnd_6623962 < baseStart_6623962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623964 : List Nat := [2, 2, 5, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_6623964 : Nat := 118140960795 + 6623964 * 2 ^ 59
def prefixEnd_6623964 : Nat := 4983230072969 + 3 ^ 40 * 6623964 * 2
def baseEnd_6623964 : Nat := 3401277370078626944086951

theorem tailTrace_6623964 : CollatzResearch.WordTrace tailWord_6623964 prefixEnd_6623964 3401277370078626944086951 := by
  unfold tailWord_6623964
  simp only [CollatzResearch.WordTrace]
  refine ⟨120797907487258592915135473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161063876649678123886847297 120797907487258592915135473)
  ·
    refine ⟨90598430615443944686351605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120797907487258592915135473 90598430615443944686351605)
    ·
      refine ⟨8493602870197869814345463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90598430615443944686351605 8493602870197869814345463)
      ·
        refine ⟨12740404305296804721518195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8493602870197869814345463 12740404305296804721518195)
        ·
          refine ⟨19110606457945207082277293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12740404305296804721518195 19110606457945207082277293)
          ·
            refine ⟨7166477421729452655853985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19110606457945207082277293 7166477421729452655853985)
            ·
              refine ⟨5374858066297089491890489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7166477421729452655853985 5374858066297089491890489)
              ·
                refine ⟨4031143549722817118917867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5374858066297089491890489 4031143549722817118917867)
                ·
                  refine ⟨6046715324584225678376801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4031143549722817118917867 6046715324584225678376801)
                  ·
                    refine ⟨4535036493438169258782601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6046715324584225678376801 4535036493438169258782601)
                    ·
                      refine ⟨3401277370078626944086951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4535036493438169258782601 3401277370078626944086951)
                      ·
                        rfl

theorem cell23_6623964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_6623964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623964 prefixEnd_6623964 := by exact prefixLift 6623964
  have htrace : WordTrace (prefixWord ++ tailWord_6623964) baseStart_6623964 baseEnd_6623964 := by
    simpa [prefixWord, tailWord_6623964, baseEnd_6623964] using wordTrace_append hprefix tailTrace_6623964
  have hstable : (prefixWord ++ tailWord_6623964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623964).length < 2 ^ (prefixWord ++ tailWord_6623964).sum := by decide
  have hdescent : baseEnd_6623964 < baseStart_6623964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623986 : List Nat := [3, 2, 1, 3, 1, 2, 1, 3, 1, 4, 2]
def baseStart_6623986 : Nat := 118140960795 + 6623986 * 2 ^ 59
def prefixEnd_6623986 : Nat := 4983230072969 + 3 ^ 40 * 6623986 * 2
def baseEnd_6623986 : Nat := 3401288666653025858011849

theorem tailTrace_6623986 : CollatzResearch.WordTrace tailWord_6623986 prefixEnd_6623986 3401288666653025858011849 := by
  unfold tailWord_6623986
  simp only [CollatzResearch.WordTrace]
  refine ⟨60399154345109370896892953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161064411586958322391714541 60399154345109370896892953)
  ·
    refine ⟨45299365758832028172669715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60399154345109370896892953 45299365758832028172669715)
    ·
      refine ⟨67949048638248042259004573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45299365758832028172669715 67949048638248042259004573)
      ·
        refine ⟨25480893239343015847126715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67949048638248042259004573 25480893239343015847126715)
        ·
          refine ⟨38221339859014523770690073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25480893239343015847126715 38221339859014523770690073)
          ·
            refine ⟨28666004894260892828017555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38221339859014523770690073 28666004894260892828017555)
            ·
              refine ⟨42999007341391339242026333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28666004894260892828017555 42999007341391339242026333)
              ·
                refine ⟨16124627753021752215759875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42999007341391339242026333 16124627753021752215759875)
                ·
                  refine ⟨24186941629532628323639813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16124627753021752215759875 24186941629532628323639813)
                  ·
                    refine ⟨4535051555537367810682465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24186941629532628323639813 4535051555537367810682465)
                    ·
                      refine ⟨3401288666653025858011849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4535051555537367810682465 3401288666653025858011849)
                      ·
                        rfl

theorem cell23_6623986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_6623986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623986 prefixEnd_6623986 := by exact prefixLift 6623986
  have htrace : WordTrace (prefixWord ++ tailWord_6623986) baseStart_6623986 baseEnd_6623986 := by
    simpa [prefixWord, tailWord_6623986, baseEnd_6623986] using wordTrace_append hprefix tailTrace_6623986
  have hstable : (prefixWord ++ tailWord_6623986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623986).length < 2 ^ (prefixWord ++ tailWord_6623986).sum := by decide
  have hdescent : baseEnd_6623986 < baseStart_6623986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6623992 : List Nat := [2, 1, 2, 1, 1, 2, 5, 2, 7]
def baseStart_6623992 : Nat := 118140960795 + 6623992 * 2 ^ 59
def prefixEnd_6623992 : Nat := 4983230072969 + 3 ^ 40 * 6623992 * 2
def baseEnd_6623992 : Nat := 377921305281883648281869

theorem tailTrace_6623992 : CollatzResearch.WordTrace tailWord_6623992 prefixEnd_6623992 377921305281883648281869 := by
  unfold tailWord_6623992
  simp only [CollatzResearch.WordTrace]
  refine ⟨120798418109207873306145115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161064557478943831074860153 120798418109207873306145115)
  ·
    refine ⟨181197627163811809959217673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120798418109207873306145115 181197627163811809959217673)
    ·
      refine ⟨135898220372858857469413255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181197627163811809959217673 135898220372858857469413255)
      ·
        refine ⟨203847330559288286204119883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135898220372858857469413255 203847330559288286204119883)
        ·
          refine ⟨305770995838932429306179825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203847330559288286204119883 305770995838932429306179825)
          ·
            refine ⟨229328246879199321979634869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305770995838932429306179825 229328246879199321979634869)
            ·
              refine ⟨21499523144924936435590769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 229328246879199321979634869 21499523144924936435590769)
              ·
                refine ⟨16124642358693702326693077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21499523144924936435590769 16124642358693702326693077)
                ·
                  refine ⟨377921305281883648281869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16124642358693702326693077 377921305281883648281869)
                  ·
                    rfl

theorem cell23_6623992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 7].length) (baseStart_6623992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6623992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6623992 prefixEnd_6623992 := by exact prefixLift 6623992
  have htrace : WordTrace (prefixWord ++ tailWord_6623992) baseStart_6623992 baseEnd_6623992 := by
    simpa [prefixWord, tailWord_6623992, baseEnd_6623992] using wordTrace_append hprefix tailTrace_6623992
  have hstable : (prefixWord ++ tailWord_6623992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6623992).length < 2 ^ (prefixWord ++ tailWord_6623992).sum := by decide
  have hdescent : baseEnd_6623992 < baseStart_6623992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6623992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624009 : List Nat := [1, 2, 1, 1, 3, 2, 3, 5, 5]
def baseStart_6624009 : Nat := 118140960795 + 6624009 * 2 ^ 59
def prefixEnd_6624009 : Nat := 4983230072969 + 3 ^ 40 * 6624009 * 2
def baseEnd_6624009 : Nat := 377922275189786585336027

theorem tailTrace_6624009 : CollatzResearch.WordTrace tailWord_6624009 prefixEnd_6624009 377922275189786585336027 := by
  unfold tailWord_6624009
  simp only [CollatzResearch.WordTrace]
  refine ⟨241597456259354158515659081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161064970839569439010439387 241597456259354158515659081)
  ·
    refine ⟨181198092194515618886744311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241597456259354158515659081 181198092194515618886744311)
    ·
      refine ⟨271797138291773428330116467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181198092194515618886744311 271797138291773428330116467)
      ·
        refine ⟨407695707437660142495174701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271797138291773428330116467 407695707437660142495174701)
        ·
          refine ⟨152885890289122553435690513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407695707437660142495174701 152885890289122553435690513)
          ·
            refine ⟨114664417716841915076767885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152885890289122553435690513 114664417716841915076767885)
            ·
              refine ⟨42999156643815718153787957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114664417716841915076767885 42999156643815718153787957)
              ·
                refine ⟨4031170935357723576917621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42999156643815718153787957 4031170935357723576917621)
                ·
                  refine ⟨377922275189786585336027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4031170935357723576917621 377922275189786585336027)
                  ·
                    rfl

theorem cell23_6624009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 5].length) (baseStart_6624009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624009 prefixEnd_6624009 := by exact prefixLift 6624009
  have htrace : WordTrace (prefixWord ++ tailWord_6624009) baseStart_6624009 baseEnd_6624009 := by
    simpa [prefixWord, tailWord_6624009, baseEnd_6624009] using wordTrace_append hprefix tailTrace_6624009
  have hstable : (prefixWord ++ tailWord_6624009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624009).length < 2 ^ (prefixWord ++ tailWord_6624009).sum := by decide
  have hdescent : baseEnd_6624009 < baseStart_6624009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624076 : List Nat := [2, 2, 1, 3, 3, 2, 1, 2, 2, 1, 4]
def baseStart_6624076 : Nat := 118140960795 + 6624076 * 2 ^ 59
def prefixEnd_6624076 : Nat := 4983230072969 + 3 ^ 40 * 6624076 * 2
def baseEnd_6624076 : Nat := 3401334879911930505886435

theorem tailTrace_6624076 : CollatzResearch.WordTrace tailWord_6624076 prefixEnd_6624076 3401334879911930505886435 := by
  unfold tailWord_6624076
  simp only [CollatzResearch.WordTrace]
  refine ⟨120799949975055714479174041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161066599966740952638898721 120799949975055714479174041)
  ·
    refine ⟨90599962481291785859380531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120799949975055714479174041 90599962481291785859380531)
    ·
      refine ⟨135899943721937678789070797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90599962481291785859380531 135899943721937678789070797)
      ·
        refine ⟨50962478895726629545901549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135899943721937678789070797 50962478895726629545901549)
        ·
          refine ⟨19110929585897486079713081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50962478895726629545901549 19110929585897486079713081)
          ·
            refine ⟨14333197189423114559784811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19110929585897486079713081 14333197189423114559784811)
            ·
              refine ⟨21499795784134671839677217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14333197189423114559784811 21499795784134671839677217)
              ·
                refine ⟨16124846838101003879757913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21499795784134671839677217 16124846838101003879757913)
                ·
                  refine ⟨12093635128575752909818435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16124846838101003879757913 12093635128575752909818435)
                  ·
                    refine ⟨18140452692863629364727653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12093635128575752909818435 18140452692863629364727653)
                    ·
                      refine ⟨3401334879911930505886435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18140452692863629364727653 3401334879911930505886435)
                      ·
                        rfl

theorem cell23_6624076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_6624076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624076 prefixEnd_6624076 := by exact prefixLift 6624076
  have htrace : WordTrace (prefixWord ++ tailWord_6624076) baseStart_6624076 baseEnd_6624076 := by
    simpa [prefixWord, tailWord_6624076, baseEnd_6624076] using wordTrace_append hprefix tailTrace_6624076
  have hstable : (prefixWord ++ tailWord_6624076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624076).length < 2 ^ (prefixWord ++ tailWord_6624076).sum := by decide
  have hdescent : baseEnd_6624076 < baseStart_6624076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624150 : List Nat := [5, 3, 1, 1, 1, 1, 2, 3, 6]
def baseStart_6624150 : Nat := 118140960795 + 6624150 * 2 ^ 59
def prefixEnd_6624150 : Nat := 4983230072969 + 3 ^ 40 * 6624150 * 2
def baseEnd_6624150 : Nat := 377930319720040357373455

theorem tailTrace_6624150 : CollatzResearch.WordTrace tailWord_6624150 prefixEnd_6624150 377930319720040357373455 := by
  unfold tailWord_6624150
  simp only [CollatzResearch.WordTrace]
  refine ⟨15100162434490208724783869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161068399301228893064361269 15100162434490208724783869)
  ·
    refine ⟨5662560912933828271793951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15100162434490208724783869 5662560912933828271793951)
    ·
      refine ⟨8493841369400742407690927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5662560912933828271793951 8493841369400742407690927)
      ·
        refine ⟨12740762054101113611536391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8493841369400742407690927 12740762054101113611536391)
        ·
          refine ⟨19111143081151670417304587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12740762054101113611536391 19111143081151670417304587)
          ·
            refine ⟨28666714621727505625956881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19111143081151670417304587 28666714621727505625956881)
            ·
              refine ⟨21500035966295629219467661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28666714621727505625956881 21500035966295629219467661)
              ·
                refine ⟨8062513487360860957300373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21500035966295629219467661 8062513487360860957300373)
                ·
                  refine ⟨377930319720040357373455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8062513487360860957300373 377930319720040357373455)
                  ·
                    rfl

theorem cell23_6624150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_6624150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624150 prefixEnd_6624150 := by exact prefixLift 6624150
  have htrace : WordTrace (prefixWord ++ tailWord_6624150) baseStart_6624150 baseEnd_6624150 := by
    simpa [prefixWord, tailWord_6624150, baseEnd_6624150] using wordTrace_append hprefix tailTrace_6624150
  have hstable : (prefixWord ++ tailWord_6624150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624150).length < 2 ^ (prefixWord ++ tailWord_6624150).sum := by decide
  have hdescent : baseEnd_6624150 < baseStart_6624150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624177 : List Nat := [1, 2, 2, 4, 3, 1, 2, 3, 1, 1, 3]
def baseStart_6624177 : Nat := 118140960795 + 6624177 * 2 ^ 59
def prefixEnd_6624177 : Nat := 4983230072969 + 3 ^ 40 * 6624177 * 2
def baseEnd_6624177 : Nat := 3401386741458034610723471

theorem tailTrace_6624177 : CollatzResearch.WordTrace tailWord_6624177 prefixEnd_6624177 3401386741458034610723471 := by
  unfold tailWord_6624177
  simp only [CollatzResearch.WordTrace]
  refine ⟨241603583722745523207774785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161069055815163682138516523 241603583722745523207774785)
  ·
    refine ⟨181202687792059142405831089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241603583722745523207774785 181202687792059142405831089)
    ·
      refine ⟨135902015844044356804373317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181202687792059142405831089 135902015844044356804373317)
      ·
        refine ⟨25481627970758316900819997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135902015844044356804373317 25481627970758316900819997)
        ·
          refine ⟨9555610489034368837807499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25481627970758316900819997 9555610489034368837807499)
          ·
            refine ⟨14333415733551553256711249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9555610489034368837807499 14333415733551553256711249)
            ·
              refine ⟨10750061800163664942533437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14333415733551553256711249 10750061800163664942533437)
              ·
                refine ⟨4031273175061374353450039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10750061800163664942533437 4031273175061374353450039)
                ·
                  refine ⟨6046909762592061530175059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4031273175061374353450039 6046909762592061530175059)
                  ·
                    refine ⟨9070364643888092295262589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6046909762592061530175059 9070364643888092295262589)
                    ·
                      refine ⟨3401386741458034610723471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9070364643888092295262589 3401386741458034610723471)
                      ·
                        rfl

theorem cell23_6624177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_6624177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624177 prefixEnd_6624177 := by exact prefixLift 6624177
  have htrace : WordTrace (prefixWord ++ tailWord_6624177) baseStart_6624177 baseEnd_6624177 := by
    simpa [prefixWord, tailWord_6624177, baseEnd_6624177] using wordTrace_append hprefix tailTrace_6624177
  have hstable : (prefixWord ++ tailWord_6624177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624177).length < 2 ^ (prefixWord ++ tailWord_6624177).sum := by decide
  have hdescent : baseEnd_6624177 < baseStart_6624177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624179 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 4]
def baseStart_6624179 : Nat := 118140960795 + 6624179 * 2 ^ 59
def prefixEnd_6624179 : Nat := 4983230072969 + 3 ^ 40 * 6624179 * 2
def baseEnd_6624179 : Nat := 3401387768419343602898461

theorem tailTrace_6624179 : CollatzResearch.WordTrace tailWord_6624179 prefixEnd_6624179 3401387768419343602898461 := by
  unfold tailWord_6624179
  simp only [CollatzResearch.WordTrace]
  refine ⟨241603656668738277549347591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161069104445825518366231727 241603656668738277549347591)
  ·
    refine ⟨362405485003107416324021387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241603656668738277549347591 362405485003107416324021387)
    ·
      refine ⟨543608227504661124486032081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362405485003107416324021387 543608227504661124486032081)
      ·
        refine ⟨407706170628495843364524061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543608227504661124486032081 407706170628495843364524061)
        ·
          refine ⟨152889813985685941261696523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407706170628495843364524061 152889813985685941261696523)
          ·
            refine ⟨229334720978528911892544785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152889813985685941261696523 229334720978528911892544785)
            ·
              refine ⟨172001040733896683919408589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229334720978528911892544785 172001040733896683919408589)
              ·
                refine ⟨64500390275211256469778221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172001040733896683919408589 64500390275211256469778221)
                ·
                  refine ⟨24187646353204221176166833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64500390275211256469778221 24187646353204221176166833)
                  ·
                    refine ⟨18140734764903165882125125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24187646353204221176166833 18140734764903165882125125)
                    ·
                      refine ⟨3401387768419343602898461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18140734764903165882125125 3401387768419343602898461)
                      ·
                        rfl

theorem cell23_6624179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 4].length) (baseStart_6624179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624179 prefixEnd_6624179 := by exact prefixLift 6624179
  have htrace : WordTrace (prefixWord ++ tailWord_6624179) baseStart_6624179 baseEnd_6624179 := by
    simpa [prefixWord, tailWord_6624179, baseEnd_6624179] using wordTrace_append hprefix tailTrace_6624179
  have hstable : (prefixWord ++ tailWord_6624179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624179).length < 2 ^ (prefixWord ++ tailWord_6624179).sum := by decide
  have hdescent : baseEnd_6624179 < baseStart_6624179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624180 : List Nat := [2, 5, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_6624180 : Nat := 118140960795 + 6624180 * 2 ^ 59
def prefixEnd_6624180 : Nat := 4983230072969 + 3 ^ 40 * 6624180 * 2
def baseEnd_6624180 : Nat := 1133796093966666032995319

theorem tailTrace_6624180 : CollatzResearch.WordTrace tailWord_6624180 prefixEnd_6624180 1133796093966666032995319 := by
  unfold tailWord_6624180
  simp only [CollatzResearch.WordTrace]
  refine ⟨120801846570867327360066997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161069128761156436480089329 120801846570867327360066997)
  ·
    refine ⟨11325173116018811940006281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120801846570867327360066997 11325173116018811940006281)
    ·
      refine ⟨8493879837014108955004711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11325173116018811940006281 8493879837014108955004711)
      ·
        refine ⟨12740819755521163432507067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8493879837014108955004711 12740819755521163432507067)
        ·
          refine ⟨19111229633281745148760601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12740819755521163432507067 19111229633281745148760601)
          ·
            refine ⟨14333422224961308861570451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19111229633281745148760601 14333422224961308861570451)
            ·
              refine ⟨21500133337441963292355677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14333422224961308861570451 21500133337441963292355677)
              ·
                refine ⟨8062550001540736234633379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21500133337441963292355677 8062550001540736234633379)
                ·
                  refine ⟨12093825002311104351950069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8062550001540736234633379 12093825002311104351950069)
                  ·
                    refine ⟨1133796093966666032995319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12093825002311104351950069 1133796093966666032995319)
                    ·
                      rfl

theorem cell23_6624180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_6624180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624180 prefixEnd_6624180 := by exact prefixLift 6624180
  have htrace : WordTrace (prefixWord ++ tailWord_6624180) baseStart_6624180 baseEnd_6624180 := by
    simpa [prefixWord, tailWord_6624180, baseEnd_6624180] using wordTrace_append hprefix tailTrace_6624180
  have hstable : (prefixWord ++ tailWord_6624180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624180).length < 2 ^ (prefixWord ++ tailWord_6624180).sum := by decide
  have hdescent : baseEnd_6624180 < baseStart_6624180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624183 : List Nat := [1, 1, 3, 1, 3, 1, 6, 1, 1, 1, 4]
def baseStart_6624183 : Nat := 118140960795 + 6624183 * 2 ^ 59
def prefixEnd_6624183 : Nat := 4983230072969 + 3 ^ 40 * 6624183 * 2
def baseEnd_6624183 : Nat := 3401389822341961587248443

theorem tailTrace_6624183 : CollatzResearch.WordTrace tailWord_6624183 prefixEnd_6624183 3401389822341961587248443 := by
  unfold tailWord_6624183
  simp only [CollatzResearch.WordTrace]
  refine ⟨241603802560723786232493203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161069201707149190821662135 241603802560723786232493203)
  ·
    refine ⟨362405703841085679348739805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241603802560723786232493203 362405703841085679348739805)
    ·
      refine ⟨135902138940407129755777427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362405703841085679348739805 135902138940407129755777427)
      ·
        refine ⟨203853208410610694633666141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135902138940407129755777427 203853208410610694633666141)
        ·
          refine ⟨76444953153979010487624803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203853208410610694633666141 76444953153979010487624803)
          ·
            refine ⟨114667429730968515731437205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76444953153979010487624803 114667429730968515731437205)
            ·
              refine ⟨5375035768639149174911119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114667429730968515731437205 5375035768639149174911119)
              ·
                refine ⟨8062553652958723762366679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5375035768639149174911119 8062553652958723762366679)
                ·
                  refine ⟨12093830479438085643550019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8062553652958723762366679 12093830479438085643550019)
                  ·
                    refine ⟨18140745719157128465325029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12093830479438085643550019 18140745719157128465325029)
                    ·
                      refine ⟨3401389822341961587248443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18140745719157128465325029 3401389822341961587248443)
                      ·
                        rfl

theorem cell23_6624183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 1, 1, 4].length) (baseStart_6624183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624183 prefixEnd_6624183 := by exact prefixLift 6624183
  have htrace : WordTrace (prefixWord ++ tailWord_6624183) baseStart_6624183 baseEnd_6624183 := by
    simpa [prefixWord, tailWord_6624183, baseEnd_6624183] using wordTrace_append hprefix tailTrace_6624183
  have hstable : (prefixWord ++ tailWord_6624183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624183).length < 2 ^ (prefixWord ++ tailWord_6624183).sum := by decide
  have hdescent : baseEnd_6624183 < baseStart_6624183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624223 : List Nat := [1, 1, 2, 3, 5, 2, 2, 7]
def baseStart_6624223 : Nat := 118140960795 + 6624223 * 2 ^ 59
def prefixEnd_6624223 : Nat := 4983230072969 + 3 ^ 40 * 6624223 * 2
def baseEnd_6624223 : Nat := 125978161539560793731417

theorem tailTrace_6624223 : CollatzResearch.WordTrace tailWord_6624223 prefixEnd_6624223 125978161539560793731417 := by
  unfold tailWord_6624223
  simp only [CollatzResearch.WordTrace]
  refine ⟨241605261480578873063949323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161070174320385915375966215 241605261480578873063949323)
  ·
    refine ⟨362407892220868309595923985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241605261480578873063949323 362407892220868309595923985)
    ·
      refine ⟨271805919165651232196942989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362407892220868309595923985 271805919165651232196942989)
      ·
        refine ⟨101927219687119212073853621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271805919165651232196942989 101927219687119212073853621)
        ·
          refine ⟨9555676845667426131923777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101927219687119212073853621 9555676845667426131923777)
          ·
            refine ⟨7166757634250569598942833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9555676845667426131923777 7166757634250569598942833)
            ·
              refine ⟨5375068225687927199207125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7166757634250569598942833 5375068225687927199207125)
              ·
                refine ⟨125978161539560793731417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5375068225687927199207125 125978161539560793731417)
                ·
                  rfl

theorem cell23_6624223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 7].length) (baseStart_6624223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624223 prefixEnd_6624223 := by exact prefixLift 6624223
  have htrace : WordTrace (prefixWord ++ tailWord_6624223) baseStart_6624223 baseEnd_6624223 := by
    simpa [prefixWord, tailWord_6624223, baseEnd_6624223] using wordTrace_append hprefix tailTrace_6624223
  have hstable : (prefixWord ++ tailWord_6624223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624223).length < 2 ^ (prefixWord ++ tailWord_6624223).sum := by decide
  have hdescent : baseEnd_6624223 < baseStart_6624223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624234 : List Nat := [3, 1, 3, 1, 2, 4, 1, 3, 1, 2, 2]
def baseStart_6624234 : Nat := 118140960795 + 6624234 * 2 ^ 59
def prefixEnd_6624234 : Nat := 4983230072969 + 3 ^ 40 * 6624234 * 2
def baseEnd_6624234 : Nat := 3401416009855340887710709

theorem tailTrace_6624234 : CollatzResearch.WordTrace tailWord_6624234 prefixEnd_6624234 3401416009855340887710709 := by
  unfold tailWord_6624234
  simp only [CollatzResearch.WordTrace]
  refine ⟨60401415670884755485649939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161070441789026014628399837 60401415670884755485649939)
  ·
    refine ⟨90602123506327133228474909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60401415670884755485649939 90602123506327133228474909)
    ·
      refine ⟨33975796314872674960678091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90602123506327133228474909 33975796314872674960678091)
      ·
        refine ⟨50963694472309012441017137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33975796314872674960678091 50963694472309012441017137)
        ·
          refine ⟨38222770854231759330762853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50963694472309012441017137 38222770854231759330762853)
          ·
            refine ⟨7166769535168454874518035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38222770854231759330762853 7166769535168454874518035)
            ·
              refine ⟨10750154302752682311777053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7166769535168454874518035 10750154302752682311777053)
              ·
                refine ⟨4031307863532255866916395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10750154302752682311777053 4031307863532255866916395)
                ·
                  refine ⟨6046961795298383800374593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4031307863532255866916395 6046961795298383800374593)
                  ·
                    refine ⟨4535221346473787850280945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6046961795298383800374593 4535221346473787850280945)
                    ·
                      refine ⟨3401416009855340887710709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4535221346473787850280945 3401416009855340887710709)
                      ·
                        rfl

theorem cell23_6624234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_6624234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624234 prefixEnd_6624234 := by exact prefixLift 6624234
  have htrace : WordTrace (prefixWord ++ tailWord_6624234) baseStart_6624234 baseEnd_6624234 := by
    simpa [prefixWord, tailWord_6624234, baseEnd_6624234] using wordTrace_append hprefix tailTrace_6624234
  have hstable : (prefixWord ++ tailWord_6624234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624234).length < 2 ^ (prefixWord ++ tailWord_6624234).sum := by decide
  have hdescent : baseEnd_6624234 < baseStart_6624234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624267 : List Nat := [1, 1, 1, 1, 6, 4, 2, 1, 2, 1, 3]
def baseStart_6624267 : Nat := 118140960795 + 6624267 * 2 ^ 59
def prefixEnd_6624267 : Nat := 4983230072969 + 3 ^ 40 * 6624267 * 2
def baseEnd_6624267 : Nat := 3401432954716939258598057

theorem tailTrace_6624267 : CollatzResearch.WordTrace tailWord_6624267 prefixEnd_6624267 3401432954716939258598057 := by
  unfold tailWord_6624267
  simp only [CollatzResearch.WordTrace]
  refine ⟨241606866292419468578551055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161071244194946312385700703 241606866292419468578551055)
  ·
    refine ⟨362410299438629202867826583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241606866292419468578551055 362410299438629202867826583)
    ·
      refine ⟨543615449157943804301739875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362410299438629202867826583 543615449157943804301739875)
      ·
        refine ⟨815423173736915706452609813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543615449157943804301739875 815423173736915706452609813)
        ·
          refine ⟨38222961268917923739966085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 815423173736915706452609813 38222961268917923739966085)
          ·
            refine ⟨7166805237922110701243641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38222961268917923739966085 7166805237922110701243641)
            ·
              refine ⟨5375103928441583025932731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7166805237922110701243641 5375103928441583025932731)
              ·
                refine ⟨8062655892662374538899097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5375103928441583025932731 8062655892662374538899097)
                ·
                  refine ⟨6046991919496780904174323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8062655892662374538899097 6046991919496780904174323)
                  ·
                    refine ⟨9070487879245171356261485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6046991919496780904174323 9070487879245171356261485)
                    ·
                      refine ⟨3401432954716939258598057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9070487879245171356261485 3401432954716939258598057)
                      ·
                        rfl

theorem cell23_6624267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 2, 1, 3].length) (baseStart_6624267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624267 prefixEnd_6624267 := by exact prefixLift 6624267
  have htrace : WordTrace (prefixWord ++ tailWord_6624267) baseStart_6624267 baseEnd_6624267 := by
    simpa [prefixWord, tailWord_6624267, baseEnd_6624267] using wordTrace_append hprefix tailTrace_6624267
  have hstable : (prefixWord ++ tailWord_6624267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624267).length < 2 ^ (prefixWord ++ tailWord_6624267).sum := by decide
  have hdescent : baseEnd_6624267 < baseStart_6624267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624277 : List Nat := [1, 3, 2, 1, 4, 3, 1, 2, 1, 3, 2]
def baseStart_6624277 : Nat := 118140960795 + 6624277 * 2 ^ 59
def prefixEnd_6624277 : Nat := 4983230072969 + 3 ^ 40 * 6624277 * 2
def baseEnd_6624277 : Nat := 3401438089523484219473011

theorem tailTrace_6624277 : CollatzResearch.WordTrace tailWord_6624277 prefixEnd_6624277 3401438089523484219473011 := by
  unfold tailWord_6624277
  simp only [CollatzResearch.WordTrace]
  refine ⟨241607231022383240286415085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161071487348255493524276723 241607231022383240286415085)
  ·
    refine ⟨90602711633393715107405657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241607231022383240286415085 90602711633393715107405657)
    ·
      refine ⟨67952033725045286330554243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90602711633393715107405657 67952033725045286330554243)
      ·
        refine ⟨101928050587567929495831365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67952033725045286330554243 101928050587567929495831365)
        ·
          refine ⟨19111509485168986780468381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101928050587567929495831365 19111509485168986780468381)
          ·
            refine ⟨7166816056938370042675643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19111509485168986780468381 7166816056938370042675643)
            ·
              refine ⟨10750224085407555064013465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7166816056938370042675643 10750224085407555064013465)
              ·
                refine ⟨8062668064055666298010099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10750224085407555064013465 8062668064055666298010099)
                ·
                  refine ⟨12094002096083499447015149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8062668064055666298010099 12094002096083499447015149)
                  ·
                    refine ⟨4535250786031312292630681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12094002096083499447015149 4535250786031312292630681)
                    ·
                      refine ⟨3401438089523484219473011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4535250786031312292630681 3401438089523484219473011)
                      ·
                        rfl

theorem cell23_6624277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_6624277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624277 prefixEnd_6624277 := by exact prefixLift 6624277
  have htrace : WordTrace (prefixWord ++ tailWord_6624277) baseStart_6624277 baseEnd_6624277 := by
    simpa [prefixWord, tailWord_6624277, baseEnd_6624277] using wordTrace_append hprefix tailTrace_6624277
  have hstable : (prefixWord ++ tailWord_6624277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624277).length < 2 ^ (prefixWord ++ tailWord_6624277).sum := by decide
  have hdescent : baseEnd_6624277 < baseStart_6624277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624290 : List Nat := [3, 3, 1, 1, 1, 4, 1, 2, 1, 4, 2]
def baseStart_6624290 : Nat := 118140960795 + 6624290 * 2 ^ 59
def prefixEnd_6624290 : Nat := 4983230072969 + 3 ^ 40 * 6624290 * 2
def baseEnd_6624290 : Nat := 3401444764771992668610451

theorem tailTrace_6624290 : CollatzResearch.WordTrace tailWord_6624290 prefixEnd_6624290 3401444764771992668610451 := by
  unfold tailWord_6624290
  simp only [CollatzResearch.WordTrace]
  refine ⟨60401926292834035876659581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161071803447557429004425549 60401926292834035876659581)
  ·
    refine ⟨22650722359812763453747343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60401926292834035876659581 22650722359812763453747343)
    ·
      refine ⟨33976083539719145180621015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22650722359812763453747343 33976083539719145180621015)
      ·
        refine ⟨50964125309578717770931523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33976083539719145180621015 50964125309578717770931523)
        ·
          refine ⟨76446187964368076656397285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50964125309578717770931523 76446187964368076656397285)
          ·
            refine ⟨14333660243319014373074491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76446187964368076656397285 14333660243319014373074491)
            ·
              refine ⟨21500490364978521559611737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14333660243319014373074491 21500490364978521559611737)
              ·
                refine ⟨16125367773733891169708803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21500490364978521559611737 16125367773733891169708803)
                ·
                  refine ⟨24188051660600836754563205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16125367773733891169708803 24188051660600836754563205)
                  ·
                    refine ⟨4535259686362656891480601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24188051660600836754563205 4535259686362656891480601)
                    ·
                      refine ⟨3401444764771992668610451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4535259686362656891480601 3401444764771992668610451)
                      ·
                        rfl

theorem cell23_6624290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_6624290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624290 prefixEnd_6624290 := by exact prefixLift 6624290
  have htrace : WordTrace (prefixWord ++ tailWord_6624290) baseStart_6624290 baseEnd_6624290 := by
    simpa [prefixWord, tailWord_6624290, baseEnd_6624290] using wordTrace_append hprefix tailTrace_6624290
  have hstable : (prefixWord ++ tailWord_6624290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624290).length < 2 ^ (prefixWord ++ tailWord_6624290).sum := by decide
  have hdescent : baseEnd_6624290 < baseStart_6624290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624407 : List Nat := [1, 1, 3, 3, 3, 1, 3, 3, 1, 4]
def baseStart_6624407 : Nat := 118140960795 + 6624407 * 2 ^ 59
def prefixEnd_6624407 : Nat := 4983230072969 + 3 ^ 40 * 6624407 * 2
def baseEnd_6624407 : Nat := 1133834947336189570282471

theorem tailTrace_6624407 : CollatzResearch.WordTrace tailWord_6624407 prefixEnd_6624407 1133834947336189570282471 := by
  unfold tailWord_6624407
  simp only [CollatzResearch.WordTrace]
  refine ⟨241611972511912272488647475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161074648341274848325764983 241611972511912272488647475)
  ·
    refine ⟨362417958767868408732971213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241611972511912272488647475 362417958767868408732971213)
    ·
      refine ⟨135906734537950653274864205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362417958767868408732971213 135906734537950653274864205)
      ·
        refine ⟨50965025451731494978074077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135906734537950653274864205 50965025451731494978074077)
        ·
          refine ⟨19111884544399310616777779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50965025451731494978074077 19111884544399310616777779)
          ·
            refine ⟨28667826816598965925166669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19111884544399310616777779 28667826816598965925166669)
            ·
              refine ⟨10750435056224612221937501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28667826816598965925166669 10750435056224612221937501)
              ·
                refine ⟨4031413146084229583226563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10750435056224612221937501 4031413146084229583226563)
                ·
                  refine ⟨6047119719126344374839845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4031413146084229583226563 6047119719126344374839845)
                  ·
                    refine ⟨1133834947336189570282471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6047119719126344374839845 1133834947336189570282471)
                    ·
                      rfl

theorem cell23_6624407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 1, 4].length) (baseStart_6624407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624407 prefixEnd_6624407 := by exact prefixLift 6624407
  have htrace : WordTrace (prefixWord ++ tailWord_6624407) baseStart_6624407 baseEnd_6624407 := by
    simpa [prefixWord, tailWord_6624407, baseEnd_6624407] using wordTrace_append hprefix tailTrace_6624407
  have hstable : (prefixWord ++ tailWord_6624407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624407).length < 2 ^ (prefixWord ++ tailWord_6624407).sum := by decide
  have hdescent : baseEnd_6624407 < baseStart_6624407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624463 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 4, 4]
def baseStart_6624463 : Nat := 118140960795 + 6624463 * 2 ^ 59
def prefixEnd_6624463 : Nat := 4983230072969 + 3 ^ 40 * 6624463 * 2
def baseEnd_6624463 : Nat := 1133844532308406830582385

theorem tailTrace_6624463 : CollatzResearch.WordTrace tailWord_6624463 prefixEnd_6624463 1133844532308406830582385 := by
  unfold tailWord_6624463
  simp only [CollatzResearch.WordTrace]
  refine ⟨241614014999709394052686043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161076009999806262701790695 241614014999709394052686043)
  ·
    refine ⟨362421022499564091079029065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241614014999709394052686043 362421022499564091079029065)
    ·
      refine ⟨271815766874673068309271799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362421022499564091079029065 271815766874673068309271799)
      ·
        refine ⟨407723650312009602463907699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271815766874673068309271799 407723650312009602463907699)
        ·
          refine ⟨611585475468014403695861549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407723650312009602463907699 611585475468014403695861549)
          ·
            refine ⟨229344553300505401385948081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 611585475468014403695861549 229344553300505401385948081)
            ·
              refine ⟨172008414975379051039461061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229344553300505401385948081 172008414975379051039461061)
              ·
                refine ⟨32251577807883572069898949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172008414975379051039461061 32251577807883572069898949)
                ·
                  refine ⟨6047170838978169763106053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32251577807883572069898949 6047170838978169763106053)
                  ·
                    refine ⟨1133844532308406830582385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6047170838978169763106053 1133844532308406830582385)
                    ·
                      rfl

theorem cell23_6624463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 4].length) (baseStart_6624463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624463 prefixEnd_6624463 := by exact prefixLift 6624463
  have htrace : WordTrace (prefixWord ++ tailWord_6624463) baseStart_6624463 baseEnd_6624463 := by
    simpa [prefixWord, tailWord_6624463, baseEnd_6624463] using wordTrace_append hprefix tailTrace_6624463
  have hstable : (prefixWord ++ tailWord_6624463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624463).length < 2 ^ (prefixWord ++ tailWord_6624463).sum := by decide
  have hdescent : baseEnd_6624463 < baseStart_6624463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624480 : List Nat := [2, 1, 1, 3, 1, 4, 1, 4, 2, 4]
def baseStart_6624480 : Nat := 118140960795 + 6624480 * 2 ^ 59
def prefixEnd_6624480 : Nat := 4983230072969 + 3 ^ 40 * 6624480 * 2
def baseEnd_6624480 : Nat := 1133847442032115641744859

theorem tailTrace_6624480 : CollatzResearch.WordTrace tailWord_6624480 prefixEnd_6624480 1133847442032115641744859 := by
  unfold tailWord_6624480
  simp only [CollatzResearch.WordTrace]
  refine ⟨120807317520323902978027447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161076423360431870637369929 120807317520323902978027447)
  ·
    refine ⟨181210976280485854467041171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120807317520323902978027447 181210976280485854467041171)
    ·
      refine ⟨271816464420728781700561757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181210976280485854467041171 271816464420728781700561757)
      ·
        refine ⟨101931174157773293137710659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271816464420728781700561757 101931174157773293137710659)
        ·
          refine ⟨152896761236659939706565989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101931174157773293137710659 152896761236659939706565989)
          ·
            refine ⟨28668142731873738694981123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152896761236659939706565989 28668142731873738694981123)
            ·
              refine ⟨43002214097810608042471685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28668142731873738694981123 43002214097810608042471685)
              ·
                refine ⟨8062915143339489007963441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43002214097810608042471685 8062915143339489007963441)
                ·
                  refine ⟨6047186357504616755972581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8062915143339489007963441 6047186357504616755972581)
                  ·
                    refine ⟨1133847442032115641744859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6047186357504616755972581 1133847442032115641744859)
                    ·
                      rfl

theorem cell23_6624480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 2, 4].length) (baseStart_6624480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624480 prefixEnd_6624480 := by exact prefixLift 6624480
  have htrace : WordTrace (prefixWord ++ tailWord_6624480) baseStart_6624480 baseEnd_6624480 := by
    simpa [prefixWord, tailWord_6624480, baseEnd_6624480] using wordTrace_append hprefix tailTrace_6624480
  have hstable : (prefixWord ++ tailWord_6624480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624480).length < 2 ^ (prefixWord ++ tailWord_6624480).sum := by decide
  have hdescent : baseEnd_6624480 < baseStart_6624480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624481 : List Nat := [1, 2, 3, 1, 3, 4, 2, 2, 1, 1, 3]
def baseStart_6624481 : Nat := 118140960795 + 6624481 * 2 ^ 59
def prefixEnd_6624481 : Nat := 4983230072969 + 3 ^ 40 * 6624481 * 2
def baseEnd_6624481 : Nat := 3401542839577001421322073

theorem tailTrace_6624481 : CollatzResearch.WordTrace tailWord_6624481 prefixEnd_6624481 3401542839577001421322073 := by
  unfold tailWord_6624481
  simp only [CollatzResearch.WordTrace]
  refine ⟨241614671513644183126841297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161076447675762788751227531 241614671513644183126841297)
  ·
    refine ⟨181211003635233137345130973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241614671513644183126841297 181211003635233137345130973)
    ·
      refine ⟨67954126363212426504424115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181211003635233137345130973 67954126363212426504424115)
      ·
        refine ⟨101931189544818639756636173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67954126363212426504424115 101931189544818639756636173)
        ·
          refine ⟨38224196079306989908738565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101931189544818639756636173 38224196079306989908738565)
          ·
            refine ⟨7167036764870060607888481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38224196079306989908738565 7167036764870060607888481)
            ·
              refine ⟨5375277573652545455916361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7167036764870060607888481 5375277573652545455916361)
              ·
                refine ⟨4031458180239409091937271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5375277573652545455916361 4031458180239409091937271)
                ·
                  refine ⟨6047187270359113637905907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4031458180239409091937271 6047187270359113637905907)
                  ·
                    refine ⟨9070780905538670456858861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6047187270359113637905907 9070780905538670456858861)
                    ·
                      refine ⟨3401542839577001421322073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9070780905538670456858861 3401542839577001421322073)
                      ·
                        rfl

theorem cell23_6624481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 1, 1, 3].length) (baseStart_6624481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624481 prefixEnd_6624481 := by exact prefixLift 6624481
  have htrace : WordTrace (prefixWord ++ tailWord_6624481) baseStart_6624481 baseEnd_6624481 := by
    simpa [prefixWord, tailWord_6624481, baseEnd_6624481] using wordTrace_append hprefix tailTrace_6624481
  have hstable : (prefixWord ++ tailWord_6624481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624481).length < 2 ^ (prefixWord ++ tailWord_6624481).sum := by decide
  have hdescent : baseEnd_6624481 < baseStart_6624481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624490 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_6624490 : Nat := 118140960795 + 6624490 * 2 ^ 59
def prefixEnd_6624490 : Nat := 4983230072969 + 3 ^ 40 * 6624490 * 2
def baseEnd_6624490 : Nat := 3401547460902891886109531

theorem tailTrace_6624490 : CollatzResearch.WordTrace tailWord_6624490 prefixEnd_6624490 3401547460902891886109531 := by
  unfold tailWord_6624490
  simp only [CollatzResearch.WordTrace]
  refine ⟨60403749942652894415979731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161076666513741051775945949 60403749942652894415979731)
  ·
    refine ⟨90605624913979341623969597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60403749942652894415979731 90605624913979341623969597)
    ·
      refine ⟨33977109342742253108988599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90605624913979341623969597 33977109342742253108988599)
      ·
        refine ⟨50965664014113379663482899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33977109342742253108988599 50965664014113379663482899)
        ·
          refine ⟨76448496021170069495224349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50965664014113379663482899 76448496021170069495224349)
          ·
            refine ⟨28668186007938776060709131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76448496021170069495224349 28668186007938776060709131)
            ·
              refine ⟨43002279011908164091063697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28668186007938776060709131 43002279011908164091063697)
              ·
                refine ⟨32251709258931123068297773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43002279011908164091063697 32251709258931123068297773)
                ·
                  refine ⟨12094390972099171150611665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32251709258931123068297773 12094390972099171150611665)
                  ·
                    refine ⟨9070793229074378362958749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12094390972099171150611665 9070793229074378362958749)
                    ·
                      refine ⟨3401547460902891886109531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9070793229074378362958749 3401547460902891886109531)
                      ·
                        rfl

theorem cell23_6624490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_6624490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624490 prefixEnd_6624490 := by exact prefixLift 6624490
  have htrace : WordTrace (prefixWord ++ tailWord_6624490) baseStart_6624490 baseEnd_6624490 := by
    simpa [prefixWord, tailWord_6624490, baseEnd_6624490] using wordTrace_append hprefix tailTrace_6624490
  have hstable : (prefixWord ++ tailWord_6624490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624490).length < 2 ^ (prefixWord ++ tailWord_6624490).sum := by decide
  have hdescent : baseEnd_6624490 < baseStart_6624490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624503 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 3]
def baseStart_6624503 : Nat := 118140960795 + 6624503 * 2 ^ 59
def prefixEnd_6624503 : Nat := 4983230072969 + 3 ^ 40 * 6624503 * 2
def baseEnd_6624503 : Nat := 3401554136151400335246971

theorem tailTrace_6624503 : CollatzResearch.WordTrace tailWord_6624503 prefixEnd_6624503 3401554136151400335246971 := by
  unfold tailWord_6624503
  simp only [CollatzResearch.WordTrace]
  refine ⟨241615473919564480884142163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161076982613042987256094775 241615473919564480884142163)
  ·
    refine ⟨362423210879346721326213245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241615473919564480884142163 362423210879346721326213245)
    ·
      refine ⟨135908704079755020497329967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362423210879346721326213245 135908704079755020497329967)
      ·
        refine ⟨203863056119632530745994951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135908704079755020497329967 203863056119632530745994951)
        ·
          refine ⟨305794584179448796118992427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203863056119632530745994951 305794584179448796118992427)
          ·
            refine ⟨458691876269173194178488641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305794584179448796118992427 458691876269173194178488641)
            ·
              refine ⟨344018907201879895633866481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458691876269173194178488641 344018907201879895633866481)
              ·
                refine ⟨258014180401409921725399861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344018907201879895633866481 258014180401409921725399861)
                ·
                  refine ⟨24188829412632180161756237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 258014180401409921725399861 24188829412632180161756237)
                  ·
                    refine ⟨9070811029737067560658589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24188829412632180161756237 9070811029737067560658589)
                    ·
                      refine ⟨3401554136151400335246971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9070811029737067560658589 3401554136151400335246971)
                      ·
                        rfl

theorem cell23_6624503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_6624503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624503 prefixEnd_6624503 := by exact prefixLift 6624503
  have htrace : WordTrace (prefixWord ++ tailWord_6624503) baseStart_6624503 baseEnd_6624503 := by
    simpa [prefixWord, tailWord_6624503, baseEnd_6624503] using wordTrace_append hprefix tailTrace_6624503
  have hstable : (prefixWord ++ tailWord_6624503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624503).length < 2 ^ (prefixWord ++ tailWord_6624503).sum := by decide
  have hdescent : baseEnd_6624503 < baseStart_6624503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624524 : List Nat := [2, 2, 1, 2, 2, 5, 2, 1, 1, 2, 3]
def baseStart_6624524 : Nat := 118140960795 + 6624524 * 2 ^ 59
def prefixEnd_6624524 : Nat := 4983230072969 + 3 ^ 40 * 6624524 * 2
def baseEnd_6624524 : Nat := 3401564919245144753084375

theorem tailTrace_6624524 : CollatzResearch.WordTrace tailWord_6624524 prefixEnd_6624524 3401564919245144753084375 := by
  unfold tailWord_6624524
  simp only [CollatzResearch.WordTrace]
  refine ⟨120808119926244200735328313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161077493234992267647104417 120808119926244200735328313)
  ·
    refine ⟨90606089944683150551496235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120808119926244200735328313 90606089944683150551496235)
    ·
      refine ⟨135909134917024725827244353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90606089944683150551496235 135909134917024725827244353)
      ·
        refine ⟨101931851187768544370433265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135909134917024725827244353 101931851187768544370433265)
        ·
          refine ⟨76448888390826408277824949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101931851187768544370433265 76448888390826408277824949)
          ·
            refine ⟨7167083286639975776046089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76448888390826408277824949 7167083286639975776046089)
            ·
              refine ⟨5375312464979981832034567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7167083286639975776046089 5375312464979981832034567)
              ·
                refine ⟨8062968697469972748051851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5375312464979981832034567 8062968697469972748051851)
                ·
                  refine ⟨12094453046204959122077777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8062968697469972748051851 12094453046204959122077777)
                  ·
                    refine ⟨9070839784653719341558333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12094453046204959122077777 9070839784653719341558333)
                    ·
                      refine ⟨3401564919245144753084375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9070839784653719341558333 3401564919245144753084375)
                      ·
                        rfl

theorem cell23_6624524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_6624524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624524 prefixEnd_6624524 := by exact prefixLift 6624524
  have htrace : WordTrace (prefixWord ++ tailWord_6624524) baseStart_6624524 baseEnd_6624524 := by
    simpa [prefixWord, tailWord_6624524, baseEnd_6624524] using wordTrace_append hprefix tailTrace_6624524
  have hstable : (prefixWord ++ tailWord_6624524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624524).length < 2 ^ (prefixWord ++ tailWord_6624524).sum := by decide
  have hdescent : baseEnd_6624524 < baseStart_6624524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624554 : List Nat := [3, 1, 4, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_6624554 : Nat := 118140960795 + 6624554 * 2 ^ 59
def prefixEnd_6624554 : Nat := 4983230072969 + 3 ^ 40 * 6624554 * 2
def baseEnd_6624554 : Nat := 3401580323664779635709237

theorem tailTrace_6624554 : CollatzResearch.WordTrace tailWord_6624554 prefixEnd_6624554 3401580323664779635709237 := by
  unfold tailWord_6624554
  simp only [CollatzResearch.WordTrace]
  refine ⟨60404333510594929148562179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161078222694919811062832477 60404333510594929148562179)
  ·
    refine ⟨90606500265892393722843269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60404333510594929148562179 90606500265892393722843269)
    ·
      refine ⟨16988718799854823823033113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90606500265892393722843269 16988718799854823823033113)
      ·
        refine ⟨12741539099891117867274835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16988718799854823823033113 12741539099891117867274835)
        ·
          refine ⟨19112308649836676800912253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12741539099891117867274835 19112308649836676800912253)
          ·
            refine ⟨7167115743688753800342095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19112308649836676800912253 7167115743688753800342095)
            ·
              refine ⟨10750673615533130700513143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7167115743688753800342095 10750673615533130700513143)
              ·
                refine ⟨16126010423299696050769715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10750673615533130700513143 16126010423299696050769715)
                ·
                  refine ⟨24189015634949544076154573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16126010423299696050769715 24189015634949544076154573)
                  ·
                    refine ⟨9070880863106079028557965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24189015634949544076154573 9070880863106079028557965)
                    ·
                      refine ⟨3401580323664779635709237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9070880863106079028557965 3401580323664779635709237)
                      ·
                        rfl

theorem cell23_6624554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_6624554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624554 prefixEnd_6624554 := by exact prefixLift 6624554
  have htrace : WordTrace (prefixWord ++ tailWord_6624554) baseStart_6624554 baseEnd_6624554 := by
    simpa [prefixWord, tailWord_6624554, baseEnd_6624554] using wordTrace_append hprefix tailTrace_6624554
  have hstable : (prefixWord ++ tailWord_6624554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624554).length < 2 ^ (prefixWord ++ tailWord_6624554).sum := by decide
  have hdescent : baseEnd_6624554 < baseStart_6624554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624593 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 1, 2, 7]
def baseStart_6624593 : Nat := 118140960795 + 6624593 * 2 ^ 59
def prefixEnd_6624593 : Nat := 4983230072969 + 3 ^ 40 * 6624593 * 2
def baseEnd_6624593 : Nat := 3401600349410304983121557

theorem tailTrace_6624593 : CollatzResearch.WordTrace tailWord_6624593 prefixEnd_6624593 3401600349410304983121557 := by
  unfold tailWord_6624593
  simp only [CollatzResearch.WordTrace]
  refine ⟨241618756489238426254918433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161079170992825617503278955 241618756489238426254918433)
  ·
    refine ⟨181214067366928819691188825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241618756489238426254918433 181214067366928819691188825)
    ·
      refine ⟨135910550525196614768391619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181214067366928819691188825 135910550525196614768391619)
      ·
        refine ⟨203865825787794922152587429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135910550525196614768391619 203865825787794922152587429)
        ·
          refine ⟨38224842335211547903610143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203865825787794922152587429 38224842335211547903610143)
          ·
            refine ⟨57337263502817321855415215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38224842335211547903610143 57337263502817321855415215)
            ·
              refine ⟨86005895254225982783122823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57337263502817321855415215 86005895254225982783122823)
              ·
                refine ⟨129008842881338974174684235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86005895254225982783122823 129008842881338974174684235)
                ·
                  refine ⟨193513264322008461262026353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129008842881338974174684235 193513264322008461262026353)
                  ·
                    refine ⟨145134948241506345946519765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 193513264322008461262026353 145134948241506345946519765)
                    ·
                      refine ⟨3401600349410304983121557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145134948241506345946519765 3401600349410304983121557)
                      ·
                        rfl

theorem cell23_6624593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_6624593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624593 prefixEnd_6624593 := by exact prefixLift 6624593
  have htrace : WordTrace (prefixWord ++ tailWord_6624593) baseStart_6624593 baseEnd_6624593 := by
    simpa [prefixWord, tailWord_6624593, baseEnd_6624593] using wordTrace_append hprefix tailTrace_6624593
  have hstable : (prefixWord ++ tailWord_6624593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624593).length < 2 ^ (prefixWord ++ tailWord_6624593).sum := by decide
  have hdescent : baseEnd_6624593 < baseStart_6624593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624594 : List Nat := [3, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2]
def baseStart_6624594 : Nat := 118140960795 + 6624594 * 2 ^ 59
def prefixEnd_6624594 : Nat := 4983230072969 + 3 ^ 40 * 6624594 * 2
def baseEnd_6624594 : Nat := 3401600862890959479209053

theorem tailTrace_6624594 : CollatzResearch.WordTrace tailWord_6624594 prefixEnd_6624594 3401600862890959479209053 := by
  unfold tailWord_6624594
  simp only [CollatzResearch.WordTrace]
  refine ⟨60404698240558700856426209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161079195308156535617136557 60404698240558700856426209)
  ·
    refine ⟨45303523680419025642319657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60404698240558700856426209 45303523680419025642319657)
    ·
      refine ⟨33977642760314269231739743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45303523680419025642319657 33977642760314269231739743)
      ·
        refine ⟨50966464140471403847609615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33977642760314269231739743 50966464140471403847609615)
        ·
          refine ⟨76449696210707105771414423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50966464140471403847609615 76449696210707105771414423)
          ·
            refine ⟨114674544316060658657121635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76449696210707105771414423 114674544316060658657121635)
            ·
              refine ⟨172011816474090987985682453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114674544316060658657121635 172011816474090987985682453)
              ·
                refine ⟨8063053897223015061828865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 172011816474090987985682453 8063053897223015061828865)
                ·
                  refine ⟨6047290422917261296371649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8063053897223015061828865 6047290422917261296371649)
                  ·
                    refine ⟨4535467817187945972278737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6047290422917261296371649 4535467817187945972278737)
                    ·
                      refine ⟨3401600862890959479209053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4535467817187945972278737 3401600862890959479209053)
                      ·
                        rfl

theorem cell23_6624594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_6624594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624594 prefixEnd_6624594 := by exact prefixLift 6624594
  have htrace : WordTrace (prefixWord ++ tailWord_6624594) baseStart_6624594 baseEnd_6624594 := by
    simpa [prefixWord, tailWord_6624594, baseEnd_6624594] using wordTrace_append hprefix tailTrace_6624594
  have hstable : (prefixWord ++ tailWord_6624594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624594).length < 2 ^ (prefixWord ++ tailWord_6624594).sum := by decide
  have hdescent : baseEnd_6624594 < baseStart_6624594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624611 : List Nat := [1, 1, 1, 5, 2, 2, 4, 1, 2, 2, 2]
def baseStart_6624611 : Nat := 118140960795 + 6624611 * 2 ^ 59
def prefixEnd_6624611 : Nat := 4983230072969 + 3 ^ 40 * 6624611 * 2
def baseEnd_6624611 : Nat := 3401609592062085912696475

theorem tailTrace_6624611 : CollatzResearch.WordTrace tailWord_6624611 prefixEnd_6624611 3401609592062085912696475 := by
  unfold tailWord_6624611
  simp only [CollatzResearch.WordTrace]
  refine ⟨241619413003173215329073687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161079608668782143552715791 241619413003173215329073687)
  ·
    refine ⟨362429119504759822993610531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241619413003173215329073687 362429119504759822993610531)
    ·
      refine ⟨543643679257139734490415797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362429119504759822993610531 543643679257139734490415797)
      ·
        refine ⟨50966594930356850108476481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 543643679257139734490415797 50966594930356850108476481)
        ·
          refine ⟨38224946197767637581357361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50966594930356850108476481 38224946197767637581357361)
          ·
            refine ⟨28668709648325728186018021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38224946197767637581357361 28668709648325728186018021)
            ·
              refine ⟨5375383059061074034878379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28668709648325728186018021 5375383059061074034878379)
              ·
                refine ⟨8063074588591611052317569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5375383059061074034878379 8063074588591611052317569)
                ·
                  refine ⟨6047305941443708289238177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8063074588591611052317569 6047305941443708289238177)
                  ·
                    refine ⟨4535479456082781216928633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6047305941443708289238177 4535479456082781216928633)
                    ·
                      refine ⟨3401609592062085912696475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4535479456082781216928633 3401609592062085912696475)
                      ·
                        rfl

theorem cell23_6624611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_6624611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624611 prefixEnd_6624611 := by exact prefixLift 6624611
  have htrace : WordTrace (prefixWord ++ tailWord_6624611) baseStart_6624611 baseEnd_6624611 := by
    simpa [prefixWord, tailWord_6624611, baseEnd_6624611] using wordTrace_append hprefix tailTrace_6624611
  have hstable : (prefixWord ++ tailWord_6624611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624611).length < 2 ^ (prefixWord ++ tailWord_6624611).sum := by decide
  have hdescent : baseEnd_6624611 < baseStart_6624611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624623 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 7]
def baseStart_6624623 : Nat := 118140960795 + 6624623 * 2 ^ 59
def prefixEnd_6624623 : Nat := 4983230072969 + 3 ^ 40 * 6624623 * 2
def baseEnd_6624623 : Nat := 3401615753829939865746419

theorem tailTrace_6624623 : CollatzResearch.WordTrace tailWord_6624623 prefixEnd_6624623 3401615753829939865746419 := by
  unfold tailWord_6624623
  simp only [CollatzResearch.WordTrace]
  refine ⟨241619850679129741378510523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161079900452753160919007015 241619850679129741378510523)
  ·
    refine ⟨362429776018694612067765785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241619850679129741378510523 362429776018694612067765785)
    ·
      refine ⟨271822332014020959050824339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362429776018694612067765785 271822332014020959050824339)
      ·
        refine ⟨407733498021031438576236509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271822332014020959050824339 407733498021031438576236509)
        ·
          refine ⟨152900061757886789466088691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407733498021031438576236509 152900061757886789466088691)
          ·
            refine ⟨229350092636830184199133037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152900061757886789466088691 229350092636830184199133037)
            ·
              refine ⟨86006284738811319074674889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229350092636830184199133037 86006284738811319074674889)
              ·
                refine ⟨64504713554108489306006167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86006284738811319074674889 64504713554108489306006167)
                ·
                  refine ⟨96757070331162733959009251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64504713554108489306006167 96757070331162733959009251)
                  ·
                    refine ⟨145135605496744100938513877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96757070331162733959009251 145135605496744100938513877)
                    ·
                      refine ⟨3401615753829939865746419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145135605496744100938513877 3401615753829939865746419)
                      ·
                        rfl

theorem cell23_6624623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_6624623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624623 prefixEnd_6624623 := by exact prefixLift 6624623
  have htrace : WordTrace (prefixWord ++ tailWord_6624623) baseStart_6624623 baseEnd_6624623 := by
    simpa [prefixWord, tailWord_6624623, baseEnd_6624623] using wordTrace_append hprefix tailTrace_6624623
  have hstable : (prefixWord ++ tailWord_6624623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624623).length < 2 ^ (prefixWord ++ tailWord_6624623).sum := by decide
  have hdescent : baseEnd_6624623 < baseStart_6624623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624737 : List Nat := [1, 2, 3, 1, 2, 3, 1, 4, 1, 5]
def baseStart_6624737 : Nat := 118140960795 + 6624737 * 2 ^ 59
def prefixEnd_6624737 : Nat := 4983230072969 + 3 ^ 40 * 6624737 * 2
def baseEnd_6624737 : Nat := 1133891430208184139906965

theorem tailTrace_6624737 : CollatzResearch.WordTrace tailWord_6624737 prefixEnd_6624737 1133891430208184139906965 := by
  unfold tailWord_6624737
  simp only [CollatzResearch.WordTrace]
  refine ⟨241624008600716738848160465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161082672400477825898773643 241624008600716738848160465)
  ·
    refine ⟨181218006450537554136120349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241624008600716738848160465 181218006450537554136120349)
    ·
      refine ⟨67956752418951582801045131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181218006450537554136120349 67956752418951582801045131)
      ·
        refine ⟨101935128628427374201567697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67956752418951582801045131 101935128628427374201567697)
        ·
          refine ⟨76451346471320530651175773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101935128628427374201567697 76451346471320530651175773)
          ·
            refine ⟨28669254926745198994190915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76451346471320530651175773 28669254926745198994190915)
            ·
              refine ⟨43003882390117798491286373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28669254926745198994190915 43003882390117798491286373)
              ·
                refine ⟨8063227948147087217116195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43003882390117798491286373 8063227948147087217116195)
                ·
                  refine ⟨12094841922220630825674293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8063227948147087217116195 12094841922220630825674293)
                  ·
                    refine ⟨1133891430208184139906965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12094841922220630825674293 1133891430208184139906965)
                    ·
                      rfl

theorem cell23_6624737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_6624737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624737 prefixEnd_6624737 := by exact prefixLift 6624737
  have htrace : WordTrace (prefixWord ++ tailWord_6624737) baseStart_6624737 baseEnd_6624737 := by
    simpa [prefixWord, tailWord_6624737, baseEnd_6624737] using wordTrace_append hprefix tailTrace_6624737
  have hstable : (prefixWord ++ tailWord_6624737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624737).length < 2 ^ (prefixWord ++ tailWord_6624737).sum := by decide
  have hdescent : baseEnd_6624737 < baseStart_6624737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624740 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_6624740 : Nat := 118140960795 + 6624740 * 2 ^ 59
def prefixEnd_6624740 : Nat := 4983230072969 + 3 ^ 40 * 6624740 * 2
def baseEnd_6624740 : Nat := 3401675831066515907983381

theorem tailTrace_6624740 : CollatzResearch.WordTrace tailWord_6624740 prefixEnd_6624740 3401675831066515907983381 := by
  unfold tailWord_6624740
  simp only [CollatzResearch.WordTrace]
  refine ⟨120812059009852935180259837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161082745346470580240346449 120812059009852935180259837)
  ·
    refine ⟨45304522128694850692597439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120812059009852935180259837 45304522128694850692597439)
    ·
      refine ⟨67956783193042276038896159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45304522128694850692597439 67956783193042276038896159)
      ·
        refine ⟨101935174789563414058344239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67956783193042276038896159 101935174789563414058344239)
        ·
          refine ⟨152902762184345121087516359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101935174789563414058344239 152902762184345121087516359)
          ·
            refine ⟨229354143276517681631274539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152902762184345121087516359 229354143276517681631274539)
            ·
              refine ⟨344031214914776522446911809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229354143276517681631274539 344031214914776522446911809)
              ·
                refine ⟨258023411186082391835183857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344031214914776522446911809 258023411186082391835183857)
                ·
                  refine ⟨193517558389561793876387893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258023411186082391835183857 193517558389561793876387893)
                  ·
                    refine ⟨18142271099021418175911365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 193517558389561793876387893 18142271099021418175911365)
                    ·
                      refine ⟨3401675831066515907983381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18142271099021418175911365 3401675831066515907983381)
                      ·
                        rfl

theorem cell23_6624740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_6624740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624740 prefixEnd_6624740 := by exact prefixLift 6624740
  have htrace : WordTrace (prefixWord ++ tailWord_6624740) baseStart_6624740 baseEnd_6624740 := by
    simpa [prefixWord, tailWord_6624740, baseEnd_6624740] using wordTrace_append hprefix tailTrace_6624740
  have hstable : (prefixWord ++ tailWord_6624740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624740).length < 2 ^ (prefixWord ++ tailWord_6624740).sum := by decide
  have hdescent : baseEnd_6624740 < baseStart_6624740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624744 : List Nat := [2, 1, 4, 1, 1, 2, 2, 3, 2, 3, 2]
def baseStart_6624744 : Nat := 118140960795 + 6624744 * 2 ^ 59
def prefixEnd_6624744 : Nat := 4983230072969 + 3 ^ 40 * 6624744 * 2
def baseEnd_6624744 : Nat := 3401677884989133892333363

theorem tailTrace_6624744 : CollatzResearch.WordTrace tailWord_6624744 prefixEnd_6624744 3401677884989133892333363 := by
  unfold tailWord_6624744
  simp only [CollatzResearch.WordTrace]
  refine ⟨120812131955845689521832643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161082842607794252695776857 120812131955845689521832643)
  ·
    refine ⟨181218197933768534282748965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120812131955845689521832643 181218197933768534282748965)
    ·
      refine ⟨33978412112581600178015431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181218197933768534282748965 33978412112581600178015431)
      ·
        refine ⟨50967618168872400267023147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33978412112581600178015431 50967618168872400267023147)
        ·
          refine ⟨76451427253308600400534721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50967618168872400267023147 76451427253308600400534721)
          ·
            refine ⟨57338570439981450300401041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76451427253308600400534721 57338570439981450300401041)
            ·
              refine ⟨43003927829986087725300781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57338570439981450300401041 43003927829986087725300781)
              ·
                refine ⟨16126472936244782896987793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43003927829986087725300781 16126472936244782896987793)
                ·
                  refine ⟨12094854702183587172740845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16126472936244782896987793 12094854702183587172740845)
                  ·
                    refine ⟨4535570513318845189777817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12094854702183587172740845 4535570513318845189777817)
                    ·
                      refine ⟨3401677884989133892333363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4535570513318845189777817 3401677884989133892333363)
                      ·
                        rfl

theorem cell23_6624744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_6624744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624744 prefixEnd_6624744 := by exact prefixLift 6624744
  have htrace : WordTrace (prefixWord ++ tailWord_6624744) baseStart_6624744 baseEnd_6624744 := by
    simpa [prefixWord, tailWord_6624744, baseEnd_6624744] using wordTrace_append hprefix tailTrace_6624744
  have hstable : (prefixWord ++ tailWord_6624744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624744).length < 2 ^ (prefixWord ++ tailWord_6624744).sum := by decide
  have hdescent : baseEnd_6624744 < baseStart_6624744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624751 : List Nat := [1, 1, 2, 1, 4, 1, 5, 3, 1, 1, 3]
def baseStart_6624751 : Nat := 118140960795 + 6624751 * 2 ^ 59
def prefixEnd_6624751 : Nat := 4983230072969 + 3 ^ 40 * 6624751 * 2
def baseEnd_6624751 : Nat := 3401681479353715364945831

theorem tailTrace_6624751 : CollatzResearch.WordTrace tailWord_6624751 prefixEnd_6624751 3401681479353715364945831 := by
  unfold tailWord_6624751
  simp only [CollatzResearch.WordTrace]
  refine ⟨241624519222666019239170107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161083012815110679492780071 241624519222666019239170107)
  ·
    refine ⟨362436778833999028858755161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241624519222666019239170107 362436778833999028858755161)
    ·
      refine ⟨271827584125499271644066371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362436778833999028858755161 271827584125499271644066371)
      ·
        refine ⟨407741376188248907466099557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271827584125499271644066371 407741376188248907466099557)
        ·
          refine ⟨76451508035296670149893667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 407741376188248907466099557 76451508035296670149893667)
          ·
            refine ⟨114677262052945005224840501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76451508035296670149893667 114677262052945005224840501)
            ·
              refine ⟨10750993317463594239828797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114677262052945005224840501 10750993317463594239828797)
              ·
                refine ⟨4031622494048847839935799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10750993317463594239828797 4031622494048847839935799)
                ·
                  refine ⟨6047433741073271759903699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4031622494048847839935799 6047433741073271759903699)
                  ·
                    refine ⟨9071150611609907639855549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6047433741073271759903699 9071150611609907639855549)
                    ·
                      refine ⟨3401681479353715364945831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9071150611609907639855549 3401681479353715364945831)
                      ·
                        rfl

theorem cell23_6624751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 1, 1, 3].length) (baseStart_6624751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624751 prefixEnd_6624751 := by exact prefixLift 6624751
  have htrace : WordTrace (prefixWord ++ tailWord_6624751) baseStart_6624751 baseEnd_6624751 := by
    simpa [prefixWord, tailWord_6624751, baseEnd_6624751] using wordTrace_append hprefix tailTrace_6624751
  have hstable : (prefixWord ++ tailWord_6624751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624751).length < 2 ^ (prefixWord ++ tailWord_6624751).sum := by decide
  have hdescent : baseEnd_6624751 < baseStart_6624751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624754 : List Nat := [3, 2, 1, 4, 1, 1, 2, 3, 1, 5]
def baseStart_6624754 : Nat := 118140960795 + 6624754 * 2 ^ 59
def prefixEnd_6624754 : Nat := 4983230072969 + 3 ^ 40 * 6624754 * 2
def baseEnd_6624754 : Nat := 1133894339931892951069439

theorem tailTrace_6624754 : CollatzResearch.WordTrace tailWord_6624754 prefixEnd_6624754 1133894339931892951069439 := by
  unfold tailWord_6624754
  simp only [CollatzResearch.WordTrace]
  refine ⟨60406157160413787687882329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161083085761103433834352877 60406157160413787687882329)
  ·
    refine ⟨45304617870310340765911747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60406157160413787687882329 45304617870310340765911747)
    ·
      refine ⟨67956926805465511148867621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45304617870310340765911747 67956926805465511148867621)
      ·
        refine ⟨12741923776024783340412679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67956926805465511148867621 12741923776024783340412679)
        ·
          refine ⟨19112885664037175010619019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12741923776024783340412679 19112885664037175010619019)
          ·
            refine ⟨28669328496055762515928529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19112885664037175010619019 28669328496055762515928529)
            ·
              refine ⟨21501996372041821886946397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28669328496055762515928529 21501996372041821886946397)
              ·
                refine ⟨8063248639515683207604899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21501996372041821886946397 8063248639515683207604899)
                ·
                  refine ⟨12094872959273524811407349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8063248639515683207604899 12094872959273524811407349)
                  ·
                    refine ⟨1133894339931892951069439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12094872959273524811407349 1133894339931892951069439)
                    ·
                      rfl

theorem cell23_6624754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_6624754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624754 prefixEnd_6624754 := by exact prefixLift 6624754
  have htrace : WordTrace (prefixWord ++ tailWord_6624754) baseStart_6624754 baseEnd_6624754 := by
    simpa [prefixWord, tailWord_6624754, baseEnd_6624754] using wordTrace_append hprefix tailTrace_6624754
  have hstable : (prefixWord ++ tailWord_6624754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624754).length < 2 ^ (prefixWord ++ tailWord_6624754).sum := by decide
  have hdescent : baseEnd_6624754 < baseStart_6624754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624777 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 3, 2, 3]
def baseStart_6624777 : Nat := 118140960795 + 6624777 * 2 ^ 59
def prefixEnd_6624777 : Nat := 4983230072969 + 3 ^ 40 * 6624777 * 2
def baseEnd_6624777 : Nat := 3401694829850732263220711

theorem tailTrace_6624777 : CollatzResearch.WordTrace tailWord_6624777 prefixEnd_6624777 3401694829850732263220711 := by
  unfold tailWord_6624777
  simp only [CollatzResearch.WordTrace]
  refine ⟨241625467520571825679616585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161083645013714550453077723 241625467520571825679616585)
  ·
    refine ⟨181219100640428869259712439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241625467520571825679616585 181219100640428869259712439)
    ·
      refine ⟨271828650960643303889568659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181219100640428869259712439 271828650960643303889568659)
      ·
        refine ⟨407742976440964955834352989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271828650960643303889568659 407742976440964955834352989)
        ·
          refine ⟨152903616165361858437882371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407742976440964955834352989 152903616165361858437882371)
          ·
            refine ⟨229355424248042787656823557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152903616165361858437882371 229355424248042787656823557)
            ·
              refine ⟨43004142046508022685654417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229355424248042787656823557 43004142046508022685654417)
              ·
                refine ⟨32253106534881017014240813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43004142046508022685654417 32253106534881017014240813)
                ·
                  refine ⟨12094914950580381380340305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32253106534881017014240813 12094914950580381380340305)
                  ·
                    refine ⟨9071186212935286035255229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12094914950580381380340305 9071186212935286035255229)
                    ·
                      refine ⟨3401694829850732263220711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9071186212935286035255229 3401694829850732263220711)
                      ·
                        rfl

theorem cell23_6624777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 2, 3].length) (baseStart_6624777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624777 prefixEnd_6624777 := by exact prefixLift 6624777
  have htrace : WordTrace (prefixWord ++ tailWord_6624777) baseStart_6624777 baseEnd_6624777 := by
    simpa [prefixWord, tailWord_6624777, baseEnd_6624777] using wordTrace_append hprefix tailTrace_6624777
  have hstable : (prefixWord ++ tailWord_6624777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624777).length < 2 ^ (prefixWord ++ tailWord_6624777).sum := by decide
  have hdescent : baseEnd_6624777 < baseStart_6624777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624788 : List Nat := [2, 4, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_6624788 : Nat := 118140960795 + 6624788 * 2 ^ 59
def prefixEnd_6624788 : Nat := 4983230072969 + 3 ^ 40 * 6624788 * 2
def baseEnd_6624788 : Nat := 1133900159379310573394387

theorem tailTrace_6624788 : CollatzResearch.WordTrace tailWord_6624788 prefixEnd_6624788 1133900159379310573394387 := by
  unfold tailWord_6624788
  simp only [CollatzResearch.WordTrace]
  refine ⟨120812934361765987279133509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161083912482354649705511345 120812934361765987279133509)
  ·
    refine ⟨22652425192831122614837533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120812934361765987279133509 22652425192831122614837533)
    ·
      refine ⟨8494659447311670980564075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22652425192831122614837533 8494659447311670980564075)
      ·
        refine ⟨12741989170967506470846113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8494659447311670980564075 12741989170967506470846113)
        ·
          refine ⟨9556491878225629853134585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12741989170967506470846113 9556491878225629853134585)
          ·
            refine ⟨7167368908669222389850939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9556491878225629853134585 7167368908669222389850939)
            ·
              refine ⟨10751053363003833584776409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7167368908669222389850939 10751053363003833584776409)
              ·
                refine ⟨8063290022252875188582307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10751053363003833584776409 8063290022252875188582307)
                ·
                  refine ⟨12094935033379312782873461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8063290022252875188582307 12094935033379312782873461)
                  ·
                    refine ⟨1133900159379310573394387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12094935033379312782873461 1133900159379310573394387)
                    ·
                      rfl

theorem cell23_6624788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_6624788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624788 prefixEnd_6624788 := by exact prefixLift 6624788
  have htrace : WordTrace (prefixWord ++ tailWord_6624788) baseStart_6624788 baseEnd_6624788 := by
    simpa [prefixWord, tailWord_6624788, baseEnd_6624788] using wordTrace_append hprefix tailTrace_6624788
  have hstable : (prefixWord ++ tailWord_6624788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624788).length < 2 ^ (prefixWord ++ tailWord_6624788).sum := by decide
  have hdescent : baseEnd_6624788 < baseStart_6624788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624808 : List Nat := [2, 1, 5, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_6624808 : Nat := 118140960795 + 6624808 * 2 ^ 59
def prefixEnd_6624808 : Nat := 4983230072969 + 3 ^ 40 * 6624808 * 2
def baseEnd_6624808 : Nat := 3401710747751021641933069

theorem tailTrace_6624808 : CollatzResearch.WordTrace tailWord_6624808 prefixEnd_6624808 3401710747751021641933069 := by
  unfold tailWord_6624808
  simp only [CollatzResearch.WordTrace]
  refine ⟨120813299091729758986997539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161084398788973011982663385 120813299091729758986997539)
  ·
    refine ⟨181219948637594638480496309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120813299091729758986997539 181219948637594638480496309)
    ·
      refine ⟨16989370184774497357546529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181219948637594638480496309 16989370184774497357546529)
      ·
        refine ⟨12742027638580873018159897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16989370184774497357546529 12742027638580873018159897)
        ·
          refine ⟨9556520728935654763619923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12742027638580873018159897 9556520728935654763619923)
          ·
            refine ⟨14334781093403482145429885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9556520728935654763619923 14334781093403482145429885)
            ·
              refine ⟨5375542910026305804536207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14334781093403482145429885 5375542910026305804536207)
              ·
                refine ⟨8063314365039458706804311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5375542910026305804536207 8063314365039458706804311)
                ·
                  refine ⟨12094971547559188060206467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8063314365039458706804311 12094971547559188060206467)
                  ·
                    refine ⟨18142457321338782090309701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12094971547559188060206467 18142457321338782090309701)
                    ·
                      refine ⟨3401710747751021641933069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18142457321338782090309701 3401710747751021641933069)
                      ·
                        rfl

theorem cell23_6624808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_6624808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624808 prefixEnd_6624808 := by exact prefixLift 6624808
  have htrace : WordTrace (prefixWord ++ tailWord_6624808) baseStart_6624808 baseEnd_6624808 := by
    simpa [prefixWord, tailWord_6624808, baseEnd_6624808] using wordTrace_append hprefix tailTrace_6624808
  have hstable : (prefixWord ++ tailWord_6624808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624808).length < 2 ^ (prefixWord ++ tailWord_6624808).sum := by decide
  have hdescent : baseEnd_6624808 < baseStart_6624808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624825 : List Nat := [1, 2, 1, 5, 1, 2, 4, 2, 1, 2, 2]
def baseStart_6624825 : Nat := 118140960795 + 6624825 * 2 ^ 59
def prefixEnd_6624825 : Nat := 4983230072969 + 3 ^ 40 * 6624825 * 2
def baseEnd_6624825 : Nat := 3401719476922148075420491

theorem tailTrace_6624825 : CollatzResearch.WordTrace tailWord_6624825 prefixEnd_6624825 3401719476922148075420491 := by
  unfold tailWord_6624825
  simp only [CollatzResearch.WordTrace]
  refine ⟨241627218224397929877363929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161084812149598619918242619 241627218224397929877363929)
  ·
    refine ⟨181220413668298447408022947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241627218224397929877363929 181220413668298447408022947)
    ·
      refine ⟨271830620502447671112034421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181220413668298447408022947 271830620502447671112034421)
      ·
        refine ⟨25484120672104469166753227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 271830620502447671112034421 25484120672104469166753227)
        ·
          refine ⟨38226181008156703750129841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25484120672104469166753227 38226181008156703750129841)
          ·
            refine ⟨28669635756117527812597381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38226181008156703750129841 28669635756117527812597381)
            ·
              refine ⟨5375556704272036464862009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28669635756117527812597381 5375556704272036464862009)
              ·
                refine ⟨4031667528204027348646507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5375556704272036464862009 4031667528204027348646507)
                ·
                  refine ⟨6047501292306041022969761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4031667528204027348646507 6047501292306041022969761)
                  ·
                    refine ⟨4535625969229530767227321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6047501292306041022969761 4535625969229530767227321)
                    ·
                      refine ⟨3401719476922148075420491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4535625969229530767227321 3401719476922148075420491)
                      ·
                        rfl

theorem cell23_6624825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_6624825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624825 prefixEnd_6624825 := by exact prefixLift 6624825
  have htrace : WordTrace (prefixWord ++ tailWord_6624825) baseStart_6624825 baseEnd_6624825 := by
    simpa [prefixWord, tailWord_6624825, baseEnd_6624825] using wordTrace_append hprefix tailTrace_6624825
  have hstable : (prefixWord ++ tailWord_6624825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624825).length < 2 ^ (prefixWord ++ tailWord_6624825).sum := by decide
  have hdescent : baseEnd_6624825 < baseStart_6624825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624838 : List Nat := [6, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_6624838 : Nat := 118140960795 + 6624838 * 2 ^ 59
def prefixEnd_6624838 : Nat := 4983230072969 + 3 ^ 40 * 6624838 * 2
def baseEnd_6624838 : Nat := 3401726152170656524557931

theorem tailTrace_6624838 : CollatzResearch.WordTrace tailWord_6624838 prefixEnd_6624838 3401726152170656524557931 := by
  unfold tailWord_6624838
  simp only [CollatzResearch.WordTrace]
  refine ⟨7550865386667213534299599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 161085128248900555398391445 7550865386667213534299599)
  ·
    refine ⟨11326298080000820301449399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7550865386667213534299599 11326298080000820301449399)
    ·
      refine ⟨16989447120001230452174099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11326298080000820301449399 16989447120001230452174099)
      ·
        refine ⟨25484170680001845678261149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16989447120001230452174099 25484170680001845678261149)
        ·
          refine ⟨9556564005000692129347931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25484170680001845678261149 9556564005000692129347931)
          ·
            refine ⟨14334846007501038194021897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9556564005000692129347931 14334846007501038194021897)
            ·
              refine ⟨10751134505625778645516423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14334846007501038194021897 10751134505625778645516423)
              ·
                refine ⟨16126701758438667968274635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10751134505625778645516423 16126701758438667968274635)
                ·
                  refine ⟨24190052637658001952411953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16126701758438667968274635 24190052637658001952411953)
                  ·
                    refine ⟨18142539478243501464308965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24190052637658001952411953 18142539478243501464308965)
                    ·
                      refine ⟨3401726152170656524557931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18142539478243501464308965 3401726152170656524557931)
                      ·
                        rfl

theorem cell23_6624838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_6624838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624838 prefixEnd_6624838 := by exact prefixLift 6624838
  have htrace : WordTrace (prefixWord ++ tailWord_6624838) baseStart_6624838 baseEnd_6624838 := by
    simpa [prefixWord, tailWord_6624838, baseEnd_6624838] using wordTrace_append hprefix tailTrace_6624838
  have hstable : (prefixWord ++ tailWord_6624838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624838).length < 2 ^ (prefixWord ++ tailWord_6624838).sum := by decide
  have hdescent : baseEnd_6624838 < baseStart_6624838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624868 : List Nat := [2, 3, 1, 1, 2, 3, 4, 1, 1, 3, 2]
def baseStart_6624868 : Nat := 118140960795 + 6624868 * 2 ^ 59
def prefixEnd_6624868 : Nat := 4983230072969 + 3 ^ 40 * 6624868 * 2
def baseEnd_6624868 : Nat := 3401741556590291407182793

theorem tailTrace_6624868 : CollatzResearch.WordTrace tailWord_6624868 prefixEnd_6624868 3401741556590291407182793 := by
  unfold tailWord_6624868
  simp only [CollatzResearch.WordTrace]
  refine ⟨120814393281621074110589629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161085857708828098814119505 120814393281621074110589629)
  ·
    refine ⟨45305397480607902791471111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120814393281621074110589629 45305397480607902791471111)
    ·
      refine ⟨67958096220911854187206667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45305397480607902791471111 67958096220911854187206667)
      ·
        refine ⟨101937144331367781280810001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67958096220911854187206667 101937144331367781280810001)
        ·
          refine ⟨76452858248525835960607501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101937144331367781280810001 76452858248525835960607501)
          ·
            refine ⟨28669821843197188485227813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76452858248525835960607501 28669821843197188485227813)
            ·
              refine ⟨5375591595599472840980215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28669821843197188485227813 5375591595599472840980215)
              ·
                refine ⟨8063387393399209261470323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5375591595599472840980215 8063387393399209261470323)
                ·
                  refine ⟨12095081090098813892205485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8063387393399209261470323 12095081090098813892205485)
                  ·
                    refine ⟨4535655408787055209577057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12095081090098813892205485 4535655408787055209577057)
                    ·
                      refine ⟨3401741556590291407182793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4535655408787055209577057 3401741556590291407182793)
                      ·
                        rfl

theorem cell23_6624868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_6624868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624868 prefixEnd_6624868 := by exact prefixLift 6624868
  have htrace : WordTrace (prefixWord ++ tailWord_6624868) baseStart_6624868 baseEnd_6624868 := by
    simpa [prefixWord, tailWord_6624868, baseEnd_6624868] using wordTrace_append hprefix tailTrace_6624868
  have hstable : (prefixWord ++ tailWord_6624868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624868).length < 2 ^ (prefixWord ++ tailWord_6624868).sum := by decide
  have hdescent : baseEnd_6624868 < baseStart_6624868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624917 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 6, 5]
def baseStart_6624917 : Nat := 118140960795 + 6624917 * 2 ^ 59
def prefixEnd_6624917 : Nat := 4983230072969 + 3 ^ 40 * 6624917 * 2
def baseEnd_6624917 : Nat := 1133922239047453905156689

theorem tailTrace_6624917 : CollatzResearch.WordTrace tailWord_6624917 prefixEnd_6624917 1133922239047453905156689 := by
  unfold tailWord_6624917
  simp only [CollatzResearch.WordTrace]
  refine ⟨241630573740064629589713005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161087049160043086393142003 241630573740064629589713005)
  ·
    refine ⟨90611465152524236096142377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241630573740064629589713005 90611465152524236096142377)
    ·
      refine ⟨67958598864393177072106783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90611465152524236096142377 67958598864393177072106783)
      ·
        refine ⟨101937898296589765608160175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67958598864393177072106783 101937898296589765608160175)
        ·
          refine ⟨152906847444884648412240263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101937898296589765608160175 152906847444884648412240263)
          ·
            refine ⟨229360271167326972618360395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152906847444884648412240263 229360271167326972618360395)
            ·
              refine ⟨344040406750990458927540593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229360271167326972618360395 344040406750990458927540593)
              ·
                refine ⟨258030305063242844195655445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344040406750990458927540593 258030305063242844195655445)
                ·
                  refine ⟨12095170549839508321671349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 258030305063242844195655445 12095170549839508321671349)
                  ·
                    refine ⟨1133922239047453905156689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12095170549839508321671349 1133922239047453905156689)
                    ·
                      rfl

theorem cell23_6624917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_6624917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624917 prefixEnd_6624917 := by exact prefixLift 6624917
  have htrace : WordTrace (prefixWord ++ tailWord_6624917) baseStart_6624917 baseEnd_6624917 := by
    simpa [prefixWord, tailWord_6624917, baseEnd_6624917] using wordTrace_append hprefix tailTrace_6624917
  have hstable : (prefixWord ++ tailWord_6624917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624917).length < 2 ^ (prefixWord ++ tailWord_6624917).sum := by decide
  have hdescent : baseEnd_6624917 < baseStart_6624917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624941 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_6624941 : Nat := 118140960795 + 6624941 * 2 ^ 59
def prefixEnd_6624941 : Nat := 4983230072969 + 3 ^ 40 * 6624941 * 2
def baseEnd_6624941 : Nat := 3401779040678069621569957

theorem tailTrace_6624941 : CollatzResearch.WordTrace tailWord_6624941 prefixEnd_6624941 3401779040678069621569957 := by
  unfold tailWord_6624941
  simp only [CollatzResearch.WordTrace]
  refine ⟨241631449091977681688586677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161087632727985121125724451 241631449091977681688586677)
  ·
    refine ⟨22652948352372907658305001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 241631449091977681688586677 22652948352372907658305001)
    ·
      refine ⟨16989711264279680743728751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22652948352372907658305001 16989711264279680743728751)
      ·
        refine ⟨25484566896419521115593127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16989711264279680743728751 25484566896419521115593127)
        ·
          refine ⟨38226850344629281673389691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25484566896419521115593127 38226850344629281673389691)
          ·
            refine ⟨57340275516943922510084537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38226850344629281673389691 57340275516943922510084537)
            ·
              refine ⟨43005206637707941882563403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57340275516943922510084537 43005206637707941882563403)
              ·
                refine ⟨64507809956561912823845105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43005206637707941882563403 64507809956561912823845105)
                ·
                  refine ⟨48380857467421434617883829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64507809956561912823845105 48380857467421434617883829)
                  ·
                    refine ⟨4535705387570759495426609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48380857467421434617883829 4535705387570759495426609)
                    ·
                      refine ⟨3401779040678069621569957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4535705387570759495426609 3401779040678069621569957)
                      ·
                        rfl

theorem cell23_6624941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_6624941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624941 prefixEnd_6624941 := by exact prefixLift 6624941
  have htrace : WordTrace (prefixWord ++ tailWord_6624941) baseStart_6624941 baseEnd_6624941 := by
    simpa [prefixWord, tailWord_6624941, baseEnd_6624941] using wordTrace_append hprefix tailTrace_6624941
  have hstable : (prefixWord ++ tailWord_6624941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624941).length < 2 ^ (prefixWord ++ tailWord_6624941).sum := by decide
  have hdescent : baseEnd_6624941 < baseStart_6624941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6624949 : List Nat := [1, 3, 3, 3, 3, 1, 2, 1, 2, 2, 2]
def baseStart_6624949 : Nat := 118140960795 + 6624949 * 2 ^ 59
def prefixEnd_6624949 : Nat := 4983230072969 + 3 ^ 40 * 6624949 * 2
def baseEnd_6624949 : Nat := 3401783148523305590269921

theorem tailTrace_6624949 : CollatzResearch.WordTrace tailWord_6624949 prefixEnd_6624949 3401783148523305590269921 := by
  unfold tailWord_6624949
  simp only [CollatzResearch.WordTrace]
  refine ⟨241631740875948699054877901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161087827250632466036585267 241631740875948699054877901)
  ·
    refine ⟨90611902828480762145579213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241631740875948699054877901 90611902828480762145579213)
    ·
      refine ⟨33979463560680285804592205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90611902828480762145579213 33979463560680285804592205)
      ·
        refine ⟨12742298835255107176722077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33979463560680285804592205 12742298835255107176722077)
        ·
          refine ⟨4778362063220665191270779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12742298835255107176722077 4778362063220665191270779)
          ·
            refine ⟨7167543094830997786906169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4778362063220665191270779 7167543094830997786906169)
            ·
              refine ⟨5375657321123248340179627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7167543094830997786906169 5375657321123248340179627)
              ·
                refine ⟨8063485981684872510269441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5375657321123248340179627 8063485981684872510269441)
                ·
                  refine ⟨6047614486263654382702081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8063485981684872510269441 6047614486263654382702081)
                  ·
                    refine ⟨4535710864697740787026561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6047614486263654382702081 4535710864697740787026561)
                    ·
                      refine ⟨3401783148523305590269921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4535710864697740787026561 3401783148523305590269921)
                      ·
                        rfl

theorem cell23_6624949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_6624949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6624949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6624949 prefixEnd_6624949 := by exact prefixLift 6624949
  have htrace : WordTrace (prefixWord ++ tailWord_6624949) baseStart_6624949 baseEnd_6624949 := by
    simpa [prefixWord, tailWord_6624949, baseEnd_6624949] using wordTrace_append hprefix tailTrace_6624949
  have hstable : (prefixWord ++ tailWord_6624949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6624949).length < 2 ^ (prefixWord ++ tailWord_6624949).sum := by decide
  have hdescent : baseEnd_6624949 < baseStart_6624949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6624949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625101 : List Nat := [1, 6, 1, 2, 1, 1, 11]
def baseStart_6625101 : Nat := 118140960795 + 6625101 * 2 ^ 59
def prefixEnd_6625101 : Nat := 4983230072969 + 3 ^ 40 * 6625101 * 2
def baseEnd_6625101 : Nat := 41998286389910975253941

theorem tailTrace_6625101 : CollatzResearch.WordTrace tailWord_6625101 prefixEnd_6625101 41998286389910975253941 := by
  unfold tailWord_6625101
  simp only [CollatzResearch.WordTrace]
  refine ⟨241637284771398029014411157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161091523180932019342940771 241637284771398029014411157)
  ·
    refine ⟨11326747723659282610050523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 241637284771398029014411157 11326747723659282610050523)
    ·
      refine ⟨16990121585488923915075785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11326747723659282610050523 16990121585488923915075785)
      ·
        refine ⟨12742591189116692936306839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16990121585488923915075785 12742591189116692936306839)
        ·
          refine ⟨19113886783675039404460259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12742591189116692936306839 19113886783675039404460259)
          ·
            refine ⟨28670830175512559106690389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19113886783675039404460259 28670830175512559106690389)
            ·
              refine ⟨41998286389910975253941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28670830175512559106690389 41998286389910975253941)
              ·
                rfl

theorem cell23_6625101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 11].length) (baseStart_6625101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625101 prefixEnd_6625101 := by exact prefixLift 6625101
  have htrace : WordTrace (prefixWord ++ tailWord_6625101) baseStart_6625101 baseEnd_6625101 := by
    simpa [prefixWord, tailWord_6625101, baseEnd_6625101] using wordTrace_append hprefix tailTrace_6625101
  have hstable : (prefixWord ++ tailWord_6625101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625101).length < 2 ^ (prefixWord ++ tailWord_6625101).sum := by decide
  have hdescent : baseEnd_6625101 < baseStart_6625101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625114 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 2, 7]
def baseStart_6625114 : Nat := 118140960795 + 6625114 * 2 ^ 59
def prefixEnd_6625114 : Nat := 4983230072969 + 3 ^ 40 * 6625114 * 2
def baseEnd_6625114 : Nat := 1133955957610432481568887

theorem tailTrace_6625114 : CollatzResearch.WordTrace tailWord_6625114 prefixEnd_6625114 1133955957610432481568887 := by
  unfold tailWord_6625114
  simp only [CollatzResearch.WordTrace]
  refine ⟨60409439730087733058658599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161091839280233954823089597 60409439730087733058658599)
  ·
    refine ⟨90614159595131599587987899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60409439730087733058658599 90614159595131599587987899)
    ·
      refine ⟨135921239392697399381981849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90614159595131599587987899 135921239392697399381981849)
      ·
        refine ⟨101940929544523049536486387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135921239392697399381981849 101940929544523049536486387)
        ·
          refine ⟨152911394316784574304729581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101940929544523049536486387 152911394316784574304729581)
          ·
            refine ⟨57341772868794215364273593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152911394316784574304729581 57341772868794215364273593)
            ·
              refine ⟨43006329651595661523205195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57341772868794215364273593 43006329651595661523205195)
              ·
                refine ⟨64509494477393492284807793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43006329651595661523205195 64509494477393492284807793)
                ·
                  refine ⟨48382120858045119213605845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64509494477393492284807793 48382120858045119213605845)
                  ·
                    refine ⟨1133955957610432481568887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48382120858045119213605845 1133955957610432481568887)
                    ·
                      rfl

theorem cell23_6625114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_6625114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625114 prefixEnd_6625114 := by exact prefixLift 6625114
  have htrace : WordTrace (prefixWord ++ tailWord_6625114) baseStart_6625114 baseEnd_6625114 := by
    simpa [prefixWord, tailWord_6625114, baseEnd_6625114] using wordTrace_append hprefix tailTrace_6625114
  have hstable : (prefixWord ++ tailWord_6625114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625114).length < 2 ^ (prefixWord ++ tailWord_6625114).sum := by decide
  have hdescent : baseEnd_6625114 < baseStart_6625114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625122 : List Nat := [3, 3, 2, 1, 2, 3, 2, 1, 2, 4]
def baseStart_6625122 : Nat := 118140960795 + 6625122 * 2 ^ 59
def prefixEnd_6625122 : Nat := 4983230072969 + 3 ^ 40 * 6625122 * 2
def baseEnd_6625122 : Nat := 1133957326892177804468875

theorem tailTrace_6625122 : CollatzResearch.WordTrace tailWord_6625122 prefixEnd_6625122 1133957326892177804468875 := by
  unfold tailWord_6625122
  simp only [CollatzResearch.WordTrace]
  refine ⟨60409512676080487400231405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161092033802881299733950413 60409512676080487400231405)
  ·
    refine ⟨22653567253530182775086777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60409512676080487400231405 22653567253530182775086777)
    ·
      refine ⟨16990175440147637081315083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22653567253530182775086777 16990175440147637081315083)
      ·
        refine ⟨25485263160221455621972625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16990175440147637081315083 25485263160221455621972625)
        ·
          refine ⟨19113947370166091716479469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25485263160221455621972625 19113947370166091716479469)
          ·
            refine ⟨7167730263812284393679801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19113947370166091716479469 7167730263812284393679801)
            ·
              refine ⟨5375797697859213295259851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7167730263812284393679801 5375797697859213295259851)
              ·
                refine ⟨8063696546788819942889777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5375797697859213295259851 8063696546788819942889777)
                ·
                  refine ⟨6047772410091614957167333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8063696546788819942889777 6047772410091614957167333)
                  ·
                    refine ⟨1133957326892177804468875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6047772410091614957167333 1133957326892177804468875)
                    ·
                      rfl

theorem cell23_6625122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_6625122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625122 prefixEnd_6625122 := by exact prefixLift 6625122
  have htrace : WordTrace (prefixWord ++ tailWord_6625122) baseStart_6625122 baseEnd_6625122 := by
    simpa [prefixWord, tailWord_6625122, baseEnd_6625122] using wordTrace_append hprefix tailTrace_6625122
  have hstable : (prefixWord ++ tailWord_6625122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625122).length < 2 ^ (prefixWord ++ tailWord_6625122).sum := by decide
  have hdescent : baseEnd_6625122 < baseStart_6625122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625162 : List Nat := [3, 1, 2, 4, 2, 1, 2, 2, 2, 1, 3]
def baseStart_6625162 : Nat := 118140960795 + 6625162 * 2 ^ 59
def prefixEnd_6625162 : Nat := 4983230072969 + 3 ^ 40 * 6625162 * 2
def baseEnd_6625162 : Nat := 3401892519902713256906441

theorem tailTrace_6625162 : CollatzResearch.WordTrace tailWord_6625162 prefixEnd_6625162 3401892519902713256906441 := by
  unfold tailWord_6625162
  simp only [CollatzResearch.WordTrace]
  refine ⟨60409877406044259108095435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161093006416118024288254493 60409877406044259108095435)
  ·
    refine ⟨90614816109066388662143153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60409877406044259108095435 90614816109066388662143153)
    ·
      refine ⟨67961112081799791496607365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90614816109066388662143153 67961112081799791496607365)
      ·
        refine ⟨12742708515337460905613881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67961112081799791496607365 12742708515337460905613881)
        ·
          refine ⟨9557031386503095679210411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12742708515337460905613881 9557031386503095679210411)
          ·
            refine ⟨14335547079754643518815617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9557031386503095679210411 14335547079754643518815617)
            ·
              refine ⟨10751660309815982639111713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14335547079754643518815617 10751660309815982639111713)
              ·
                refine ⟨8063745232361986979333785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10751660309815982639111713 8063745232361986979333785)
                ·
                  refine ⟨6047808924271490234500339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8063745232361986979333785 6047808924271490234500339)
                  ·
                    refine ⟨9071713386407235351750509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6047808924271490234500339 9071713386407235351750509)
                    ·
                      refine ⟨3401892519902713256906441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9071713386407235351750509 3401892519902713256906441)
                      ·
                        rfl

theorem cell23_6625162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_6625162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625162 prefixEnd_6625162 := by exact prefixLift 6625162
  have htrace : WordTrace (prefixWord ++ tailWord_6625162) baseStart_6625162 baseEnd_6625162 := by
    simpa [prefixWord, tailWord_6625162, baseEnd_6625162] using wordTrace_append hprefix tailTrace_6625162
  have hstable : (prefixWord ++ tailWord_6625162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625162).length < 2 ^ (prefixWord ++ tailWord_6625162).sum := by decide
  have hdescent : baseEnd_6625162 < baseStart_6625162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625164 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 2, 3, 6]
def baseStart_6625164 : Nat := 118140960795 + 6625164 * 2 ^ 59
def prefixEnd_6625164 : Nat := 4983230072969 + 3 ^ 40 * 6625164 * 2
def baseEnd_6625164 : Nat := 3401893546864022249081431

theorem tailTrace_6625164 : CollatzResearch.WordTrace tailWord_6625164 prefixEnd_6625164 3401893546864022249081431 := by
  unfold tailWord_6625164
  simp only [CollatzResearch.WordTrace]
  refine ⟨120819791285084895386977273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161093055046779860515969697 120819791285084895386977273)
  ·
    refine ⟨90614843463813671540232955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120819791285084895386977273 90614843463813671540232955)
    ·
      refine ⟨135922265195720507310349433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90614843463813671540232955 135922265195720507310349433)
      ·
        refine ⟨101941698896790380482762075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135922265195720507310349433 101941698896790380482762075)
        ·
          refine ⟨152912548345185570724143113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101941698896790380482762075 152912548345185570724143113)
          ·
            refine ⟨114684411258889178043107335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152912548345185570724143113 114684411258889178043107335)
            ·
              refine ⟨172026616888333767064661003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114684411258889178043107335 172026616888333767064661003)
              ·
                refine ⟨258039925332500650596991505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172026616888333767064661003 258039925332500650596991505)
                ·
                  refine ⟨193529943999375487947743629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258039925332500650596991505 193529943999375487947743629)
                  ·
                    refine ⟨72573728999765807980403861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193529943999375487947743629 72573728999765807980403861)
                    ·
                      refine ⟨3401893546864022249081431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72573728999765807980403861 3401893546864022249081431)
                      ·
                        rfl

theorem cell23_6625164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_6625164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625164 prefixEnd_6625164 := by exact prefixLift 6625164
  have htrace : WordTrace (prefixWord ++ tailWord_6625164) baseStart_6625164 baseEnd_6625164 := by
    simpa [prefixWord, tailWord_6625164, baseEnd_6625164] using wordTrace_append hprefix tailTrace_6625164
  have hstable : (prefixWord ++ tailWord_6625164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625164).length < 2 ^ (prefixWord ++ tailWord_6625164).sum := by decide
  have hdescent : baseEnd_6625164 < baseStart_6625164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625181 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_6625181 : Nat := 118140960795 + 6625181 * 2 ^ 59
def prefixEnd_6625181 : Nat := 4983230072969 + 3 ^ 40 * 6625181 * 2
def baseEnd_6625181 : Nat := 3401902276035148682568853

theorem tailTrace_6625181 : CollatzResearch.WordTrace tailWord_6625181 prefixEnd_6625181 3401902276035148682568853 := by
  unfold tailWord_6625181
  simp only [CollatzResearch.WordTrace]
  refine ⟨241640202611108202677323397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161093468407405468451548931 241640202611108202677323397)
  ·
    refine ⟨45307537989582788001998137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241640202611108202677323397 45307537989582788001998137)
    ·
      refine ⟨33980653492187091001498603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45307537989582788001998137 33980653492187091001498603)
      ·
        refine ⟨50970980238280636502247905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33980653492187091001498603 50970980238280636502247905)
        ·
          refine ⟨38228235178710477376685929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50970980238280636502247905 38228235178710477376685929)
          ·
            refine ⟨28671176384032858032514447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38228235178710477376685929 28671176384032858032514447)
            ·
              refine ⟨43006764576049287048771671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28671176384032858032514447 43006764576049287048771671)
              ·
                refine ⟨64510146864073930573157507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43006764576049287048771671 64510146864073930573157507)
                ·
                  refine ⟨96765220296110895859736261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64510146864073930573157507 96765220296110895859736261)
                  ·
                    refine ⟨18143478805520792973700549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96765220296110895859736261 18143478805520792973700549)
                    ·
                      refine ⟨3401902276035148682568853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18143478805520792973700549 3401902276035148682568853)
                      ·
                        rfl

theorem cell23_6625181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_6625181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625181 prefixEnd_6625181 := by exact prefixLift 6625181
  have htrace : WordTrace (prefixWord ++ tailWord_6625181) baseStart_6625181 baseEnd_6625181 := by
    simpa [prefixWord, tailWord_6625181, baseEnd_6625181] using wordTrace_append hprefix tailTrace_6625181
  have hstable : (prefixWord ++ tailWord_6625181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625181).length < 2 ^ (prefixWord ++ tailWord_6625181).sum := by decide
  have hdescent : baseEnd_6625181 < baseStart_6625181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625191 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 9]
def baseStart_6625191 : Nat := 118140960795 + 6625191 * 2 ^ 59
def prefixEnd_6625191 : Nat := 4983230072969 + 3 ^ 40 * 6625191 * 2
def baseEnd_6625191 : Nat := 377989712315743738160423

theorem tailTrace_6625191 : CollatzResearch.WordTrace tailWord_6625191 prefixEnd_6625191 377989712315743738160423 := by
  unfold tailWord_6625191
  simp only [CollatzResearch.WordTrace]
  refine ⟨241640567341071974385187427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161093711560714649590124951 241640567341071974385187427)
  ·
    refine ⟨362460851011607961577781141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241640567341071974385187427 362460851011607961577781141)
    ·
      refine ⟨16990352391169123198958491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 362460851011607961577781141 16990352391169123198958491)
      ·
        refine ⟨25485528586753684798437737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16990352391169123198958491 25485528586753684798437737)
        ·
          refine ⟨19114146440065263598828303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25485528586753684798437737 19114146440065263598828303)
          ·
            refine ⟨28671219660097895398242455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19114146440065263598828303 28671219660097895398242455)
            ·
              refine ⟨43006829490146843097363683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28671219660097895398242455 43006829490146843097363683)
              ·
                refine ⟨64510244235220264646045525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43006829490146843097363683 64510244235220264646045525)
                ·
                  refine ⟨377989712315743738160423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64510244235220264646045525 377989712315743738160423)
                  ·
                    rfl

theorem cell23_6625191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 9].length) (baseStart_6625191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625191 prefixEnd_6625191 := by exact prefixLift 6625191
  have htrace : WordTrace (prefixWord ++ tailWord_6625191) baseStart_6625191 baseEnd_6625191 := by
    simpa [prefixWord, tailWord_6625191, baseEnd_6625191] using wordTrace_append hprefix tailTrace_6625191
  have hstable : (prefixWord ++ tailWord_6625191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625191).length < 2 ^ (prefixWord ++ tailWord_6625191).sum := by decide
  have hdescent : baseEnd_6625191 < baseStart_6625191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625208 : List Nat := [2, 1, 2, 1, 2, 3, 4, 3, 5]
def baseStart_6625208 : Nat := 118140960795 + 6625208 * 2 ^ 59
def prefixEnd_6625208 : Nat := 4983230072969 + 3 ^ 40 * 6625208 * 2
def baseEnd_6625208 : Nat := 377990682223646675214581

theorem tailTrace_6625208 : CollatzResearch.WordTrace tailWord_6625208 prefixEnd_6625208 377990682223646675214581 := by
  unfold tailWord_6625208
  simp only [CollatzResearch.WordTrace]
  refine ⟨120820593691005193144278139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161094124921340257525704185 120820593691005193144278139)
  ·
    refine ⟨181230890536507789716417209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120820593691005193144278139 181230890536507789716417209)
    ·
      refine ⟨135923167902380842287312907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181230890536507789716417209 135923167902380842287312907)
      ·
        refine ⟨203884751853571263430969361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135923167902380842287312907 203884751853571263430969361)
        ·
          refine ⟨152913563890178447573227021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203884751853571263430969361 152913563890178447573227021)
          ·
            refine ⟨57342586458816917839960133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152913563890178447573227021 57342586458816917839960133)
            ·
              refine ⟨10751734961028172094992525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57342586458816917839960133 10751734961028172094992525)
              ·
                refine ⟨4031900610385564535622197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10751734961028172094992525 4031900610385564535622197)
                ·
                  refine ⟨377990682223646675214581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4031900610385564535622197 377990682223646675214581)
                  ·
                    rfl

theorem cell23_6625208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 5].length) (baseStart_6625208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625208 prefixEnd_6625208 := by exact prefixLift 6625208
  have htrace : WordTrace (prefixWord ++ tailWord_6625208) baseStart_6625208 baseEnd_6625208 := by
    simpa [prefixWord, tailWord_6625208, baseEnd_6625208] using wordTrace_append hprefix tailTrace_6625208
  have hstable : (prefixWord ++ tailWord_6625208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625208).length < 2 ^ (prefixWord ++ tailWord_6625208).sum := by decide
  have hdescent : baseEnd_6625208 < baseStart_6625208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625258 : List Nat := [3, 1, 3, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_6625258 : Nat := 118140960795 + 6625258 * 2 ^ 59
def prefixEnd_6625258 : Nat := 4983230072969 + 3 ^ 40 * 6625258 * 2
def baseEnd_6625258 : Nat := 3401941814045544881305999

theorem tailTrace_6625258 : CollatzResearch.WordTrace tailWord_6625258 prefixEnd_6625258 3401941814045544881305999 := by
  unfold tailWord_6625258
  simp only [CollatzResearch.WordTrace]
  refine ⟨60410752757957311206969107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161095340687886163218584285 60410752757957311206969107)
  ·
    refine ⟨90616129136935966810453661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60410752757957311206969107 90616129136935966810453661)
    ·
      refine ⟨33981048426350987553920123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90616129136935966810453661 33981048426350987553920123)
      ·
        refine ⟨50971572639526481330880185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33981048426350987553920123 50971572639526481330880185)
        ·
          refine ⟨38228679479644860998160139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50971572639526481330880185 38228679479644860998160139)
          ·
            refine ⟨57343019219467291497240209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38228679479644860998160139 57343019219467291497240209)
            ·
              refine ⟨43007264414600468622930157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57343019219467291497240209 43007264414600468622930157)
              ·
                refine ⟨16127724155475175733598809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43007264414600468622930157 16127724155475175733598809)
                ·
                  refine ⟨12095793116606381800199107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16127724155475175733598809 12095793116606381800199107)
                  ·
                    refine ⟨18143689674909572700298661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12095793116606381800199107 18143689674909572700298661)
                    ·
                      refine ⟨3401941814045544881305999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18143689674909572700298661 3401941814045544881305999)
                      ·
                        rfl

theorem cell23_6625258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_6625258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625258 prefixEnd_6625258 := by exact prefixLift 6625258
  have htrace : WordTrace (prefixWord ++ tailWord_6625258) baseStart_6625258 baseEnd_6625258 := by
    simpa [prefixWord, tailWord_6625258, baseEnd_6625258] using wordTrace_append hprefix tailTrace_6625258
  have hstable : (prefixWord ++ tailWord_6625258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625258).length < 2 ^ (prefixWord ++ tailWord_6625258).sum := by decide
  have hdescent : baseEnd_6625258 < baseStart_6625258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625281 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 8]
def baseStart_6625281 : Nat := 118140960795 + 6625281 * 2 ^ 59
def prefixEnd_6625281 : Nat := 4983230072969 + 3 ^ 40 * 6625281 * 2
def baseEnd_6625281 : Nat := 377994847122288699035377

theorem tailTrace_6625281 : CollatzResearch.WordTrace tailWord_6625281 prefixEnd_6625281 377994847122288699035377 := by
  unfold tailWord_6625281
  simp only [CollatzResearch.WordTrace]
  refine ⟨241643849910745919755963697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161095899940497279837309131 241643849910745919755963697)
  ·
    refine ⟨181232887433059439816972773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241643849910745919755963697 181232887433059439816972773)
    ·
      refine ⟨33981166393698644965682395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181232887433059439816972773 33981166393698644965682395)
      ·
        refine ⟨50971749590547967448523593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33981166393698644965682395 50971749590547967448523593)
        ·
          refine ⟨38228812192910975586392695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50971749590547967448523593 38228812192910975586392695)
          ·
            refine ⟨57343218289366463379589043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38228812192910975586392695 57343218289366463379589043)
            ·
              refine ⟨86014827434049695069383565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57343218289366463379589043 86014827434049695069383565)
              ·
                refine ⟨32255560287768635651018837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86014827434049695069383565 32255560287768635651018837)
                ·
                  refine ⟨377994847122288699035377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32255560287768635651018837 377994847122288699035377)
                  ·
                    rfl

theorem cell23_6625281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 8].length) (baseStart_6625281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625281 prefixEnd_6625281 := by exact prefixLift 6625281
  have htrace : WordTrace (prefixWord ++ tailWord_6625281) baseStart_6625281 baseEnd_6625281 := by
    simpa [prefixWord, tailWord_6625281, baseEnd_6625281] using wordTrace_append hprefix tailTrace_6625281
  have hstable : (prefixWord ++ tailWord_6625281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625281).length < 2 ^ (prefixWord ++ tailWord_6625281).sum := by decide
  have hdescent : baseEnd_6625281 < baseStart_6625281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625285 : List Nat := [1, 3, 1, 1, 2, 6, 1, 1, 3, 4]
def baseStart_6625285 : Nat := 118140960795 + 6625285 * 2 ^ 59
def prefixEnd_6625285 : Nat := 4983230072969 + 3 ^ 40 * 6625285 * 2
def baseEnd_6625285 : Nat := 1133985226007738758556125

theorem tailTrace_6625285 : CollatzResearch.WordTrace tailWord_6625285 prefixEnd_6625285 1133985226007738758556125 := by
  unfold tailWord_6625285
  simp only [CollatzResearch.WordTrace]
  refine ⟨241643995802731428439109309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161095997201820952292739539 241643995802731428439109309)
  ·
    refine ⟨90616498426024285664665991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241643995802731428439109309 90616498426024285664665991)
    ·
      refine ⟨135924747639036428496998987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90616498426024285664665991 135924747639036428496998987)
      ·
        refine ⟨203887121458554642745498481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135924747639036428496998987 203887121458554642745498481)
        ·
          refine ⟨152915341093915982059123861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203887121458554642745498481 152915341093915982059123861)
          ·
            refine ⟨7167906613777311659021431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152915341093915982059123861 7167906613777311659021431)
            ·
              refine ⟨10751859920665967488532147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7167906613777311659021431 10751859920665967488532147)
              ·
                refine ⟨16127789880998951232798221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10751859920665967488532147 16127789880998951232798221)
                ·
                  refine ⟨6047921205374606712299333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16127789880998951232798221 6047921205374606712299333)
                  ·
                    refine ⟨1133985226007738758556125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6047921205374606712299333 1133985226007738758556125)
                    ·
                      rfl

theorem cell23_6625285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 4].length) (baseStart_6625285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625285 prefixEnd_6625285 := by exact prefixLift 6625285
  have htrace : WordTrace (prefixWord ++ tailWord_6625285) baseStart_6625285 baseEnd_6625285 := by
    simpa [prefixWord, tailWord_6625285, baseEnd_6625285] using wordTrace_append hprefix tailTrace_6625285
  have hstable : (prefixWord ++ tailWord_6625285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625285).length < 2 ^ (prefixWord ++ tailWord_6625285).sum := by decide
  have hdescent : baseEnd_6625285 < baseStart_6625285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625332 : List Nat := [2, 5, 1, 2, 2, 1, 2, 2, 6]
def baseStart_6625332 : Nat := 118140960795 + 6625332 * 2 ^ 59
def prefixEnd_6625332 : Nat := 4983230072969 + 3 ^ 40 * 6625332 * 2
def baseEnd_6625332 : Nat := 377997756845997510197851

theorem tailTrace_6625332 : CollatzResearch.WordTrace tailWord_6625332 prefixEnd_6625332 377997756845997510197851 := by
  unfold tailWord_6625332
  simp only [CollatzResearch.WordTrace]
  refine ⟨120822855016780577733035125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161097140022374103644046833 120822855016780577733035125)
  ·
    refine ⟨11327142657823179162472043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120822855016780577733035125 11327142657823179162472043)
    ·
      refine ⟨16990713986734768743708065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11327142657823179162472043 16990713986734768743708065)
      ·
        refine ⟨12743035490051076557781049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16990713986734768743708065 12743035490051076557781049)
        ·
          refine ⟨9557276617538307418335787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12743035490051076557781049 9557276617538307418335787)
          ·
            refine ⟨14335914926307461127503681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9557276617538307418335787 14335914926307461127503681)
            ·
              refine ⟨10751936194730595845627761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14335914926307461127503681 10751936194730595845627761)
              ·
                refine ⟨8063952146047946884220821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10751936194730595845627761 8063952146047946884220821)
                ·
                  refine ⟨377997756845997510197851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8063952146047946884220821 377997756845997510197851)
                  ·
                    rfl

theorem cell23_6625332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_6625332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625332 prefixEnd_6625332 := by exact prefixLift 6625332
  have htrace : WordTrace (prefixWord ++ tailWord_6625332) baseStart_6625332 baseEnd_6625332 := by
    simpa [prefixWord, tailWord_6625332, baseEnd_6625332] using wordTrace_append hprefix tailTrace_6625332
  have hstable : (prefixWord ++ tailWord_6625332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625332).length < 2 ^ (prefixWord ++ tailWord_6625332).sum := by decide
  have hdescent : baseEnd_6625332 < baseStart_6625332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625335 : List Nat := [1, 1, 3, 1, 2, 2, 4, 2, 2, 3, 2]
def baseStart_6625335 : Nat := 118140960795 + 6625335 * 2 ^ 59
def prefixEnd_6625335 : Nat := 4983230072969 + 3 ^ 40 * 6625335 * 2
def baseEnd_6625335 : Nat := 3401981352055941080043145

theorem tailTrace_6625335 : CollatzResearch.WordTrace tailWord_6625335 prefixEnd_6625335 3401981352055941080043145 := by
  unfold tailWord_6625335
  simp only [CollatzResearch.WordTrace]
  refine ⟨241645819452550286978429459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161097212968366857985619639 241645819452550286978429459)
  ·
    refine ⟨362468729178825430467644189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241645819452550286978429459 362468729178825430467644189)
    ·
      refine ⟨135925773442059536425366571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362468729178825430467644189 135925773442059536425366571)
      ·
        refine ⟨203888660163089304638049857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135925773442059536425366571 203888660163089304638049857)
        ·
          refine ⟨152916495122316978478537393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203888660163089304638049857 152916495122316978478537393)
          ·
            refine ⟨114687371341737733858903045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152916495122316978478537393 114687371341737733858903045)
            ·
              refine ⟨21503882126575825098544321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114687371341737733858903045 21503882126575825098544321)
              ·
                refine ⟨16127911594931868823908241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21503882126575825098544321 16127911594931868823908241)
                ·
                  refine ⟨12095933696198901617931181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16127911594931868823908241 12095933696198901617931181)
                  ·
                    refine ⟨4535975136074588106724193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12095933696198901617931181 4535975136074588106724193)
                    ·
                      refine ⟨3401981352055941080043145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4535975136074588106724193 3401981352055941080043145)
                      ·
                        rfl

theorem cell23_6625335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 3, 2].length) (baseStart_6625335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625335 prefixEnd_6625335 := by exact prefixLift 6625335
  have htrace : WordTrace (prefixWord ++ tailWord_6625335) baseStart_6625335 baseEnd_6625335 := by
    simpa [prefixWord, tailWord_6625335, baseEnd_6625335] using wordTrace_append hprefix tailTrace_6625335
  have hstable : (prefixWord ++ tailWord_6625335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625335).length < 2 ^ (prefixWord ++ tailWord_6625335).sum := by decide
  have hdescent : baseEnd_6625335 < baseStart_6625335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625336 : List Nat := [2, 1, 2, 1, 7, 1, 2, 2, 1, 4]
def baseStart_6625336 : Nat := 118140960795 + 6625336 * 2 ^ 59
def prefixEnd_6625336 : Nat := 4983230072969 + 3 ^ 40 * 6625336 * 2
def baseEnd_6625336 : Nat := 1133993955178865192043547

theorem tailTrace_6625336 : CollatzResearch.WordTrace tailWord_6625336 prefixEnd_6625336 1133993955178865192043547 := by
  unfold tailWord_6625336
  simp only [CollatzResearch.WordTrace]
  refine ⟨120822927962773332074607931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161097237283697776099477241 120822927962773332074607931)
  ·
    refine ⟨181234391944159998111911897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120822927962773332074607931 181234391944159998111911897)
    ·
      refine ⟨135925793958119998583933923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181234391944159998111911897 135925793958119998583933923)
      ·
        refine ⟨203888690937179997875900885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135925793958119998583933923 203888690937179997875900885)
        ·
          refine ⟨4778641193840156200216427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 203888690937179997875900885 4778641193840156200216427)
          ·
            refine ⟨7167961790760234300324641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4778641193840156200216427 7167961790760234300324641)
            ·
              refine ⟨5375971343070175725243481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7167961790760234300324641 5375971343070175725243481)
              ·
                refine ⟨4031978507302631793932611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5375971343070175725243481 4031978507302631793932611)
                ·
                  refine ⟨6047967760953947690898917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4031978507302631793932611 6047967760953947690898917)
                  ·
                    refine ⟨1133993955178865192043547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6047967760953947690898917 1133993955178865192043547)
                    ·
                      rfl

theorem cell23_6625336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 1, 4].length) (baseStart_6625336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625336 prefixEnd_6625336 := by exact prefixLift 6625336
  have htrace : WordTrace (prefixWord ++ tailWord_6625336) baseStart_6625336 baseEnd_6625336 := by
    simpa [prefixWord, tailWord_6625336, baseEnd_6625336] using wordTrace_append hprefix tailTrace_6625336
  have hstable : (prefixWord ++ tailWord_6625336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625336).length < 2 ^ (prefixWord ++ tailWord_6625336).sum := by decide
  have hdescent : baseEnd_6625336 < baseStart_6625336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625358 : List Nat := [4, 1, 1, 1, 1, 4, 1, 3, 1, 6]
def baseStart_6625358 : Nat := 118140960795 + 6625358 * 2 ^ 59
def prefixEnd_6625358 : Nat := 4983230072969 + 3 ^ 40 * 6625358 * 2
def baseEnd_6625358 : Nat := 1133997720703664830018513

theorem tailTrace_6625358 : CollatzResearch.WordTrace tailWord_6625358 prefixEnd_6625358 1133997720703664830018513 := by
  unfold tailWord_6625358
  simp only [CollatzResearch.WordTrace]
  refine ⟨30205832291433370238314591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161097772220977974604344485 30205832291433370238314591)
  ·
    refine ⟨45308748437150055357471887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30205832291433370238314591 45308748437150055357471887)
    ·
      refine ⟨67963122655725083036207831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45308748437150055357471887 67963122655725083036207831)
      ·
        refine ⟨101944683983587624554311747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67963122655725083036207831 101944683983587624554311747)
        ·
          refine ⟨152917025975381436831467621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101944683983587624554311747 152917025975381436831467621)
          ·
            refine ⟨28671942370384019405900179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152917025975381436831467621 28671942370384019405900179)
            ·
              refine ⟨43007913555576029108850269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28671942370384019405900179 43007913555576029108850269)
              ·
                refine ⟨16127967583341010915818851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43007913555576029108850269 16127967583341010915818851)
                ·
                  refine ⟨24191951375011516373728277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16127967583341010915818851 24191951375011516373728277)
                  ·
                    refine ⟨1133997720703664830018513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24191951375011516373728277 1133997720703664830018513)
                    ·
                      rfl

theorem cell23_6625358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_6625358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625358 prefixEnd_6625358 := by exact prefixLift 6625358
  have htrace : WordTrace (prefixWord ++ tailWord_6625358) baseStart_6625358 baseEnd_6625358 := by
    simpa [prefixWord, tailWord_6625358, baseEnd_6625358] using wordTrace_append hprefix tailTrace_6625358
  have hstable : (prefixWord ++ tailWord_6625358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625358).length < 2 ^ (prefixWord ++ tailWord_6625358).sum := by decide
  have hdescent : baseEnd_6625358 < baseStart_6625358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625385 : List Nat := [1, 2, 1, 1, 1, 5, 3, 3, 1, 2, 3]
def baseStart_6625385 : Nat := 118140960795 + 6625385 * 2 ^ 59
def prefixEnd_6625385 : Nat := 4983230072969 + 3 ^ 40 * 6625385 * 2
def baseEnd_6625385 : Nat := 3402007026088665884417915

theorem tailTrace_6625385 : CollatzResearch.WordTrace tailWord_6625385 prefixEnd_6625385 3402007026088665884417915 := by
  unfold tailWord_6625385
  simp only [CollatzResearch.WordTrace]
  refine ⟨241647643102369145517749609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161098428734912763678499739 241647643102369145517749609)
  ·
    refine ⟨181235732326776859138312207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241647643102369145517749609 181235732326776859138312207)
    ·
      refine ⟨271853598490165288707468311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181235732326776859138312207 271853598490165288707468311)
      ·
        refine ⟨407780397735247933061202467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271853598490165288707468311 407780397735247933061202467)
        ·
          refine ⟨611670596602871899591803701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407780397735247933061202467 611670596602871899591803701)
          ·
            refine ⟨57344118431519240586731597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 611670596602871899591803701 57344118431519240586731597)
            ·
              refine ⟨21504044411819715220024349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57344118431519240586731597 21504044411819715220024349)
              ·
                refine ⟨8064016654432393207509131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21504044411819715220024349 8064016654432393207509131)
                ·
                  refine ⟨12096024981648589811263697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8064016654432393207509131 12096024981648589811263697)
                  ·
                    refine ⟨9072018736236442358447773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12096024981648589811263697 9072018736236442358447773)
                    ·
                      refine ⟨3402007026088665884417915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9072018736236442358447773 3402007026088665884417915)
                      ·
                        rfl

theorem cell23_6625385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 2, 3].length) (baseStart_6625385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625385 prefixEnd_6625385 := by exact prefixLift 6625385
  have htrace : WordTrace (prefixWord ++ tailWord_6625385) baseStart_6625385 baseEnd_6625385 := by
    simpa [prefixWord, tailWord_6625385, baseEnd_6625385] using wordTrace_append hprefix tailTrace_6625385
  have hstable : (prefixWord ++ tailWord_6625385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625385).length < 2 ^ (prefixWord ++ tailWord_6625385).sum := by decide
  have hdescent : baseEnd_6625385 < baseStart_6625385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625392 : List Nat := [2, 1, 1, 1, 5, 4, 1, 2, 2, 4]
def baseStart_6625392 : Nat := 118140960795 + 6625392 * 2 ^ 59
def prefixEnd_6625392 : Nat := 4983230072969 + 3 ^ 40 * 6625392 * 2
def baseEnd_6625392 : Nat := 1134003540151082452343461

theorem tailTrace_6625392 : CollatzResearch.WordTrace tailWord_6625392 prefixEnd_6625392 1134003540151082452343461 := by
  unfold tailWord_6625392
  simp only [CollatzResearch.WordTrace]
  refine ⟨120823949206671892856627215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161098598942229190475502953 120823949206671892856627215)
  ·
    refine ⟨181235923810007839284940823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120823949206671892856627215 181235923810007839284940823)
    ·
      refine ⟨271853885715011758927411235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181235923810007839284940823 271853885715011758927411235)
      ·
        refine ⟨407780828572517638391116853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271853885715011758927411235 407780828572517638391116853)
        ·
          refine ⟨38229452678673528599167205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 407780828572517638391116853 38229452678673528599167205)
          ·
            refine ⟨7168022377251286612343851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38229452678673528599167205 7168022377251286612343851)
            ·
              refine ⟨10752033565876929918515777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7168022377251286612343851 10752033565876929918515777)
              ·
                refine ⟨8064025174407697438886833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10752033565876929918515777 8064025174407697438886833)
                ·
                  refine ⟨6048018880805773079165125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8064025174407697438886833 6048018880805773079165125)
                  ·
                    refine ⟨1134003540151082452343461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6048018880805773079165125 1134003540151082452343461)
                    ·
                      rfl

theorem cell23_6625392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 2, 4].length) (baseStart_6625392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625392 prefixEnd_6625392 := by exact prefixLift 6625392
  have htrace : WordTrace (prefixWord ++ tailWord_6625392) baseStart_6625392 baseEnd_6625392 := by
    simpa [prefixWord, tailWord_6625392, baseEnd_6625392] using wordTrace_append hprefix tailTrace_6625392
  have hstable : (prefixWord ++ tailWord_6625392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625392).length < 2 ^ (prefixWord ++ tailWord_6625392).sum := by decide
  have hdescent : baseEnd_6625392 < baseStart_6625392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625399 : List Nat := [1, 1, 3, 1, 1, 5, 2, 4, 1, 2, 2]
def baseStart_6625399 : Nat := 118140960795 + 6625399 * 2 ^ 59
def prefixEnd_6625399 : Nat := 4983230072969 + 3 ^ 40 * 6625399 * 2
def baseEnd_6625399 : Nat := 3402014214817828829642851

theorem tailTrace_6625399 : CollatzResearch.WordTrace tailWord_6625399 prefixEnd_6625399 3402014214817828829642851 := by
  unfold tailWord_6625399
  simp only [CollatzResearch.WordTrace]
  refine ⟨241648153724318425908759251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161098769149545617272506167 241648153724318425908759251)
  ·
    refine ⟨362472230586477638863138877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241648153724318425908759251 362472230586477638863138877)
    ·
      refine ⟨135927086469929114573677079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362472230586477638863138877 135927086469929114573677079)
      ·
        refine ⟨203890629704893671860515619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135927086469929114573677079 203890629704893671860515619)
        ·
          refine ⟨305835944557340507790773429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203890629704893671860515619 305835944557340507790773429)
          ·
            refine ⟨28672119802250672605385009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 305835944557340507790773429 28672119802250672605385009)
            ·
              refine ⟨21504089851688004454038757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28672119802250672605385009 21504089851688004454038757)
              ·
                refine ⟨4032016847191500835132267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21504089851688004454038757 4032016847191500835132267)
                ·
                  refine ⟨6048025270787251252698401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4032016847191500835132267 6048025270787251252698401)
                  ·
                    refine ⟨4536018953090438439523801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6048025270787251252698401 4536018953090438439523801)
                    ·
                      refine ⟨3402014214817828829642851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4536018953090438439523801 3402014214817828829642851)
                      ·
                        rfl

theorem cell23_6625399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 1, 2, 2].length) (baseStart_6625399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625399 prefixEnd_6625399 := by exact prefixLift 6625399
  have htrace : WordTrace (prefixWord ++ tailWord_6625399) baseStart_6625399 baseEnd_6625399 := by
    simpa [prefixWord, tailWord_6625399, baseEnd_6625399] using wordTrace_append hprefix tailTrace_6625399
  have hstable : (prefixWord ++ tailWord_6625399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625399).length < 2 ^ (prefixWord ++ tailWord_6625399).sum := by decide
  have hdescent : baseEnd_6625399 < baseStart_6625399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625409 : List Nat := [1, 2, 4, 2, 3, 1, 3, 1, 2, 4]
def baseStart_6625409 : Nat := 118140960795 + 6625409 * 2 ^ 59
def prefixEnd_6625409 : Nat := 4983230072969 + 3 ^ 40 * 6625409 * 2
def baseEnd_6625409 : Nat := 1134006449874791263505935

theorem tailTrace_6625409 : CollatzResearch.WordTrace tailWord_6625409 prefixEnd_6625409 1134006449874791263505935 := by
  unfold tailWord_6625409
  simp only [CollatzResearch.WordTrace]
  refine ⟨241648518454282197616623281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161099012302854798411082187 241648518454282197616623281)
  ·
    refine ⟨181236388840711648212467461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241648518454282197616623281 181236388840711648212467461)
    ·
      refine ⟨33981822907633434039837649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181236388840711648212467461 33981822907633434039837649)
      ·
        refine ⟨25486367180725075529878237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33981822907633434039837649 25486367180725075529878237)
        ·
          refine ⟨9557387692771903323704339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25486367180725075529878237 9557387692771903323704339)
          ·
            refine ⟨14336081539157854985556509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9557387692771903323704339 14336081539157854985556509)
            ·
              refine ⟨5376030577184195619583691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14336081539157854985556509 5376030577184195619583691)
              ·
                refine ⟨8064045865776293429375537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5376030577184195619583691 8064045865776293429375537)
                ·
                  refine ⟨6048034399332220072031653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8064045865776293429375537 6048034399332220072031653)
                  ·
                    refine ⟨1134006449874791263505935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6048034399332220072031653 1134006449874791263505935)
                    ·
                      rfl

theorem cell23_6625409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_6625409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625409 prefixEnd_6625409 := by exact prefixLift 6625409
  have htrace : WordTrace (prefixWord ++ tailWord_6625409) baseStart_6625409 baseEnd_6625409 := by
    simpa [prefixWord, tailWord_6625409, baseEnd_6625409] using wordTrace_append hprefix tailTrace_6625409
  have hstable : (prefixWord ++ tailWord_6625409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625409).length < 2 ^ (prefixWord ++ tailWord_6625409).sum := by decide
  have hdescent : baseEnd_6625409 < baseStart_6625409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625415 : List Nat := [1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 3]
def baseStart_6625415 : Nat := 118140960795 + 6625415 * 2 ^ 59
def prefixEnd_6625415 : Nat := 4983230072969 + 3 ^ 40 * 6625415 * 2
def baseEnd_6625415 : Nat := 3402022430508300767042777

theorem tailTrace_6625415 : CollatzResearch.WordTrace tailWord_6625415 prefixEnd_6625415 3402022430508300767042777 := by
  unfold tailWord_6625415
  simp only [CollatzResearch.WordTrace]
  refine ⟨241648737292260460641341699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161099158194840307094227799 241648737292260460641341699)
  ·
    refine ⟨362473105938390690962012549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241648737292260460641341699 362473105938390690962012549)
    ·
      refine ⟨67963707363448254555377353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 362473105938390690962012549 67963707363448254555377353)
      ·
        refine ⟨50972780522586190916533015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67963707363448254555377353 50972780522586190916533015)
        ·
          refine ⟨76459170783879286374799523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50972780522586190916533015 76459170783879286374799523)
          ·
            refine ⟨114688756175818929562199285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76459170783879286374799523 114688756175818929562199285)
            ·
              refine ⟨10752070891483024646456183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114688756175818929562199285 10752070891483024646456183)
              ·
                refine ⟨16128106337224536969684275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10752070891483024646456183 16128106337224536969684275)
                ·
                  refine ⟨24192159505836805454526413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16128106337224536969684275 24192159505836805454526413)
                  ·
                    refine ⟨9072059814688802045447405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24192159505836805454526413 9072059814688802045447405)
                    ·
                      refine ⟨3402022430508300767042777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9072059814688802045447405 3402022430508300767042777)
                      ·
                        rfl

theorem cell23_6625415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_6625415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625415 prefixEnd_6625415 := by exact prefixLift 6625415
  have htrace : WordTrace (prefixWord ++ tailWord_6625415) baseStart_6625415 baseEnd_6625415 := by
    simpa [prefixWord, tailWord_6625415, baseEnd_6625415] using wordTrace_append hprefix tailTrace_6625415
  have hstable : (prefixWord ++ tailWord_6625415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625415).length < 2 ^ (prefixWord ++ tailWord_6625415).sum := by decide
  have hdescent : baseEnd_6625415 < baseStart_6625415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625422 : List Nat := [4, 1, 1, 3, 3, 2, 2, 7]
def baseStart_6625422 : Nat := 118140960795 + 6625422 * 2 ^ 59
def prefixEnd_6625422 : Nat := 4983230072969 + 3 ^ 40 * 6625422 * 2
def baseEnd_6625422 : Nat := 126000963884180823690935

theorem tailTrace_6625422 : CollatzResearch.WordTrace tailWord_6625422 prefixEnd_6625422 126000963884180823690935 := by
  unfold tailWord_6625422
  simp only [CollatzResearch.WordTrace]
  refine ⟨30206124075404387604605815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161099328402156733891231013 30206124075404387604605815)
  ·
    refine ⟨45309186113106581406908723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30206124075404387604605815 45309186113106581406908723)
    ·
      refine ⟨67963779169659872110363085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45309186113106581406908723 67963779169659872110363085)
      ·
        refine ⟨25486417188622452041386157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67963779169659872110363085 25486417188622452041386157)
        ·
          refine ⟨9557406445733419515519809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25486417188622452041386157 9557406445733419515519809)
          ·
            refine ⟨7168054834300064636639857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9557406445733419515519809 7168054834300064636639857)
            ·
              refine ⟨5376041125725048477479893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7168054834300064636639857 5376041125725048477479893)
              ·
                refine ⟨126000963884180823690935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5376041125725048477479893 126000963884180823690935)
                ·
                  rfl

theorem cell23_6625422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 7].length) (baseStart_6625422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625422 prefixEnd_6625422 := by exact prefixLift 6625422
  have htrace : WordTrace (prefixWord ++ tailWord_6625422) baseStart_6625422 baseEnd_6625422 := by
    simpa [prefixWord, tailWord_6625422, baseEnd_6625422] using wordTrace_append hprefix tailTrace_6625422
  have hstable : (prefixWord ++ tailWord_6625422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625422).length < 2 ^ (prefixWord ++ tailWord_6625422).sum := by decide
  have hdescent : baseEnd_6625422 < baseStart_6625422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625450 : List Nat := [3, 1, 5, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_6625450 : Nat := 118140960795 + 6625450 * 2 ^ 59
def prefixEnd_6625450 : Nat := 4983230072969 + 3 ^ 40 * 6625450 * 2
def baseEnd_6625450 : Nat := 3402040402331208130105117

theorem tailTrace_6625450 : CollatzResearch.WordTrace tailWord_6625450 prefixEnd_6625450 3402040402331208130105117 := by
  unfold tailWord_6625450
  simp only [CollatzResearch.WordTrace]
  refine ⟨60412503461783415404716451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161100009231422441079243869 60412503461783415404716451)
  ·
    refine ⟨90618755192675123107074677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60412503461783415404716451 90618755192675123107074677)
    ·
      refine ⟨8495508299313292791288251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90618755192675123107074677 8495508299313292791288251)
      ·
        refine ⟨12743262448969939186932377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8495508299313292791288251 12743262448969939186932377)
        ·
          refine ⟨9557446836727454390199283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12743262448969939186932377 9557446836727454390199283)
          ·
            refine ⟨14336170255091181585298925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9557446836727454390199283 14336170255091181585298925)
            ·
              refine ⟨5376063845659193094487097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14336170255091181585298925 5376063845659193094487097)
              ·
                refine ⟨4032047884244394820865323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5376063845659193094487097 4032047884244394820865323)
                ·
                  refine ⟨6048071826366592231297985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4032047884244394820865323 6048071826366592231297985)
                  ·
                    refine ⟨4536053869774944173473489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6048071826366592231297985 4536053869774944173473489)
                    ·
                      refine ⟨3402040402331208130105117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4536053869774944173473489 3402040402331208130105117)
                      ·
                        rfl

theorem cell23_6625450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_6625450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625450 prefixEnd_6625450 := by exact prefixLift 6625450
  have htrace : WordTrace (prefixWord ++ tailWord_6625450) baseStart_6625450 baseEnd_6625450 := by
    simpa [prefixWord, tailWord_6625450, baseEnd_6625450] using wordTrace_append hprefix tailTrace_6625450
  have hstable : (prefixWord ++ tailWord_6625450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625450).length < 2 ^ (prefixWord ++ tailWord_6625450).sum := by decide
  have hdescent : baseEnd_6625450 < baseStart_6625450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625458 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_6625458 : Nat := 118140960795 + 6625458 * 2 ^ 59
def prefixEnd_6625458 : Nat := 4983230072969 + 3 ^ 40 * 6625458 * 2
def baseEnd_6625458 : Nat := 3402044510176444098805079

theorem tailTrace_6625458 : CollatzResearch.WordTrace tailWord_6625458 prefixEnd_6625458 3402044510176444098805079 := by
  unfold tailWord_6625458
  simp only [CollatzResearch.WordTrace]
  refine ⟨60412576407776169746289257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161100203754069785990104685 60412576407776169746289257)
  ·
    refine ⟨45309432305832127309716943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60412576407776169746289257 45309432305832127309716943)
    ·
      refine ⟨67964148458748190964575415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45309432305832127309716943 67964148458748190964575415)
      ·
        refine ⟨101946222688122286446863123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67964148458748190964575415 101946222688122286446863123)
        ·
          refine ⟨152919334032183429670294685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101946222688122286446863123 152919334032183429670294685)
          ·
            refine ⟨57344750262068786126360507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152919334032183429670294685 57344750262068786126360507)
            ·
              refine ⟨86017125393103179189540761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57344750262068786126360507 86017125393103179189540761)
              ·
                refine ⟨64512844044827384392155571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86017125393103179189540761 64512844044827384392155571)
                ·
                  refine ⟨96769266067241076588233357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64512844044827384392155571 96769266067241076588233357)
                  ·
                    refine ⟨36288474775215403720587509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96769266067241076588233357 36288474775215403720587509)
                    ·
                      refine ⟨3402044510176444098805079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36288474775215403720587509 3402044510176444098805079)
                      ·
                        rfl

theorem cell23_6625458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_6625458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625458 prefixEnd_6625458 := by exact prefixLift 6625458
  have htrace : WordTrace (prefixWord ++ tailWord_6625458) baseStart_6625458 baseEnd_6625458 := by
    simpa [prefixWord, tailWord_6625458, baseEnd_6625458] using wordTrace_append hprefix tailTrace_6625458
  have hstable : (prefixWord ++ tailWord_6625458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625458).length < 2 ^ (prefixWord ++ tailWord_6625458).sum := by decide
  have hdescent : baseEnd_6625458 < baseStart_6625458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625460 : List Nat := [2, 5, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_6625460 : Nat := 118140960795 + 6625460 * 2 ^ 59
def prefixEnd_6625460 : Nat := 4983230072969 + 3 ^ 40 * 6625460 * 2
def baseEnd_6625460 : Nat := 1134015179045917696993357

theorem tailTrace_6625460 : CollatzResearch.WordTrace tailWord_6625460 prefixEnd_6625460 1134015179045917696993357 := by
  unfold tailWord_6625460
  simp only [CollatzResearch.WordTrace]
  refine ⟨120825189288548716663364917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161100252384731622217819889 120825189288548716663364917)
  ·
    refine ⟨11327361495801442187190461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120825189288548716663364917 11327361495801442187190461)
    ·
      refine ⟨4247760560925540820196423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11327361495801442187190461 4247760560925540820196423)
      ·
        refine ⟨6371640841388311230294635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4247760560925540820196423 6371640841388311230294635)
        ·
          refine ⟨9557461262082466845441953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6371640841388311230294635 9557461262082466845441953)
          ·
            refine ⟨7168095946561850134081465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9557461262082466845441953 7168095946561850134081465)
            ·
              refine ⟨5376071959921387600561099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7168095946561850134081465 5376071959921387600561099)
              ·
                refine ⟨8064107939882081400841649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5376071959921387600561099 8064107939882081400841649)
                ·
                  refine ⟨6048080954911561050631237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8064107939882081400841649 6048080954911561050631237)
                  ·
                    refine ⟨1134015179045917696993357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6048080954911561050631237 1134015179045917696993357)
                    ·
                      rfl

theorem cell23_6625460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_6625460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625460 prefixEnd_6625460 := by exact prefixLift 6625460
  have htrace : WordTrace (prefixWord ++ tailWord_6625460) baseStart_6625460 baseEnd_6625460 := by
    simpa [prefixWord, tailWord_6625460, baseEnd_6625460] using wordTrace_append hprefix tailTrace_6625460
  have hstable : (prefixWord ++ tailWord_6625460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625460).length < 2 ^ (prefixWord ++ tailWord_6625460).sum := by decide
  have hdescent : baseEnd_6625460 < baseStart_6625460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625476 : List Nat := [2, 3, 3, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_6625476 : Nat := 118140960795 + 6625476 * 2 ^ 59
def prefixEnd_6625476 : Nat := 4983230072969 + 3 ^ 40 * 6625476 * 2
def baseEnd_6625476 : Nat := 3402053752828225028379997

theorem tailTrace_6625476 : CollatzResearch.WordTrace tailWord_6625476 prefixEnd_6625476 3402053752828225028379997 := by
  unfold tailWord_6625476
  simp only [CollatzResearch.WordTrace]
  refine ⟨120825481072519734029656141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161100641430026312039541521 120825481072519734029656141)
  ·
    refine ⟨45309555402194900261121053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120825481072519734029656141 45309555402194900261121053)
    ·
      refine ⟨16991083275823087597920395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45309555402194900261121053 16991083275823087597920395)
      ·
        refine ⟨25486624913734631396880593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16991083275823087597920395 25486624913734631396880593)
        ·
          refine ⟨19114968685300973547660445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25486624913734631396880593 19114968685300973547660445)
          ·
            refine ⟨7168113256987865080372667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19114968685300973547660445 7168113256987865080372667)
            ·
              refine ⟨10752169885481797620559001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7168113256987865080372667 10752169885481797620559001)
              ·
                refine ⟨8064127414111348215419251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10752169885481797620559001 8064127414111348215419251)
                ·
                  refine ⟨12096191121167022323128877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8064127414111348215419251 12096191121167022323128877)
                  ·
                    refine ⟨4536071670437633371173329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12096191121167022323128877 4536071670437633371173329)
                    ·
                      refine ⟨3402053752828225028379997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4536071670437633371173329 3402053752828225028379997)
                      ·
                        rfl

theorem cell23_6625476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_6625476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625476 prefixEnd_6625476 := by exact prefixLift 6625476
  have htrace : WordTrace (prefixWord ++ tailWord_6625476) baseStart_6625476 baseEnd_6625476 := by
    simpa [prefixWord, tailWord_6625476, baseEnd_6625476] using wordTrace_append hprefix tailTrace_6625476
  have hstable : (prefixWord ++ tailWord_6625476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625476).length < 2 ^ (prefixWord ++ tailWord_6625476).sum := by decide
  have hdescent : baseEnd_6625476 < baseStart_6625476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625495 : List Nat := [1, 1, 3, 2, 1, 2, 1, 7, 5]
def baseStart_6625495 : Nat := 118140960795 + 6625495 * 2 ^ 59
def prefixEnd_6625495 : Nat := 4983230072969 + 3 ^ 40 * 6625495 * 2
def baseEnd_6625495 : Nat := 378007056551184494893601

theorem tailTrace_6625495 : CollatzResearch.WordTrace tailWord_6625495 prefixEnd_6625495 378007056551184494893601 := by
  unfold tailWord_6625495
  simp only [CollatzResearch.WordTrace]
  refine ⟨241651655131970634304253939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161101103421313756202835959 241651655131970634304253939)
  ·
    refine ⟨362477482697955951456380909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241651655131970634304253939 362477482697955951456380909)
    ·
      refine ⟨135929056011733481796142841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362477482697955951456380909 135929056011733481796142841)
      ·
        refine ⟨101946792008800111347107131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135929056011733481796142841 101946792008800111347107131)
        ·
          refine ⟨152920188013200167020660697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101946792008800111347107131 152920188013200167020660697)
          ·
            refine ⟨114690141009900125265495523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152920188013200167020660697 114690141009900125265495523)
            ·
              refine ⟨172035211514850187898243285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114690141009900125265495523 172035211514850187898243285)
              ·
                refine ⟨4032075269879301278865077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 172035211514850187898243285 4032075269879301278865077)
                ·
                  refine ⟨378007056551184494893601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4032075269879301278865077 378007056551184494893601)
                  ·
                    rfl

theorem cell23_6625495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 5].length) (baseStart_6625495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625495 prefixEnd_6625495 := by exact prefixLift 6625495
  have htrace : WordTrace (prefixWord ++ tailWord_6625495) baseStart_6625495 baseEnd_6625495 := by
    simpa [prefixWord, tailWord_6625495, baseEnd_6625495] using wordTrace_append hprefix tailTrace_6625495
  have hstable : (prefixWord ++ tailWord_6625495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625495).length < 2 ^ (prefixWord ++ tailWord_6625495).sum := by decide
  have hdescent : baseEnd_6625495 < baseStart_6625495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625505 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 2, 3, 3]
def baseStart_6625505 : Nat := 118140960795 + 6625505 * 2 ^ 59
def prefixEnd_6625505 : Nat := 4983230072969 + 3 ^ 40 * 6625505 * 2
def baseEnd_6625505 : Nat := 3402068643767205414917363

theorem tailTrace_6625505 : CollatzResearch.WordTrace tailWord_6625505 prefixEnd_6625505 3402068643767205414917363 := by
  unfold tailWord_6625505
  simp only [CollatzResearch.WordTrace]
  refine ⟨241652019861934406012117969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161101346574622937341411979 241652019861934406012117969)
  ·
    refine ⟨181239014896450804509088477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241652019861934406012117969 181239014896450804509088477)
    ·
      refine ⟨67964630586169051690908179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181239014896450804509088477 67964630586169051690908179)
      ·
        refine ⟨101946945879253577536362269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67964630586169051690908179 101946945879253577536362269)
        ·
          refine ⟨38230104704720091576135851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101946945879253577536362269 38230104704720091576135851)
          ·
            refine ⟨57345157057080137364203777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38230104704720091576135851 57345157057080137364203777)
            ·
              refine ⟨43008867792810103023152833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57345157057080137364203777 43008867792810103023152833)
              ·
                refine ⟨32256650844607577267364625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43008867792810103023152833 32256650844607577267364625)
                ·
                  refine ⟨24192488133455682950523469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32256650844607577267364625 24192488133455682950523469)
                  ·
                    refine ⟨9072183050045881106446301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24192488133455682950523469 9072183050045881106446301)
                    ·
                      refine ⟨3402068643767205414917363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9072183050045881106446301 3402068643767205414917363)
                      ·
                        rfl

theorem cell23_6625505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_6625505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625505 prefixEnd_6625505 := by exact prefixLift 6625505
  have htrace : WordTrace (prefixWord ++ tailWord_6625505) baseStart_6625505 baseEnd_6625505 := by
    simpa [prefixWord, tailWord_6625505, baseEnd_6625505] using wordTrace_append hprefix tailTrace_6625505
  have hstable : (prefixWord ++ tailWord_6625505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625505).length < 2 ^ (prefixWord ++ tailWord_6625505).sum := by decide
  have hdescent : baseEnd_6625505 < baseStart_6625505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625508 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 3, 7]
def baseStart_6625508 : Nat := 118140960795 + 6625508 * 2 ^ 59
def prefixEnd_6625508 : Nat := 4983230072969 + 3 ^ 40 * 6625508 * 2
def baseEnd_6625508 : Nat := 1134023394736389634393283

theorem tailTrace_6625508 : CollatzResearch.WordTrace tailWord_6625508 prefixEnd_6625508 1134023394736389634393283 := by
  unfold tailWord_6625508
  simp only [CollatzResearch.WordTrace]
  refine ⟨120826064640461768762238589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161101419520615691682984785 120826064640461768762238589)
  ·
    refine ⟨45309774240173163285839471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120826064640461768762238589 45309774240173163285839471)
    ·
      refine ⟨67964661360259744928759207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45309774240173163285839471 67964661360259744928759207)
      ·
        refine ⟨101946992040389617393138811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67964661360259744928759207 101946992040389617393138811)
        ·
          refine ⟨152920488060584426089708217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101946992040389617393138811 152920488060584426089708217)
          ·
            refine ⟨114690366045438319567281163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152920488060584426089708217 114690366045438319567281163)
            ·
              refine ⟨172035549068157479350921745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114690366045438319567281163 172035549068157479350921745)
              ·
                refine ⟨129026661801118109513191309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172035549068157479350921745 129026661801118109513191309)
                ·
                  refine ⟨48384998175419291067446741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129026661801118109513191309 48384998175419291067446741)
                  ·
                    refine ⟨1134023394736389634393283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48384998175419291067446741 1134023394736389634393283)
                    ·
                      rfl

theorem cell23_6625508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_6625508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625508 prefixEnd_6625508 := by exact prefixLift 6625508
  have htrace : WordTrace (prefixWord ++ tailWord_6625508) baseStart_6625508 baseEnd_6625508 := by
    simpa [prefixWord, tailWord_6625508, baseEnd_6625508] using wordTrace_append hprefix tailTrace_6625508
  have hstable : (prefixWord ++ tailWord_6625508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625508).length < 2 ^ (prefixWord ++ tailWord_6625508).sum := by decide
  have hdescent : baseEnd_6625508 < baseStart_6625508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625512 : List Nat := [2, 1, 4, 1, 2, 3, 1, 4, 5]
def baseStart_6625512 : Nat := 118140960795 + 6625512 * 2 ^ 59
def prefixEnd_6625512 : Nat := 4983230072969 + 3 ^ 40 * 6625512 * 2
def baseEnd_6625512 : Nat := 378008026459087431947759

theorem tailTrace_6625512 : CollatzResearch.WordTrace tailWord_6625512 prefixEnd_6625512 378008026459087431947759 := by
  unfold tailWord_6625512
  simp only [CollatzResearch.WordTrace]
  refine ⟨120826137586454523103811395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161101516781939364138415193 120826137586454523103811395)
  ·
    refine ⟨181239206379681784655717093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120826137586454523103811395 181239206379681784655717093)
    ·
      refine ⟨33982351196190334622946955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181239206379681784655717093 33982351196190334622946955)
      ·
        refine ⟨50973526794285501934420433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33982351196190334622946955 50973526794285501934420433)
        ·
          refine ⟨38230145095714126450815325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50973526794285501934420433 38230145095714126450815325)
          ·
            refine ⟨14336304410892797419055747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38230145095714126450815325 14336304410892797419055747)
            ·
              refine ⟨21504456616339196128583621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14336304410892797419055747 21504456616339196128583621)
              ·
                refine ⟨4032085615563599274109429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21504456616339196128583621 4032085615563599274109429)
                ·
                  refine ⟨378008026459087431947759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4032085615563599274109429 378008026459087431947759)
                  ·
                    rfl

theorem cell23_6625512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 5].length) (baseStart_6625512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625512 prefixEnd_6625512 := by exact prefixLift 6625512
  have htrace : WordTrace (prefixWord ++ tailWord_6625512) baseStart_6625512 baseEnd_6625512 := by
    simpa [prefixWord, tailWord_6625512, baseEnd_6625512] using wordTrace_append hprefix tailTrace_6625512
  have hstable : (prefixWord ++ tailWord_6625512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625512).length < 2 ^ (prefixWord ++ tailWord_6625512).sum := by decide
  have hdescent : baseEnd_6625512 < baseStart_6625512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625515 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 1, 7, 2]
def baseStart_6625515 : Nat := 118140960795 + 6625515 * 2 ^ 59
def prefixEnd_6625515 : Nat := 4983230072969 + 3 ^ 40 * 6625515 * 2
def baseEnd_6625515 : Nat := 3402073778573750375792317

theorem tailTrace_6625515 : CollatzResearch.WordTrace tailWord_6625515 prefixEnd_6625515 3402073778573750375792317 := by
  unfold tailWord_6625515
  simp only [CollatzResearch.WordTrace]
  refine ⟨241652384591898177719981999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161101589727932118479987999 241652384591898177719981999)
  ·
    refine ⟨362478576887847266579972999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241652384591898177719981999 362478576887847266579972999)
    ·
      refine ⟨543717865331770899869959499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362478576887847266579972999 543717865331770899869959499)
      ·
        refine ⟨815576797997656349804939249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543717865331770899869959499 815576797997656349804939249)
        ·
          refine ⟨611682598498242262353704437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 815576797997656349804939249 611682598498242262353704437)
          ·
            refine ⟨57345243609210212095659791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 611682598498242262353704437 57345243609210212095659791)
            ·
              refine ⟨86017865413815318143489687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57345243609210212095659791 86017865413815318143489687)
              ·
                refine ⟨129026798120722977215234531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86017865413815318143489687 129026798120722977215234531)
                ·
                  refine ⟨193540197181084465822851797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129026798120722977215234531 193540197181084465822851797)
                  ·
                    refine ⟨4536098371431667167723089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 193540197181084465822851797 4536098371431667167723089)
                    ·
                      refine ⟨3402073778573750375792317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4536098371431667167723089 3402073778573750375792317)
                      ·
                        rfl

theorem cell23_6625515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 7, 2].length) (baseStart_6625515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625515 prefixEnd_6625515 := by exact prefixLift 6625515
  have htrace : WordTrace (prefixWord ++ tailWord_6625515) baseStart_6625515 baseEnd_6625515 := by
    simpa [prefixWord, tailWord_6625515, baseEnd_6625515] using wordTrace_append hprefix tailTrace_6625515
  have hstable : (prefixWord ++ tailWord_6625515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625515).length < 2 ^ (prefixWord ++ tailWord_6625515).sum := by decide
  have hdescent : baseEnd_6625515 < baseStart_6625515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625522 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 2, 3, 3]
def baseStart_6625522 : Nat := 118140960795 + 6625522 * 2 ^ 59
def prefixEnd_6625522 : Nat := 4983230072969 + 3 ^ 40 * 6625522 * 2
def baseEnd_6625522 : Nat := 3402077372938331848404785

theorem tailTrace_6625522 : CollatzResearch.WordTrace tailWord_6625522 prefixEnd_6625522 3402077372938331848404785 := by
  unfold tailWord_6625522
  simp only [CollatzResearch.WordTrace]
  refine ⟨60413159975718204478871705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161101759935248545276991213 60413159975718204478871705)
  ·
    refine ⟨45309869981788653359153779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60413159975718204478871705 45309869981788653359153779)
    ·
      refine ⟨67964804972682980038730669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45309869981788653359153779 67964804972682980038730669)
      ·
        refine ⟨25486801864756117514524001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67964804972682980038730669 25486801864756117514524001)
        ·
          refine ⟨19115101398567088135893001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25486801864756117514524001 19115101398567088135893001)
          ·
            refine ⟨14336326048925316101919751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19115101398567088135893001 14336326048925316101919751)
            ·
              refine ⟨21504489073387974152879627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14336326048925316101919751 21504489073387974152879627)
              ·
                refine ⟨32256733610081961229319441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21504489073387974152879627 32256733610081961229319441)
                ·
                  refine ⟨24192550207561470921989581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32256733610081961229319441 24192550207561470921989581)
                  ·
                    refine ⟨9072206327835551595746093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24192550207561470921989581 9072206327835551595746093)
                    ·
                      refine ⟨3402077372938331848404785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9072206327835551595746093 3402077372938331848404785)
                      ·
                        rfl

theorem cell23_6625522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_6625522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625522 prefixEnd_6625522 := by exact prefixLift 6625522
  have htrace : WordTrace (prefixWord ++ tailWord_6625522) baseStart_6625522 baseEnd_6625522 := by
    simpa [prefixWord, tailWord_6625522, baseEnd_6625522] using wordTrace_append hprefix tailTrace_6625522
  have hstable : (prefixWord ++ tailWord_6625522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625522).length < 2 ^ (prefixWord ++ tailWord_6625522).sum := by decide
  have hdescent : baseEnd_6625522 < baseStart_6625522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625545 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 1, 3, 4]
def baseStart_6625545 : Nat := 118140960795 + 6625545 * 2 ^ 59
def prefixEnd_6625545 : Nat := 4983230072969 + 3 ^ 40 * 6625545 * 2
def baseEnd_6625545 : Nat := 3402089182993385258417179

theorem tailTrace_6625545 : CollatzResearch.WordTrace tailWord_6625545 prefixEnd_6625545 3402089182993385258417179 := by
  unfold tailWord_6625545
  simp only [CollatzResearch.WordTrace]
  refine ⟨241653478781789492843574089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161102319187859661895716059 241653478781789492843574089)
  ·
    refine ⟨181240109086342119632680567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241653478781789492843574089 181240109086342119632680567)
    ·
      refine ⟨271860163629513179449020851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181240109086342119632680567 271860163629513179449020851)
      ·
        refine ⟨407790245444269769173531277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271860163629513179449020851 407790245444269769173531277)
        ·
          refine ⟨152921342041601163440074229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407790245444269769173531277 152921342041601163440074229)
          ·
            refine ⟨14336375816400109072506959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152921342041601163440074229 14336375816400109072506959)
            ·
              refine ⟨21504563724600163608760439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14336375816400109072506959 21504563724600163608760439)
              ·
                refine ⟨32256845586900245413140659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21504563724600163608760439 32256845586900245413140659)
                ·
                  refine ⟨48385268380350368119710989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32256845586900245413140659 48385268380350368119710989)
                  ·
                    refine ⟨18144475642631388044891621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48385268380350368119710989 18144475642631388044891621)
                    ·
                      refine ⟨3402089182993385258417179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18144475642631388044891621 3402089182993385258417179)
                      ·
                        rfl

theorem cell23_6625545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 3, 4].length) (baseStart_6625545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625545 prefixEnd_6625545 := by exact prefixLift 6625545
  have htrace : WordTrace (prefixWord ++ tailWord_6625545) baseStart_6625545 baseEnd_6625545 := by
    simpa [prefixWord, tailWord_6625545, baseEnd_6625545] using wordTrace_append hprefix tailTrace_6625545
  have hstable : (prefixWord ++ tailWord_6625545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625545).length < 2 ^ (prefixWord ++ tailWord_6625545).sum := by decide
  have hdescent : baseEnd_6625545 < baseStart_6625545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625572 : List Nat := [2, 3, 1, 3, 1, 2, 1, 3, 3, 4]
def baseStart_6625572 : Nat := 118140960795 + 6625572 * 2 ^ 59
def prefixEnd_6625572 : Nat := 4983230072969 + 3 ^ 40 * 6625572 * 2
def baseEnd_6625572 : Nat := 1134034348990352217593185

theorem tailTrace_6625572 : CollatzResearch.WordTrace tailWord_6625572 prefixEnd_6625572 1134034348990352217593185 := by
  unfold tailWord_6625572
  simp only [CollatzResearch.WordTrace]
  refine ⟨120827231776345838227403485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161102975701794450969871313 120827231776345838227403485)
  ·
    refine ⟨45310211916129689335276307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120827231776345838227403485 45310211916129689335276307)
    ·
      refine ⟨67965317874194534002914461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45310211916129689335276307 67965317874194534002914461)
      ·
        refine ⟨25486994202822950251092923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67965317874194534002914461 25486994202822950251092923)
        ·
          refine ⟨38230491304234425376639385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25486994202822950251092923 38230491304234425376639385)
          ·
            refine ⟨28672868478175819032479539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38230491304234425376639385 28672868478175819032479539)
            ·
              refine ⟨43009302717263728548719309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28672868478175819032479539 43009302717263728548719309)
              ·
                refine ⟨16128488518973898205769741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43009302717263728548719309 16128488518973898205769741)
                ·
                  refine ⟨6048183194615211827163653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16128488518973898205769741 6048183194615211827163653)
                  ·
                    refine ⟨1134034348990352217593185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6048183194615211827163653 1134034348990352217593185)
                    ·
                      rfl

theorem cell23_6625572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_6625572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625572 prefixEnd_6625572 := by exact prefixLift 6625572
  have htrace : WordTrace (prefixWord ++ tailWord_6625572) baseStart_6625572 baseEnd_6625572 := by
    simpa [prefixWord, tailWord_6625572, baseEnd_6625572] using wordTrace_append hprefix tailTrace_6625572
  have hstable : (prefixWord ++ tailWord_6625572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625572).length < 2 ^ (prefixWord ++ tailWord_6625572).sum := by decide
  have hdescent : baseEnd_6625572 < baseStart_6625572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625736 : List Nat := [2, 1, 3, 1, 3, 2, 3, 2, 2, 1, 3]
def baseStart_6625736 : Nat := 118140960795 + 6625736 * 2 ^ 59
def prefixEnd_6625736 : Nat := 4983230072969 + 3 ^ 40 * 6625736 * 2
def baseEnd_6625736 : Nat := 3402187257798394011128801

theorem tailTrace_6625736 : CollatzResearch.WordTrace tailWord_6625736 prefixEnd_6625736 3402187257798394011128801 := by
  unfold tailWord_6625736
  simp only [CollatzResearch.WordTrace]
  refine ⟨120830222562048766231888531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161106963416065021642518041 120830222562048766231888531)
  ·
    refine ⟨181245333843073149347832797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120830222562048766231888531 181245333843073149347832797)
    ·
      refine ⟨67967000191152431005437299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181245333843073149347832797 67967000191152431005437299)
      ·
        refine ⟨101950500286728646508155949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67967000191152431005437299 101950500286728646508155949)
        ·
          refine ⟨38231437607523242440558481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101950500286728646508155949 38231437607523242440558481)
          ·
            refine ⟨28673578205642431830418861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38231437607523242440558481 28673578205642431830418861)
            ·
              refine ⟨10752591827115911936407073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28673578205642431830418861 10752591827115911936407073)
              ·
                refine ⟨8064443870336933952305305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10752591827115911936407073 8064443870336933952305305)
                ·
                  refine ⟨6048332902752700464228979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8064443870336933952305305 6048332902752700464228979)
                  ·
                    refine ⟨9072499354129050696343469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6048332902752700464228979 9072499354129050696343469)
                    ·
                      refine ⟨3402187257798394011128801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9072499354129050696343469 3402187257798394011128801)
                      ·
                        rfl

theorem cell23_6625736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_6625736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625736 prefixEnd_6625736 := by exact prefixLift 6625736
  have htrace : WordTrace (prefixWord ++ tailWord_6625736) baseStart_6625736 baseEnd_6625736 := by
    simpa [prefixWord, tailWord_6625736, baseEnd_6625736] using wordTrace_append hprefix tailTrace_6625736
  have hstable : (prefixWord ++ tailWord_6625736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625736).length < 2 ^ (prefixWord ++ tailWord_6625736).sum := by decide
  have hdescent : baseEnd_6625736 < baseStart_6625736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625763 : List Nat := [1, 1, 1, 6, 3, 1, 2, 2, 1, 3, 2]
def baseStart_6625763 : Nat := 118140960795 + 6625763 * 2 ^ 59
def prefixEnd_6625763 : Nat := 4983230072969 + 3 ^ 40 * 6625763 * 2
def baseEnd_6625763 : Nat := 3402201121776065405491177

theorem tailTrace_6625763 : CollatzResearch.WordTrace tailWord_6625763 prefixEnd_6625763 3402201121776065405491177 := by
  unfold tailWord_6625763
  simp only [CollatzResearch.WordTrace]
  refine ⟨241661429894999716075009943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161107619929999810716673295 241661429894999716075009943)
  ·
    refine ⟨362492144842499574112514915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241661429894999716075009943 362492144842499574112514915)
    ·
      refine ⟨543738217263749361168772373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362492144842499574112514915 543738217263749361168772373)
      ·
        refine ⟨25487728934238251304786205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 543738217263749361168772373 25487728934238251304786205)
        ·
          refine ⟨9557898350339344239294827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25487728934238251304786205 9557898350339344239294827)
          ·
            refine ⟨14336847525509016358942241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9557898350339344239294827 14336847525509016358942241)
            ·
              refine ⟨10752635644131762269206681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14336847525509016358942241 10752635644131762269206681)
              ·
                refine ⟨8064476733098821701905011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10752635644131762269206681 8064476733098821701905011)
                ·
                  refine ⟨12096715099648232552857517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8064476733098821701905011 12096715099648232552857517)
                  ·
                    refine ⟨4536268162368087207321569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12096715099648232552857517 4536268162368087207321569)
                    ·
                      refine ⟨3402201121776065405491177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4536268162368087207321569 3402201121776065405491177)
                      ·
                        rfl

theorem cell23_6625763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_6625763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625763 prefixEnd_6625763 := by exact prefixLift 6625763
  have htrace : WordTrace (prefixWord ++ tailWord_6625763) baseStart_6625763 baseEnd_6625763 := by
    simpa [prefixWord, tailWord_6625763, baseEnd_6625763] using wordTrace_append hprefix tailTrace_6625763
  have hstable : (prefixWord ++ tailWord_6625763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625763).length < 2 ^ (prefixWord ++ tailWord_6625763).sum := by decide
  have hdescent : baseEnd_6625763 < baseStart_6625763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625846 : List Nat := [5, 1, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_6625846 : Nat := 118140960795 + 6625846 * 2 ^ 59
def prefixEnd_6625846 : Nat := 4983230072969 + 3 ^ 40 * 6625846 * 2
def baseEnd_6625846 : Nat := 1134081246890129526917765

theorem tailTrace_6625846 : CollatzResearch.WordTrace tailWord_6625846 prefixEnd_6625846 1134081246890129526917765 := by
  unfold tailWord_6625846
  simp only [CollatzResearch.WordTrace]
  refine ⟨15104028572106188828142587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161109638102466014166854261 15104028572106188828142587)
  ·
    refine ⟨22656042858159283242213881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15104028572106188828142587 22656042858159283242213881)
    ·
      refine ⟨16992032143619462431660411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22656042858159283242213881 16992032143619462431660411)
      ·
        refine ⟨25488048215429193647490617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16992032143619462431660411 25488048215429193647490617)
        ·
          refine ⟨19116036161571895235617963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25488048215429193647490617 19116036161571895235617963)
          ·
            refine ⟨28674054242357842853426945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19116036161571895235617963 28674054242357842853426945)
            ·
              refine ⟨21505540681768382140070209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28674054242357842853426945 21505540681768382140070209)
              ·
                refine ⟨16129155511326286605052657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21505540681768382140070209 16129155511326286605052657)
                ·
                  refine ⟨12096866633494714953789493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16129155511326286605052657 12096866633494714953789493)
                  ·
                    refine ⟨1134081246890129526917765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12096866633494714953789493 1134081246890129526917765)
                    ·
                      rfl

theorem cell23_6625846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_6625846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625846 prefixEnd_6625846 := by exact prefixLift 6625846
  have htrace : WordTrace (prefixWord ++ tailWord_6625846) baseStart_6625846 baseEnd_6625846 := by
    simpa [prefixWord, tailWord_6625846, baseEnd_6625846] using wordTrace_append hprefix tailTrace_6625846
  have hstable : (prefixWord ++ tailWord_6625846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625846).length < 2 ^ (prefixWord ++ tailWord_6625846).sum := by decide
  have hdescent : baseEnd_6625846 < baseStart_6625846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625849 : List Nat := [1, 2, 1, 5, 1, 1, 1, 4, 2, 1, 4]
def baseStart_6625849 : Nat := 118140960795 + 6625849 * 2 ^ 59
def prefixEnd_6625849 : Nat := 4983230072969 + 3 ^ 40 * 6625849 * 2
def baseEnd_6625849 : Nat := 3402245281112352069015781

theorem tailTrace_6625849 : CollatzResearch.WordTrace tailWord_6625849 prefixEnd_6625849 3402245281112352069015781 := by
  unfold tailWord_6625849
  simp only [CollatzResearch.WordTrace]
  refine ⟨241664566572688152762640601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161109711048458768508427067 241664566572688152762640601)
  ·
    refine ⟨181248424929516114571980451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241664566572688152762640601 181248424929516114571980451)
    ·
      refine ⟨271872637394274171857970677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181248424929516114571980451 271872637394274171857970677)
      ·
        refine ⟨25488059755713203611684751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 271872637394274171857970677 25488059755713203611684751)
        ·
          refine ⟨38232089633569805417527127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25488059755713203611684751 38232089633569805417527127)
          ·
            refine ⟨57348134450354708126290691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38232089633569805417527127 57348134450354708126290691)
            ·
              refine ⟨86022201675532062189436037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57348134450354708126290691 86022201675532062189436037)
              ·
                refine ⟨16129162814162261660519257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86022201675532062189436037 16129162814162261660519257)
                ·
                  refine ⟨12096872110621696245389443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16129162814162261660519257 12096872110621696245389443)
                  ·
                    refine ⟨18145308165932544368084165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12096872110621696245389443 18145308165932544368084165)
                    ·
                      refine ⟨3402245281112352069015781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18145308165932544368084165 3402245281112352069015781)
                      ·
                        rfl

theorem cell23_6625849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_6625849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625849 prefixEnd_6625849 := by exact prefixLift 6625849
  have htrace : WordTrace (prefixWord ++ tailWord_6625849) baseStart_6625849 baseEnd_6625849 := by
    simpa [prefixWord, tailWord_6625849, baseEnd_6625849] using wordTrace_append hprefix tailTrace_6625849
  have hstable : (prefixWord ++ tailWord_6625849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625849).length < 2 ^ (prefixWord ++ tailWord_6625849).sum := by decide
  have hdescent : baseEnd_6625849 < baseStart_6625849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625860 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_6625860 : Nat := 118140960795 + 6625860 * 2 ^ 59
def prefixEnd_6625860 : Nat := 4983230072969 + 3 ^ 40 * 6625860 * 2
def baseEnd_6625860 : Nat := 3402250929399551525978231

theorem tailTrace_6625860 : CollatzResearch.WordTrace tailWord_6625860 prefixEnd_6625860 3402250929399551525978231 := by
  unfold tailWord_6625860
  simp only [CollatzResearch.WordTrace]
  refine ⟨120832483887824150820645517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161109978517098867760860689 120832483887824150820645517)
  ·
    refine ⟨45312181457934056557742069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120832483887824150820645517 45312181457934056557742069)
    ·
      refine ⟨4248017011681317802288319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45312181457934056557742069 4248017011681317802288319)
      ·
        refine ⟨6372025517521976703432479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4248017011681317802288319 6372025517521976703432479)
        ·
          refine ⟨9558038276282965055148719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6372025517521976703432479 9558038276282965055148719)
          ·
            refine ⟨14337057414424447582723079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9558038276282965055148719 14337057414424447582723079)
            ·
              refine ⟨21505586121636671374084619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14337057414424447582723079 21505586121636671374084619)
              ·
                refine ⟨32258379182455007061126929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21505586121636671374084619 32258379182455007061126929)
                ·
                  refine ⟨24193784386841255295845197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32258379182455007061126929 24193784386841255295845197)
                  ·
                    refine ⟨9072669145065470735941949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24193784386841255295845197 9072669145065470735941949)
                    ·
                      refine ⟨3402250929399551525978231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9072669145065470735941949 3402250929399551525978231)
                      ·
                        rfl

theorem cell23_6625860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_6625860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625860 prefixEnd_6625860 := by exact prefixLift 6625860
  have htrace : WordTrace (prefixWord ++ tailWord_6625860) baseStart_6625860 baseEnd_6625860 := by
    simpa [prefixWord, tailWord_6625860, baseEnd_6625860] using wordTrace_append hprefix tailTrace_6625860
  have hstable : (prefixWord ++ tailWord_6625860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625860).length < 2 ^ (prefixWord ++ tailWord_6625860).sum := by decide
  have hdescent : baseEnd_6625860 < baseStart_6625860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625866 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 2, 4, 2]
def baseStart_6625866 : Nat := 118140960795 + 6625866 * 2 ^ 59
def prefixEnd_6625866 : Nat := 4983230072969 + 3 ^ 40 * 6625866 * 2
def baseEnd_6625866 : Nat := 3402254010283478502503203

theorem tailTrace_6625866 : CollatzResearch.WordTrace tailWord_6625866 prefixEnd_6625866 3402254010283478502503203 := by
  unfold tailWord_6625866
  simp only [CollatzResearch.WordTrace]
  refine ⟨60416296653406641166502363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161110124409084376444006301 60416296653406641166502363)
  ·
    refine ⟨90624444980109961749753545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60416296653406641166502363 90624444980109961749753545)
    ·
      refine ⟨67968333735082471312315159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90624444980109961749753545 67968333735082471312315159)
      ·
        refine ⟨101952500602623706968472739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67968333735082471312315159 101952500602623706968472739)
        ·
          refine ⟨152928750903935560452709109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101952500602623706968472739 152928750903935560452709109)
          ·
            refine ⟨14337070397243958792441479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152928750903935560452709109 14337070397243958792441479)
            ·
              refine ⟨21505605595865938188662219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14337070397243958792441479 21505605595865938188662219)
              ·
                refine ⟨32258408393798907282993329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21505605595865938188662219 32258408393798907282993329)
                ·
                  refine ⟨24193806295349180462244997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32258408393798907282993329 24193806295349180462244997)
                  ·
                    refine ⟨4536338680377971336670937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24193806295349180462244997 4536338680377971336670937)
                    ·
                      refine ⟨3402254010283478502503203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4536338680377971336670937 3402254010283478502503203)
                      ·
                        rfl

theorem cell23_6625866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_6625866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625866 prefixEnd_6625866 := by exact prefixLift 6625866
  have htrace : WordTrace (prefixWord ++ tailWord_6625866) baseStart_6625866 baseEnd_6625866 := by
    simpa [prefixWord, tailWord_6625866, baseEnd_6625866] using wordTrace_append hprefix tailTrace_6625866
  have hstable : (prefixWord ++ tailWord_6625866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625866).length < 2 ^ (prefixWord ++ tailWord_6625866).sum := by decide
  have hdescent : baseEnd_6625866 < baseStart_6625866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625876 : List Nat := [2, 4, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_6625876 : Nat := 118140960795 + 6625876 * 2 ^ 59
def prefixEnd_6625876 : Nat := 4983230072969 + 3 ^ 40 * 6625876 * 2
def baseEnd_6625876 : Nat := 1134086381696674487792719

theorem tailTrace_6625876 : CollatzResearch.WordTrace tailWord_6625876 prefixEnd_6625876 1134086381696674487792719 := by
  unfold tailWord_6625876
  simp only [CollatzResearch.WordTrace]
  refine ⟨120832775671795168186936741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161110367562393557582582321 120832775671795168186936741)
  ·
    refine ⟨22656145438461594035050639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120832775671795168186936741 22656145438461594035050639)
    ·
      refine ⟨33984218157692391052575959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22656145438461594035050639 33984218157692391052575959)
      ·
        refine ⟨50976327236538586578863939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33984218157692391052575959 50976327236538586578863939)
        ·
          refine ⟨76464490854807879868295909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50976327236538586578863939 76464490854807879868295909)
          ·
            refine ⟨14337092035276477475305483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76464490854807879868295909 14337092035276477475305483)
            ·
              refine ⟨21505638052914716212958225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14337092035276477475305483 21505638052914716212958225)
              ·
                refine ⟨16129228539686037159718669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21505638052914716212958225 16129228539686037159718669)
                ·
                  refine ⟨6048460702382263934894501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16129228539686037159718669 6048460702382263934894501)
                  ·
                    refine ⟨1134086381696674487792719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6048460702382263934894501 1134086381696674487792719)
                    ·
                      rfl

theorem cell23_6625876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_6625876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625876 prefixEnd_6625876 := by exact prefixLift 6625876
  have htrace : WordTrace (prefixWord ++ tailWord_6625876) baseStart_6625876 baseEnd_6625876 := by
    simpa [prefixWord, tailWord_6625876, baseEnd_6625876] using wordTrace_append hprefix tailTrace_6625876
  have hstable : (prefixWord ++ tailWord_6625876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625876).length < 2 ^ (prefixWord ++ tailWord_6625876).sum := by decide
  have hdescent : baseEnd_6625876 < baseStart_6625876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625912 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 2, 4, 5]
def baseStart_6625912 : Nat := 118140960795 + 6625912 * 2 ^ 59
def prefixEnd_6625912 : Nat := 4983230072969 + 3 ^ 40 * 6625912 * 2
def baseEnd_6625912 : Nat := 3402277630393585322527991

theorem tailTrace_6625912 : CollatzResearch.WordTrace tailWord_6625912 prefixEnd_6625912 3402277630393585322527991 := by
  unfold tailWord_6625912
  simp only [CollatzResearch.WordTrace]
  refine ⟨120833432185729957261091995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161111242914306609681455993 120833432185729957261091995)
  ·
    refine ⟨181250148278594935891637993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120833432185729957261091995 181250148278594935891637993)
    ·
      refine ⟨135937611208946201918728495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181250148278594935891637993 135937611208946201918728495)
      ·
        refine ⟨203906416813419302878092743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135937611208946201918728495 203906416813419302878092743)
        ·
          refine ⟨305859625220128954317139115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203906416813419302878092743 305859625220128954317139115)
          ·
            refine ⟨458789437830193431475708673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305859625220128954317139115 458789437830193431475708673)
            ·
              refine ⟨344092078372645073606781505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458789437830193431475708673 344092078372645073606781505)
              ·
                refine ⟨258069058779483805205086129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344092078372645073606781505 258069058779483805205086129)
                ·
                  refine ⟨193551794084612853903814597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258069058779483805205086129 193551794084612853903814597)
                  ·
                    refine ⟨36290961390864910106965237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 193551794084612853903814597 36290961390864910106965237)
                    ·
                      refine ⟨3402277630393585322527991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36290961390864910106965237 3402277630393585322527991)
                      ·
                        rfl

theorem cell23_6625912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_6625912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625912 prefixEnd_6625912 := by exact prefixLift 6625912
  have htrace : WordTrace (prefixWord ++ tailWord_6625912) baseStart_6625912 baseEnd_6625912 := by
    simpa [prefixWord, tailWord_6625912, baseEnd_6625912] using wordTrace_append hprefix tailTrace_6625912
  have hstable : (prefixWord ++ tailWord_6625912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625912).length < 2 ^ (prefixWord ++ tailWord_6625912).sum := by decide
  have hdescent : baseEnd_6625912 < baseStart_6625912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625916 : List Nat := [2, 2, 2, 1, 1, 2, 3, 3, 3, 1, 3]
def baseStart_6625916 : Nat := 118140960795 + 6625916 * 2 ^ 59
def prefixEnd_6625916 : Nat := 4983230072969 + 3 ^ 40 * 6625916 * 2
def baseEnd_6625916 : Nat := 3402279684316203306877973

theorem tailTrace_6625916 : CollatzResearch.WordTrace tailWord_6625916 prefixEnd_6625916 3402279684316203306877973 := by
  unfold tailWord_6625916
  simp only [CollatzResearch.WordTrace]
  refine ⟨120833505131722711602664801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161111340175630282136886401 120833505131722711602664801)
  ·
    refine ⟨90625128848792033701998601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120833505131722711602664801 90625128848792033701998601)
    ·
      refine ⟨67968846636594025276498951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90625128848792033701998601 67968846636594025276498951)
      ·
        refine ⟨101953269954891037914748427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67968846636594025276498951 101953269954891037914748427)
        ·
          refine ⟨152929904932336556872122641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101953269954891037914748427 152929904932336556872122641)
          ·
            refine ⟨114697428699252417654091981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152929904932336556872122641 114697428699252417654091981)
            ·
              refine ⟨43011535762219656620284493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114697428699252417654091981 43011535762219656620284493)
              ·
                refine ⟨16129325910832371232606685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43011535762219656620284493 16129325910832371232606685)
                ·
                  refine ⟨6048497216562139212227507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16129325910832371232606685 6048497216562139212227507)
                  ·
                    refine ⟨9072745824843208818341261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6048497216562139212227507 9072745824843208818341261)
                    ·
                      refine ⟨3402279684316203306877973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9072745824843208818341261 3402279684316203306877973)
                      ·
                        rfl

theorem cell23_6625916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_6625916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625916 prefixEnd_6625916 := by exact prefixLift 6625916
  have htrace : WordTrace (prefixWord ++ tailWord_6625916) baseStart_6625916 baseEnd_6625916 := by
    simpa [prefixWord, tailWord_6625916, baseEnd_6625916] using wordTrace_append hprefix tailTrace_6625916
  have hstable : (prefixWord ++ tailWord_6625916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625916).length < 2 ^ (prefixWord ++ tailWord_6625916).sum := by decide
  have hdescent : baseEnd_6625916 < baseStart_6625916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625949 : List Nat := [1, 4, 2, 1, 1, 1, 2, 4, 1, 6]
def baseStart_6625949 : Nat := 118140960795 + 6625949 * 2 ^ 59
def prefixEnd_6625949 : Nat := 4983230072969 + 3 ^ 40 * 6625949 * 2
def baseEnd_6625949 : Nat := 1134098876392600559255107

theorem tailTrace_6625949 : CollatzResearch.WordTrace tailWord_6625949 prefixEnd_6625949 1134098876392600559255107 := by
  unfold tailWord_6625949
  simp only [CollatzResearch.WordTrace]
  refine ⟨241668213872325869841280901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161112142581550579894187267 241668213872325869841280901)
  ·
    refine ⟨45312790101061100595240169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241668213872325869841280901 45312790101061100595240169)
    ·
      refine ⟨33984592575795825446430127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45312790101061100595240169 33984592575795825446430127)
      ·
        refine ⟨50976888863693738169645191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33984592575795825446430127 50976888863693738169645191)
        ·
          refine ⟨76465333295540607254467787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50976888863693738169645191 76465333295540607254467787)
          ·
            refine ⟨114697999943310910881701681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76465333295540607254467787 114697999943310910881701681)
            ·
              refine ⟨86023499957483183161276261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114697999943310910881701681 86023499957483183161276261)
              ·
                refine ⟨16129406242028096842739299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86023499957483183161276261 16129406242028096842739299)
                ·
                  refine ⟨24194109363042145264108949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16129406242028096842739299 24194109363042145264108949)
                  ·
                    refine ⟨1134098876392600559255107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24194109363042145264108949 1134098876392600559255107)
                    ·
                      rfl

theorem cell23_6625949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_6625949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625949 prefixEnd_6625949 := by exact prefixLift 6625949
  have htrace : WordTrace (prefixWord ++ tailWord_6625949) baseStart_6625949 baseEnd_6625949 := by
    simpa [prefixWord, tailWord_6625949, baseEnd_6625949] using wordTrace_append hprefix tailTrace_6625949
  have hstable : (prefixWord ++ tailWord_6625949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625949).length < 2 ^ (prefixWord ++ tailWord_6625949).sum := by decide
  have hdescent : baseEnd_6625949 < baseStart_6625949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625956 : List Nat := [2, 3, 1, 2, 2, 1, 1, 5, 1, 1, 4]
def baseStart_6625956 : Nat := 118140960795 + 6625956 * 2 ^ 59
def prefixEnd_6625956 : Nat := 4983230072969 + 3 ^ 40 * 6625956 * 2
def baseEnd_6625956 : Nat := 3402300223542383150377789

theorem tailTrace_6625956 : CollatzResearch.WordTrace tailWord_6625956 prefixEnd_6625956 3402300223542383150377789 := by
  unfold tailWord_6625956
  simp only [CollatzResearch.WordTrace]
  refine ⟨120834234591650255018392861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161112312788867006691190481 120834234591650255018392861)
  ·
    refine ⟨45312837971868845631897323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120834234591650255018392861 45312837971868845631897323)
    ·
      refine ⟨67969256957803268447845985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45312837971868845631897323 67969256957803268447845985)
      ·
        refine ⟨50976942718352451335884489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67969256957803268447845985 50976942718352451335884489)
        ·
          refine ⟨38232707038764338501913367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50976942718352451335884489 38232707038764338501913367)
          ·
            refine ⟨57349060558146507752870051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38232707038764338501913367 57349060558146507752870051)
            ·
              refine ⟨86023590837219761629305077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57349060558146507752870051 86023590837219761629305077)
              ·
                refine ⟨8064711640989352652747351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86023590837219761629305077 8064711640989352652747351)
                ·
                  refine ⟨12097067461484028979121027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8064711640989352652747351 12097067461484028979121027)
                  ·
                    refine ⟨18145601192226043468681541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12097067461484028979121027 18145601192226043468681541)
                    ·
                      refine ⟨3402300223542383150377789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18145601192226043468681541 3402300223542383150377789)
                      ·
                        rfl

theorem cell23_6625956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_6625956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625956 prefixEnd_6625956 := by exact prefixLift 6625956
  have htrace : WordTrace (prefixWord ++ tailWord_6625956) baseStart_6625956 baseEnd_6625956 := by
    simpa [prefixWord, tailWord_6625956, baseEnd_6625956] using wordTrace_append hprefix tailTrace_6625956
  have hstable : (prefixWord ++ tailWord_6625956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625956).length < 2 ^ (prefixWord ++ tailWord_6625956).sum := by decide
  have hdescent : baseEnd_6625956 < baseStart_6625956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6625983 : List Nat := [1, 1, 2, 2, 2, 4, 4, 1, 2, 4]
def baseStart_6625983 : Nat := 118140960795 + 6625983 * 2 ^ 59
def prefixEnd_6625983 : Nat := 4983230072969 + 3 ^ 40 * 6625983 * 2
def baseEnd_6625983 : Nat := 1134104695840018181580055

theorem tailTrace_6625983 : CollatzResearch.WordTrace tailWord_6625983 prefixEnd_6625983 1134104695840018181580055 := by
  unfold tailWord_6625983
  simp only [CollatzResearch.WordTrace]
  refine ⟨241669453954202693648018603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161112969302801795765345735 241669453954202693648018603)
  ·
    refine ⟨362504180931304040472027905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241669453954202693648018603 362504180931304040472027905)
    ·
      refine ⟨271878135698478030354020929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362504180931304040472027905 271878135698478030354020929)
      ·
        refine ⟨203908601773858522765515697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271878135698478030354020929 203908601773858522765515697)
        ·
          refine ⟨152931451330393892074136773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203908601773858522765515697 152931451330393892074136773)
          ·
            refine ⟨28674647124448854763900645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152931451330393892074136773 28674647124448854763900645)
            ·
              refine ⟨5376496335834160268231371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28674647124448854763900645 5376496335834160268231371)
              ·
                refine ⟨8064744503751240402347057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5376496335834160268231371 8064744503751240402347057)
                ·
                  refine ⟨6048558377813430301760293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8064744503751240402347057 6048558377813430301760293)
                  ·
                    refine ⟨1134104695840018181580055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6048558377813430301760293 1134104695840018181580055)
                    ·
                      rfl

theorem cell23_6625983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 2, 4].length) (baseStart_6625983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6625983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6625983 prefixEnd_6625983 := by exact prefixLift 6625983
  have htrace : WordTrace (prefixWord ++ tailWord_6625983) baseStart_6625983 baseEnd_6625983 := by
    simpa [prefixWord, tailWord_6625983, baseEnd_6625983] using wordTrace_append hprefix tailTrace_6625983
  have hstable : (prefixWord ++ tailWord_6625983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6625983).length < 2 ^ (prefixWord ++ tailWord_6625983).sum := by decide
  have hdescent : baseEnd_6625983 < baseStart_6625983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6625983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626037 : List Nat := [1, 3, 6, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_6626037 : Nat := 118140960795 + 6626037 * 2 ^ 59
def prefixEnd_6626037 : Nat := 4983230072969 + 3 ^ 40 * 6626037 * 2
def baseEnd_6626037 : Nat := 3402341815475397333464917

theorem tailTrace_6626037 : CollatzResearch.WordTrace tailWord_6626037 prefixEnd_6626037 3402341815475397333464917 := by
  unfold tailWord_6626037
  simp only [CollatzResearch.WordTrace]
  refine ⟨241671423496007060870484365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161114282330671373913656243 241671423496007060870484365)
  ·
    refine ⟨90626783811002647826431637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241671423496007060870484365 90626783811002647826431637)
    ·
      refine ⟨4248130491140749116863983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 90626783811002647826431637 4248130491140749116863983)
      ·
        refine ⟨6372195736711123675295975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4248130491140749116863983 6372195736711123675295975)
        ·
          refine ⟨9558293605066685512943963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6372195736711123675295975 9558293605066685512943963)
          ·
            refine ⟨14337440407600028269415945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9558293605066685512943963 14337440407600028269415945)
            ·
              refine ⟨10753080305700021202061959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14337440407600028269415945 10753080305700021202061959)
              ·
                refine ⟨16129620458550031803092939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10753080305700021202061959 16129620458550031803092939)
                ·
                  refine ⟨24194430687825047704639409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16129620458550031803092939 24194430687825047704639409)
                  ·
                    refine ⟨18145823015868785778479557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24194430687825047704639409 18145823015868785778479557)
                    ·
                      refine ⟨3402341815475397333464917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18145823015868785778479557 3402341815475397333464917)
                      ·
                        rfl

theorem cell23_6626037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_6626037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626037 prefixEnd_6626037 := by exact prefixLift 6626037
  have htrace : WordTrace (prefixWord ++ tailWord_6626037) baseStart_6626037 baseEnd_6626037 := by
    simpa [prefixWord, tailWord_6626037, baseEnd_6626037] using wordTrace_append hprefix tailTrace_6626037
  have hstable : (prefixWord ++ tailWord_6626037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626037).length < 2 ^ (prefixWord ++ tailWord_6626037).sum := by decide
  have hdescent : baseEnd_6626037 < baseStart_6626037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626050 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_6626050 : Nat := 118140960795 + 6626050 * 2 ^ 59
def prefixEnd_6626050 : Nat := 4983230072969 + 3 ^ 40 * 6626050 * 2
def baseEnd_6626050 : Nat := 3402348490723905782602357

theorem tailTrace_6626050 : CollatzResearch.WordTrace tailWord_6626050 prefixEnd_6626050 3402348490723905782602357 := by
  unfold tailWord_6626050
  simp only [CollatzResearch.WordTrace]
  refine ⟨60417974411239991022676901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161114598429973309393805069 60417974411239991022676901)
  ·
    refine ⟨11328370202107498316751919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60417974411239991022676901 11328370202107498316751919)
    ·
      refine ⟨16992555303161247475127879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11328370202107498316751919 16992555303161247475127879)
      ·
        refine ⟨25488832954741871212691819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16992555303161247475127879 25488832954741871212691819)
        ·
          refine ⟨38233249432112806819037729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25488832954741871212691819 38233249432112806819037729)
          ·
            refine ⟨28674937074084605114278297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38233249432112806819037729 28674937074084605114278297)
            ·
              refine ⟨21506202805563453835708723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28674937074084605114278297 21506202805563453835708723)
              ·
                refine ⟨32259304208345180753563085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21506202805563453835708723 32259304208345180753563085)
                ·
                  refine ⟨12097239078129442782586157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32259304208345180753563085 12097239078129442782586157)
                  ·
                    refine ⟨4536464654298541043469809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12097239078129442782586157 4536464654298541043469809)
                    ·
                      refine ⟨3402348490723905782602357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4536464654298541043469809 3402348490723905782602357)
                      ·
                        rfl

theorem cell23_6626050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_6626050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626050 prefixEnd_6626050 := by exact prefixLift 6626050
  have htrace : WordTrace (prefixWord ++ tailWord_6626050) baseStart_6626050 baseEnd_6626050 := by
    simpa [prefixWord, tailWord_6626050, baseEnd_6626050] using wordTrace_append hprefix tailTrace_6626050
  have hstable : (prefixWord ++ tailWord_6626050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626050).length < 2 ^ (prefixWord ++ tailWord_6626050).sum := by decide
  have hdescent : baseEnd_6626050 < baseStart_6626050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626059 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 4]
def baseStart_6626059 : Nat := 118140960795 + 6626059 * 2 ^ 59
def prefixEnd_6626059 : Nat := 4983230072969 + 3 ^ 40 * 6626059 * 2
def baseEnd_6626059 : Nat := 3402353112049796247389815

theorem tailTrace_6626059 : CollatzResearch.WordTrace tailWord_6626059 prefixEnd_6626059 3402353112049796247389815 := by
  unfold tailWord_6626059
  simp only [CollatzResearch.WordTrace]
  refine ⟨241672225901927358627785231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161114817267951572418523487 241672225901927358627785231)
  ·
    refine ⟨362508338852891037941677847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241672225901927358627785231 362508338852891037941677847)
    ·
      refine ⟨543762508279336556912516771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362508338852891037941677847 543762508279336556912516771)
      ·
        refine ⟨815643762419004835368775157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543762508279336556912516771 815643762419004835368775157)
        ·
          refine ⟨76466602726781703315822671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 815643762419004835368775157 76466602726781703315822671)
          ·
            refine ⟨114699904090172554973734007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76466602726781703315822671 114699904090172554973734007)
            ·
              refine ⟨172049856135258832460601011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114699904090172554973734007 172049856135258832460601011)
              ·
                refine ⟨258074784202888248690901517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172049856135258832460601011 258074784202888248690901517)
                ·
                  refine ⟨96778044076083093259088069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 258074784202888248690901517 96778044076083093259088069)
                  ·
                    refine ⟨18145883264265579986079013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96778044076083093259088069 18145883264265579986079013)
                    ·
                      refine ⟨3402353112049796247389815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18145883264265579986079013 3402353112049796247389815)
                      ·
                        rfl

theorem cell23_6626059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 4].length) (baseStart_6626059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626059 prefixEnd_6626059 := by exact prefixLift 6626059
  have htrace : WordTrace (prefixWord ++ tailWord_6626059) baseStart_6626059 baseEnd_6626059 := by
    simpa [prefixWord, tailWord_6626059, baseEnd_6626059] using wordTrace_append hprefix tailTrace_6626059
  have hstable : (prefixWord ++ tailWord_6626059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626059).length < 2 ^ (prefixWord ++ tailWord_6626059).sum := by decide
  have hdescent : baseEnd_6626059 < baseStart_6626059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626063 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 4, 2, 2]
def baseStart_6626063 : Nat := 118140960795 + 6626063 * 2 ^ 59
def prefixEnd_6626063 : Nat := 4983230072969 + 3 ^ 40 * 6626063 * 2
def baseEnd_6626063 : Nat := 3402355165972414231739797

theorem tailTrace_6626063 : CollatzResearch.WordTrace tailWord_6626063 prefixEnd_6626063 3402355165972414231739797 := by
  unfold tailWord_6626063
  simp only [CollatzResearch.WordTrace]
  refine ⟨241672371793912867310930843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161114914529275244873953895 241672371793912867310930843)
  ·
    refine ⟨362508557690869300966396265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241672371793912867310930843 362508557690869300966396265)
    ·
      refine ⟨271881418268151975724797199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362508557690869300966396265 271881418268151975724797199)
      ·
        refine ⟨407822127402227963587195799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271881418268151975724797199 407822127402227963587195799)
        ·
          refine ⟨611733191103341945380793699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407822127402227963587195799 611733191103341945380793699)
          ·
            refine ⟨917599786655012918071190549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611733191103341945380793699 917599786655012918071190549)
            ·
              refine ⟨43012489999453730534587057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 917599786655012918071190549 43012489999453730534587057)
              ·
                refine ⟨32259367499590297900940293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43012489999453730534587057 32259367499590297900940293)
                ·
                  refine ⟨6048631406173180856426305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32259367499590297900940293 6048631406173180856426305)
                  ·
                    refine ⟨4536473554629885642319729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6048631406173180856426305 4536473554629885642319729)
                    ·
                      refine ⟨3402355165972414231739797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4536473554629885642319729 3402355165972414231739797)
                      ·
                        rfl

theorem cell23_6626063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 2, 2].length) (baseStart_6626063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626063 prefixEnd_6626063 := by exact prefixLift 6626063
  have htrace : WordTrace (prefixWord ++ tailWord_6626063) baseStart_6626063 baseEnd_6626063 := by
    simpa [prefixWord, tailWord_6626063, baseEnd_6626063] using wordTrace_append hprefix tailTrace_6626063
  have hstable : (prefixWord ++ tailWord_6626063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626063).length < 2 ^ (prefixWord ++ tailWord_6626063).sum := by decide
  have hdescent : baseEnd_6626063 < baseStart_6626063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626069 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 9]
def baseStart_6626069 : Nat := 118140960795 + 6626069 * 2 ^ 59
def prefixEnd_6626069 : Nat := 4983230072969 + 3 ^ 40 * 6626069 * 2
def baseEnd_6626069 : Nat := 378039805206260134251641

theorem tailTrace_6626069 : CollatzResearch.WordTrace tailWord_6626069 prefixEnd_6626069 378039805206260134251641 := by
  unfold tailWord_6626069
  simp only [CollatzResearch.WordTrace]
  refine ⟨241672590631891130335649261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161115060421260753557099507 241672590631891130335649261)
  ·
    refine ⟨90627221486959173875868473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241672590631891130335649261 90627221486959173875868473)
    ·
      refine ⟨67970416115219380406901355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90627221486959173875868473 67970416115219380406901355)
      ·
        refine ⟨101955624172829070610352033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67970416115219380406901355 101955624172829070610352033)
        ·
          refine ⟨76466718129621802957764025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101955624172829070610352033 76466718129621802957764025)
          ·
            refine ⟨57350038597216352218323019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76466718129621802957764025 57350038597216352218323019)
            ·
              refine ⟨86025057895824528327484529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57350038597216352218323019 86025057895824528327484529)
              ·
                refine ⟨64518793421868396245613397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86025057895824528327484529 64518793421868396245613397)
                ·
                  refine ⟨378039805206260134251641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64518793421868396245613397 378039805206260134251641)
                  ·
                    rfl

theorem cell23_6626069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 9].length) (baseStart_6626069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626069 prefixEnd_6626069 := by exact prefixLift 6626069
  have htrace : WordTrace (prefixWord ++ tailWord_6626069) baseStart_6626069 baseEnd_6626069 := by
    simpa [prefixWord, tailWord_6626069, baseEnd_6626069] using wordTrace_append hprefix tailTrace_6626069
  have hstable : (prefixWord ++ tailWord_6626069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626069).length < 2 ^ (prefixWord ++ tailWord_6626069).sum := by decide
  have hdescent : baseEnd_6626069 < baseStart_6626069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626076 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_6626076 : Nat := 118140960795 + 6626076 * 2 ^ 59
def prefixEnd_6626076 : Nat := 4983230072969 + 3 ^ 40 * 6626076 * 2
def baseEnd_6626076 : Nat := 3402361841220922680877237

theorem tailTrace_6626076 : CollatzResearch.WordTrace tailWord_6626076 prefixEnd_6626076 3402361841220922680877237 := by
  unfold tailWord_6626076
  simp only [CollatzResearch.WordTrace]
  refine ⟨120836422971432885265577041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161115230628577180354102721 120836422971432885265577041)
  ·
    refine ⟨90627317228574663949182781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120836422971432885265577041 90627317228574663949182781)
    ·
      refine ⟨33985243960715498980943543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90627317228574663949182781 33985243960715498980943543)
      ·
        refine ⟨50977865941073248471415315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33985243960715498980943543 50977865941073248471415315)
        ·
          refine ⟨76466798911609872707122973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50977865941073248471415315 76466798911609872707122973)
          ·
            refine ⟨28675049591853702265171115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76466798911609872707122973 28675049591853702265171115)
            ·
              refine ⟨43012574387780553397756673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28675049591853702265171115 43012574387780553397756673)
              ·
                refine ⟨32259430790835415048317505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43012574387780553397756673 32259430790835415048317505)
                ·
                  refine ⟨24194573093126561286238129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32259430790835415048317505 24194573093126561286238129)
                  ·
                    refine ⟨18145929819844920964678597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24194573093126561286238129 18145929819844920964678597)
                    ·
                      refine ⟨3402361841220922680877237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18145929819844920964678597 3402361841220922680877237)
                      ·
                        rfl

theorem cell23_6626076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_6626076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626076 prefixEnd_6626076 := by exact prefixLift 6626076
  have htrace : WordTrace (prefixWord ++ tailWord_6626076) baseStart_6626076 baseEnd_6626076 := by
    simpa [prefixWord, tailWord_6626076, baseEnd_6626076] using wordTrace_append hprefix tailTrace_6626076
  have hstable : (prefixWord ++ tailWord_6626076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626076).length < 2 ^ (prefixWord ++ tailWord_6626076).sum := by decide
  have hdescent : baseEnd_6626076 < baseStart_6626076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626080 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 4, 2, 2]
def baseStart_6626080 : Nat := 118140960795 + 6626080 * 2 ^ 59
def prefixEnd_6626080 : Nat := 4983230072969 + 3 ^ 40 * 6626080 * 2
def baseEnd_6626080 : Nat := 3402363895143540665227219

theorem tailTrace_6626080 : CollatzResearch.WordTrace tailWord_6626080 prefixEnd_6626080 3402363895143540665227219 := by
  unfold tailWord_6626080
  simp only [CollatzResearch.WordTrace]
  refine ⟨120836495917425639607149847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161115327889900852809533129 120836495917425639607149847)
  ·
    refine ⟨181254743876138459410724771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120836495917425639607149847 181254743876138459410724771)
    ·
      refine ⟨271882115814207689116087157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181254743876138459410724771 271882115814207689116087157)
      ·
        refine ⟨25488948357581970854633171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 271882115814207689116087157 25488948357581970854633171)
        ·
          refine ⟨38233422536372956281949757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25488948357581970854633171 38233422536372956281949757)
          ·
            refine ⟨14337533451139858605731159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38233422536372956281949757 14337533451139858605731159)
            ·
              refine ⟨21506300176709787908596739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14337533451139858605731159 21506300176709787908596739)
              ·
                refine ⟨32259450265064681862895109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21506300176709787908596739 32259450265064681862895109)
                ·
                  refine ⟨6048646924699627849292833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32259450265064681862895109 6048646924699627849292833)
                  ·
                    refine ⟨4536485193524720886969625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6048646924699627849292833 4536485193524720886969625)
                    ·
                      refine ⟨3402363895143540665227219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4536485193524720886969625 3402363895143540665227219)
                      ·
                        rfl

theorem cell23_6626080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_6626080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626080 prefixEnd_6626080 := by exact prefixLift 6626080
  have htrace : WordTrace (prefixWord ++ tailWord_6626080) baseStart_6626080 baseEnd_6626080 := by
    simpa [prefixWord, tailWord_6626080, baseEnd_6626080] using wordTrace_append hprefix tailTrace_6626080
  have hstable : (prefixWord ++ tailWord_6626080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626080).length < 2 ^ (prefixWord ++ tailWord_6626080).sum := by decide
  have hdescent : baseEnd_6626080 < baseStart_6626080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626097 : List Nat := [1, 2, 2, 3, 2, 1, 5, 1, 2, 2, 2]
def baseStart_6626097 : Nat := 118140960795 + 6626097 * 2 ^ 59
def prefixEnd_6626097 : Nat := 4983230072969 + 3 ^ 40 * 6626097 * 2
def baseEnd_6626097 : Nat := 3402372624314667098714641

theorem tailTrace_6626097 : CollatzResearch.WordTrace tailWord_6626097 prefixEnd_6626097 3402372624314667098714641 := by
  unfold tailWord_6626097
  simp only [CollatzResearch.WordTrace]
  refine ⟨241673611875789691117668545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161115741250526460745112363 241673611875789691117668545)
  ·
    refine ⟨181255208906842268338251409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241673611875789691117668545 181255208906842268338251409)
    ·
      refine ⟨135941406680131701253688557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181255208906842268338251409 135941406680131701253688557)
      ·
        refine ⟨50978027505049387970133209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135941406680131701253688557 50978027505049387970133209)
        ·
          refine ⟨38233520628787040977599907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50978027505049387970133209 38233520628787040977599907)
          ·
            refine ⟨57350280943180561466399861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38233520628787040977599907 57350280943180561466399861)
            ·
              refine ⟨5376588838423177637474987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57350280943180561466399861 5376588838423177637474987)
              ·
                refine ⟨8064883257634766456212481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5376588838423177637474987 8064883257634766456212481)
                ·
                  refine ⟨6048662443226074842159361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8064883257634766456212481 6048662443226074842159361)
                  ·
                    refine ⟨4536496832419556131619521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6048662443226074842159361 4536496832419556131619521)
                    ·
                      refine ⟨3402372624314667098714641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4536496832419556131619521 3402372624314667098714641)
                      ·
                        rfl

theorem cell23_6626097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_6626097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626097 prefixEnd_6626097 := by exact prefixLift 6626097
  have htrace : WordTrace (prefixWord ++ tailWord_6626097) baseStart_6626097 baseEnd_6626097 := by
    simpa [prefixWord, tailWord_6626097, baseEnd_6626097] using wordTrace_append hprefix tailTrace_6626097
  have hstable : (prefixWord ++ tailWord_6626097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626097).length < 2 ^ (prefixWord ++ tailWord_6626097).sum := by decide
  have hdescent : baseEnd_6626097 < baseStart_6626097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626173 : List Nat := [1, 4, 1, 1, 2, 1, 3, 3, 2, 2, 3]
def baseStart_6626173 : Nat := 118140960795 + 6626173 * 2 ^ 59
def prefixEnd_6626173 : Nat := 4983230072969 + 3 ^ 40 * 6626173 * 2
def baseEnd_6626173 : Nat := 3402411648844408801364291

theorem tailTrace_6626173 : CollatzResearch.WordTrace tailWord_6626173 prefixEnd_6626173 3402411648844408801364291 := by
  unfold tailWord_6626173
  simp only [CollatzResearch.WordTrace]
  refine ⟨241676383823514356097435173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161117589215676237398290115 241676383823514356097435173)
  ·
    refine ⟨45314321966908941768269095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241676383823514356097435173 45314321966908941768269095)
    ·
      refine ⟨67971482950363412652403643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45314321966908941768269095 67971482950363412652403643)
      ·
        refine ⟨101957224425545118978605465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67971482950363412652403643 101957224425545118978605465)
        ·
          refine ⟨76467918319158839233954099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101957224425545118978605465 76467918319158839233954099)
          ·
            refine ⟨114701877478738258850931149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76467918319158839233954099 114701877478738258850931149)
            ·
              refine ⟨43013204054526847069099181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114701877478738258850931149 43013204054526847069099181)
              ·
                refine ⟨16129951520447567650912193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43013204054526847069099181 16129951520447567650912193)
                ·
                  refine ⟨12097463640335675738184145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16129951520447567650912193 12097463640335675738184145)
                  ·
                    refine ⟨9073097730251756803638109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12097463640335675738184145 9073097730251756803638109)
                    ·
                      refine ⟨3402411648844408801364291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9073097730251756803638109 3402411648844408801364291)
                      ·
                        rfl

theorem cell23_6626173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_6626173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626173 prefixEnd_6626173 := by exact prefixLift 6626173
  have htrace : WordTrace (prefixWord ++ tailWord_6626173) baseStart_6626173 baseEnd_6626173 := by
    simpa [prefixWord, tailWord_6626173, baseEnd_6626173] using wordTrace_append hprefix tailTrace_6626173
  have hstable : (prefixWord ++ tailWord_6626173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626173).length < 2 ^ (prefixWord ++ tailWord_6626173).sum := by decide
  have hdescent : baseEnd_6626173 < baseStart_6626173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626180 : List Nat := [2, 3, 2, 1, 1, 1, 1, 7, 1, 4]
def baseStart_6626180 : Nat := 118140960795 + 6626180 * 2 ^ 59
def prefixEnd_6626180 : Nat := 4983230072969 + 3 ^ 40 * 6626180 * 2
def baseEnd_6626180 : Nat := 1134138414402996757992253

theorem tailTrace_6626180 : CollatzResearch.WordTrace tailWord_6626180 prefixEnd_6626180 1134138414402996757992253 := by
  unfold tailWord_6626180
  simp only [CollatzResearch.WordTrace]
  refine ⟨120838319567244498146469997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161117759422992664195293329 120838319567244498146469997)
  ·
    refine ⟨45314369837716686804926249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120838319567244498146469997 45314369837716686804926249)
    ·
      refine ⟨33985777378287515103694687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45314369837716686804926249 33985777378287515103694687)
      ·
        refine ⟨50978666067431272655542031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33985777378287515103694687 50978666067431272655542031)
        ·
          refine ⟨76467999101146908983313047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50978666067431272655542031 76467999101146908983313047)
          ·
            refine ⟨114701998651720363474969571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76467999101146908983313047 114701998651720363474969571)
            ·
              refine ⟨172052997977580545212454357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114701998651720363474969571 172052997977580545212454357)
              ·
                refine ⟨4032492140099544028416899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 172052997977580545212454357 4032492140099544028416899)
                ·
                  refine ⟨6048738210149316042625349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4032492140099544028416899 6048738210149316042625349)
                  ·
                    refine ⟨1134138414402996757992253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6048738210149316042625349 1134138414402996757992253)
                    ·
                      rfl

theorem cell23_6626180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_6626180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626180 prefixEnd_6626180 := by exact prefixLift 6626180
  have htrace : WordTrace (prefixWord ++ tailWord_6626180) baseStart_6626180 baseEnd_6626180 := by
    simpa [prefixWord, tailWord_6626180, baseEnd_6626180] using wordTrace_append hprefix tailTrace_6626180
  have hstable : (prefixWord ++ tailWord_6626180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626180).length < 2 ^ (prefixWord ++ tailWord_6626180).sum := by decide
  have hdescent : baseEnd_6626180 < baseStart_6626180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626197 : List Nat := [1, 3, 2, 1, 1, 4, 4, 2, 1, 4]
def baseStart_6626197 : Nat := 118140960795 + 6626197 * 2 ^ 59
def prefixEnd_6626197 : Nat := 4983230072969 + 3 ^ 40 * 6626197 * 2
def baseEnd_6626197 : Nat := 1134141324126705569154727

theorem tailTrace_6626197 : CollatzResearch.WordTrace tailWord_6626197 prefixEnd_6626197 1134141324126705569154727 := by
  unfold tailWord_6626197
  simp only [CollatzResearch.WordTrace]
  refine ⟨241677259175427408196308845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161118172783618272130872563 241677259175427408196308845)
  ·
    refine ⟨90628972190785278073615817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241677259175427408196308845 90628972190785278073615817)
    ·
      refine ⟨67971729143088958555211863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90628972190785278073615817 67971729143088958555211863)
      ·
        refine ⟨101957593714633437832817795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67971729143088958555211863 101957593714633437832817795)
        ·
          refine ⟨152936390571950156749226693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101957593714633437832817795 152936390571950156749226693)
          ·
            refine ⟨28675573232240654390480005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152936390571950156749226693 28675573232240654390480005)
            ·
              refine ⟨5376669981045122698215001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28675573232240654390480005 5376669981045122698215001)
              ·
                refine ⟨4032502485783842023661251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5376669981045122698215001 4032502485783842023661251)
                ·
                  refine ⟨6048753728675763035491877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4032502485783842023661251 6048753728675763035491877)
                  ·
                    refine ⟨1134141324126705569154727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6048753728675763035491877 1134141324126705569154727)
                    ·
                      rfl

theorem cell23_6626197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_6626197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626197 prefixEnd_6626197 := by exact prefixLift 6626197
  have htrace : WordTrace (prefixWord ++ tailWord_6626197) baseStart_6626197 baseEnd_6626197 := by
    simpa [prefixWord, tailWord_6626197, baseEnd_6626197] using wordTrace_append hprefix tailTrace_6626197
  have hstable : (prefixWord ++ tailWord_6626197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626197).length < 2 ^ (prefixWord ++ tailWord_6626197).sum := by decide
  have hdescent : baseEnd_6626197 < baseStart_6626197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626240 : List Nat := [2, 1, 1, 2, 3, 3, 4, 1, 1, 5]
def baseStart_6626240 : Nat := 118140960795 + 6626240 * 2 ^ 59
def prefixEnd_6626240 : Nat := 4983230072969 + 3 ^ 40 * 6626240 * 2
def baseEnd_6626240 : Nat := 1134148684016086679742161

theorem tailTrace_6626240 : CollatzResearch.WordTrace tailWord_6626240 prefixEnd_6626240 1134148684016086679742161 := by
  unfold tailWord_6626240
  simp only [CollatzResearch.WordTrace]
  refine ⟨120839413757135813270062087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161119218342847751026749449 120839413757135813270062087)
  ·
    refine ⟨181259120635703719905093131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120839413757135813270062087 181259120635703719905093131)
    ·
      refine ⟨271888680953555579857639697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181259120635703719905093131 271888680953555579857639697)
      ·
        refine ⟨203916510715166684893229773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271888680953555579857639697 203916510715166684893229773)
        ·
          refine ⟨76468691518187506834961165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203916510715166684893229773 76468691518187506834961165)
          ·
            refine ⟨28675759319320315063110437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76468691518187506834961165 28675759319320315063110437)
            ·
              refine ⟨5376704872372559074333207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28675759319320315063110437 5376704872372559074333207)
              ·
                refine ⟨8065057308558838611499811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5376704872372559074333207 8065057308558838611499811)
                ·
                  refine ⟨12097585962838257917249717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8065057308558838611499811 12097585962838257917249717)
                  ·
                    refine ⟨1134148684016086679742161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12097585962838257917249717 1134148684016086679742161)
                    ·
                      rfl

theorem cell23_6626240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 1, 5].length) (baseStart_6626240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626240 prefixEnd_6626240 := by exact prefixLift 6626240
  have htrace : WordTrace (prefixWord ++ tailWord_6626240) baseStart_6626240 baseEnd_6626240 := by
    simpa [prefixWord, tailWord_6626240, baseEnd_6626240] using wordTrace_append hprefix tailTrace_6626240
  have hstable : (prefixWord ++ tailWord_6626240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626240).length < 2 ^ (prefixWord ++ tailWord_6626240).sum := by decide
  have hdescent : baseEnd_6626240 < baseStart_6626240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626243 : List Nat := [1, 1, 1, 3, 1, 1, 2, 7, 1, 1, 4]
def baseStart_6626243 : Nat := 118140960795 + 6626243 * 2 ^ 59
def prefixEnd_6626243 : Nat := 4983230072969 + 3 ^ 40 * 6626243 * 2
def baseEnd_6626243 : Nat := 3402447592490223527488969

theorem tailTrace_6626243 : CollatzResearch.WordTrace tailWord_6626243 prefixEnd_6626243 3402447592490223527488969 := by
  unfold tailWord_6626243
  simp only [CollatzResearch.WordTrace]
  refine ⟨241678936933260758052483383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161119291288840505368322255 241678936933260758052483383)
  ·
    refine ⟨362518405399891137078725075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241678936933260758052483383 362518405399891137078725075)
    ·
      refine ⟨543777608099836705618087613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362518405399891137078725075 543777608099836705618087613)
      ·
        refine ⟨203916603037438764606782855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 543777608099836705618087613 203916603037438764606782855)
        ·
          refine ⟨305874904556158146910174283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203916603037438764606782855 305874904556158146910174283)
          ·
            refine ⟨458812356834237220365261425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305874904556158146910174283 458812356834237220365261425)
            ·
              refine ⟨344109267625677915273946069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458812356834237220365261425 344109267625677915273946069)
              ·
                refine ⟨8065060959976826139233111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 344109267625677915273946069 8065060959976826139233111)
                ·
                  refine ⟨12097591439965239208849667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8065060959976826139233111 12097591439965239208849667)
                  ·
                    refine ⟨18146387159947858813274501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12097591439965239208849667 18146387159947858813274501)
                    ·
                      refine ⟨3402447592490223527488969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18146387159947858813274501 3402447592490223527488969)
                      ·
                        rfl

theorem cell23_6626243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 1, 4].length) (baseStart_6626243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626243 prefixEnd_6626243 := by exact prefixLift 6626243
  have htrace : WordTrace (prefixWord ++ tailWord_6626243) baseStart_6626243 baseEnd_6626243 := by
    simpa [prefixWord, tailWord_6626243, baseEnd_6626243] using wordTrace_append hprefix tailTrace_6626243
  have hstable : (prefixWord ++ tailWord_6626243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626243).length < 2 ^ (prefixWord ++ tailWord_6626243).sum := by decide
  have hdescent : baseEnd_6626243 < baseStart_6626243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626244 : List Nat := [2, 3, 3, 3, 2, 1, 1, 2, 6]
def baseStart_6626244 : Nat := 118140960795 + 6626244 * 2 ^ 59
def prefixEnd_6626244 : Nat := 4983230072969 + 3 ^ 40 * 6626244 * 2
def baseEnd_6626244 : Nat := 378049789552319780397385

theorem tailTrace_6626244 : CollatzResearch.WordTrace tailWord_6626244 prefixEnd_6626244 378049789552319780397385 := by
  unfold tailWord_6626244
  simp only [CollatzResearch.WordTrace]
  refine ⟨120839486703128567611634893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161119315604171423482179857 120839486703128567611634893)
  ·
    refine ⟨45314807513673212854363085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120839486703128567611634893 45314807513673212854363085)
    ·
      refine ⟨16993052817627454820386157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45314807513673212854363085 16993052817627454820386157)
      ·
        refine ⟨6372394806610295557644809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16993052817627454820386157 6372394806610295557644809)
        ·
          refine ⟨4779296104957721668233607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6372394806610295557644809 4779296104957721668233607)
          ·
            refine ⟨7168944157436582502350411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4779296104957721668233607 7168944157436582502350411)
            ·
              refine ⟨10753416236154873753525617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7168944157436582502350411 10753416236154873753525617)
              ·
                refine ⟨8065062177116155315144213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10753416236154873753525617 8065062177116155315144213)
                ·
                  refine ⟨378049789552319780397385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8065062177116155315144213 378049789552319780397385)
                  ·
                    rfl

theorem cell23_6626244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_6626244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626244 prefixEnd_6626244 := by exact prefixLift 6626244
  have htrace : WordTrace (prefixWord ++ tailWord_6626244) baseStart_6626244 baseEnd_6626244 := by
    simpa [prefixWord, tailWord_6626244, baseEnd_6626244] using wordTrace_append hprefix tailTrace_6626244
  have hstable : (prefixWord ++ tailWord_6626244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626244).length < 2 ^ (prefixWord ++ tailWord_6626244).sum := by decide
  have hdescent : baseEnd_6626244 < baseStart_6626244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626256 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 6]
def baseStart_6626256 : Nat := 118140960795 + 6626256 * 2 ^ 59
def prefixEnd_6626256 : Nat := 4983230072969 + 3 ^ 40 * 6626256 * 2
def baseEnd_6626256 : Nat := 3402454267738731976626409

theorem tailTrace_6626256 : CollatzResearch.WordTrace tailWord_6626256 prefixEnd_6626256 3402454267738731976626409 := by
  unfold tailWord_6626256
  simp only [CollatzResearch.WordTrace]
  refine ⟨120839705541106830636353311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161119607388142440848471081 120839705541106830636353311)
  ·
    refine ⟨181259558311660245954529967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120839705541106830636353311 181259558311660245954529967)
    ·
      refine ⟨271889337467490368931794951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181259558311660245954529967 271889337467490368931794951)
      ·
        refine ⟨407834006201235553397692427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271889337467490368931794951 407834006201235553397692427)
        ·
          refine ⟨611751009301853330096538641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407834006201235553397692427 611751009301853330096538641)
          ·
            refine ⟨458813256976389997572403981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 611751009301853330096538641 458813256976389997572403981)
            ·
              refine ⟨172054971366146249089651493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 458813256976389997572403981 172054971366146249089651493)
              ·
                refine ⟨32260307131152421704309655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172054971366146249089651493 32260307131152421704309655)
                ·
                  refine ⟨48390460696728632556464483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32260307131152421704309655 48390460696728632556464483)
                  ·
                    refine ⟨72585691045092948834696725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48390460696728632556464483 72585691045092948834696725)
                    ·
                      refine ⟨3402454267738731976626409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72585691045092948834696725 3402454267738731976626409)
                      ·
                        rfl

theorem cell23_6626256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_6626256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626256 prefixEnd_6626256 := by exact prefixLift 6626256
  have htrace : WordTrace (prefixWord ++ tailWord_6626256) baseStart_6626256 baseEnd_6626256 := by
    simpa [prefixWord, tailWord_6626256, baseEnd_6626256] using wordTrace_append hprefix tailTrace_6626256
  have hstable : (prefixWord ++ tailWord_6626256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626256).length < 2 ^ (prefixWord ++ tailWord_6626256).sum := by decide
  have hdescent : baseEnd_6626256 < baseStart_6626256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626263 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 3]
def baseStart_6626263 : Nat := 118140960795 + 6626263 * 2 ^ 59
def prefixEnd_6626263 : Nat := 4983230072969 + 3 ^ 40 * 6626263 * 2
def baseEnd_6626263 : Nat := 3402457862103313449238877

theorem tailTrace_6626263 : CollatzResearch.WordTrace tailWord_6626263 prefixEnd_6626263 3402457862103313449238877 := by
  unfold tailWord_6626263
  simp only [CollatzResearch.WordTrace]
  refine ⟨241679666393188301468211443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161119777595458867645474295 241679666393188301468211443)
  ·
    refine ⟨362519499589782452202317165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241679666393188301468211443 362519499589782452202317165)
    ·
      refine ⟨135944812346168419575868937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362519499589782452202317165 135944812346168419575868937)
      ·
        refine ⟨101958609259626314681901703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135944812346168419575868937 101958609259626314681901703)
        ·
          refine ⟨152937913889439472022852555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101958609259626314681901703 152937913889439472022852555)
          ·
            refine ⟨229406870834159208034278833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152937913889439472022852555 229406870834159208034278833)
            ·
              refine ⟨172055153125619406025709125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229406870834159208034278833 172055153125619406025709125)
              ·
                refine ⟨32260341211053638629820461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172055153125619406025709125 32260341211053638629820461)
                ·
                  refine ⟨12097627954145114486182673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32260341211053638629820461 12097627954145114486182673)
                  ·
                    refine ⟨9073220965608835864637005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12097627954145114486182673 9073220965608835864637005)
                    ·
                      refine ⟨3402457862103313449238877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9073220965608835864637005 3402457862103313449238877)
                      ·
                        rfl

theorem cell23_6626263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_6626263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626263 prefixEnd_6626263 := by exact prefixLift 6626263
  have htrace : WordTrace (prefixWord ++ tailWord_6626263) baseStart_6626263 baseEnd_6626263 := by
    simpa [prefixWord, tailWord_6626263, baseEnd_6626263] using wordTrace_append hprefix tailTrace_6626263
  have hstable : (prefixWord ++ tailWord_6626263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626263).length < 2 ^ (prefixWord ++ tailWord_6626263).sum := by decide
  have hdescent : baseEnd_6626263 < baseStart_6626263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626280 : List Nat := [2, 1, 4, 1, 1, 1, 3, 4, 1, 2, 3]
def baseStart_6626280 : Nat := 118140960795 + 6626280 * 2 ^ 59
def prefixEnd_6626280 : Nat := 4983230072969 + 3 ^ 40 * 6626280 * 2
def baseEnd_6626280 : Nat := 3402466591274439882726299

theorem tailTrace_6626280 : CollatzResearch.WordTrace tailWord_6626280 prefixEnd_6626280 3402466591274439882726299 := by
  unfold tailWord_6626280
  simp only [CollatzResearch.WordTrace]
  refine ⟨120840143217063356685790147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161120190956084475581053529 120840143217063356685790147)
  ·
    refine ⟨181260214825595035028685221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120840143217063356685790147 181260214825595035028685221)
    ·
      refine ⟨33986290279799069067878479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181260214825595035028685221 33986290279799069067878479)
      ·
        refine ⟨50979435419698603601817719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33986290279799069067878479 50979435419698603601817719)
        ·
          refine ⟨76469153129547905402726579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50979435419698603601817719 76469153129547905402726579)
          ·
            refine ⟨114703729694321858104089869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76469153129547905402726579 114703729694321858104089869)
            ·
              refine ⟨43013898635370696789033701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114703729694321858104089869 43013898635370696789033701)
              ·
                refine ⟨8065105994132005647943819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43013898635370696789033701 8065105994132005647943819)
                ·
                  refine ⟨12097658991198008471915729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8065105994132005647943819 12097658991198008471915729)
                  ·
                    refine ⟨9073244243398506353936797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12097658991198008471915729 9073244243398506353936797)
                    ·
                      refine ⟨3402466591274439882726299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9073244243398506353936797 3402466591274439882726299)
                      ·
                        rfl

theorem cell23_6626280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_6626280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626280 prefixEnd_6626280 := by exact prefixLift 6626280
  have htrace : WordTrace (prefixWord ++ tailWord_6626280) baseStart_6626280 baseEnd_6626280 := by
    simpa [prefixWord, tailWord_6626280, baseEnd_6626280] using wordTrace_append hprefix tailTrace_6626280
  have hstable : (prefixWord ++ tailWord_6626280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626280).length < 2 ^ (prefixWord ++ tailWord_6626280).sum := by decide
  have hdescent : baseEnd_6626280 < baseStart_6626280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626296 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 1, 9]
def baseStart_6626296 : Nat := 118140960795 + 6626296 * 2 ^ 59
def prefixEnd_6626296 : Nat := 4983230072969 + 3 ^ 40 * 6626296 * 2
def baseEnd_6626296 : Nat := 1134158268988303940042075

theorem tailTrace_6626296 : CollatzResearch.WordTrace tailWord_6626296 prefixEnd_6626296 1134158268988303940042075 := by
  unfold tailWord_6626296
  simp only [CollatzResearch.WordTrace]
  refine ⟨120840435001034374052081371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161120580001379165402775161 120840435001034374052081371)
  ·
    refine ⟨181260652501551561078122057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120840435001034374052081371 181260652501551561078122057)
    ·
      refine ⟨135945489376163670808591543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181260652501551561078122057 135945489376163670808591543)
      ·
        refine ⟨203918234064245506212887315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135945489376163670808591543 203918234064245506212887315)
        ·
          refine ⟨305877351096368259319330973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203918234064245506212887315 305877351096368259319330973)
          ·
            refine ⟨114704006661138097244749115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305877351096368259319330973 114704006661138097244749115)
            ·
              refine ⟨172056009991707145867123673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114704006661138097244749115 172056009991707145867123673)
              ·
                refine ⟨129042007493780359400342755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172056009991707145867123673 129042007493780359400342755)
                ·
                  refine ⟨193563011240670539100514133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129042007493780359400342755 193563011240670539100514133)
                  ·
                    refine ⟨1134158268988303940042075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 193563011240670539100514133 1134158268988303940042075)
                    ·
                      rfl

theorem cell23_6626296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_6626296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626296 prefixEnd_6626296 := by exact prefixLift 6626296
  have htrace : WordTrace (prefixWord ++ tailWord_6626296) baseStart_6626296 baseEnd_6626296 := by
    simpa [prefixWord, tailWord_6626296, baseEnd_6626296] using wordTrace_append hprefix tailTrace_6626296
  have hstable : (prefixWord ++ tailWord_6626296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626296).length < 2 ^ (prefixWord ++ tailWord_6626296).sum := by decide
  have hdescent : baseEnd_6626296 < baseStart_6626296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626311 : List Nat := [1, 1, 4, 3, 1, 1, 5, 2, 1, 2, 2]
def baseStart_6626311 : Nat := 118140960795 + 6626311 * 2 ^ 59
def prefixEnd_6626311 : Nat := 4983230072969 + 3 ^ 40 * 6626311 * 2
def baseEnd_6626311 : Nat := 3402482509174729261438657

theorem tailTrace_6626311 : CollatzResearch.WordTrace tailWord_6626311 prefixEnd_6626311 3402482509174729261438657 := by
  unfold tailWord_6626311
  simp only [CollatzResearch.WordTrace]
  refine ⟨241681417097014405665958787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161120944731342937110639191 241681417097014405665958787)
  ·
    refine ⟨362522125645521608498938181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241681417097014405665958787 362522125645521608498938181)
    ·
      refine ⟨67972898558535301593550909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 362522125645521608498938181 67972898558535301593550909)
      ·
        refine ⟨25489836959450738097581591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67972898558535301593550909 25489836959450738097581591)
        ·
          refine ⟨38234755439176107146372387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25489836959450738097581591 38234755439176107146372387)
          ·
            refine ⟨57352133158764160719558581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38234755439176107146372387 57352133158764160719558581)
            ·
              refine ⟨5376762483634140067458617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57352133158764160719558581 5376762483634140067458617)
              ·
                refine ⟨4032571862725605050593963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5376762483634140067458617 4032571862725605050593963)
                ·
                  refine ⟨6048857794088407575890945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4032571862725605050593963 6048857794088407575890945)
                  ·
                    refine ⟨4536643345566305681918209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6048857794088407575890945 4536643345566305681918209)
                    ·
                      refine ⟨3402482509174729261438657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4536643345566305681918209 3402482509174729261438657)
                      ·
                        rfl

theorem cell23_6626311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_6626311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626311 prefixEnd_6626311 := by exact prefixLift 6626311
  have htrace : WordTrace (prefixWord ++ tailWord_6626311) baseStart_6626311 baseEnd_6626311 := by
    simpa [prefixWord, tailWord_6626311, baseEnd_6626311] using wordTrace_append hprefix tailTrace_6626311
  have hstable : (prefixWord ++ tailWord_6626311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626311).length < 2 ^ (prefixWord ++ tailWord_6626311).sum := by decide
  have hdescent : baseEnd_6626311 < baseStart_6626311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626337 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 3, 3, 2]
def baseStart_6626337 : Nat := 118140960795 + 6626337 * 2 ^ 59
def prefixEnd_6626337 : Nat := 4983230072969 + 3 ^ 40 * 6626337 * 2
def baseEnd_6626337 : Nat := 3402495859671746159713537

theorem tailTrace_6626337 : CollatzResearch.WordTrace tailWord_6626337 prefixEnd_6626337 3402495859671746159713537 := by
  unfold tailWord_6626337
  simp only [CollatzResearch.WordTrace]
  refine ⟨241682365394920212106405265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161121576929946808070936843 241682365394920212106405265)
  ·
    refine ⟨181261774046190159079803949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241682365394920212106405265 181261774046190159079803949)
    ·
      refine ⟨67973165267321309654926481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181261774046190159079803949 67973165267321309654926481)
      ·
        refine ⟨50979873950490982241194861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67973165267321309654926481 50979873950490982241194861)
        ·
          refine ⟨19117452731434118340448073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50979873950490982241194861 19117452731434118340448073)
          ·
            refine ⟨14338089548575588755336055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19117452731434118340448073 14338089548575588755336055)
            ·
              refine ⟨21507134322863383133004083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14338089548575588755336055 21507134322863383133004083)
              ·
                refine ⟨32260701484295074699506125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21507134322863383133004083 32260701484295074699506125)
                ·
                  refine ⟨12097763056610653012314797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32260701484295074699506125 12097763056610653012314797)
                  ·
                    refine ⟨4536661146228994879618049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12097763056610653012314797 4536661146228994879618049)
                    ·
                      refine ⟨3402495859671746159713537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4536661146228994879618049 3402495859671746159713537)
                      ·
                        rfl

theorem cell23_6626337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_6626337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626337 prefixEnd_6626337 := by exact prefixLift 6626337
  have htrace : WordTrace (prefixWord ++ tailWord_6626337) baseStart_6626337 baseEnd_6626337 := by
    simpa [prefixWord, tailWord_6626337, baseEnd_6626337] using wordTrace_append hprefix tailTrace_6626337
  have hstable : (prefixWord ++ tailWord_6626337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626337).length < 2 ^ (prefixWord ++ tailWord_6626337).sum := by decide
  have hdescent : baseEnd_6626337 < baseStart_6626337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626353 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 2, 1, 5]
def baseStart_6626353 : Nat := 118140960795 + 6626353 * 2 ^ 59
def prefixEnd_6626353 : Nat := 4983230072969 + 3 ^ 40 * 6626353 * 2
def baseEnd_6626353 : Nat := 3402504075362218097113463

theorem tailTrace_6626353 : CollatzResearch.WordTrace tailWord_6626353 prefixEnd_6626353 3402504075362218097113463 := by
  unfold tailWord_6626353
  simp only [CollatzResearch.WordTrace]
  refine ⟨241682948962862246838987713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161121965975241497892658475 241682948962862246838987713)
  ·
    refine ⟨181262211722146685129240785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241682948962862246838987713 181262211722146685129240785)
    ·
      refine ⟨135946658791610013846930589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181262211722146685129240785 135946658791610013846930589)
      ·
        refine ⟨50979997046853755192598971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135946658791610013846930589 50979997046853755192598971)
        ·
          refine ⟨76469995570280632788898457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50979997046853755192598971 76469995570280632788898457)
          ·
            refine ⟨57352496677710474591673843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76469995570280632788898457 57352496677710474591673843)
            ·
              refine ⟨86028745016565711887510765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57352496677710474591673843 86028745016565711887510765)
              ·
                refine ⟨32260779381212141957816537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86028745016565711887510765 32260779381212141957816537)
                ·
                  refine ⟨24195584535909106468362403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32260779381212141957816537 24195584535909106468362403)
                  ·
                    refine ⟨36293376803863659702543605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24195584535909106468362403 36293376803863659702543605)
                    ·
                      refine ⟨3402504075362218097113463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36293376803863659702543605 3402504075362218097113463)
                      ·
                        rfl

theorem cell23_6626353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_6626353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626353 prefixEnd_6626353 := by exact prefixLift 6626353
  have htrace : WordTrace (prefixWord ++ tailWord_6626353) baseStart_6626353 baseEnd_6626353 := by
    simpa [prefixWord, tailWord_6626353, baseEnd_6626353] using wordTrace_append hprefix tailTrace_6626353
  have hstable : (prefixWord ++ tailWord_6626353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626353).length < 2 ^ (prefixWord ++ tailWord_6626353).sum := by decide
  have hdescent : baseEnd_6626353 < baseStart_6626353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626354 : List Nat := [3, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2]
def baseStart_6626354 : Nat := 118140960795 + 6626354 * 2 ^ 59
def prefixEnd_6626354 : Nat := 4983230072969 + 3 ^ 40 * 6626354 * 2
def baseEnd_6626354 : Nat := 3402504588842872593200959

theorem tailTrace_6626354 : CollatzResearch.WordTrace tailWord_6626354 prefixEnd_6626354 3402504588842872593200959 := by
  unfold tailWord_6626354
  simp only [CollatzResearch.WordTrace]
  refine ⟨60420746358964656002443529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161121990290572416006516077 60420746358964656002443529)
  ·
    refine ⟨45315559769223492001832647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60420746358964656002443529 45315559769223492001832647)
    ·
      refine ⟨67973339653835238002748971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45315559769223492001832647 67973339653835238002748971)
      ·
        refine ⟨101960009480752857004123457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67973339653835238002748971 101960009480752857004123457)
        ·
          refine ⟨76470007110564642753092593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101960009480752857004123457 76470007110564642753092593)
          ·
            refine ⟨57352505332923482064819445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76470007110564642753092593 57352505332923482064819445)
            ·
              refine ⟨5376797374961576443576823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57352505332923482064819445 5376797374961576443576823)
              ·
                refine ⟨8065196062442364665365235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5376797374961576443576823 8065196062442364665365235)
                ·
                  refine ⟨12097794093663546998047853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8065196062442364665365235 12097794093663546998047853)
                  ·
                    refine ⟨4536672785123830124267945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12097794093663546998047853 4536672785123830124267945)
                    ·
                      refine ⟨3402504588842872593200959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4536672785123830124267945 3402504588842872593200959)
                      ·
                        rfl

theorem cell23_6626354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_6626354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626354 prefixEnd_6626354 := by exact prefixLift 6626354
  have htrace : WordTrace (prefixWord ++ tailWord_6626354) baseStart_6626354 baseEnd_6626354 := by
    simpa [prefixWord, tailWord_6626354, baseEnd_6626354] using wordTrace_append hprefix tailTrace_6626354
  have hstable : (prefixWord ++ tailWord_6626354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626354).length < 2 ^ (prefixWord ++ tailWord_6626354).sum := by decide
  have hdescent : baseEnd_6626354 < baseStart_6626354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626407 : List Nat := [1, 1, 5, 1, 1, 4, 2, 3, 5]
def baseStart_6626407 : Nat := 118140960795 + 6626407 * 2 ^ 59
def prefixEnd_6626407 : Nat := 4983230072969 + 3 ^ 40 * 6626407 * 2
def baseEnd_6626407 : Nat := 378059089257506765093135

theorem tailTrace_6626407 : CollatzResearch.WordTrace tailWord_6626407 prefixEnd_6626407 378059089257506765093135 := by
  unfold tailWord_6626407
  simp only [CollatzResearch.WordTrace]
  refine ⟨241684918504666614061453475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161123279003111076040968983 241684918504666614061453475)
  ·
    refine ⟨362527377756999921092180213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241684918504666614061453475 362527377756999921092180213)
    ·
      refine ⟨33986941664718742602391895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 362527377756999921092180213 33986941664718742602391895)
      ·
        refine ⟨50980412497078113903587843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33986941664718742602391895 50980412497078113903587843)
        ·
          refine ⟨76470618745617170855381765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50980412497078113903587843 76470618745617170855381765)
          ·
            refine ⟨14338241014803219535384081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76470618745617170855381765 14338241014803219535384081)
            ·
              refine ⟨10753680761102414651538061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14338241014803219535384081 10753680761102414651538061)
              ·
                refine ⟨4032630285413405494326773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10753680761102414651538061 4032630285413405494326773)
                ·
                  refine ⟨378059089257506765093135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4032630285413405494326773 378059089257506765093135)
                  ·
                    rfl

theorem cell23_6626407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 5].length) (baseStart_6626407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626407 prefixEnd_6626407 := by exact prefixLift 6626407
  have htrace : WordTrace (prefixWord ++ tailWord_6626407) baseStart_6626407 baseEnd_6626407 := by
    simpa [prefixWord, tailWord_6626407, baseEnd_6626407] using wordTrace_append hprefix tailTrace_6626407
  have hstable : (prefixWord ++ tailWord_6626407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626407).length < 2 ^ (prefixWord ++ tailWord_6626407).sum := by decide
  have hdescent : baseEnd_6626407 < baseStart_6626407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626453 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_6626453 : Nat := 118140960795 + 6626453 * 2 ^ 59
def prefixEnd_6626453 : Nat := 4983230072969 + 3 ^ 40 * 6626453 * 2
def baseEnd_6626453 : Nat := 3402555423427667705863003

theorem tailTrace_6626453 : CollatzResearch.WordTrace tailWord_6626453 prefixEnd_6626453 3402555423427667705863003 := by
  unfold tailWord_6626453
  simp only [CollatzResearch.WordTrace]
  refine ⟨241686596262499963917628013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161124397508333309278418675 241686596262499963917628013)
  ·
    refine ⟨90632473598437486469110505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241686596262499963917628013 90632473598437486469110505)
    ·
      refine ⟨67974355198828114851832879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90632473598437486469110505 67974355198828114851832879)
      ·
        refine ⟨101961532798242172277749319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67974355198828114851832879 101961532798242172277749319)
        ·
          refine ⟨152942299197363258416623979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101961532798242172277749319 152942299197363258416623979)
          ·
            refine ⟨229413448796044887624935969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152942299197363258416623979 229413448796044887624935969)
            ·
              refine ⟨172060086597033665718701977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229413448796044887624935969 172060086597033665718701977)
              ·
                refine ⟨129045064947775249289026483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172060086597033665718701977 129045064947775249289026483)
                ·
                  refine ⟨193567597421662873933539725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129045064947775249289026483 193567597421662873933539725)
                  ·
                    refine ⟨72587849033123577725077397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193567597421662873933539725 72587849033123577725077397)
                    ·
                      refine ⟨3402555423427667705863003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72587849033123577725077397 3402555423427667705863003)
                      ·
                        rfl

theorem cell23_6626453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_6626453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626453 prefixEnd_6626453 := by exact prefixLift 6626453
  have htrace : WordTrace (prefixWord ++ tailWord_6626453) baseStart_6626453 baseEnd_6626453 := by
    simpa [prefixWord, tailWord_6626453, baseEnd_6626453] using wordTrace_append hprefix tailTrace_6626453
  have hstable : (prefixWord ++ tailWord_6626453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626453).length < 2 ^ (prefixWord ++ tailWord_6626453).sum := by decide
  have hdescent : baseEnd_6626453 < baseStart_6626453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626474 : List Nat := [3, 1, 5, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_6626474 : Nat := 118140960795 + 6626474 * 2 ^ 59
def prefixEnd_6626474 : Nat := 4983230072969 + 3 ^ 40 * 6626474 * 2
def baseEnd_6626474 : Nat := 3402566206521412123700407

theorem tailTrace_6626474 : CollatzResearch.WordTrace tailWord_6626474 prefixEnd_6626474 3402566206521412123700407 := by
  unfold tailWord_6626474
  simp only [CollatzResearch.WordTrace]
  refine ⟨60421840548855971126035619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161124908130282589669428317 60421840548855971126035619)
  ·
    refine ⟨90632760823283956689053429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60421840548855971126035619 90632760823283956689053429)
    ·
      refine ⟨8496821327182870939598759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90632760823283956689053429 8496821327182870939598759)
      ·
        refine ⟨12745231990774306409398139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8496821327182870939598759 12745231990774306409398139)
        ·
          refine ⟨19117847986161459614097209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12745231990774306409398139 19117847986161459614097209)
          ·
            refine ⟨14338385989621094710572907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19117847986161459614097209 14338385989621094710572907)
            ·
              refine ⟨21507578984431642065859361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14338385989621094710572907 21507578984431642065859361)
              ·
                refine ⟨16130684238323731549394521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21507578984431642065859361 16130684238323731549394521)
                ·
                  refine ⟨12098013178742798662045891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16130684238323731549394521 12098013178742798662045891)
                  ·
                    refine ⟨18147019768114197993068837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12098013178742798662045891 18147019768114197993068837)
                    ·
                      refine ⟨3402566206521412123700407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18147019768114197993068837 3402566206521412123700407)
                      ·
                        rfl

theorem cell23_6626474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_6626474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626474 prefixEnd_6626474 := by exact prefixLift 6626474
  have htrace : WordTrace (prefixWord ++ tailWord_6626474) baseStart_6626474 baseEnd_6626474 := by
    simpa [prefixWord, tailWord_6626474, baseEnd_6626474] using wordTrace_append hprefix tailTrace_6626474
  have hstable : (prefixWord ++ tailWord_6626474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626474).length < 2 ^ (prefixWord ++ tailWord_6626474).sum := by decide
  have hdescent : baseEnd_6626474 < baseStart_6626474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626483 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 8]
def baseStart_6626483 : Nat := 118140960795 + 6626483 * 2 ^ 59
def prefixEnd_6626483 : Nat := 4983230072969 + 3 ^ 40 * 6626483 * 2
def baseEnd_6626483 : Nat := 3402570827847302588487865

theorem tailTrace_6626483 : CollatzResearch.WordTrace tailWord_6626483 prefixEnd_6626483 3402570827847302588487865 := by
  unfold tailWord_6626483
  simp only [CollatzResearch.WordTrace]
  refine ⟨241687690452391279041220103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161125126968260852694146735 241687690452391279041220103)
  ·
    refine ⟨362531535678586918561830155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241687690452391279041220103 362531535678586918561830155)
    ·
      refine ⟨543797303517880377842745233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362531535678586918561830155 543797303517880377842745233)
      ·
        refine ⟨407847977638410283382058925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543797303517880377842745233 407847977638410283382058925)
        ·
          refine ⟨152942991614403856268272097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407847977638410283382058925 152942991614403856268272097)
          ·
            refine ⟨114707243710802892201204073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152942991614403856268272097 114707243710802892201204073)
            ·
              refine ⟨86030432783102169150903055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114707243710802892201204073 86030432783102169150903055)
              ·
                refine ⟨129045649174653253726354583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86030432783102169150903055 129045649174653253726354583)
                ·
                  refine ⟨193568473761979880589531875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129045649174653253726354583 193568473761979880589531875)
                  ·
                    refine ⟨290352710642969820884297813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 193568473761979880589531875 290352710642969820884297813)
                    ·
                      refine ⟨3402570827847302588487865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 290352710642969820884297813 3402570827847302588487865)
                      ·
                        rfl

theorem cell23_6626483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_6626483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626483 prefixEnd_6626483 := by exact prefixLift 6626483
  have htrace : WordTrace (prefixWord ++ tailWord_6626483) baseStart_6626483 baseEnd_6626483 := by
    simpa [prefixWord, tailWord_6626483, baseEnd_6626483] using wordTrace_append hprefix tailTrace_6626483
  have hstable : (prefixWord ++ tailWord_6626483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626483).length < 2 ^ (prefixWord ++ tailWord_6626483).sum := by decide
  have hdescent : baseEnd_6626483 < baseStart_6626483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626523 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 2, 10]
def baseStart_6626523 : Nat := 118140960795 + 6626523 * 2 ^ 59
def prefixEnd_6626523 : Nat := 4983230072969 + 3 ^ 40 * 6626523 * 2
def baseEnd_6626523 : Nat := 1134197122357827477329227

theorem tailTrace_6626523 : CollatzResearch.WordTrace tailWord_6626523 prefixEnd_6626523 1134197122357827477329227 := by
  unfold tailWord_6626523
  simp only [CollatzResearch.WordTrace]
  refine ⟨241689149372246365872676223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161126099581497577248450815 241689149372246365872676223)
  ·
    refine ⟨362533724058369548809014335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241689149372246365872676223 362533724058369548809014335)
    ·
      refine ⟨543800586087554323213521503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362533724058369548809014335 543800586087554323213521503)
      ·
        refine ⟨815700879131331484820282255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543800586087554323213521503 815700879131331484820282255)
        ·
          refine ⟨1223551318696997227230423383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815700879131331484820282255 1223551318696997227230423383)
          ·
            refine ⟨1835326978045495840845635075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1223551318696997227230423383 1835326978045495840845635075)
            ·
              refine ⟨2752990467068243761268452613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835326978045495840845635075 2752990467068243761268452613)
              ·
                refine ⟨516185712575295705237834865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2752990467068243761268452613 516185712575295705237834865)
                ·
                  refine ⟨387139284431471778928376149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 516185712575295705237834865 387139284431471778928376149)
                  ·
                    refine ⟨1134197122357827477329227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 387139284431471778928376149 1134197122357827477329227)
                    ·
                      rfl

theorem cell23_6626523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 10].length) (baseStart_6626523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626523 prefixEnd_6626523 := by exact prefixLift 6626523
  have htrace : WordTrace (prefixWord ++ tailWord_6626523) baseStart_6626523 baseEnd_6626523 := by
    simpa [prefixWord, tailWord_6626523, baseEnd_6626523] using wordTrace_append hprefix tailTrace_6626523
  have hstable : (prefixWord ++ tailWord_6626523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626523).length < 2 ^ (prefixWord ++ tailWord_6626523).sum := by decide
  have hdescent : baseEnd_6626523 < baseStart_6626523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626535 : List Nat := [1, 1, 5, 3, 3, 1, 2, 2, 1, 4]
def baseStart_6626535 : Nat := 118140960795 + 6626535 * 2 ^ 59
def prefixEnd_6626535 : Nat := 4983230072969 + 3 ^ 40 * 6626535 * 2
def baseEnd_6626535 : Nat := 1134199176280445461679209

theorem tailTrace_6626535 : CollatzResearch.WordTrace tailWord_6626535 prefixEnd_6626535 1134199176280445461679209 := by
  unfold tailWord_6626535
  simp only [CollatzResearch.WordTrace]
  refine ⟨241689587048202891922113059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161126391365468594614742039 241689587048202891922113059)
  ·
    refine ⟨362534380572304337883169589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241689587048202891922113059 362534380572304337883169589)
    ·
      refine ⟨33987598178653531676547149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 362534380572304337883169589 33987598178653531676547149)
      ·
        refine ⟨12745349316995074378705181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33987598178653531676547149 12745349316995074378705181)
        ·
          refine ⟨4779505993873152892014443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12745349316995074378705181 4779505993873152892014443)
          ·
            refine ⟨7169258990809729338021665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4779505993873152892014443 7169258990809729338021665)
            ·
              refine ⟨5376944243107297003516249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7169258990809729338021665 5376944243107297003516249)
              ·
                refine ⟨4032708182330472752637187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5376944243107297003516249 4032708182330472752637187)
                ·
                  refine ⟨6049062273495709128955781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4032708182330472752637187 6049062273495709128955781)
                  ·
                    refine ⟨1134199176280445461679209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6049062273495709128955781 1134199176280445461679209)
                    ·
                      rfl

theorem cell23_6626535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_6626535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626535 prefixEnd_6626535 := by exact prefixLift 6626535
  have htrace : WordTrace (prefixWord ++ tailWord_6626535) baseStart_6626535 baseEnd_6626535 := by
    simpa [prefixWord, tailWord_6626535, baseEnd_6626535] using wordTrace_append hprefix tailTrace_6626535
  have hstable : (prefixWord ++ tailWord_6626535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626535).length < 2 ^ (prefixWord ++ tailWord_6626535).sum := by decide
  have hdescent : baseEnd_6626535 < baseStart_6626535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626568 : List Nat := [2, 1, 3, 2, 5, 1, 1, 1, 2, 3, 2]
def baseStart_6626568 : Nat := 118140960795 + 6626568 * 2 ^ 59
def prefixEnd_6626568 : Nat := 4983230072969 + 3 ^ 40 * 6626568 * 2
def baseEnd_6626568 : Nat := 3402614473702934755924975

theorem tailTrace_6626568 : CollatzResearch.WordTrace tailWord_6626568 prefixEnd_6626568 3402614473702934755924975 := by
  unfold tailWord_6626568
  simp only [CollatzResearch.WordTrace]
  refine ⟨120845395328541669279032179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161127193771388892372042905 120845395328541669279032179)
  ·
    refine ⟨181268092992812503918548269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120845395328541669279032179 181268092992812503918548269)
    ·
      refine ⟨67975534872304688969455601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181268092992812503918548269 67975534872304688969455601)
      ·
        refine ⟨50981651154228516727091701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67975534872304688969455601 50981651154228516727091701)
        ·
          refine ⟨4779529795708923443164847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50981651154228516727091701 4779529795708923443164847)
          ·
            refine ⟨7169294693563385164747271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4779529795708923443164847 7169294693563385164747271)
            ·
              refine ⟨10753942040345077747120907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7169294693563385164747271 10753942040345077747120907)
              ·
                refine ⟨16130913060517616620681361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10753942040345077747120907 16130913060517616620681361)
                ·
                  refine ⟨12098184795388212465511021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16130913060517616620681361 12098184795388212465511021)
                  ·
                    refine ⟨4536819298270579674566633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12098184795388212465511021 4536819298270579674566633)
                    ·
                      refine ⟨3402614473702934755924975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4536819298270579674566633 3402614473702934755924975)
                      ·
                        rfl

theorem cell23_6626568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_6626568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626568 prefixEnd_6626568 := by exact prefixLift 6626568
  have htrace : WordTrace (prefixWord ++ tailWord_6626568) baseStart_6626568 baseEnd_6626568 := by
    simpa [prefixWord, tailWord_6626568, baseEnd_6626568] using wordTrace_append hprefix tailTrace_6626568
  have hstable : (prefixWord ++ tailWord_6626568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626568).length < 2 ^ (prefixWord ++ tailWord_6626568).sum := by decide
  have hdescent : baseEnd_6626568 < baseStart_6626568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626584 : List Nat := [2, 1, 2, 3, 1, 4, 1, 3, 1, 2, 3]
def baseStart_6626584 : Nat := 118140960795 + 6626584 * 2 ^ 59
def prefixEnd_6626584 : Nat := 4983230072969 + 3 ^ 40 * 6626584 * 2
def baseEnd_6626584 : Nat := 3402622689393406693324901

theorem tailTrace_6626584 : CollatzResearch.WordTrace tailWord_6626584 prefixEnd_6626584 3402622689393406693324901 := by
  unfold tailWord_6626584
  simp only [CollatzResearch.WordTrace]
  refine ⟨120845687112512686645323403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161127582816683582193764537 120845687112512686645323403)
  ·
    refine ⟨181268530668769029967985105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120845687112512686645323403 181268530668769029967985105)
    ·
      refine ⟨135951398001576772475988829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181268530668769029967985105 135951398001576772475988829)
      ·
        refine ⟨50981774250591289678495811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135951398001576772475988829 50981774250591289678495811)
        ·
          refine ⟨76472661375886934517743717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50981774250591289678495811 76472661375886934517743717)
          ·
            refine ⟨14338624007978800222076947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76472661375886934517743717 14338624007978800222076947)
            ·
              refine ⟨21507936011968200333115421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14338624007978800222076947 21507936011968200333115421)
              ·
                refine ⟨8065476004488075124918283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21507936011968200333115421 8065476004488075124918283)
                ·
                  refine ⟨12098214006732112687377425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8065476004488075124918283 12098214006732112687377425)
                  ·
                    refine ⟨9073660505049084515533069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12098214006732112687377425 9073660505049084515533069)
                    ·
                      refine ⟨3402622689393406693324901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9073660505049084515533069 3402622689393406693324901)
                      ·
                        rfl

theorem cell23_6626584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_6626584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626584 prefixEnd_6626584 := by exact prefixLift 6626584
  have htrace : WordTrace (prefixWord ++ tailWord_6626584) baseStart_6626584 baseEnd_6626584 := by
    simpa [prefixWord, tailWord_6626584, baseEnd_6626584] using wordTrace_append hprefix tailTrace_6626584
  have hstable : (prefixWord ++ tailWord_6626584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626584).length < 2 ^ (prefixWord ++ tailWord_6626584).sum := by decide
  have hdescent : baseEnd_6626584 < baseStart_6626584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626591 : List Nat := [1, 1, 2, 4, 4, 2, 1, 2, 2, 4]
def baseStart_6626591 : Nat := 118140960795 + 6626591 * 2 ^ 59
def prefixEnd_6626591 : Nat := 4983230072969 + 3 ^ 40 * 6626591 * 2
def baseEnd_6626591 : Nat := 1134208761252662721979123

theorem tailTrace_6626591 : CollatzResearch.WordTrace tailWord_6626591 prefixEnd_6626591 1134208761252662721979123 := by
  unfold tailWord_6626591
  simp only [CollatzResearch.WordTrace]
  refine ⟨241691629536000013486151627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161127753024000008990767751 241691629536000013486151627)
  ·
    refine ⟨362537444304000020229227441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241691629536000013486151627 362537444304000020229227441)
    ·
      refine ⟨271903083228000015171920581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362537444304000020229227441 271903083228000015171920581)
      ·
        refine ⟨50981828105250002844735109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271903083228000015171920581 50981828105250002844735109)
        ·
          refine ⟨9559092769734375533387833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50981828105250002844735109 9559092769734375533387833)
          ·
            refine ⟨7169319577300781650040875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9559092769734375533387833 7169319577300781650040875)
            ·
              refine ⟨10753979365951172475061313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7169319577300781650040875 10753979365951172475061313)
              ·
                refine ⟨8065484524463379356295985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10753979365951172475061313 8065484524463379356295985)
                ·
                  refine ⟨6049113393347534517221989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8065484524463379356295985 6049113393347534517221989)
                  ·
                    refine ⟨1134208761252662721979123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6049113393347534517221989 1134208761252662721979123)
                    ·
                      rfl

theorem cell23_6626591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 4].length) (baseStart_6626591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626591 prefixEnd_6626591 := by exact prefixLift 6626591
  have htrace : WordTrace (prefixWord ++ tailWord_6626591) baseStart_6626591 baseEnd_6626591 := by
    simpa [prefixWord, tailWord_6626591, baseEnd_6626591] using wordTrace_append hprefix tailTrace_6626591
  have hstable : (prefixWord ++ tailWord_6626591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626591).length < 2 ^ (prefixWord ++ tailWord_6626591).sum := by decide
  have hdescent : baseEnd_6626591 < baseStart_6626591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626621 : List Nat := [1, 4, 1, 5, 1, 2, 2, 7]
def baseStart_6626621 : Nat := 118140960795 + 6626621 * 2 ^ 59
def prefixEnd_6626621 : Nat := 4983230072969 + 3 ^ 40 * 6626621 * 2
def baseEnd_6626621 : Nat := 126023766228800853650453

theorem tailTrace_6626621 : CollatzResearch.WordTrace tailWord_6626621 prefixEnd_6626621 126023766228800853650453 := by
  unfold tailWord_6626621
  simp only [CollatzResearch.WordTrace]
  refine ⟨241692723725891328609743717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161128482483927552406495811 241692723725891328609743717)
  ·
    refine ⟨45317385698604624114326947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241692723725891328609743717 45317385698604624114326947)
    ·
      refine ⟨67976078547906936171490421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45317385698604624114326947 67976078547906936171490421)
      ·
        refine ⟨6372757363866275266077227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67976078547906936171490421 6372757363866275266077227)
        ·
          refine ⟨9559136045799412899115841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6372757363866275266077227 9559136045799412899115841)
          ·
            refine ⟨7169352034349559674336881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9559136045799412899115841 7169352034349559674336881)
            ·
              refine ⟨5377014025762169755752661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7169352034349559674336881 5377014025762169755752661)
              ·
                refine ⟨126023766228800853650453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5377014025762169755752661 126023766228800853650453)
                ·
                  rfl

theorem cell23_6626621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 7].length) (baseStart_6626621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626621 prefixEnd_6626621 := by exact prefixLift 6626621
  have htrace : WordTrace (prefixWord ++ tailWord_6626621) baseStart_6626621 baseEnd_6626621 := by
    simpa [prefixWord, tailWord_6626621, baseEnd_6626621] using wordTrace_append hprefix tailTrace_6626621
  have hstable : (prefixWord ++ tailWord_6626621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626621).length < 2 ^ (prefixWord ++ tailWord_6626621).sum := by decide
  have hdescent : baseEnd_6626621 < baseStart_6626621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626671 : List Nat := [1, 1, 2, 1, 3, 1, 5, 3, 2, 2, 2]
def baseStart_6626671 : Nat := 118140960795 + 6626671 * 2 ^ 59
def prefixEnd_6626671 : Nat := 4983230072969 + 3 ^ 40 * 6626671 * 2
def baseEnd_6626671 : Nat := 3402667362210347852937001

theorem tailTrace_6626671 : CollatzResearch.WordTrace tailWord_6626671 prefixEnd_6626671 3402667362210347852937001 := by
  unfold tailWord_6626671
  simp only [CollatzResearch.WordTrace]
  refine ⟨241694547375710187149063867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161129698250473458099375911 241694547375710187149063867)
  ·
    refine ⟨362541821063565280723595801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241694547375710187149063867 362541821063565280723595801)
    ·
      refine ⟨271906365797673960542696851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362541821063565280723595801 271906365797673960542696851)
      ·
        refine ⟨407859548696510940814045277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271906365797673960542696851 407859548696510940814045277)
        ·
          refine ⟨152947330761191602805266979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407859548696510940814045277 152947330761191602805266979)
          ·
            refine ⟨229420996141787404207900469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152947330761191602805266979 229420996141787404207900469)
            ·
              refine ⟨21508218388292569144490669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 229420996141787404207900469 21508218388292569144490669)
              ·
                refine ⟨8065581895609713429184001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21508218388292569144490669 8065581895609713429184001)
                ·
                  refine ⟨6049186421707285071888001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8065581895609713429184001 6049186421707285071888001)
                  ·
                    refine ⟨4536889816280463803916001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6049186421707285071888001 4536889816280463803916001)
                    ·
                      refine ⟨3402667362210347852937001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4536889816280463803916001 3402667362210347852937001)
                      ·
                        rfl

theorem cell23_6626671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 2, 2].length) (baseStart_6626671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626671 prefixEnd_6626671 := by exact prefixLift 6626671
  have htrace : WordTrace (prefixWord ++ tailWord_6626671) baseStart_6626671 baseEnd_6626671 := by
    simpa [prefixWord, tailWord_6626671, baseEnd_6626671] using wordTrace_append hprefix tailTrace_6626671
  have hstable : (prefixWord ++ tailWord_6626671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626671).length < 2 ^ (prefixWord ++ tailWord_6626671).sum := by decide
  have hdescent : baseEnd_6626671 < baseStart_6626671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626680 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 4, 1, 8]
def baseStart_6626680 : Nat := 118140960795 + 6626680 * 2 ^ 59
def prefixEnd_6626680 : Nat := 4983230072969 + 3 ^ 40 * 6626680 * 2
def baseEnd_6626680 : Nat := 3402671983536238317724459

theorem tailTrace_6626680 : CollatzResearch.WordTrace tailWord_6626680 prefixEnd_6626680 3402671983536238317724459 := by
  unfold tailWord_6626680
  simp only [CollatzResearch.WordTrace]
  refine ⟨120847437816338790843070747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161129917088451721124094329 120847437816338790843070747)
  ·
    refine ⟨181271156724508186264606121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120847437816338790843070747 181271156724508186264606121)
    ·
      refine ⟨135953367543381139698454591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181271156724508186264606121 135953367543381139698454591)
      ·
        refine ⟨203930051315071709547681887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135953367543381139698454591 203930051315071709547681887)
        ·
          refine ⟨305895076972607564321522831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203930051315071709547681887 305895076972607564321522831)
          ·
            refine ⟨458842615458911346482284247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305895076972607564321522831 458842615458911346482284247)
            ·
              refine ⟨688263923188367019723426371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458842615458911346482284247 688263923188367019723426371)
              ·
                refine ⟨1032395884782550529585139557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 688263923188367019723426371 1032395884782550529585139557)
                ·
                  refine ⟨193574228396728224297213667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1032395884782550529585139557 193574228396728224297213667)
                  ·
                    refine ⟨290361342595092336445820501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 193574228396728224297213667 290361342595092336445820501)
                    ·
                      refine ⟨3402671983536238317724459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 290361342595092336445820501 3402671983536238317724459)
                      ·
                        rfl

theorem cell23_6626680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_6626680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626680 prefixEnd_6626680 := by exact prefixLift 6626680
  have htrace : WordTrace (prefixWord ++ tailWord_6626680) baseStart_6626680 baseEnd_6626680 := by
    simpa [prefixWord, tailWord_6626680, baseEnd_6626680] using wordTrace_append hprefix tailTrace_6626680
  have hstable : (prefixWord ++ tailWord_6626680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626680).length < 2 ^ (prefixWord ++ tailWord_6626680).sum := by decide
  have hdescent : baseEnd_6626680 < baseStart_6626680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626714 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2]
def baseStart_6626714 : Nat := 118140960795 + 6626714 * 2 ^ 59
def prefixEnd_6626714 : Nat := 4983230072969 + 3 ^ 40 * 6626714 * 2
def baseEnd_6626714 : Nat := 3402689441878491184699303

theorem tailTrace_6626714 : CollatzResearch.WordTrace tailWord_6626714 prefixEnd_6626714 3402689441878491184699303 := by
  unfold tailWord_6626714
  simp only [CollatzResearch.WordTrace]
  refine ⟨60424028928638601373219799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161130743809702936995252797 60424028928638601373219799)
  ·
    refine ⟨90636043392957902059829699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60424028928638601373219799 90636043392957902059829699)
    ·
      refine ⟨135954065089436853089744549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90636043392957902059829699 135954065089436853089744549)
      ·
        refine ⟨25491387204269409954327103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135954065089436853089744549 25491387204269409954327103)
        ·
          refine ⟨38237080806404114931490655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25491387204269409954327103 38237080806404114931490655)
          ·
            refine ⟨57355621209606172397235983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38237080806404114931490655 57355621209606172397235983)
            ·
              refine ⟨86033431814409258595853975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57355621209606172397235983 86033431814409258595853975)
              ·
                refine ⟨129050147721613887893780963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86033431814409258595853975 129050147721613887893780963)
                ·
                  refine ⟨193575221582420831840671445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129050147721613887893780963 193575221582420831840671445)
                  ·
                    refine ⟨4536919255837988246265737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 193575221582420831840671445 4536919255837988246265737)
                    ·
                      refine ⟨3402689441878491184699303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4536919255837988246265737 3402689441878491184699303)
                      ·
                        rfl

theorem cell23_6626714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_6626714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626714 prefixEnd_6626714 := by exact prefixLift 6626714
  have htrace : WordTrace (prefixWord ++ tailWord_6626714) baseStart_6626714 baseEnd_6626714 := by
    simpa [prefixWord, tailWord_6626714, baseEnd_6626714] using wordTrace_append hprefix tailTrace_6626714
  have hstable : (prefixWord ++ tailWord_6626714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626714).length < 2 ^ (prefixWord ++ tailWord_6626714).sum := by decide
  have hdescent : baseEnd_6626714 < baseStart_6626714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626741 : List Nat := [1, 3, 3, 2, 2, 3, 1, 1, 2, 5]
def baseStart_6626741 : Nat := 118140960795 + 6626741 * 2 ^ 59
def prefixEnd_6626741 : Nat := 4983230072969 + 3 ^ 40 * 6626741 * 2
def baseEnd_6626741 : Nat := 1134234435285387526353893

theorem tailTrace_6626741 : CollatzResearch.WordTrace tailWord_6626741 prefixEnd_6626741 1134234435285387526353893 := by
  unfold tailWord_6626741
  simp only [CollatzResearch.WordTrace]
  refine ⟨241697100485456589104112077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161131400323637726069408051 241697100485456589104112077)
  ·
    refine ⟨90636412682046220914042029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241697100485456589104112077 90636412682046220914042029)
    ·
      refine ⟨33988654755767332842765761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90636412682046220914042029 33988654755767332842765761)
      ·
        refine ⟨25491491066825499632074321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33988654755767332842765761 25491491066825499632074321)
        ·
          refine ⟨19118618300119124724055741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25491491066825499632074321 19118618300119124724055741)
          ·
            refine ⟨7169481862544671771520903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19118618300119124724055741 7169481862544671771520903)
            ·
              refine ⟨10754222793817007657281355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7169481862544671771520903 10754222793817007657281355)
              ·
                refine ⟨16131334190725511485922033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10754222793817007657281355 16131334190725511485922033)
                ·
                  refine ⟨12098500643044133614441525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16131334190725511485922033 12098500643044133614441525)
                  ·
                    refine ⟨1134234435285387526353893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12098500643044133614441525 1134234435285387526353893)
                    ·
                      rfl

theorem cell23_6626741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_6626741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626741 prefixEnd_6626741 := by exact prefixLift 6626741
  have htrace : WordTrace (prefixWord ++ tailWord_6626741) baseStart_6626741 baseEnd_6626741 := by
    simpa [prefixWord, tailWord_6626741, baseEnd_6626741] using wordTrace_append hprefix tailTrace_6626741
  have hstable : (prefixWord ++ tailWord_6626741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626741).length < 2 ^ (prefixWord ++ tailWord_6626741).sum := by decide
  have hdescent : baseEnd_6626741 < baseStart_6626741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626744 : List Nat := [2, 1, 2, 1, 2, 2, 5, 1, 2, 1, 4]
def baseStart_6626744 : Nat := 118140960795 + 6626744 * 2 ^ 59
def prefixEnd_6626744 : Nat := 4983230072969 + 3 ^ 40 * 6626744 * 2
def baseEnd_6626744 : Nat := 3402704846298126067324165

theorem tailTrace_6626744 : CollatzResearch.WordTrace tailWord_6626744 prefixEnd_6626744 3402704846298126067324165 := by
  unfold tailWord_6626744
  simp only [CollatzResearch.WordTrace]
  refine ⟨120848604952222860308235643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161131473269630480410980857 120848604952222860308235643)
  ·
    refine ⟨181272907428334290462353465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120848604952222860308235643 181272907428334290462353465)
    ·
      refine ⟨135954680571250717846765099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181272907428334290462353465 135954680571250717846765099)
      ·
        refine ⟨203932020856876076770147649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135954680571250717846765099 203932020856876076770147649)
        ·
          refine ⟨152949015642657057577610737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203932020856876076770147649 152949015642657057577610737)
          ·
            refine ⟨114711761731992793183208053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152949015642657057577610737 114711761731992793183208053)
            ·
              refine ⟨10754227662374324360925755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114711761731992793183208053 10754227662374324360925755)
              ·
                refine ⟨16131341493561486541388633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10754227662374324360925755 16131341493561486541388633)
                ·
                  refine ⟨12098506120171114906041475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16131341493561486541388633 12098506120171114906041475)
                  ·
                    refine ⟨18147759180256672359062213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12098506120171114906041475 18147759180256672359062213)
                    ·
                      refine ⟨3402704846298126067324165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18147759180256672359062213 3402704846298126067324165)
                      ·
                        rfl

theorem cell23_6626744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_6626744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626744 prefixEnd_6626744 := by exact prefixLift 6626744
  have htrace : WordTrace (prefixWord ++ tailWord_6626744) baseStart_6626744 baseEnd_6626744 := by
    simpa [prefixWord, tailWord_6626744, baseEnd_6626744] using wordTrace_append hprefix tailTrace_6626744
  have hstable : (prefixWord ++ tailWord_6626744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626744).length < 2 ^ (prefixWord ++ tailWord_6626744).sum := by decide
  have hdescent : baseEnd_6626744 < baseStart_6626744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626805 : List Nat := [1, 3, 5, 1, 1, 1, 3, 3, 1, 4]
def baseStart_6626805 : Nat := 118140960795 + 6626805 * 2 ^ 59
def prefixEnd_6626805 : Nat := 4983230072969 + 3 ^ 40 * 6626805 * 2
def baseEnd_6626805 : Nat := 1134245389539350109553795

theorem tailTrace_6626805 : CollatzResearch.WordTrace tailWord_6626805 prefixEnd_6626805 1134245389539350109553795 := by
  unfold tailWord_6626805
  simp only [CollatzResearch.WordTrace]
  refine ⟨241699434757224728034441869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161132956504816485356294579 241699434757224728034441869)
  ·
    refine ⟨90637288033959273012915701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241699434757224728034441869 90637288033959273012915701)
    ·
      refine ⟨8497245753183681844960847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90637288033959273012915701 8497245753183681844960847)
      ·
        refine ⟨12745868629775522767441271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8497245753183681844960847 12745868629775522767441271)
        ·
          refine ⟨19118802944663284151161907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12745868629775522767441271 19118802944663284151161907)
          ·
            refine ⟨28678204416994926226742861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19118802944663284151161907 28678204416994926226742861)
            ·
              refine ⟨10754326656373097335028573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28678204416994926226742861 10754326656373097335028573)
              ·
                refine ⟨4032872496139911500635715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10754326656373097335028573 4032872496139911500635715)
                ·
                  refine ⟨6049308744209867250953573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4032872496139911500635715 6049308744209867250953573)
                  ·
                    refine ⟨1134245389539350109553795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6049308744209867250953573 1134245389539350109553795)
                    ·
                      rfl

theorem cell23_6626805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_6626805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626805 prefixEnd_6626805 := by exact prefixLift 6626805
  have htrace : WordTrace (prefixWord ++ tailWord_6626805) baseStart_6626805 baseEnd_6626805 := by
    simpa [prefixWord, tailWord_6626805, baseEnd_6626805] using wordTrace_append hprefix tailTrace_6626805
  have hstable : (prefixWord ++ tailWord_6626805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626805).length < 2 ^ (prefixWord ++ tailWord_6626805).sum := by decide
  have hdescent : baseEnd_6626805 < baseStart_6626805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626844 : List Nat := [2, 2, 3, 1, 2, 1, 2, 3, 1, 6]
def baseStart_6626844 : Nat := 118140960795 + 6626844 * 2 ^ 59
def prefixEnd_6626844 : Nat := 4983230072969 + 3 ^ 40 * 6626844 * 2
def baseEnd_6626844 : Nat := 1134252064787858558691235

theorem tailTrace_6626844 : CollatzResearch.WordTrace tailWord_6626844 prefixEnd_6626844 1134252064787858558691235 := by
  unfold tailWord_6626844
  simp only [CollatzResearch.WordTrace]
  refine ⟨120850428602041718847555793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161133904802722291796741057 120850428602041718847555793)
  ·
    refine ⟨90637821451531289135666845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120850428602041718847555793 90637821451531289135666845)
    ·
      refine ⟨33989183044324233425875067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90637821451531289135666845 33989183044324233425875067)
      ·
        refine ⟨50983774566486350138812601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33989183044324233425875067 50983774566486350138812601)
        ·
          refine ⟨38237830924864762604109451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50983774566486350138812601 38237830924864762604109451)
          ·
            refine ⟨57356746387297143906164177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38237830924864762604109451 57356746387297143906164177)
            ·
              refine ⟨43017559790472857929623133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57356746387297143906164177 43017559790472857929623133)
              ·
                refine ⟨16131584921427321723608675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43017559790472857929623133 16131584921427321723608675)
                ·
                  refine ⟨24197377382140982585413013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16131584921427321723608675 24197377382140982585413013)
                  ·
                    refine ⟨1134252064787858558691235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24197377382140982585413013 1134252064787858558691235)
                    ·
                      rfl

theorem cell23_6626844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_6626844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626844 prefixEnd_6626844 := by exact prefixLift 6626844
  have htrace : WordTrace (prefixWord ++ tailWord_6626844) baseStart_6626844 baseEnd_6626844 := by
    simpa [prefixWord, tailWord_6626844, baseEnd_6626844] using wordTrace_append hprefix tailTrace_6626844
  have hstable : (prefixWord ++ tailWord_6626844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626844).length < 2 ^ (prefixWord ++ tailWord_6626844).sum := by decide
  have hdescent : baseEnd_6626844 < baseStart_6626844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626848 : List Nat := [2, 1, 1, 6, 1, 3, 1, 2, 1, 5]
def baseStart_6626848 : Nat := 118140960795 + 6626848 * 2 ^ 59
def prefixEnd_6626848 : Nat := 4983230072969 + 3 ^ 40 * 6626848 * 2
def baseEnd_6626848 : Nat := 1134252749428731220141229

theorem tailTrace_6626848 : CollatzResearch.WordTrace tailWord_6626848 prefixEnd_6626848 1134252749428731220141229 := by
  unfold tailWord_6626848
  simp only [CollatzResearch.WordTrace]
  refine ⟨120850501548034473189128599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161134002064045964252171465 120850501548034473189128599)
  ·
    refine ⟨181275752322051709783692899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120850501548034473189128599 181275752322051709783692899)
    ·
      refine ⟨271913628483077564675539349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181275752322051709783692899 271913628483077564675539349)
      ·
        refine ⟨12745951335144260844165907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 271913628483077564675539349 12745951335144260844165907)
        ·
          refine ⟨19118927002716391266248861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12745951335144260844165907 19118927002716391266248861)
          ·
            refine ⟨7169597626018646724843323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19118927002716391266248861 7169597626018646724843323)
            ·
              refine ⟨10754396439027970087264985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7169597626018646724843323 10754396439027970087264985)
              ·
                refine ⟨8065797329270977565448739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10754396439027970087264985 8065797329270977565448739)
                ·
                  refine ⟨12098695993906466348173109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8065797329270977565448739 12098695993906466348173109)
                  ·
                    refine ⟨1134252749428731220141229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12098695993906466348173109 1134252749428731220141229)
                    ·
                      rfl

theorem cell23_6626848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 1, 5].length) (baseStart_6626848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626848 prefixEnd_6626848 := by exact prefixLift 6626848
  have htrace : WordTrace (prefixWord ++ tailWord_6626848) baseStart_6626848 baseEnd_6626848 := by
    simpa [prefixWord, tailWord_6626848, baseEnd_6626848] using wordTrace_append hprefix tailTrace_6626848
  have hstable : (prefixWord ++ tailWord_6626848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626848).length < 2 ^ (prefixWord ++ tailWord_6626848).sum := by decide
  have hdescent : baseEnd_6626848 < baseStart_6626848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626851 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 4]
def baseStart_6626851 : Nat := 118140960795 + 6626851 * 2 ^ 59
def prefixEnd_6626851 : Nat := 4983230072969 + 3 ^ 40 * 6626851 * 2
def baseEnd_6626851 : Nat := 3402759788728157148686173

theorem tailTrace_6626851 : CollatzResearch.WordTrace tailWord_6626851 prefixEnd_6626851 3402759788728157148686173 := by
  unfold tailWord_6626851
  simp only [CollatzResearch.WordTrace]
  refine ⟨241701112515058077890616407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161134075010038718593744271 241701112515058077890616407)
  ·
    refine ⟨362551668772587116835924611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241701112515058077890616407 362551668772587116835924611)
    ·
      refine ⟨543827503158880675253886917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362551668772587116835924611 543827503158880675253886917)
      ·
        refine ⟨101967656842290126610103797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 543827503158880675253886917 101967656842290126610103797)
        ·
          refine ⟨9559467828964699369697231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101967656842290126610103797 9559467828964699369697231)
          ·
            refine ⟨14339201743447049054545847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9559467828964699369697231 14339201743447049054545847)
            ·
              refine ⟨21508802615170573581818771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14339201743447049054545847 21508802615170573581818771)
              ·
                refine ⟨32263203922755860372728157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21508802615170573581818771 32263203922755860372728157)
                ·
                  refine ⟨12098701471033447639773059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32263203922755860372728157 12098701471033447639773059)
                  ·
                    refine ⟨18148052206550171459659589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12098701471033447639773059 18148052206550171459659589)
                    ·
                      refine ⟨3402759788728157148686173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18148052206550171459659589 3402759788728157148686173)
                      ·
                        rfl

theorem cell23_6626851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_6626851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626851 prefixEnd_6626851 := by exact prefixLift 6626851
  have htrace : WordTrace (prefixWord ++ tailWord_6626851) baseStart_6626851 baseEnd_6626851 := by
    simpa [prefixWord, tailWord_6626851, baseEnd_6626851] using wordTrace_append hprefix tailTrace_6626851
  have hstable : (prefixWord ++ tailWord_6626851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626851).length < 2 ^ (prefixWord ++ tailWord_6626851).sum := by decide
  have hdescent : baseEnd_6626851 < baseStart_6626851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626871 : List Nat := [1, 1, 3, 1, 2, 6, 1, 1, 1, 1, 5]
def baseStart_6626871 : Nat := 118140960795 + 6626871 * 2 ^ 59
def prefixEnd_6626871 : Nat := 4983230072969 + 3 ^ 40 * 6626871 * 2
def baseEnd_6626871 : Nat := 3402770058341247070436081

theorem tailTrace_6626871 : CollatzResearch.WordTrace tailWord_6626871 prefixEnd_6626871 3402770058341247070436081 := by
  unfold tailWord_6626871
  simp only [CollatzResearch.WordTrace]
  refine ⟨241701841974985621306344467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161134561316657080870896311 241701841974985621306344467)
  ·
    refine ⟨362552762962478431959516701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241701841974985621306344467 362552762962478431959516701)
    ·
      refine ⟨135957286110929411984818763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362552762962478431959516701 135957286110929411984818763)
      ·
        refine ⟨203935929166394117977228145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135957286110929411984818763 203935929166394117977228145)
        ·
          refine ⟨152951946874795588482921109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203935929166394117977228145 152951946874795588482921109)
          ·
            refine ⟨7169622509756043210136927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152951946874795588482921109 7169622509756043210136927)
            ·
              refine ⟨10754433764634064815205391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7169622509756043210136927 10754433764634064815205391)
              ·
                refine ⟨16131650646951097222808087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10754433764634064815205391 16131650646951097222808087)
                ·
                  refine ⟨24197475970426645834212131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16131650646951097222808087 24197475970426645834212131)
                  ·
                    refine ⟨36296213955639968751318197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24197475970426645834212131 36296213955639968751318197)
                    ·
                      refine ⟨3402770058341247070436081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36296213955639968751318197 3402770058341247070436081)
                      ·
                        rfl

theorem cell23_6626871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 1, 5].length) (baseStart_6626871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626871 prefixEnd_6626871 := by exact prefixLift 6626871
  have htrace : WordTrace (prefixWord ++ tailWord_6626871) baseStart_6626871 baseEnd_6626871 := by
    simpa [prefixWord, tailWord_6626871, baseEnd_6626871] using wordTrace_append hprefix tailTrace_6626871
  have hstable : (prefixWord ++ tailWord_6626871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626871).length < 2 ^ (prefixWord ++ tailWord_6626871).sum := by decide
  have hdescent : baseEnd_6626871 < baseStart_6626871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626885 : List Nat := [1, 3, 1, 1, 1, 4, 3, 4, 1, 2, 2]
def baseStart_6626885 : Nat := 118140960795 + 6626885 * 2 ^ 59
def prefixEnd_6626885 : Nat := 4983230072969 + 3 ^ 40 * 6626885 * 2
def baseEnd_6626885 : Nat := 3402777247070410015661017

theorem tailTrace_6626885 : CollatzResearch.WordTrace tailWord_6626885 prefixEnd_6626885 3402777247070410015661017 := by
  unfold tailWord_6626885
  simp only [CollatzResearch.WordTrace]
  refine ⟨241702352596934901697354109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161134901731289934464902739 241702352596934901697354109)
  ·
    refine ⟨90638382223850588136507791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241702352596934901697354109 90638382223850588136507791)
    ·
      refine ⟨135957573335775882204761687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90638382223850588136507791 135957573335775882204761687)
      ·
        refine ⟨203936360003663823307142531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135957573335775882204761687 203936360003663823307142531)
        ·
          refine ⟨305904540005495734960713797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203936360003663823307142531 305904540005495734960713797)
          ·
            refine ⟨57357101251030450305133837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 305904540005495734960713797 57357101251030450305133837)
            ·
              refine ⟨21508912969136418864425189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57357101251030450305133837 21508912969136418864425189)
              ·
                refine ⟨4032921181713078537079723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21508912969136418864425189 4032921181713078537079723)
                ·
                  refine ⟨6049381772569617805619585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4032921181713078537079723 6049381772569617805619585)
                  ·
                    refine ⟨4537036329427213354214689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6049381772569617805619585 4537036329427213354214689)
                    ·
                      refine ⟨3402777247070410015661017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4537036329427213354214689 3402777247070410015661017)
                      ·
                        rfl

theorem cell23_6626885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 1, 2, 2].length) (baseStart_6626885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626885 prefixEnd_6626885 := by exact prefixLift 6626885
  have htrace : WordTrace (prefixWord ++ tailWord_6626885) baseStart_6626885 baseEnd_6626885 := by
    simpa [prefixWord, tailWord_6626885, baseEnd_6626885] using wordTrace_append hprefix tailTrace_6626885
  have hstable : (prefixWord ++ tailWord_6626885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626885).length < 2 ^ (prefixWord ++ tailWord_6626885).sum := by decide
  have hdescent : baseEnd_6626885 < baseStart_6626885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626901 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 6, 1, 3]
def baseStart_6626901 : Nat := 118140960795 + 6626901 * 2 ^ 59
def prefixEnd_6626901 : Nat := 4983230072969 + 3 ^ 40 * 6626901 * 2
def baseEnd_6626901 : Nat := 3402785462760881953060943

theorem tailTrace_6626901 : CollatzResearch.WordTrace tailWord_6626901 prefixEnd_6626901 3402785462760881953060943 := by
  unfold tailWord_6626901
  simp only [CollatzResearch.WordTrace]
  refine ⟨241702936164876936429936557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161135290776584624286624371 241702936164876936429936557)
  ·
    refine ⟨90638601061828851161226209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241702936164876936429936557 90638601061828851161226209)
    ·
      refine ⟨67978950796371638370919657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90638601061828851161226209 67978950796371638370919657)
      ·
        refine ⟨50984213097278728778189743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67978950796371638370919657 50984213097278728778189743)
        ·
          refine ⟨76476319645918093167284615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50984213097278728778189743 76476319645918093167284615)
          ·
            refine ⟨114714479468877139750926923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76476319645918093167284615 114714479468877139750926923)
            ·
              refine ⟨172071719203315709626390385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114714479468877139750926923 172071719203315709626390385)
              ·
                refine ⟨129053789402486782219792789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172071719203315709626390385 129053789402486782219792789)
                ·
                  refine ⟨6049396378241567916552787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129053789402486782219792789 6049396378241567916552787)
                  ·
                    refine ⟨9074094567362351874829181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6049396378241567916552787 9074094567362351874829181)
                    ·
                      refine ⟨3402785462760881953060943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9074094567362351874829181 3402785462760881953060943)
                      ·
                        rfl

theorem cell23_6626901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_6626901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626901 prefixEnd_6626901 := by exact prefixLift 6626901
  have htrace : WordTrace (prefixWord ++ tailWord_6626901) baseStart_6626901 baseEnd_6626901 := by
    simpa [prefixWord, tailWord_6626901, baseEnd_6626901] using wordTrace_append hprefix tailTrace_6626901
  have hstable : (prefixWord ++ tailWord_6626901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626901).length < 2 ^ (prefixWord ++ tailWord_6626901).sum := by decide
  have hdescent : baseEnd_6626901 < baseStart_6626901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626952 : List Nat := [2, 1, 3, 5, 2, 1, 1, 1, 1, 3, 3]
def baseStart_6626952 : Nat := 118140960795 + 6626952 * 2 ^ 59
def prefixEnd_6626952 : Nat := 4983230072969 + 3 ^ 40 * 6626952 * 2
def baseEnd_6626952 : Nat := 3402811650274261253523209

theorem tailTrace_6626952 : CollatzResearch.WordTrace tailWord_6626952 prefixEnd_6626952 3402811650274261253523209 := by
  unfold tailWord_6626952
  simp only [CollatzResearch.WordTrace]
  refine ⟨120852398143846086070021555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161136530858461448093362073 120852398143846086070021555)
  ·
    refine ⟨181278597215769129105032333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120852398143846086070021555 181278597215769129105032333)
    ·
      refine ⟨67979473955913423414387125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181278597215769129105032333 67979473955913423414387125)
      ·
        refine ⟨6373075683366883445098793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67979473955913423414387125 6373075683366883445098793)
        ·
          refine ⟨4779806762525162583824095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6373075683366883445098793 4779806762525162583824095)
          ·
            refine ⟨7169710143787743875736143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4779806762525162583824095 7169710143787743875736143)
            ·
              refine ⟨10754565215681615813604215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7169710143787743875736143 10754565215681615813604215)
              ·
                refine ⟨16131847823522423720406323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10754565215681615813604215 16131847823522423720406323)
                ·
                  refine ⟨24197771735283635580609485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16131847823522423720406323 24197771735283635580609485)
                  ·
                    refine ⟨9074164400731363342728557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24197771735283635580609485 9074164400731363342728557)
                    ·
                      refine ⟨3402811650274261253523209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9074164400731363342728557 3402811650274261253523209)
                      ·
                        rfl

theorem cell23_6626952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_6626952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626952 prefixEnd_6626952 := by exact prefixLift 6626952
  have htrace : WordTrace (prefixWord ++ tailWord_6626952) baseStart_6626952 baseEnd_6626952 := by
    simpa [prefixWord, tailWord_6626952, baseEnd_6626952] using wordTrace_append hprefix tailTrace_6626952
  have hstable : (prefixWord ++ tailWord_6626952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626952).length < 2 ^ (prefixWord ++ tailWord_6626952).sum := by decide
  have hdescent : baseEnd_6626952 < baseStart_6626952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6626962 : List Nat := [3, 2, 3, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_6626962 : Nat := 118140960795 + 6626962 * 2 ^ 59
def prefixEnd_6626962 : Nat := 4983230072969 + 3 ^ 40 * 6626962 * 2
def baseEnd_6626962 : Nat := 3402816785080806214398163

theorem tailTrace_6626962 : CollatzResearch.WordTrace tailWord_6626962 prefixEnd_6626962 3402816785080806214398163 := by
  unfold tailWord_6626962
  simp only [CollatzResearch.WordTrace]
  refine ⟨60426290254413985961976785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161136774011770629231938093 60426290254413985961976785)
  ·
    refine ⟨45319717690810489471482589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60426290254413985961976785 45319717690810489471482589)
    ·
      refine ⟨16994894134053933551805971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45319717690810489471482589 16994894134053933551805971)
      ·
        refine ⟨25492341201080900327708957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16994894134053933551805971 25492341201080900327708957)
        ·
          refine ⟨9559627950405337622890859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25492341201080900327708957 9559627950405337622890859)
          ·
            refine ⟨14339441925608006434336289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9559627950405337622890859 14339441925608006434336289)
            ·
              refine ⟨10754581444206004825752217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14339441925608006434336289 10754581444206004825752217)
              ·
                refine ⟨8065936083154503619314163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10754581444206004825752217 8065936083154503619314163)
                ·
                  refine ⟨12098904124731755428971245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8065936083154503619314163 12098904124731755428971245)
                  ·
                    refine ⟨4537089046774408285864217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12098904124731755428971245 4537089046774408285864217)
                    ·
                      refine ⟨3402816785080806214398163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4537089046774408285864217 3402816785080806214398163)
                      ·
                        rfl

theorem cell23_6626962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_6626962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6626962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6626962 prefixEnd_6626962 := by exact prefixLift 6626962
  have htrace : WordTrace (prefixWord ++ tailWord_6626962) baseStart_6626962 baseEnd_6626962 := by
    simpa [prefixWord, tailWord_6626962, baseEnd_6626962] using wordTrace_append hprefix tailTrace_6626962
  have hstable : (prefixWord ++ tailWord_6626962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6626962).length < 2 ^ (prefixWord ++ tailWord_6626962).sum := by decide
  have hdescent : baseEnd_6626962 < baseStart_6626962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6626962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627028 : List Nat := [2, 4, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_6627028 : Nat := 118140960795 + 6627028 * 2 ^ 59
def prefixEnd_6627028 : Nat := 4983230072969 + 3 ^ 40 * 6627028 * 2
def baseEnd_6627028 : Nat := 1134283558268000985390953

theorem tailTrace_6627028 : CollatzResearch.WordTrace tailWord_6627028 prefixEnd_6627028 1134283558268000985390953 := by
  unfold tailWord_6627028
  simp only [CollatzResearch.WordTrace]
  refine ⟨120853784117708418559904869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161138378823611224746539825 120853784117708418559904869)
  ·
    refine ⟨22660084522070328479982163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120853784117708418559904869 22660084522070328479982163)
    ·
      refine ⟨33990126783105492719973245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22660084522070328479982163 33990126783105492719973245)
      ·
        refine ⟨12746297543664559769989967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33990126783105492719973245 12746297543664559769989967)
        ·
          refine ⟨19119446315496839654984951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12746297543664559769989967 19119446315496839654984951)
          ·
            refine ⟨28679169473245259482477427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19119446315496839654984951 28679169473245259482477427)
            ·
              refine ⟨43018754209867889223716141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28679169473245259482477427 43018754209867889223716141)
              ·
                refine ⟨16132032828700458458893553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43018754209867889223716141 16132032828700458458893553)
                ·
                  refine ⟨12099024621525343844170165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16132032828700458458893553 12099024621525343844170165)
                  ·
                    refine ⟨1134283558268000985390953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12099024621525343844170165 1134283558268000985390953)
                    ·
                      rfl

theorem cell23_6627028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_6627028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627028 prefixEnd_6627028 := by exact prefixLift 6627028
  have htrace : WordTrace (prefixWord ++ tailWord_6627028) baseStart_6627028 baseEnd_6627028 := by
    simpa [prefixWord, tailWord_6627028, baseEnd_6627028] using wordTrace_append hprefix tailTrace_6627028
  have hstable : (prefixWord ++ tailWord_6627028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627028).length < 2 ^ (prefixWord ++ tailWord_6627028).sum := by decide
  have hdescent : baseEnd_6627028 < baseStart_6627028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627048 : List Nat := [2, 1, 4, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_6627048 : Nat := 118140960795 + 6627048 * 2 ^ 59
def prefixEnd_6627048 : Nat := 4983230072969 + 3 ^ 40 * 6627048 * 2
def baseEnd_6627048 : Nat := 3402860944417092877922767

theorem tailTrace_6627048 : CollatzResearch.WordTrace tailWord_6627048 prefixEnd_6627048 3402860944417092877922767 := by
  unfold tailWord_6627048
  simp only [CollatzResearch.WordTrace]
  refine ⟨120854148847672190267768899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161138865130229587023691865 120854148847672190267768899)
  ·
    refine ⟨181281223271508285401653349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120854148847672190267768899 181281223271508285401653349)
    ·
      refine ⟨33990229363407803512810003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181281223271508285401653349 33990229363407803512810003)
      ·
        refine ⟨50985344045111705269215005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33990229363407803512810003 50985344045111705269215005)
        ·
          refine ⟨19119504016916889475955627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50985344045111705269215005 19119504016916889475955627)
          ·
            refine ⟨28679256025375334213933441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19119504016916889475955627 28679256025375334213933441)
            ·
              refine ⟨21509442019031500660450081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28679256025375334213933441 21509442019031500660450081)
              ·
                refine ⟨16132081514273625495337561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21509442019031500660450081 16132081514273625495337561)
                ·
                  refine ⟨12099061135705219121503171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16132081514273625495337561 12099061135705219121503171)
                  ·
                    refine ⟨18148591703557828682254757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12099061135705219121503171 18148591703557828682254757)
                    ·
                      refine ⟨3402860944417092877922767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18148591703557828682254757 3402860944417092877922767)
                      ·
                        rfl

theorem cell23_6627048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_6627048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627048 prefixEnd_6627048 := by exact prefixLift 6627048
  have htrace : WordTrace (prefixWord ++ tailWord_6627048) baseStart_6627048 baseEnd_6627048 := by
    simpa [prefixWord, tailWord_6627048, baseEnd_6627048] using wordTrace_append hprefix tailTrace_6627048
  have hstable : (prefixWord ++ tailWord_6627048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627048).length < 2 ^ (prefixWord ++ tailWord_6627048).sum := by decide
  have hdescent : baseEnd_6627048 < baseStart_6627048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627058 : List Nat := [3, 2, 1, 3, 1, 1, 2, 3, 3, 4]
def baseStart_6627058 : Nat := 118140960795 + 6627058 * 2 ^ 59
def prefixEnd_6627058 : Nat := 4983230072969 + 3 ^ 40 * 6627058 * 2
def baseEnd_6627058 : Nat := 1134288693074545946265907

theorem tailTrace_6627058 : CollatzResearch.WordTrace tailWord_6627058 prefixEnd_6627058 1134288693074545946265907 := by
  unfold tailWord_6627058
  simp only [CollatzResearch.WordTrace]
  refine ⟨60427165606327038060850457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161139108283538768162267885 60427165606327038060850457)
  ·
    refine ⟨45320374204745278545637843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60427165606327038060850457 45320374204745278545637843)
    ·
      refine ⟨67980561307117917818456765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45320374204745278545637843 67980561307117917818456765)
      ·
        refine ⟨25492710490169219181921287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67980561307117917818456765 25492710490169219181921287)
        ·
          refine ⟨38239065735253828772881931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25492710490169219181921287 38239065735253828772881931)
          ·
            refine ⟨57358598602880743159322897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38239065735253828772881931 57358598602880743159322897)
            ·
              refine ⟨43018948952160557369492173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57358598602880743159322897 43018948952160557369492173)
              ·
                refine ⟨16132105857060209013559565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43018948952160557369492173 16132105857060209013559565)
                ·
                  refine ⟨6049539696397578380084837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16132105857060209013559565 6049539696397578380084837)
                  ·
                    refine ⟨1134288693074545946265907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6049539696397578380084837 1134288693074545946265907)
                    ·
                      rfl

theorem cell23_6627058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_6627058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627058 prefixEnd_6627058 := by exact prefixLift 6627058
  have htrace : WordTrace (prefixWord ++ tailWord_6627058) baseStart_6627058 baseEnd_6627058 := by
    simpa [prefixWord, tailWord_6627058, baseEnd_6627058] using wordTrace_append hprefix tailTrace_6627058
  have hstable : (prefixWord ++ tailWord_6627058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627058).length < 2 ^ (prefixWord ++ tailWord_6627058).sum := by decide
  have hdescent : baseEnd_6627058 < baseStart_6627058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627071 : List Nat := [1, 1, 2, 2, 1, 3, 4, 3, 6]
def baseStart_6627071 : Nat := 118140960795 + 6627071 * 2 ^ 59
def prefixEnd_6627071 : Nat := 4983230072969 + 3 ^ 40 * 6627071 * 2
def baseEnd_6627071 : Nat := 378096972719127365326129

theorem tailTrace_6627071 : CollatzResearch.WordTrace tailWord_6627071 prefixEnd_6627071 378096972719127365326129 := by
  unfold tailWord_6627071
  simp only [CollatzResearch.WordTrace]
  refine ⟨241709136574261055463625067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161139424382840703642416711 241709136574261055463625067)
  ·
    refine ⟨362563704861391583195437601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241709136574261055463625067 362563704861391583195437601)
    ·
      refine ⟨271922778646043687396578201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362563704861391583195437601 271922778646043687396578201)
      ·
        refine ⟨203942083984532765547433651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271922778646043687396578201 203942083984532765547433651)
        ·
          refine ⟨305913125976799148321150477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203942083984532765547433651 305913125976799148321150477)
          ·
            refine ⟨114717422241299680620431429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305913125976799148321150477 114717422241299680620431429)
            ·
              refine ⟨21509516670243690116330893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114717422241299680620431429 21509516670243690116330893)
              ·
                refine ⟨8066068751341383793624085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21509516670243690116330893 8066068751341383793624085)
                ·
                  refine ⟨378096972719127365326129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8066068751341383793624085 378096972719127365326129)
                  ·
                    rfl

theorem cell23_6627071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 6].length) (baseStart_6627071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627071 prefixEnd_6627071 := by exact prefixLift 6627071
  have htrace : WordTrace (prefixWord ++ tailWord_6627071) baseStart_6627071 baseEnd_6627071 := by
    simpa [prefixWord, tailWord_6627071, baseEnd_6627071] using wordTrace_append hprefix tailTrace_6627071
  have hstable : (prefixWord ++ tailWord_6627071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627071).length < 2 ^ (prefixWord ++ tailWord_6627071).sum := by decide
  have hdescent : baseEnd_6627071 < baseStart_6627071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627135 : List Nat := [1, 1, 2, 2, 6, 1, 2, 2, 1, 5]
def baseStart_6627135 : Nat := 118140960795 + 6627135 * 2 ^ 59
def prefixEnd_6627135 : Nat := 4983230072969 + 3 ^ 40 * 6627135 * 2
def baseEnd_6627135 : Nat := 1134301872411344679178289

theorem tailTrace_6627135 : CollatzResearch.WordTrace tailWord_6627135 prefixEnd_6627135 1134301872411344679178289 := by
  unfold tailWord_6627135
  simp only [CollatzResearch.WordTrace]
  refine ⟨241711470846029194393954859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161140980564019462929303239 241711470846029194393954859)
  ·
    refine ⟨362567206269043791590932289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241711470846029194393954859 362567206269043791590932289)
    ·
      refine ⟨271925404701782843693199217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362567206269043791590932289 271925404701782843693199217)
      ·
        refine ⟨203944053526337132769899413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271925404701782843693199217 203944053526337132769899413)
        ·
          refine ⟨9559877509047053098589035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 203944053526337132769899413 9559877509047053098589035)
          ·
            refine ⟨14339816263570579647883553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9559877509047053098589035 14339816263570579647883553)
            ·
              refine ⟨10754862197677934735912665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14339816263570579647883553 10754862197677934735912665)
              ·
                refine ⟨8066146648258451051934499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10754862197677934735912665 8066146648258451051934499)
                ·
                  refine ⟨12099219972387676577901749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8066146648258451051934499 12099219972387676577901749)
                  ·
                    refine ⟨1134301872411344679178289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12099219972387676577901749 1134301872411344679178289)
                    ·
                      rfl

theorem cell23_6627135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 5].length) (baseStart_6627135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627135 prefixEnd_6627135 := by exact prefixLift 6627135
  have htrace : WordTrace (prefixWord ++ tailWord_6627135) baseStart_6627135 baseEnd_6627135 := by
    simpa [prefixWord, tailWord_6627135, baseEnd_6627135] using wordTrace_append hprefix tailTrace_6627135
  have hstable : (prefixWord ++ tailWord_6627135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627135).length < 2 ^ (prefixWord ++ tailWord_6627135).sum := by decide
  have hdescent : baseEnd_6627135 < baseStart_6627135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627141 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 3, 1, 5]
def baseStart_6627141 : Nat := 118140960795 + 6627141 * 2 ^ 59
def prefixEnd_6627141 : Nat := 4983230072969 + 3 ^ 40 * 6627141 * 2
def baseEnd_6627141 : Nat := 3402908698117961014059839

theorem tailTrace_6627141 : CollatzResearch.WordTrace tailWord_6627141 prefixEnd_6627141 3402908698117961014059839 := by
  unfold tailWord_6627141
  simp only [CollatzResearch.WordTrace]
  refine ⟨241711689684007457418673277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161141126456004971612448851 241711689684007457418673277)
  ·
    refine ⟨90641883631502796532002479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241711689684007457418673277 90641883631502796532002479)
    ·
      refine ⟨135962825447254194798003719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90641883631502796532002479 135962825447254194798003719)
      ·
        refine ⟨203944238170881292197005579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135962825447254194798003719 203944238170881292197005579)
        ·
          refine ⟨305916357256321938295508369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203944238170881292197005579 305916357256321938295508369)
          ·
            refine ⟨229437267942241453721631277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305916357256321938295508369 229437267942241453721631277)
            ·
              refine ⟨86038975478340545145611729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229437267942241453721631277 86038975478340545145611729)
              ·
                refine ⟨64529231608755408859208797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86038975478340545145611729 64529231608755408859208797)
                ·
                  refine ⟨24198461853283278322203299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64529231608755408859208797 24198461853283278322203299)
                  ·
                    refine ⟨36297692779924917483304949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24198461853283278322203299 36297692779924917483304949)
                    ·
                      refine ⟨3402908698117961014059839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36297692779924917483304949 3402908698117961014059839)
                      ·
                        rfl

theorem cell23_6627141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_6627141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627141 prefixEnd_6627141 := by exact prefixLift 6627141
  have htrace : WordTrace (prefixWord ++ tailWord_6627141) baseStart_6627141 baseEnd_6627141 := by
    simpa [prefixWord, tailWord_6627141, baseEnd_6627141] using wordTrace_append hprefix tailTrace_6627141
  have hstable : (prefixWord ++ tailWord_6627141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627141).length < 2 ^ (prefixWord ++ tailWord_6627141).sum := by decide
  have hdescent : baseEnd_6627141 < baseStart_6627141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627182 : List Nat := [4, 1, 2, 3, 1, 2, 1, 3, 2, 4]
def baseStart_6627182 : Nat := 118140960795 + 6627182 * 2 ^ 59
def prefixEnd_6627182 : Nat := 4983230072969 + 3 ^ 40 * 6627182 * 2
def baseEnd_6627182 : Nat := 1134309916941598451215717

theorem tailTrace_6627182 : CollatzResearch.WordTrace tailWord_6627182 prefixEnd_6627182 1134309916941598451215717 := by
  unfold tailWord_6627182
  simp only [CollatzResearch.WordTrace]
  refine ⟨30214148134607365177614475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161142123384572614280610533 30214148134607365177614475)
  ·
    refine ⟨45321222201911047766421713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30214148134607365177614475 45321222201911047766421713)
    ·
      refine ⟨33990916651433285824816285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45321222201911047766421713 33990916651433285824816285)
      ·
        refine ⟨12746593744287482184306107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33990916651433285824816285 12746593744287482184306107)
        ·
          refine ⟨19119890616431223276459161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12746593744287482184306107 19119890616431223276459161)
          ·
            refine ⟨14339917962323417457344371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19119890616431223276459161 14339917962323417457344371)
            ·
              refine ⟨21509876943485126186016557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14339917962323417457344371 21509876943485126186016557)
              ·
                refine ⟨8066203853806922319756209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21509876943485126186016557 8066203853806922319756209)
                ·
                  refine ⟨6049652890355191739817157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8066203853806922319756209 6049652890355191739817157)
                  ·
                    refine ⟨1134309916941598451215717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6049652890355191739817157 1134309916941598451215717)
                    ·
                      rfl

theorem cell23_6627182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_6627182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627182 prefixEnd_6627182 := by exact prefixLift 6627182
  have htrace : WordTrace (prefixWord ++ tailWord_6627182) baseStart_6627182 baseEnd_6627182 := by
    simpa [prefixWord, tailWord_6627182, baseEnd_6627182] using wordTrace_append hprefix tailTrace_6627182
  have hstable : (prefixWord ++ tailWord_6627182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627182).length < 2 ^ (prefixWord ++ tailWord_6627182).sum := by decide
  have hdescent : baseEnd_6627182 < baseStart_6627182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627262 : List Nat := [4, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2]
def baseStart_6627262 : Nat := 118140960795 + 6627262 * 2 ^ 59
def prefixEnd_6627262 : Nat := 4983230072969 + 3 ^ 40 * 6627262 * 2
def baseEnd_6627262 : Nat := 3402970829277155040646783

theorem tailTrace_6627262 : CollatzResearch.WordTrace tailWord_6627262 prefixEnd_6627262 3402970829277155040646783 := by
  unfold tailWord_6627262
  simp only [CollatzResearch.WordTrace]
  refine ⟨30214512864571136885478505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161144068611046063389218693 30214512864571136885478505)
  ·
    refine ⟨22660884648428352664108879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30214512864571136885478505 22660884648428352664108879)
    ·
      refine ⟨33991326972642528996163319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22660884648428352664108879 33991326972642528996163319)
      ·
        refine ⟨50986990458963793494244979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33991326972642528996163319 50986990458963793494244979)
        ·
          refine ⟨76480485688445690241367469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50986990458963793494244979 76480485688445690241367469)
          ·
            refine ⟨28680182133167133840512801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76480485688445690241367469 28680182133167133840512801)
            ·
              refine ⟨21510136599875350380384601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28680182133167133840512801 21510136599875350380384601)
              ·
                refine ⟨16132602449906512785288451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21510136599875350380384601 16132602449906512785288451)
                ·
                  refine ⟨24198903674859769177932677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16132602449906512785288451 24198903674859769177932677)
                  ·
                    refine ⟨4537294439036206720862377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24198903674859769177932677 4537294439036206720862377)
                    ·
                      refine ⟨3402970829277155040646783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4537294439036206720862377 3402970829277155040646783)
                      ·
                        rfl

theorem cell23_6627262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_6627262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627262 prefixEnd_6627262 := by exact prefixLift 6627262
  have htrace : WordTrace (prefixWord ++ tailWord_6627262) baseStart_6627262 baseEnd_6627262 := by
    simpa [prefixWord, tailWord_6627262, baseEnd_6627262] using wordTrace_append hprefix tailTrace_6627262
  have hstable : (prefixWord ++ tailWord_6627262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627262).length < 2 ^ (prefixWord ++ tailWord_6627262).sum := by decide
  have hdescent : baseEnd_6627262 < baseStart_6627262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627285 : List Nat := [1, 3, 2, 3, 2, 2, 2, 1, 7]
def baseStart_6627285 : Nat := 118140960795 + 6627285 * 2 ^ 59
def prefixEnd_6627285 : Nat := 4983230072969 + 3 ^ 40 * 6627285 * 2
def baseEnd_6627285 : Nat := 378109182148023161184353

theorem tailTrace_6627285 : CollatzResearch.WordTrace tailWord_6627285 prefixEnd_6627285 378109182148023161184353 := by
  unfold tailWord_6627285
  simp only [CollatzResearch.WordTrace]
  refine ⟨241716941795485770011915309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161144627863657180007943539 241716941795485770011915309)
  ·
    refine ⟨90643853173307163754468241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241716941795485770011915309 90643853173307163754468241)
    ·
      refine ⟨67982889879980372815851181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90643853173307163754468241 67982889879980372815851181)
      ·
        refine ⟨25493583704992639805944193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67982889879980372815851181 25493583704992639805944193)
        ·
          refine ⟨19120187778744479854458145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25493583704992639805944193 19120187778744479854458145)
          ·
            refine ⟨14340140834058359890843609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19120187778744479854458145 14340140834058359890843609)
            ·
              refine ⟨10755105625543769918132707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14340140834058359890843609 10755105625543769918132707)
              ·
                refine ⟨16132658438315654877199061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10755105625543769918132707 16132658438315654877199061)
                ·
                  refine ⟨378109182148023161184353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16132658438315654877199061 378109182148023161184353)
                  ·
                    rfl

theorem cell23_6627285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 7].length) (baseStart_6627285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627285 prefixEnd_6627285 := by exact prefixLift 6627285
  have htrace : WordTrace (prefixWord ++ tailWord_6627285) baseStart_6627285 baseEnd_6627285 := by
    simpa [prefixWord, tailWord_6627285, baseEnd_6627285] using wordTrace_append hprefix tailTrace_6627285
  have hstable : (prefixWord ++ tailWord_6627285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627285).length < 2 ^ (prefixWord ++ tailWord_6627285).sum := by decide
  have hdescent : baseEnd_6627285 < baseStart_6627285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627295 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 3]
def baseStart_6627295 : Nat := 118140960795 + 6627295 * 2 ^ 59
def prefixEnd_6627295 : Nat := 4983230072969 + 3 ^ 40 * 6627295 * 2
def baseEnd_6627295 : Nat := 3402987774138753411534131

theorem tailTrace_6627295 : CollatzResearch.WordTrace tailWord_6627295 prefixEnd_6627295 3402987774138753411534131 := by
  unfold tailWord_6627295
  simp only [CollatzResearch.WordTrace]
  refine ⟨241717306525449541719779339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161144871016966361146519559 241717306525449541719779339)
  ·
    refine ⟨362575959788174312579669009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241717306525449541719779339 362575959788174312579669009)
    ·
      refine ⟨271931969841130734434751757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362575959788174312579669009 271931969841130734434751757)
      ·
        refine ⟨101974488690424025413031909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271931969841130734434751757 101974488690424025413031909)
        ·
          refine ⟨19120216629454504764943483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101974488690424025413031909 19120216629454504764943483)
          ·
            refine ⟨28680324944181757147415225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19120216629454504764943483 28680324944181757147415225)
            ·
              refine ⟨21510243708136317860561419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28680324944181757147415225 21510243708136317860561419)
              ·
                refine ⟨32265365562204476790842129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21510243708136317860561419 32265365562204476790842129)
                ·
                  refine ⟨24199024171653357593131597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32265365562204476790842129 24199024171653357593131597)
                  ·
                    refine ⟨9074634064370009097424349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24199024171653357593131597 9074634064370009097424349)
                    ·
                      refine ⟨3402987774138753411534131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9074634064370009097424349 3402987774138753411534131)
                      ·
                        rfl

theorem cell23_6627295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_6627295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627295 prefixEnd_6627295 := by exact prefixLift 6627295
  have htrace : WordTrace (prefixWord ++ tailWord_6627295) baseStart_6627295 baseEnd_6627295 := by
    simpa [prefixWord, tailWord_6627295, baseEnd_6627295] using wordTrace_append hprefix tailTrace_6627295
  have hstable : (prefixWord ++ tailWord_6627295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627295).length < 2 ^ (prefixWord ++ tailWord_6627295).sum := by decide
  have hdescent : baseEnd_6627295 < baseStart_6627295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627335 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 4]
def baseStart_6627335 : Nat := 118140960795 + 6627335 * 2 ^ 59
def prefixEnd_6627335 : Nat := 4983230072969 + 3 ^ 40 * 6627335 * 2
def baseEnd_6627335 : Nat := 3403008313364933255033947

theorem tailTrace_6627335 : CollatzResearch.WordTrace tailWord_6627335 prefixEnd_6627335 3403008313364933255033947 := by
  unfold tailWord_6627335
  simp only [CollatzResearch.WordTrace]
  refine ⟨241718765445304628551235459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161145843630203085700823639 241718765445304628551235459)
  ·
    refine ⟨362578148167956942826853189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241718765445304628551235459 362578148167956942826853189)
    ·
      refine ⟨67983402781491926780034973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 362578148167956942826853189 67983402781491926780034973)
      ·
        refine ⟨25493776043059472542513115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67983402781491926780034973 25493776043059472542513115)
        ·
          refine ⟨38240664064589208813769673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25493776043059472542513115 38240664064589208813769673)
          ·
            refine ⟨28680498048441906610327255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38240664064589208813769673 28680498048441906610327255)
            ·
              refine ⟨43020747072662859915490883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28680498048441906610327255 43020747072662859915490883)
              ·
                refine ⟨64531120608994289873236325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43020747072662859915490883 64531120608994289873236325)
                ·
                  refine ⟨12099585114186429351231811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64531120608994289873236325 12099585114186429351231811)
                  ·
                    refine ⟨18149377671279644026847717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12099585114186429351231811 18149377671279644026847717)
                    ·
                      refine ⟨3403008313364933255033947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18149377671279644026847717 3403008313364933255033947)
                      ·
                        rfl

theorem cell23_6627335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_6627335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627335 prefixEnd_6627335 := by exact prefixLift 6627335
  have htrace : WordTrace (prefixWord ++ tailWord_6627335) baseStart_6627335 baseEnd_6627335 := by
    simpa [prefixWord, tailWord_6627335, baseEnd_6627335] using wordTrace_append hprefix tailTrace_6627335
  have hstable : (prefixWord ++ tailWord_6627335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627335).length < 2 ^ (prefixWord ++ tailWord_6627335).sum := by decide
  have hdescent : baseEnd_6627335 < baseStart_6627335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627402 : List Nat := [3, 1, 2, 1, 1, 2, 1, 5, 3, 1, 3]
def baseStart_6627402 : Nat := 118140960795 + 6627402 * 2 ^ 59
def prefixEnd_6627402 : Nat := 4983230072969 + 3 ^ 40 * 6627402 * 2
def baseEnd_6627402 : Nat := 3403042716568784492896139

theorem tailTrace_6627402 : CollatzResearch.WordTrace tailWord_6627402 prefixEnd_6627402 3403042716568784492896139 := by
  unfold tailWord_6627402
  simp only [CollatzResearch.WordTrace]
  refine ⟨60430302284015474748481115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161147472757374599329282973 60430302284015474748481115)
  ·
    refine ⟨90645453426023212122721673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60430302284015474748481115 90645453426023212122721673)
    ·
      refine ⟨67984090069517409092041255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90645453426023212122721673 67984090069517409092041255)
      ·
        refine ⟨101976135104276113638061883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67984090069517409092041255 101976135104276113638061883)
        ·
          refine ⟨152964202656414170457092825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101976135104276113638061883 152964202656414170457092825)
          ·
            refine ⟨114723151992310627842819619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152964202656414170457092825 114723151992310627842819619)
            ·
              refine ⟨172084727988465941764229429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114723151992310627842819619 172084727988465941764229429)
              ·
                refine ⟨16132943248918682040396509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172084727988465941764229429 16132943248918682040396509)
                ·
                  refine ⟨6049853718344505765148691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16132943248918682040396509 6049853718344505765148691)
                  ·
                    refine ⟨9074780577516758647723037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6049853718344505765148691 9074780577516758647723037)
                    ·
                      refine ⟨3403042716568784492896139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9074780577516758647723037 3403042716568784492896139)
                      ·
                        rfl

theorem cell23_6627402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_6627402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627402 prefixEnd_6627402 := by exact prefixLift 6627402
  have htrace : WordTrace (prefixWord ++ tailWord_6627402) baseStart_6627402 baseEnd_6627402 := by
    simpa [prefixWord, tailWord_6627402, baseEnd_6627402] using wordTrace_append hprefix tailTrace_6627402
  have hstable : (prefixWord ++ tailWord_6627402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627402).length < 2 ^ (prefixWord ++ tailWord_6627402).sum := by decide
  have hdescent : baseEnd_6627402 < baseStart_6627402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627412 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 1, 5, 2]
def baseStart_6627412 : Nat := 118140960795 + 6627412 * 2 ^ 59
def prefixEnd_6627412 : Nat := 4983230072969 + 3 ^ 40 * 6627412 * 2
def baseEnd_6627412 : Nat := 3403047851375329453771093

theorem tailTrace_6627412 : CollatzResearch.WordTrace tailWord_6627412 prefixEnd_6627412 3403047851375329453771093 := by
  unfold tailWord_6627412
  simp only [CollatzResearch.WordTrace]
  refine ⟨120860786933012835350894245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161147715910683780467858993 120860786933012835350894245)
  ·
    refine ⟨22661397549939906628292671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120860786933012835350894245 22661397549939906628292671)
    ·
      refine ⟨33992096324909859942439007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22661397549939906628292671 33992096324909859942439007)
      ·
        refine ⟨50988144487364789913658511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33992096324909859942439007 50988144487364789913658511)
        ·
          refine ⟨76482216731047184870487767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50988144487364789913658511 76482216731047184870487767)
          ·
            refine ⟨114723325096570777305731651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76482216731047184870487767 114723325096570777305731651)
            ·
              refine ⟨172084987644856165958597477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114723325096570777305731651 172084987644856165958597477)
              ·
                refine ⟨32265935183410531117237027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172084987644856165958597477 32265935183410531117237027)
                ·
                  refine ⟨48398902775115796675855541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32265935183410531117237027 48398902775115796675855541)
                  ·
                    refine ⟨4537397135167105938361457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48398902775115796675855541 4537397135167105938361457)
                    ·
                      refine ⟨3403047851375329453771093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4537397135167105938361457 3403047851375329453771093)
                      ·
                        rfl

theorem cell23_6627412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_6627412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627412 prefixEnd_6627412 := by exact prefixLift 6627412
  have htrace : WordTrace (prefixWord ++ tailWord_6627412) baseStart_6627412 baseEnd_6627412 := by
    simpa [prefixWord, tailWord_6627412, baseEnd_6627412] using wordTrace_append hprefix tailTrace_6627412
  have hstable : (prefixWord ++ tailWord_6627412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627412).length < 2 ^ (prefixWord ++ tailWord_6627412).sum := by decide
  have hdescent : baseEnd_6627412 < baseStart_6627412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627429 : List Nat := [1, 3, 1, 3, 2, 2, 3, 1, 2, 3, 2]
def baseStart_6627429 : Nat := 118140960795 + 6627429 * 2 ^ 59
def prefixEnd_6627429 : Nat := 4983230072969 + 3 ^ 40 * 6627429 * 2
def baseEnd_6627429 : Nat := 3403056580546455887258515

theorem tailTrace_6627429 : CollatzResearch.WordTrace tailWord_6627429 prefixEnd_6627429 3403056580546455887258515 := by
  unfold tailWord_6627429
  simp only [CollatzResearch.WordTrace]
  refine ⟨241722193906964082605157341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161148129271309388403438227 241722193906964082605157341)
  ·
    refine ⟨90645822715111530976934003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241722193906964082605157341 90645822715111530976934003)
    ·
      refine ⟨135968734072667296465401005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90645822715111530976934003 135968734072667296465401005)
      ·
        refine ⟨50988275277250236174525377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135968734072667296465401005 50988275277250236174525377)
        ·
          refine ⟨38241206457937677130894033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50988275277250236174525377 38241206457937677130894033)
          ·
            refine ⟨28680904843453257848170525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38241206457937677130894033 28680904843453257848170525)
            ·
              refine ⟨10755339316294971693063947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28680904843453257848170525 10755339316294971693063947)
              ·
                refine ⟨16133008974442457539595921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10755339316294971693063947 16133008974442457539595921)
                ·
                  refine ⟨12099756730831843154696941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16133008974442457539595921 12099756730831843154696941)
                  ·
                    refine ⟨4537408774061941183011353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12099756730831843154696941 4537408774061941183011353)
                    ·
                      refine ⟨3403056580546455887258515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4537408774061941183011353 3403056580546455887258515)
                      ·
                        rfl

theorem cell23_6627429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_6627429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627429 prefixEnd_6627429 := by exact prefixLift 6627429
  have htrace : WordTrace (prefixWord ++ tailWord_6627429) baseStart_6627429 baseEnd_6627429 := by
    simpa [prefixWord, tailWord_6627429, baseEnd_6627429] using wordTrace_append hprefix tailTrace_6627429
  have hstable : (prefixWord ++ tailWord_6627429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627429).length < 2 ^ (prefixWord ++ tailWord_6627429).sum := by decide
  have hdescent : baseEnd_6627429 < baseStart_6627429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627436 : List Nat := [2, 2, 1, 1, 3, 4, 2, 3, 1, 1, 3]
def baseStart_6627436 : Nat := 118140960795 + 6627436 * 2 ^ 59
def prefixEnd_6627436 : Nat := 4983230072969 + 3 ^ 40 * 6627436 * 2
def baseEnd_6627436 : Nat := 3403060174911037359870983

theorem tailTrace_6627436 : CollatzResearch.WordTrace tailWord_6627436 prefixEnd_6627436 3403060174911037359870983 := by
  unfold tailWord_6627436
  simp only [CollatzResearch.WordTrace]
  refine ⟨120861224608969361400331081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161148299478625815200441441 120861224608969361400331081)
  ·
    refine ⟨90645918456727021050248311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120861224608969361400331081 90645918456727021050248311)
    ·
      refine ⟨135968877685090531575372467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90645918456727021050248311 135968877685090531575372467)
      ·
        refine ⟨203953316527635797363058701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135968877685090531575372467 203953316527635797363058701)
        ·
          refine ⟨76482493697863424011147013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203953316527635797363058701 76482493697863424011147013)
          ·
            refine ⟨14340467568349392002090065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76482493697863424011147013 14340467568349392002090065)
            ·
              refine ⟨10755350676262044001567549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14340467568349392002090065 10755350676262044001567549)
              ·
                refine ⟨4033256503598266500587831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10755350676262044001567549 4033256503598266500587831)
                ·
                  refine ⟨6049884755397399750881747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4033256503598266500587831 6049884755397399750881747)
                  ·
                    refine ⟨9074827133096099626322621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6049884755397399750881747 9074827133096099626322621)
                    ·
                      refine ⟨3403060174911037359870983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9074827133096099626322621 3403060174911037359870983)
                      ·
                        rfl

theorem cell23_6627436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 1, 1, 3].length) (baseStart_6627436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627436 prefixEnd_6627436 := by exact prefixLift 6627436
  have htrace : WordTrace (prefixWord ++ tailWord_6627436) baseStart_6627436 baseEnd_6627436 := by
    simpa [prefixWord, tailWord_6627436, baseEnd_6627436] using wordTrace_append hprefix tailTrace_6627436
  have hstable : (prefixWord ++ tailWord_6627436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627436).length < 2 ^ (prefixWord ++ tailWord_6627436).sum := by decide
  have hdescent : baseEnd_6627436 < baseStart_6627436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627439 : List Nat := [1, 1, 2, 1, 3, 6, 2, 1, 1, 5]
def baseStart_6627439 : Nat := 118140960795 + 6627439 * 2 ^ 59
def prefixEnd_6627439 : Nat := 4983230072969 + 3 ^ 40 * 6627439 * 2
def baseEnd_6627439 : Nat := 1134353905117666949377823

theorem tailTrace_6627439 : CollatzResearch.WordTrace tailWord_6627439 prefixEnd_6627439 1134353905117666949377823 := by
  unfold tailWord_6627439
  simp only [CollatzResearch.WordTrace]
  refine ⟨241722558636927854313021371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161148372424618569542014247 241722558636927854313021371)
  ·
    refine ⟨362583837955391781469532057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241722558636927854313021371 362583837955391781469532057)
    ·
      refine ⟨271937878466543836102149043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362583837955391781469532057 271937878466543836102149043)
      ·
        refine ⟨407906817699815754153223565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271937878466543836102149043 407906817699815754153223565)
        ·
          refine ⟨152965056637430907807458837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407906817699815754153223565 152965056637430907807458837)
          ·
            refine ⟨7170237029879573803474633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152965056637430907807458837 7170237029879573803474633)
            ·
              refine ⟨5377677772409680352605975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7170237029879573803474633 5377677772409680352605975)
              ·
                refine ⟨8066516658614520528908963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5377677772409680352605975 8066516658614520528908963)
                ·
                  refine ⟨12099774987921780793363445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8066516658614520528908963 12099774987921780793363445)
                  ·
                    refine ⟨1134353905117666949377823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12099774987921780793363445 1134353905117666949377823)
                    ·
                      rfl

theorem cell23_6627439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 1, 5].length) (baseStart_6627439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627439 prefixEnd_6627439 := by exact prefixLift 6627439
  have htrace : WordTrace (prefixWord ++ tailWord_6627439) baseStart_6627439 baseEnd_6627439 := by
    simpa [prefixWord, tailWord_6627439, baseEnd_6627439] using wordTrace_append hprefix tailTrace_6627439
  have hstable : (prefixWord ++ tailWord_6627439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627439).length < 2 ^ (prefixWord ++ tailWord_6627439).sum := by decide
  have hdescent : baseEnd_6627439 < baseStart_6627439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627452 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 4, 4]
def baseStart_6627452 : Nat := 118140960795 + 6627452 * 2 ^ 59
def prefixEnd_6627452 : Nat := 4983230072969 + 3 ^ 40 * 6627452 * 2
def baseEnd_6627452 : Nat := 1134356130200503099090303

theorem tailTrace_6627452 : CollatzResearch.WordTrace tailWord_6627452 prefixEnd_6627452 1134356130200503099090303 := by
  unfold tailWord_6627452
  simp only [CollatzResearch.WordTrace]
  refine ⟨120861516392940378766622305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161148688523920505022163073 120861516392940378766622305)
  ·
    refine ⟨90646137294705284074966729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120861516392940378766622305 90646137294705284074966729)
    ·
      refine ⟨67984602971028963056225047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90646137294705284074966729 67984602971028963056225047)
      ·
        refine ⟨101976904456543444584337571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67984602971028963056225047 101976904456543444584337571)
        ·
          refine ⟨152965356684815166876506357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101976904456543444584337571 152965356684815166876506357)
          ·
            refine ⟨14340502189201421894672471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152965356684815166876506357 14340502189201421894672471)
            ·
              refine ⟨21510753283802132842008707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14340502189201421894672471 21510753283802132842008707)
              ·
                refine ⟨32266129925703199263013061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21510753283802132842008707 32266129925703199263013061)
                ·
                  refine ⟨6049899361069349861814949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32266129925703199263013061 6049899361069349861814949)
                  ·
                    refine ⟨1134356130200503099090303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6049899361069349861814949 1134356130200503099090303)
                    ·
                      rfl

theorem cell23_6627452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_6627452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627452 prefixEnd_6627452 := by exact prefixLift 6627452
  have htrace : WordTrace (prefixWord ++ tailWord_6627452) baseStart_6627452 baseEnd_6627452 := by
    simpa [prefixWord, tailWord_6627452, baseEnd_6627452] using wordTrace_append hprefix tailTrace_6627452
  have hstable : (prefixWord ++ tailWord_6627452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627452).length < 2 ^ (prefixWord ++ tailWord_6627452).sum := by decide
  have hdescent : baseEnd_6627452 < baseStart_6627452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627459 : List Nat := [1, 1, 1, 3, 3, 3, 1, 3, 3, 2, 2]
def baseStart_6627459 : Nat := 118140960795 + 6627459 * 2 ^ 59
def prefixEnd_6627459 : Nat := 4983230072969 + 3 ^ 40 * 6627459 * 2
def baseEnd_6627459 : Nat := 3403071984966090769883377

theorem tailTrace_6627459 : CollatzResearch.WordTrace tailWord_6627459 prefixEnd_6627459 3403071984966090769883377 := by
  unfold tailWord_6627459
  simp only [CollatzResearch.WordTrace]
  refine ⟨241723288096855397728749431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161148858731236931819166287 241723288096855397728749431)
  ·
    refine ⟨362584932145283096593124147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241723288096855397728749431 362584932145283096593124147)
    ·
      refine ⟨543877398217924644889686221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362584932145283096593124147 543877398217924644889686221)
      ·
        refine ⟨203954024331721741833632333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 543877398217924644889686221 203954024331721741833632333)
        ·
          refine ⟨76482759124395653187612125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203954024331721741833632333 76482759124395653187612125)
          ·
            refine ⟨28681034671648369945354547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76482759124395653187612125 28681034671648369945354547)
            ·
              refine ⟨43021552007472554918031821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28681034671648369945354547 43021552007472554918031821)
              ·
                refine ⟨16133082002802208094261933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43021552007472554918031821 16133082002802208094261933)
                ·
                  refine ⟨6049905751050828035348225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16133082002802208094261933 6049905751050828035348225)
                  ·
                    refine ⟨4537429313288121026511169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6049905751050828035348225 4537429313288121026511169)
                    ·
                      refine ⟨3403071984966090769883377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4537429313288121026511169 3403071984966090769883377)
                      ·
                        rfl

theorem cell23_6627459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 2, 2].length) (baseStart_6627459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627459 prefixEnd_6627459 := by exact prefixLift 6627459
  have htrace : WordTrace (prefixWord ++ tailWord_6627459) baseStart_6627459 baseEnd_6627459 := by
    simpa [prefixWord, tailWord_6627459, baseEnd_6627459] using wordTrace_append hprefix tailTrace_6627459
  have hstable : (prefixWord ++ tailWord_6627459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627459).length < 2 ^ (prefixWord ++ tailWord_6627459).sum := by decide
  have hdescent : baseEnd_6627459 < baseStart_6627459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627482 : List Nat := [3, 1, 1, 5, 2, 1, 1, 9]
def baseStart_6627482 : Nat := 118140960795 + 6627482 * 2 ^ 59
def prefixEnd_6627482 : Nat := 4983230072969 + 3 ^ 40 * 6627482 * 2
def baseEnd_6627482 : Nat := 126040140556338673329473

theorem tailTrace_6627482 : CollatzResearch.WordTrace tailWord_6627482 prefixEnd_6627482 126040140556338673329473 := by
  unfold tailWord_6627482
  simp only [CollatzResearch.WordTrace]
  refine ⟨60431031743943018164209175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161149417983848048437891133 60431031743943018164209175)
  ·
    refine ⟨90646547615914527246313763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60431031743943018164209175 90646547615914527246313763)
    ·
      refine ⟨135969821423871790869470645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90646547615914527246313763 135969821423871790869470645)
      ·
        refine ⟨12747170758487980394012873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135969821423871790869470645 12747170758487980394012873)
        ·
          refine ⟨9560378068865985295509655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12747170758487980394012873 9560378068865985295509655)
          ·
            refine ⟨14340567103298977943264483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9560378068865985295509655 14340567103298977943264483)
            ·
              refine ⟨21510850654948466914896725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14340567103298977943264483 21510850654948466914896725)
              ·
                refine ⟨126040140556338673329473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21510850654948466914896725 126040140556338673329473)
                ·
                  rfl

theorem cell23_6627482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 9].length) (baseStart_6627482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627482 prefixEnd_6627482 := by exact prefixLift 6627482
  have htrace : WordTrace (prefixWord ++ tailWord_6627482) baseStart_6627482 baseEnd_6627482 := by
    simpa [prefixWord, tailWord_6627482, baseEnd_6627482] using wordTrace_append hprefix tailTrace_6627482
  have hstable : (prefixWord ++ tailWord_6627482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627482).length < 2 ^ (prefixWord ++ tailWord_6627482).sum := by decide
  have hdescent : baseEnd_6627482 < baseStart_6627482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627515 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 4]
def baseStart_6627515 : Nat := 118140960795 + 6627515 * 2 ^ 59
def prefixEnd_6627515 : Nat := 4983230072969 + 3 ^ 40 * 6627515 * 2
def baseEnd_6627515 : Nat := 3403100739882742550783119

theorem tailTrace_6627515 : CollatzResearch.WordTrace tailWord_6627515 prefixEnd_6627515 3403100739882742550783119 := by
  unfold tailWord_6627515
  simp only [CollatzResearch.WordTrace]
  refine ⟨241725330584652519292787999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161150220389768346195191999 241725330584652519292787999)
  ·
    refine ⟨362587995876978778939181999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241725330584652519292787999 362587995876978778939181999)
    ·
      refine ⟨543881993815468168408772999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362587995876978778939181999 543881993815468168408772999)
      ·
        refine ⟨815822990723202252613159499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543881993815468168408772999 815822990723202252613159499)
        ·
          refine ⟨1223734486084803378919739249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815822990723202252613159499 1223734486084803378919739249)
          ·
            refine ⟨917800864563602534189804437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1223734486084803378919739249 917800864563602534189804437)
            ·
              refine ⟨43021915526418868790147083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 917800864563602534189804437 43021915526418868790147083)
              ·
                refine ⟨64532873289628303185220625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43021915526418868790147083 64532873289628303185220625)
                ·
                  refine ⟨48399654967221227388915469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64532873289628303185220625 48399654967221227388915469)
                  ·
                    refine ⟨18149870612707960270843301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48399654967221227388915469 18149870612707960270843301)
                    ·
                      refine ⟨3403100739882742550783119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18149870612707960270843301 3403100739882742550783119)
                      ·
                        rfl

theorem cell23_6627515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 4].length) (baseStart_6627515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627515 prefixEnd_6627515 := by exact prefixLift 6627515
  have htrace : WordTrace (prefixWord ++ tailWord_6627515) baseStart_6627515 baseEnd_6627515 := by
    simpa [prefixWord, tailWord_6627515, baseEnd_6627515] using wordTrace_append hprefix tailTrace_6627515
  have hstable : (prefixWord ++ tailWord_6627515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627515).length < 2 ^ (prefixWord ++ tailWord_6627515).sum := by decide
  have hdescent : baseEnd_6627515 < baseStart_6627515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627525 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 2, 6]
def baseStart_6627525 : Nat := 118140960795 + 6627525 * 2 ^ 59
def prefixEnd_6627525 : Nat := 4983230072969 + 3 ^ 40 * 6627525 * 2
def baseEnd_6627525 : Nat := 1134368624896429170552691

theorem tailTrace_6627525 : CollatzResearch.WordTrace tailWord_6627525 prefixEnd_6627525 1134368624896429170552691 := by
  unfold tailWord_6627525
  simp only [CollatzResearch.WordTrace]
  refine ⟨241725695314616291000652029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161150463543077527333768019 241725695314616291000652029)
  ·
    refine ⟨90647135742981109125244511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241725695314616291000652029 90647135742981109125244511)
    ·
      refine ⟨135970703614471663687866767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90647135742981109125244511 135970703614471663687866767)
      ·
        refine ⟨203956055421707495531800151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135970703614471663687866767 203956055421707495531800151)
        ·
          refine ⟨305934083132561243297700227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203956055421707495531800151 305934083132561243297700227)
          ·
            refine ⟨458901124698841864946550341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305934083132561243297700227 458901124698841864946550341)
            ·
              refine ⟨86043960881032849677478189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 458901124698841864946550341 86043960881032849677478189)
              ·
                refine ⟨32266485330387318629054321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86043960881032849677478189 32266485330387318629054321)
                ·
                  refine ⟨24199863997790488971790741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32266485330387318629054321 24199863997790488971790741)
                  ·
                    refine ⟨1134368624896429170552691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24199863997790488971790741 1134368624896429170552691)
                    ·
                      rfl

theorem cell23_6627525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_6627525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627525 prefixEnd_6627525 := by exact prefixLift 6627525
  have htrace : WordTrace (prefixWord ++ tailWord_6627525) baseStart_6627525 baseEnd_6627525 := by
    simpa [prefixWord, tailWord_6627525, baseEnd_6627525] using wordTrace_append hprefix tailTrace_6627525
  have hstable : (prefixWord ++ tailWord_6627525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627525).length < 2 ^ (prefixWord ++ tailWord_6627525).sum := by decide
  have hdescent : baseEnd_6627525 < baseStart_6627525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627535 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 5]
def baseStart_6627535 : Nat := 118140960795 + 6627535 * 2 ^ 59
def prefixEnd_6627535 : Nat := 4983230072969 + 3 ^ 40 * 6627535 * 2
def baseEnd_6627535 : Nat := 3403111009495832472533027

theorem tailTrace_6627535 : CollatzResearch.WordTrace tailWord_6627535 prefixEnd_6627535 3403111009495832472533027 := by
  unfold tailWord_6627535
  simp only [CollatzResearch.WordTrace]
  refine ⟨241726060044580062708516059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161150706696386708472344039 241726060044580062708516059)
  ·
    refine ⟨362589090066870094062774089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241726060044580062708516059 362589090066870094062774089)
    ·
      refine ⟨271941817550152570547080567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362589090066870094062774089 271941817550152570547080567)
      ·
        refine ⟨407912726325228855820620851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271941817550152570547080567 407912726325228855820620851)
        ·
          refine ⟨611869089487843283730931277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407912726325228855820620851 611869089487843283730931277)
          ·
            refine ⟨229450908557941231399099229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 611869089487843283730931277 229450908557941231399099229)
            ·
              refine ⟨86044090709227961774662211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229450908557941231399099229 86044090709227961774662211)
              ·
                refine ⟨129066136063841942661993317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86044090709227961774662211 129066136063841942661993317)
                ·
                  refine ⟨24199900511970364249123747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129066136063841942661993317 24199900511970364249123747)
                  ·
                    refine ⟨36299850767955546373685621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24199900511970364249123747 36299850767955546373685621)
                    ·
                      refine ⟨3403111009495832472533027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36299850767955546373685621 3403111009495832472533027)
                      ·
                        rfl

theorem cell23_6627535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 5].length) (baseStart_6627535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627535 prefixEnd_6627535 := by exact prefixLift 6627535
  have htrace : WordTrace (prefixWord ++ tailWord_6627535) baseStart_6627535 baseEnd_6627535 := by
    simpa [prefixWord, tailWord_6627535, baseEnd_6627535] using wordTrace_append hprefix tailTrace_6627535
  have hstable : (prefixWord ++ tailWord_6627535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627535).length < 2 ^ (prefixWord ++ tailWord_6627535).sum := by decide
  have hdescent : baseEnd_6627535 < baseStart_6627535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627562 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_6627562 : Nat := 118140960795 + 6627562 * 2 ^ 59
def prefixEnd_6627562 : Nat := 4983230072969 + 3 ^ 40 * 6627562 * 2
def baseEnd_6627562 : Nat := 3403124873473503866895403

theorem tailTrace_6627562 : CollatzResearch.WordTrace tailWord_6627562 prefixEnd_6627562 3403124873473503866895403 := by
  unfold tailWord_6627562
  simp only [CollatzResearch.WordTrace]
  refine ⟨60431761203870561579937235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161151363210321497546499293 60431761203870561579937235)
  ·
    refine ⟨90647641805805842369905853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60431761203870561579937235 90647641805805842369905853)
    ·
      refine ⟨33992865677177190888714695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90647641805805842369905853 33992865677177190888714695)
      ·
        refine ⟨50989298515765786333072043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33992865677177190888714695 50989298515765786333072043)
        ·
          refine ⟨76483947773648679499608065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50989298515765786333072043 76483947773648679499608065)
          ·
            refine ⟨57362960830236509624706049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76483947773648679499608065 57362960830236509624706049)
            ·
              refine ⟨43022220622677382218529537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57362960830236509624706049 43022220622677382218529537)
              ·
                refine ⟨32266665467008036663897153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43022220622677382218529537 32266665467008036663897153)
                ·
                  refine ⟨24199999100256027497922865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32266665467008036663897153 24199999100256027497922865)
                  ·
                    refine ⟨18149999325192020623442149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24199999100256027497922865 18149999325192020623442149)
                    ·
                      refine ⟨3403124873473503866895403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18149999325192020623442149 3403124873473503866895403)
                      ·
                        rfl

theorem cell23_6627562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_6627562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627562 prefixEnd_6627562 := by exact prefixLift 6627562
  have htrace : WordTrace (prefixWord ++ tailWord_6627562) baseStart_6627562 baseEnd_6627562 := by
    simpa [prefixWord, tailWord_6627562, baseEnd_6627562] using wordTrace_append hprefix tailTrace_6627562
  have hstable : (prefixWord ++ tailWord_6627562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627562).length < 2 ^ (prefixWord ++ tailWord_6627562).sum := by decide
  have hdescent : baseEnd_6627562 < baseStart_6627562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627623 : List Nat := [1, 1, 8, 1, 1, 1, 2, 1, 7]
def baseStart_6627623 : Nat := 118140960795 + 6627623 * 2 ^ 59
def prefixEnd_6627623 : Nat := 4983230072969 + 3 ^ 40 * 6627623 * 2
def baseEnd_6627623 : Nat := 378128466199269792025847

theorem tailTrace_6627623 : CollatzResearch.WordTrace tailWord_6627623 prefixEnd_6627623 378128466199269792025847 := by
  unfold tailWord_6627623
  simp only [CollatzResearch.WordTrace]
  refine ⟨241729269668261253737719523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161152846445507502491813015 241729269668261253737719523)
  ·
    refine ⟨362593904502391880606579285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241729269668261253737719523 362593904502391880606579285)
    ·
      refine ⟨4249147318387404850858351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 362593904502391880606579285 4249147318387404850858351)
      ·
        refine ⟨6373720977581107276287527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4249147318387404850858351 6373720977581107276287527)
        ·
          refine ⟨9560581466371660914431291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6373720977581107276287527 9560581466371660914431291)
          ·
            refine ⟨14340872199557491371646937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9560581466371660914431291 14340872199557491371646937)
            ·
              refine ⟨10755654149668118528735203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14340872199557491371646937 10755654149668118528735203)
              ·
                refine ⟨16133481224502177793102805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10755654149668118528735203 16133481224502177793102805)
                ·
                  refine ⟨378128466199269792025847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16133481224502177793102805 378128466199269792025847)
                  ·
                    rfl

theorem cell23_6627623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 7].length) (baseStart_6627623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627623 prefixEnd_6627623 := by exact prefixLift 6627623
  have htrace : WordTrace (prefixWord ++ tailWord_6627623) baseStart_6627623 baseEnd_6627623 := by
    simpa [prefixWord, tailWord_6627623, baseEnd_6627623] using wordTrace_append hprefix tailTrace_6627623
  have hstable : (prefixWord ++ tailWord_6627623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627623).length < 2 ^ (prefixWord ++ tailWord_6627623).sum := by decide
  have hdescent : baseEnd_6627623 < baseStart_6627623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627625 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 11]
def baseStart_6627625 : Nat := 118140960795 + 6627625 * 2 ^ 59
def prefixEnd_6627625 : Nat := 4983230072969 + 3 ^ 40 * 6627625 * 2
def baseEnd_6627625 : Nat := 3403157222754737120407613

theorem tailTrace_6627625 : CollatzResearch.WordTrace tailWord_6627625 prefixEnd_6627625 3403157222754737120407613 := by
  unfold tailWord_6627625
  simp only [CollatzResearch.WordTrace]
  refine ⟨241729342614254008079292329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161152895076169338719528219 241729342614254008079292329)
  ·
    refine ⟨181297006960690506059469247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241729342614254008079292329 181297006960690506059469247)
    ·
      refine ⟨271945510441035759089203871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181297006960690506059469247 271945510441035759089203871)
      ·
        refine ⟨407918265661553638633805807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271945510441035759089203871 407918265661553638633805807)
        ·
          refine ⟨611877398492330457950708711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407918265661553638633805807 611877398492330457950708711)
          ·
            refine ⟨917816097738495686926063067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611877398492330457950708711 917816097738495686926063067)
            ·
              refine ⟨1376724146607743530389094601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917816097738495686926063067 1376724146607743530389094601)
              ·
                refine ⟨1032543109955807647791820951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1376724146607743530389094601 1032543109955807647791820951)
                ·
                  refine ⟨1548814664933711471687731427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1032543109955807647791820951 1548814664933711471687731427)
                  ·
                    refine ⟨2323221997400567207531597141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1548814664933711471687731427 2323221997400567207531597141)
                    ·
                      refine ⟨3403157222754737120407613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 2323221997400567207531597141 3403157222754737120407613)
                      ·
                        rfl

theorem cell23_6627625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_6627625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627625 prefixEnd_6627625 := by exact prefixLift 6627625
  have htrace : WordTrace (prefixWord ++ tailWord_6627625) baseStart_6627625 baseEnd_6627625 := by
    simpa [prefixWord, tailWord_6627625, baseEnd_6627625] using wordTrace_append hprefix tailTrace_6627625
  have hstable : (prefixWord ++ tailWord_6627625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627625).length < 2 ^ (prefixWord ++ tailWord_6627625).sum := by decide
  have hdescent : baseEnd_6627625 < baseStart_6627625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627683 : List Nat := [1, 1, 1, 5, 2, 1, 5, 2, 1, 4]
def baseStart_6627683 : Nat := 118140960795 + 6627683 * 2 ^ 59
def prefixEnd_6627683 : Nat := 4983230072969 + 3 ^ 40 * 6627683 * 2
def baseEnd_6627683 : Nat := 1134395668210899297827449

theorem tailTrace_6627683 : CollatzResearch.WordTrace tailWord_6627683 prefixEnd_6627683 1134395668210899297827449 := by
  unfold tailWord_6627683
  simp only [CollatzResearch.WordTrace]
  refine ⟨241731458048043883984903703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161154305365362589323269135 241731458048043883984903703)
  ·
    refine ⟨362597187072065825977355555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241731458048043883984903703 362597187072065825977355555)
    ·
      refine ⟨543895780608098738966033333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362597187072065825977355555 543895780608098738966033333)
      ·
        refine ⟨50990229432009256778065625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 543895780608098738966033333 50990229432009256778065625)
        ·
          refine ⟨38242672074006942583549219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50990229432009256778065625 38242672074006942583549219)
          ·
            refine ⟨57364008111010413875323829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38242672074006942583549219 57364008111010413875323829)
            ·
              refine ⟨5377875760407226300811609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57364008111010413875323829 5377875760407226300811609)
              ·
                refine ⟨4033406820305419725608707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5377875760407226300811609 4033406820305419725608707)
                ·
                  refine ⟨6050110230458129588413061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4033406820305419725608707 6050110230458129588413061)
                  ·
                    refine ⟨1134395668210899297827449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6050110230458129588413061 1134395668210899297827449)
                    ·
                      rfl

theorem cell23_6627683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 1, 4].length) (baseStart_6627683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627683 prefixEnd_6627683 := by exact prefixLift 6627683
  have htrace : WordTrace (prefixWord ++ tailWord_6627683) baseStart_6627683 baseEnd_6627683 := by
    simpa [prefixWord, tailWord_6627683, baseEnd_6627683] using wordTrace_append hprefix tailTrace_6627683
  have hstable : (prefixWord ++ tailWord_6627683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627683).length < 2 ^ (prefixWord ++ tailWord_6627683).sum := by decide
  have hdescent : baseEnd_6627683 < baseStart_6627683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627696 : List Nat := [2, 1, 1, 1, 4, 5, 2, 1, 6]
def baseStart_6627696 : Nat := 118140960795 + 6627696 * 2 ^ 59
def prefixEnd_6627696 : Nat := 4983230072969 + 3 ^ 40 * 6627696 * 2
def baseEnd_6627696 : Nat := 378132631097911815846643

theorem tailTrace_6627696 : CollatzResearch.WordTrace tailWord_6627696 prefixEnd_6627696 378132631097911815846643 := by
  unfold tailWord_6627696
  simp only [CollatzResearch.WordTrace]
  refine ⟨120865966098498393602563471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161154621464664524803417961 120865966098498393602563471)
  ·
    refine ⟨181298949147747590403845207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120865966098498393602563471 181298949147747590403845207)
    ·
      refine ⟨271948423721621385605767811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181298949147747590403845207 271948423721621385605767811)
      ·
        refine ⟨407922635582432078408651717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271948423721621385605767811 407922635582432078408651717)
        ·
          refine ⟨76485494171706014701622197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 407922635582432078408651717 76485494171706014701622197)
          ·
            refine ⟨7170515078597438878277081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76485494171706014701622197 7170515078597438878277081)
            ·
              refine ⟨5377886308948079158707811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7170515078597438878277081 5377886308948079158707811)
              ·
                refine ⟨8066829463422118738061717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5377886308948079158707811 8066829463422118738061717)
                ·
                  refine ⟨378132631097911815846643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8066829463422118738061717 378132631097911815846643)
                  ·
                    rfl

theorem cell23_6627696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 6].length) (baseStart_6627696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627696 prefixEnd_6627696 := by exact prefixLift 6627696
  have htrace : WordTrace (prefixWord ++ tailWord_6627696) baseStart_6627696 baseEnd_6627696 := by
    simpa [prefixWord, tailWord_6627696, baseEnd_6627696] using wordTrace_append hprefix tailTrace_6627696
  have hstable : (prefixWord ++ tailWord_6627696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627696).length < 2 ^ (prefixWord ++ tailWord_6627696).sum := by decide
  have hdescent : baseEnd_6627696 < baseStart_6627696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627709 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 3, 5]
def baseStart_6627709 : Nat := 118140960795 + 6627709 * 2 ^ 59
def prefixEnd_6627709 : Nat := 4983230072969 + 3 ^ 40 * 6627709 * 2
def baseEnd_6627709 : Nat := 1134400118376571597252409

theorem tailTrace_6627709 : CollatzResearch.WordTrace tailWord_6627709 prefixEnd_6627709 1134400118376571597252409 := by
  unfold tailWord_6627709
  simp only [CollatzResearch.WordTrace]
  refine ⟨241732406345949690425350181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161154937563966460283566787 241732406345949690425350181)
  ·
    refine ⟨45324826189865566954753159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241732406345949690425350181 45324826189865566954753159)
    ·
      refine ⟨67987239284798350432129739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45324826189865566954753159 67987239284798350432129739)
      ·
        refine ⟨101980858927197525648194609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67987239284798350432129739 101980858927197525648194609)
        ·
          refine ⟨76485644195398144236145957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101980858927197525648194609 76485644195398144236145957)
          ·
            refine ⟨14341058286637152044277367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76485644195398144236145957 14341058286637152044277367)
            ·
              refine ⟨21511587429955728066416051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14341058286637152044277367 21511587429955728066416051)
              ·
                refine ⟨32267381144933592099624077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21511587429955728066416051 32267381144933592099624077)
                ·
                  refine ⟨12100267929350097037359029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32267381144933592099624077 12100267929350097037359029)
                  ·
                    refine ⟨1134400118376571597252409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12100267929350097037359029 1134400118376571597252409)
                    ·
                      rfl

theorem cell23_6627709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_6627709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627709 prefixEnd_6627709 := by exact prefixLift 6627709
  have htrace : WordTrace (prefixWord ++ tailWord_6627709) baseStart_6627709 baseEnd_6627709 := by
    simpa [prefixWord, tailWord_6627709, baseEnd_6627709] using wordTrace_append hprefix tailTrace_6627709
  have hstable : (prefixWord ++ tailWord_6627709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627709).length < 2 ^ (prefixWord ++ tailWord_6627709).sum := by decide
  have hdescent : baseEnd_6627709 < baseStart_6627709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627734 : List Nat := [5, 3, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_6627734 : Nat := 118140960795 + 6627734 * 2 ^ 59
def prefixEnd_6627734 : Nat := 4983230072969 + 3 ^ 40 * 6627734 * 2
def baseEnd_6627734 : Nat := 1134404397382025731314871

theorem tailTrace_6627734 : CollatzResearch.WordTrace tailWord_6627734 prefixEnd_6627734 1134404397382025731314871 := by
  unfold tailWord_6627734
  simp only [CollatzResearch.WordTrace]
  refine ⟨15108332385678694980938141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161155545447239413130006837 15108332385678694980938141)
  ·
    refine ⟨5665624644629510617851803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15108332385678694980938141 5665624644629510617851803)
    ·
      refine ⟨8498436966944265926777705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5665624644629510617851803 8498436966944265926777705)
      ·
        refine ⟨6373827725208199445083279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8498436966944265926777705 6373827725208199445083279)
        ·
          refine ⟨9560741587812299167624919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6373827725208199445083279 9560741587812299167624919)
          ·
            refine ⟨14341112381718448751437379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9560741587812299167624919 14341112381718448751437379)
            ·
              refine ⟨21511668572577673127156069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14341112381718448751437379 21511668572577673127156069)
              ·
                refine ⟨4033437857358313711341763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21511668572577673127156069 4033437857358313711341763)
                ·
                  refine ⟨6050156786037470567012645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4033437857358313711341763 6050156786037470567012645)
                  ·
                    refine ⟨1134404397382025731314871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6050156786037470567012645 1134404397382025731314871)
                    ·
                      rfl

theorem cell23_6627734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_6627734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627734 prefixEnd_6627734 := by exact prefixLift 6627734
  have htrace : WordTrace (prefixWord ++ tailWord_6627734) baseStart_6627734 baseEnd_6627734 := by
    simpa [prefixWord, tailWord_6627734, baseEnd_6627734] using wordTrace_append hprefix tailTrace_6627734
  have hstable : (prefixWord ++ tailWord_6627734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627734).length < 2 ^ (prefixWord ++ tailWord_6627734).sum := by decide
  have hdescent : baseEnd_6627734 < baseStart_6627734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627749 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 5, 2, 3]
def baseStart_6627749 : Nat := 118140960795 + 6627749 * 2 ^ 59
def prefixEnd_6627749 : Nat := 4983230072969 + 3 ^ 40 * 6627749 * 2
def baseEnd_6627749 : Nat := 3403220894355894635257043

theorem tailTrace_6627749 : CollatzResearch.WordTrace tailWord_6627749 prefixEnd_6627749 3403220894355894635257043 := by
  unfold tailWord_6627749
  simp only [CollatzResearch.WordTrace]
  refine ⟨241733865265804777256806301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161155910177203184837870867 241733865265804777256806301)
  ·
    refine ⟨90650199474676791471302363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241733865265804777256806301 90650199474676791471302363)
    ·
      refine ⟨135975299212015187206953545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90650199474676791471302363 135975299212015187206953545)
      ·
        refine ⟨101981474409011390405215159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135975299212015187206953545 101981474409011390405215159)
        ·
          refine ⟨152972211613517085607822739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101981474409011390405215159 152972211613517085607822739)
          ·
            refine ⟨229458317420275628411734109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152972211613517085607822739 229458317420275628411734109)
            ·
              refine ⟨86046869032603360654400291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229458317420275628411734109 86046869032603360654400291)
              ·
                refine ⟨129070303548905040981600437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86046869032603360654400291 129070303548905040981600437)
                ·
                  refine ⟨12100340957709847592025041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129070303548905040981600437 12100340957709847592025041)
                  ·
                    refine ⟨9075255718282385694018781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12100340957709847592025041 9075255718282385694018781)
                    ·
                      refine ⟨3403220894355894635257043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9075255718282385694018781 3403220894355894635257043)
                      ·
                        rfl

theorem cell23_6627749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_6627749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627749 prefixEnd_6627749 := by exact prefixLift 6627749
  have htrace : WordTrace (prefixWord ++ tailWord_6627749) baseStart_6627749 baseEnd_6627749 := by
    simpa [prefixWord, tailWord_6627749, baseEnd_6627749] using wordTrace_append hprefix tailTrace_6627749
  have hstable : (prefixWord ++ tailWord_6627749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627749).length < 2 ^ (prefixWord ++ tailWord_6627749).sum := by decide
  have hdescent : baseEnd_6627749 < baseStart_6627749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627783 : List Nat := [1, 1, 4, 1, 1, 4, 4, 1, 1, 2, 3]
def baseStart_6627783 : Nat := 118140960795 + 6627783 * 2 ^ 59
def prefixEnd_6627783 : Nat := 4983230072969 + 3 ^ 40 * 6627783 * 2
def baseEnd_6627783 : Nat := 3403238352698147502231887

theorem tailTrace_6627783 : CollatzResearch.WordTrace tailWord_6627783 prefixEnd_6627783 3403238352698147502231887 := by
  unfold tailWord_6627783
  simp only [CollatzResearch.WordTrace]
  refine ⟨241735105347681601063544003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161156736898454400709029335 241735105347681601063544003)
  ·
    refine ⟨362602658021522401595316005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241735105347681601063544003 362602658021522401595316005)
    ·
      refine ⟨67987998379035450299121751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 362602658021522401595316005 67987998379035450299121751)
      ·
        refine ⟨101981997568553175448682627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67987998379035450299121751 101981997568553175448682627)
        ·
          refine ⟨152972996352829763173023941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101981997568553175448682627 152972996352829763173023941)
          ·
            refine ⟨28682436816155580594941989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152972996352829763173023941 28682436816155580594941989)
            ·
              refine ⟨5377956903029171361551623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28682436816155580594941989 5377956903029171361551623)
              ·
                refine ⟨8066935354543757042327435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5377956903029171361551623 8066935354543757042327435)
                ·
                  refine ⟨12100403031815635563491153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8066935354543757042327435 12100403031815635563491153)
                  ·
                    refine ⟨9075302273861726672618365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12100403031815635563491153 9075302273861726672618365)
                    ·
                      refine ⟨3403238352698147502231887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9075302273861726672618365 3403238352698147502231887)
                      ·
                        rfl

theorem cell23_6627783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_6627783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627783 prefixEnd_6627783 := by exact prefixLift 6627783
  have htrace : WordTrace (prefixWord ++ tailWord_6627783) baseStart_6627783 baseEnd_6627783 := by
    simpa [prefixWord, tailWord_6627783, baseEnd_6627783] using wordTrace_append hprefix tailTrace_6627783
  have hstable : (prefixWord ++ tailWord_6627783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627783).length < 2 ^ (prefixWord ++ tailWord_6627783).sum := by decide
  have hdescent : baseEnd_6627783 < baseStart_6627783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627792 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 7]
def baseStart_6627792 : Nat := 118140960795 + 6627792 * 2 ^ 59
def prefixEnd_6627792 : Nat := 4983230072969 + 3 ^ 40 * 6627792 * 2
def baseEnd_6627792 : Nat := 3403242974024037967019345

theorem tailTrace_6627792 : CollatzResearch.WordTrace tailWord_6627792 prefixEnd_6627792 3403242974024037967019345 := by
  unfold tailWord_6627792
  simp only [CollatzResearch.WordTrace]
  refine ⟨120867716802324497800310815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161156955736432663733747753 120867716802324497800310815)
  ·
    refine ⟨181301575203486746700466223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120867716802324497800310815 181301575203486746700466223)
    ·
      refine ⟨271952362805230120050699335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181301575203486746700466223 271952362805230120050699335)
      ·
        refine ⟨407928544207845180076049003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271952362805230120050699335 407928544207845180076049003)
        ·
          refine ⟨611892816311767770114073505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407928544207845180076049003 611892816311767770114073505)
          ·
            refine ⟨458919612233825827585555129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 611892816311767770114073505 458919612233825827585555129)
            ·
              refine ⟨344189709175369370689166347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458919612233825827585555129 344189709175369370689166347)
              ·
                refine ⟨516284563763054056033749521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344189709175369370689166347 516284563763054056033749521)
                ·
                  refine ⟨387213422822290542025312141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 516284563763054056033749521 387213422822290542025312141)
                  ·
                    refine ⟨145205033558358953259492053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 387213422822290542025312141 145205033558358953259492053)
                    ·
                      refine ⟨3403242974024037967019345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145205033558358953259492053 3403242974024037967019345)
                      ·
                        rfl

theorem cell23_6627792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_6627792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627792 prefixEnd_6627792 := by exact prefixLift 6627792
  have htrace : WordTrace (prefixWord ++ tailWord_6627792) baseStart_6627792 baseEnd_6627792 := by
    simpa [prefixWord, tailWord_6627792, baseEnd_6627792] using wordTrace_append hprefix tailTrace_6627792
  have hstable : (prefixWord ++ tailWord_6627792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627792).length < 2 ^ (prefixWord ++ tailWord_6627792).sum := by decide
  have hdescent : baseEnd_6627792 < baseStart_6627792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
