import V185TrunkScan20Chunk054

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_334430 : List Nat := [4, 4, 1, 2, 1, 1, 2, 3, 2]
def baseStart_334430 : Nat := 118140960795 + 334430 * 2 ^ 59
def prefixEnd_334430 : Nat := 4983230072969 + 3 ^ 40 * 334430 * 2
def baseEnd_334430 : Nat := 152642964696206022032881

theorem tailTrace_334430 : CollatzResearch.WordTrace tailWord_334430 prefixEnd_334430 152642964696206022032881 := by
  unfold tailWord_334430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1524708022303087617733093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8131776118949800627909829 1524708022303087617733093)
  ·
    refine ⟨285882754181828928324955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1524708022303087617733093 285882754181828928324955)
    ·
      refine ⟨428824131272743392487433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285882754181828928324955 428824131272743392487433)
      ·
        refine ⟨321618098454557544365575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428824131272743392487433 321618098454557544365575)
        ·
          refine ⟨482427147681836316548363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321618098454557544365575 482427147681836316548363)
          ·
            refine ⟨723640721522754474822545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482427147681836316548363 723640721522754474822545)
            ·
              refine ⟨542730541142065856116909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723640721522754474822545 542730541142065856116909)
              ·
                refine ⟨203523952928274696043841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 542730541142065856116909 203523952928274696043841)
                ·
                  refine ⟨152642964696206022032881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203523952928274696043841 152642964696206022032881)
                  ·
                    rfl

theorem cell20_334430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_334430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334430 prefixEnd_334430 := by exact prefixLift 334430
  have htrace : WordTrace (prefixWord ++ tailWord_334430) baseStart_334430 baseEnd_334430 := by
    simpa [prefixWord, tailWord_334430, baseEnd_334430] using wordTrace_append hprefix tailTrace_334430
  have hstable : (prefixWord ++ tailWord_334430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334430).length < 2 ^ (prefixWord ++ tailWord_334430).sum := by decide
  have hdescent : baseEnd_334430 < baseStart_334430 := by decide
  rcases family_descends (prefixWord ++ tailWord_334430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334435 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 5]
def baseStart_334435 : Nat := 118140960795 + 334435 * 2 ^ 59
def prefixEnd_334435 : Nat := 4983230072969 + 3 ^ 40 * 334435 * 2
def baseEnd_334435 : Nat := 152645246832448226866193

theorem tailTrace_334435 : CollatzResearch.WordTrace tailWord_334435 prefixEnd_334435 152645246832448226866193 := by
  unfold tailWord_334435
  simp only [CollatzResearch.WordTrace]
  refine ⟨12197846543406586795796759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8131897695604391197197839 12197846543406586795796759)
  ·
    refine ⟨18296769815109880193695139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12197846543406586795796759 18296769815109880193695139)
    ·
      refine ⟨27445154722664820290542709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18296769815109880193695139 27445154722664820290542709)
      ·
        refine ⟨2572983255249826902238379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27445154722664820290542709 2572983255249826902238379)
        ·
          refine ⟨3859474882874740353357569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2572983255249826902238379 3859474882874740353357569)
          ·
            refine ⟨2894606162156055265018177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3859474882874740353357569 2894606162156055265018177)
            ·
              refine ⟨2170954621617041448763633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2894606162156055265018177 2170954621617041448763633)
              ·
                refine ⟨1628215966212781086572725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2170954621617041448763633 1628215966212781086572725)
                ·
                  refine ⟨152645246832448226866193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1628215966212781086572725 152645246832448226866193)
                  ·
                    rfl

theorem cell20_334435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_334435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334435 prefixEnd_334435 := by exact prefixLift 334435
  have htrace : WordTrace (prefixWord ++ tailWord_334435) baseStart_334435 baseEnd_334435 := by
    simpa [prefixWord, tailWord_334435, baseEnd_334435] using wordTrace_append hprefix tailTrace_334435
  have hstable : (prefixWord ++ tailWord_334435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334435).length < 2 ^ (prefixWord ++ tailWord_334435).sum := by decide
  have hdescent : baseEnd_334435 < baseStart_334435 := by decide
  rcases family_descends (prefixWord ++ tailWord_334435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334448 : List Nat := [2, 1, 1, 1, 8, 1, 1, 2, 3]
def baseStart_334448 : Nat := 118140960795 + 334448 * 2 ^ 59
def prefixEnd_334448 : Nat := 4983230072969 + 3 ^ 40 * 334448 * 2
def baseEnd_334448 : Nat := 152651180386677959432807

theorem tailTrace_334448 : CollatzResearch.WordTrace tailWord_334448 prefixEnd_334448 152651180386677959432807 := by
  unfold tailWord_334448
  simp only [CollatzResearch.WordTrace]
  refine ⟨6099160346179745008009999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8132213794906326677346665 6099160346179745008009999)
  ·
    refine ⟨9148740519269617512014999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6099160346179745008009999 9148740519269617512014999)
    ·
      refine ⟨13723110778904426268022499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9148740519269617512014999 13723110778904426268022499)
      ·
        refine ⟨20584666168356639402033749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13723110778904426268022499 20584666168356639402033749)
        ·
          refine ⟨241226556660429367992583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 20584666168356639402033749 241226556660429367992583)
          ·
            refine ⟨361839834990644051988875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241226556660429367992583 361839834990644051988875)
            ·
              refine ⟨542759752485966077983313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361839834990644051988875 542759752485966077983313)
              ·
                refine ⟨407069814364474558487485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 542759752485966077983313 407069814364474558487485)
                ·
                  refine ⟨152651180386677959432807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 407069814364474558487485 152651180386677959432807)
                  ·
                    rfl

theorem cell20_334448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 3].length) (baseStart_334448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334448 prefixEnd_334448 := by exact prefixLift 334448
  have htrace : WordTrace (prefixWord ++ tailWord_334448) baseStart_334448 baseEnd_334448 := by
    simpa [prefixWord, tailWord_334448, baseEnd_334448] using wordTrace_append hprefix tailTrace_334448
  have hstable : (prefixWord ++ tailWord_334448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334448).length < 2 ^ (prefixWord ++ tailWord_334448).sum := by decide
  have hdescent : baseEnd_334448 < baseStart_334448 := by decide
  rcases family_descends (prefixWord ++ tailWord_334448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334469 : List Nat := [1, 3, 1, 1, 4, 3, 3, 1, 3]
def baseStart_334469 : Nat := 118140960795 + 334469 * 2 ^ 59
def prefixEnd_334469 : Nat := 4983230072969 + 3 ^ 40 * 334469 * 2
def baseEnd_334469 : Nat := 152660765358895219732721

theorem tailTrace_334469 : CollatzResearch.WordTrace tailWord_334469 prefixEnd_334469 152660765358895219732721 := by
  unfold tailWord_334469
  simp only [CollatzResearch.WordTrace]
  refine ⟨12199086625283410602534461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8132724416855607068356307 12199086625283410602534461)
  ·
    refine ⟨4574657484481278975950423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12199086625283410602534461 4574657484481278975950423)
    ·
      refine ⟨6861986226721918463925635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4574657484481278975950423 6861986226721918463925635)
      ·
        refine ⟨10292979340082877695888453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6861986226721918463925635 10292979340082877695888453)
        ·
          refine ⟨1929933626265539567979085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10292979340082877695888453 1929933626265539567979085)
          ·
            refine ⟨723725109849577337992157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1929933626265539567979085 723725109849577337992157)
            ·
              refine ⟨271396916193591501747059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 723725109849577337992157 271396916193591501747059)
              ·
                refine ⟨407095374290387252620589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271396916193591501747059 407095374290387252620589)
                ·
                  refine ⟨152660765358895219732721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 407095374290387252620589 152660765358895219732721)
                  ·
                    rfl

theorem cell20_334469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_334469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334469 prefixEnd_334469 := by exact prefixLift 334469
  have htrace : WordTrace (prefixWord ++ tailWord_334469) baseStart_334469 baseEnd_334469 := by
    simpa [prefixWord, tailWord_334469, baseEnd_334469] using wordTrace_append hprefix tailTrace_334469
  have hstable : (prefixWord ++ tailWord_334469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334469).length < 2 ^ (prefixWord ++ tailWord_334469).sum := by decide
  have hdescent : baseEnd_334469 < baseStart_334469 := by decide
  rcases family_descends (prefixWord ++ tailWord_334469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334511 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 5]
def baseStart_334511 : Nat := 118140960795 + 334511 * 2 ^ 59
def prefixEnd_334511 : Nat := 4983230072969 + 3 ^ 40 * 334511 * 2
def baseEnd_334511 : Nat := 152679935303329740332549

theorem tailTrace_334511 : CollatzResearch.WordTrace tailWord_334511 prefixEnd_334511 152679935303329740332549 := by
  unfold tailWord_334511
  simp only [CollatzResearch.WordTrace]
  refine ⟨12200618491131251775563387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8133745660754167850375591 12200618491131251775563387)
  ·
    refine ⟨18300927736696877663345081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12200618491131251775563387 18300927736696877663345081)
    ·
      refine ⟨13725695802522658247508811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18300927736696877663345081 13725695802522658247508811)
      ·
        refine ⟨20588543703783987371263217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13725695802522658247508811 20588543703783987371263217)
        ·
          refine ⟨15441407777837990528447413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20588543703783987371263217 15441407777837990528447413)
          ·
            refine ⟨1447631979172311612041945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15441407777837990528447413 1447631979172311612041945)
            ·
              refine ⟨1085723984379233709031459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447631979172311612041945 1085723984379233709031459)
              ·
                refine ⟨1628585976568850563547189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085723984379233709031459 1628585976568850563547189)
                ·
                  refine ⟨152679935303329740332549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1628585976568850563547189 152679935303329740332549)
                  ·
                    rfl

theorem cell20_334511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 5].length) (baseStart_334511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334511 prefixEnd_334511 := by exact prefixLift 334511
  have htrace : WordTrace (prefixWord ++ tailWord_334511) baseStart_334511 baseEnd_334511 := by
    simpa [prefixWord, tailWord_334511, baseEnd_334511] using wordTrace_append hprefix tailTrace_334511
  have hstable : (prefixWord ++ tailWord_334511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334511).length < 2 ^ (prefixWord ++ tailWord_334511).sum := by decide
  have hdescent : baseEnd_334511 < baseStart_334511 := by decide
  rcases family_descends (prefixWord ++ tailWord_334511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334528 : List Nat := [2, 1, 1, 2, 4, 3, 1, 3, 3]
def baseStart_334528 : Nat := 118140960795 + 334528 * 2 ^ 59
def prefixEnd_334528 : Nat := 4983230072969 + 3 ^ 40 * 334528 * 2
def baseEnd_334528 : Nat := 152687694566553236765813

theorem tailTrace_334528 : CollatzResearch.WordTrace tailWord_334528 prefixEnd_334528 152687694566553236765813 := by
  unfold tailWord_334528
  simp only [CollatzResearch.WordTrace]
  refine ⟨6100619266034831839466119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8134159021379775785954825 6100619266034831839466119)
  ·
    refine ⟨9150928899052247759199179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6100619266034831839466119 9150928899052247759199179)
    ·
      refine ⟨13726393348578371638798769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9150928899052247759199179 13726393348578371638798769)
      ·
        refine ⟨10294795011433778729099077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13726393348578371638798769 10294795011433778729099077)
        ·
          refine ⟨1930274064643833511706077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10294795011433778729099077 1930274064643833511706077)
          ·
            refine ⟨723852774241437566889779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1930274064643833511706077 723852774241437566889779)
            ·
              refine ⟨1085779161362156350334669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 723852774241437566889779 1085779161362156350334669)
              ·
                refine ⟨407167185510808631375501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1085779161362156350334669 407167185510808631375501)
                ·
                  refine ⟨152687694566553236765813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 407167185510808631375501 152687694566553236765813)
                  ·
                    rfl

theorem cell20_334528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_334528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334528 prefixEnd_334528 := by exact prefixLift 334528
  have htrace : WordTrace (prefixWord ++ tailWord_334528) baseStart_334528 baseEnd_334528 := by
    simpa [prefixWord, tailWord_334528, baseEnd_334528] using wordTrace_append hprefix tailTrace_334528
  have hstable : (prefixWord ++ tailWord_334528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334528).length < 2 ^ (prefixWord ++ tailWord_334528).sum := by decide
  have hdescent : baseEnd_334528 < baseStart_334528 := by decide
  rcases family_descends (prefixWord ++ tailWord_334528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334542 : List Nat := [4, 1, 1, 1, 3, 2, 2, 6]
def baseStart_334542 : Nat := 118140960795 + 334542 * 2 ^ 59
def prefixEnd_334542 : Nat := 4983230072969 + 3 ^ 40 * 334542 * 2
def baseEnd_334542 : Nat := 50898028182677136766363

theorem tailTrace_334542 : CollatzResearch.WordTrace tailWord_334542 prefixEnd_334542 50898028182677136766363 := by
  unfold tailWord_334542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1525218644252368008742735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8134499436012629379961253 1525218644252368008742735)
  ·
    refine ⟨2287827966378552013114103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1525218644252368008742735 2287827966378552013114103)
    ·
      refine ⟨3431741949567828019671155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2287827966378552013114103 3431741949567828019671155)
      ·
        refine ⟨5147612924351742029506733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3431741949567828019671155 5147612924351742029506733)
        ·
          refine ⟨1930354846631903261065025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5147612924351742029506733 1930354846631903261065025)
          ·
            refine ⟨1447766134973927445798769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1930354846631903261065025 1447766134973927445798769)
            ·
              refine ⟨1085824601230445584349077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447766134973927445798769 1085824601230445584349077)
              ·
                refine ⟨50898028182677136766363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1085824601230445584349077 50898028182677136766363)
                ·
                  rfl

theorem cell20_334542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_334542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334542 prefixEnd_334542 := by exact prefixLift 334542
  have htrace : WordTrace (prefixWord ++ tailWord_334542) baseStart_334542 baseEnd_334542 := by
    simpa [prefixWord, tailWord_334542, baseEnd_334542] using wordTrace_append hprefix tailTrace_334542
  have hstable : (prefixWord ++ tailWord_334542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334542).length < 2 ^ (prefixWord ++ tailWord_334542).sum := by decide
  have hdescent : baseEnd_334542 < baseStart_334542 := by decide
  rcases family_descends (prefixWord ++ tailWord_334542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334573 : List Nat := [1, 5, 1, 2, 1, 1, 2, 3, 4]
def baseStart_334573 : Nat := 118140960795 + 334573 * 2 ^ 59
def prefixEnd_334573 : Nat := 4983230072969 + 3 ^ 40 * 334573 * 2
def baseEnd_334573 : Nat := 152708233792733080265629

theorem tailTrace_334573 : CollatzResearch.WordTrace tailWord_334573 prefixEnd_334573 152708233792733080265629 := by
  unfold tailWord_334573
  simp only [CollatzResearch.WordTrace]
  refine ⟨12202879816906636364320373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8135253211271090909546915 12202879816906636364320373)
  ·
    refine ⟨1144019982834997159155035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12202879816906636364320373 1144019982834997159155035)
    ·
      refine ⟨1716029974252495738732553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1144019982834997159155035 1716029974252495738732553)
      ·
        refine ⟨1287022480689371804049415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1716029974252495738732553 1287022480689371804049415)
        ·
          refine ⟨1930533721034057706074123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1287022480689371804049415 1930533721034057706074123)
          ·
            refine ⟨2895800581551086559111185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930533721034057706074123 2895800581551086559111185)
            ·
              refine ⟨2171850436163314919333389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2895800581551086559111185 2171850436163314919333389)
              ·
                refine ⟨814443913561243094750021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2171850436163314919333389 814443913561243094750021)
                ·
                  refine ⟨152708233792733080265629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 814443913561243094750021 152708233792733080265629)
                  ·
                    rfl

theorem cell20_334573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_334573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334573 prefixEnd_334573 := by exact prefixLift 334573
  have htrace : WordTrace (prefixWord ++ tailWord_334573) baseStart_334573 baseEnd_334573 := by
    simpa [prefixWord, tailWord_334573, baseEnd_334573] using wordTrace_append hprefix tailTrace_334573
  have hstable : (prefixWord ++ tailWord_334573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334573).length < 2 ^ (prefixWord ++ tailWord_334573).sum := by decide
  have hdescent : baseEnd_334573 < baseStart_334573 := by decide
  rcases family_descends (prefixWord ++ tailWord_334573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334590 : List Nat := [4, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_334590 : Nat := 118140960795 + 334590 * 2 ^ 59
def prefixEnd_334590 : Nat := 4983230072969 + 3 ^ 40 * 334590 * 2
def baseEnd_334590 : Nat := 152715993055956576698893

theorem tailTrace_334590 : CollatzResearch.WordTrace tailWord_334590 prefixEnd_334590 152715993055956576698893 := by
  unfold tailWord_334590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1525437482230631033461153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8135666571896698845126149 1525437482230631033461153)
  ·
    refine ⟨1144078111672973275095865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1525437482230631033461153 1144078111672973275095865)
    ·
      refine ⟨858058583754729956321899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1144078111672973275095865 858058583754729956321899)
      ·
        refine ⟨1287087875632094934482849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 858058583754729956321899 1287087875632094934482849)
        ·
          refine ⟨965315906724071200862137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1287087875632094934482849 965315906724071200862137)
          ·
            refine ⟨723986930043053400646603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 965315906724071200862137 723986930043053400646603)
            ·
              refine ⟨1085980395064580100969905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 723986930043053400646603 1085980395064580100969905)
              ·
                refine ⟨814485296298435075727429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1085980395064580100969905 814485296298435075727429)
                ·
                  refine ⟨152715993055956576698893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 814485296298435075727429 152715993055956576698893)
                  ·
                    rfl

theorem cell20_334590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_334590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334590 prefixEnd_334590 := by exact prefixLift 334590
  have htrace : WordTrace (prefixWord ++ tailWord_334590) baseStart_334590 baseEnd_334590 := by
    simpa [prefixWord, tailWord_334590, baseEnd_334590] using wordTrace_append hprefix tailTrace_334590
  have hstable : (prefixWord ++ tailWord_334590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334590).length < 2 ^ (prefixWord ++ tailWord_334590).sum := by decide
  have hdescent : baseEnd_334590 < baseStart_334590 := by decide
  rcases family_descends (prefixWord ++ tailWord_334590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334601 : List Nat := [1, 2, 1, 1, 3, 2, 2, 8]
def baseStart_334601 : Nat := 118140960795 + 334601 * 2 ^ 59
def prefixEnd_334601 : Nat := 4983230072969 + 3 ^ 40 * 334601 * 2
def baseEnd_334601 : Nat := 50907004585229809110727

theorem tailTrace_334601 : CollatzResearch.WordTrace tailWord_334601 prefixEnd_334601 50907004585229809110727 := by
  unfold tailWord_334601
  simp only [CollatzResearch.WordTrace]
  refine ⟨12203901060805197146339657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8135934040536798097559771 12203901060805197146339657)
  ·
    refine ⟨9152925795603897859754743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12203901060805197146339657 9152925795603897859754743)
    ·
      refine ⟨13729388693405846789632115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9152925795603897859754743 13729388693405846789632115)
      ·
        refine ⟨20594083040108770184448173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13729388693405846789632115 20594083040108770184448173)
        ·
          refine ⟨7722781140040788819168065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20594083040108770184448173 7722781140040788819168065)
          ·
            refine ⟨5792085855030591614376049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7722781140040788819168065 5792085855030591614376049)
            ·
              refine ⟨4344064391272943710782037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5792085855030591614376049 4344064391272943710782037)
              ·
                refine ⟨50907004585229809110727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4344064391272943710782037 50907004585229809110727)
                ·
                  rfl

theorem cell20_334601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 8].length) (baseStart_334601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334601 prefixEnd_334601 := by exact prefixLift 334601
  have htrace : WordTrace (prefixWord ++ tailWord_334601) baseStart_334601 baseEnd_334601 := by
    simpa [prefixWord, tailWord_334601, baseEnd_334601] using wordTrace_append hprefix tailTrace_334601
  have hstable : (prefixWord ++ tailWord_334601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334601).length < 2 ^ (prefixWord ++ tailWord_334601).sum := by decide
  have hdescent : baseEnd_334601 < baseStart_334601 := by decide
  rcases family_descends (prefixWord ++ tailWord_334601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334621 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 5]
def baseStart_334621 : Nat := 118140960795 + 334621 * 2 ^ 59
def prefixEnd_334621 : Nat := 4983230072969 + 3 ^ 40 * 334621 * 2
def baseEnd_334621 : Nat := 152730142300658246665433

theorem tailTrace_334621 : CollatzResearch.WordTrace tailWord_334621 prefixEnd_334621 152730142300658246665433 := by
  unfold tailWord_334621
  simp only [CollatzResearch.WordTrace]
  refine ⟨12204630520732740562067717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8136420347155160374711811 12204630520732740562067717)
  ·
    refine ⟨2288368222637388855387697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12204630520732740562067717 2288368222637388855387697)
    ·
      refine ⟨1716276166978041641540773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2288368222637388855387697 1716276166978041641540773)
      ·
        refine ⟨321801781308382807788895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1716276166978041641540773 321801781308382807788895)
        ·
          refine ⟨482702671962574211683343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321801781308382807788895 482702671962574211683343)
          ·
            refine ⟨724054007943861317525015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482702671962574211683343 724054007943861317525015)
            ·
              refine ⟨1086081011915791976287523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 724054007943861317525015 1086081011915791976287523)
              ·
                refine ⟨1629121517873687964431285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1086081011915791976287523 1629121517873687964431285)
                ·
                  refine ⟨152730142300658246665433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1629121517873687964431285 152730142300658246665433)
                  ·
                    rfl

theorem cell20_334621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_334621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334621 prefixEnd_334621 := by exact prefixLift 334621
  have htrace : WordTrace (prefixWord ++ tailWord_334621) baseStart_334621 baseEnd_334621 := by
    simpa [prefixWord, tailWord_334621, baseEnd_334621] using wordTrace_append hprefix tailTrace_334621
  have hstable : (prefixWord ++ tailWord_334621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334621).length < 2 ^ (prefixWord ++ tailWord_334621).sum := by decide
  have hdescent : baseEnd_334621 < baseStart_334621 := by decide
  rcases family_descends (prefixWord ++ tailWord_334621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334625 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 5]
def baseStart_334625 : Nat := 118140960795 + 334625 * 2 ^ 59
def prefixEnd_334625 : Nat := 4983230072969 + 3 ^ 40 * 334625 * 2
def baseEnd_334625 : Nat := 152731968009652010532083

theorem tailTrace_334625 : CollatzResearch.WordTrace tailWord_334625 prefixEnd_334625 152731968009652010532083 := by
  unfold tailWord_334625
  simp only [CollatzResearch.WordTrace]
  refine ⟨12204776412718249245213329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8136517608478832830142219 12204776412718249245213329)
  ·
    refine ⟨9153582309538686933909997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12204776412718249245213329 9153582309538686933909997)
    ·
      refine ⟨3432593366077007600216249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9153582309538686933909997 3432593366077007600216249)
      ·
        refine ⟨2574445024557755700162187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3432593366077007600216249 2574445024557755700162187)
        ·
          refine ⟨3861667536836633550243281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2574445024557755700162187 3861667536836633550243281)
          ·
            refine ⟨2896250652627475162682461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3861667536836633550243281 2896250652627475162682461)
            ·
              refine ⟨1086093994735303186005923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2896250652627475162682461 1086093994735303186005923)
              ·
                refine ⟨1629140992102954779008885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1086093994735303186005923 1629140992102954779008885)
                ·
                  refine ⟨152731968009652010532083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1629140992102954779008885 152731968009652010532083)
                  ·
                    rfl

theorem cell20_334625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_334625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334625 prefixEnd_334625 := by exact prefixLift 334625
  have htrace : WordTrace (prefixWord ++ tailWord_334625) baseStart_334625 baseEnd_334625 := by
    simpa [prefixWord, tailWord_334625, baseEnd_334625] using wordTrace_append hprefix tailTrace_334625
  have hstable : (prefixWord ++ tailWord_334625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334625).length < 2 ^ (prefixWord ++ tailWord_334625).sum := by decide
  have hdescent : baseEnd_334625 < baseStart_334625 := by decide
  rcases family_descends (prefixWord ++ tailWord_334625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334628 : List Nat := [2, 3, 1, 3, 3, 1, 2, 1, 4]
def baseStart_334628 : Nat := 118140960795 + 334628 * 2 ^ 59
def prefixEnd_334628 : Nat := 4983230072969 + 3 ^ 40 * 334628 * 2
def baseEnd_334628 : Nat := 152733337291397333432071

theorem tailTrace_334628 : CollatzResearch.WordTrace tailWord_334628 prefixEnd_334628 152733337291397333432071 := by
  unfold tailWord_334628
  simp only [CollatzResearch.WordTrace]
  refine ⟨6102442915853690378786269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8136590554471587171715025 6102442915853690378786269)
  ·
    refine ⟨2288416093445133892044851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6102442915853690378786269 2288416093445133892044851)
    ·
      refine ⟨3432624140167700838067277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2288416093445133892044851 3432624140167700838067277)
      ·
        refine ⟨1287234052562887814275229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3432624140167700838067277 1287234052562887814275229)
        ·
          refine ⟨482712769711082930353211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1287234052562887814275229 482712769711082930353211)
          ·
            refine ⟨724069154566624395529817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482712769711082930353211 724069154566624395529817)
            ·
              refine ⟨543051865924968296647363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 724069154566624395529817 543051865924968296647363)
              ·
                refine ⟨814577798887452444971045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543051865924968296647363 814577798887452444971045)
                ·
                  refine ⟨152733337291397333432071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 814577798887452444971045 152733337291397333432071)
                  ·
                    rfl

theorem cell20_334628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_334628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334628 prefixEnd_334628 := by exact prefixLift 334628
  have htrace : WordTrace (prefixWord ++ tailWord_334628) baseStart_334628 baseEnd_334628 := by
    simpa [prefixWord, tailWord_334628, baseEnd_334628] using wordTrace_append hprefix tailTrace_334628
  have hstable : (prefixWord ++ tailWord_334628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334628).length < 2 ^ (prefixWord ++ tailWord_334628).sum := by decide
  have hdescent : baseEnd_334628 < baseStart_334628 := by decide
  rcases family_descends (prefixWord ++ tailWord_334628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334638 : List Nat := [4, 1, 3, 2, 1, 2, 3, 1, 3]
def baseStart_334638 : Nat := 118140960795 + 334638 * 2 ^ 59
def prefixEnd_334638 : Nat := 4983230072969 + 3 ^ 40 * 334638 * 2
def baseEnd_334638 : Nat := 152737901563881743098697

theorem tailTrace_334638 : CollatzResearch.WordTrace tailWord_334638 prefixEnd_334638 152737901563881743098697 := by
  unfold tailWord_334638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1525656320208894058179571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8136833707780768310291045 1525656320208894058179571)
  ·
    refine ⟨2288484480313341087269357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1525656320208894058179571 2288484480313341087269357)
    ·
      refine ⟨858181680117502907726009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2288484480313341087269357 858181680117502907726009)
      ·
        refine ⟨643636260088127180794507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 858181680117502907726009 643636260088127180794507)
        ·
          refine ⟨965454390132190771191761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 643636260088127180794507 965454390132190771191761)
          ·
            refine ⟨724090792599143078393821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 965454390132190771191761 724090792599143078393821)
            ·
              refine ⟨271534047224678654397683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 724090792599143078393821 271534047224678654397683)
              ·
                refine ⟨407301070837017981596525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271534047224678654397683 407301070837017981596525)
                ·
                  refine ⟨152737901563881743098697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 407301070837017981596525 152737901563881743098697)
                  ·
                    rfl

theorem cell20_334638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_334638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334638 prefixEnd_334638 := by exact prefixLift 334638
  have htrace : WordTrace (prefixWord ++ tailWord_334638) baseStart_334638 baseEnd_334638 := by
    simpa [prefixWord, tailWord_334638, baseEnd_334638] using wordTrace_append hprefix tailTrace_334638
  have hstable : (prefixWord ++ tailWord_334638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334638).length < 2 ^ (prefixWord ++ tailWord_334638).sum := by decide
  have hdescent : baseEnd_334638 < baseStart_334638 := by decide
  rcases family_descends (prefixWord ++ tailWord_334638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334670 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_334670 : Nat := 118140960795 + 334670 * 2 ^ 59
def prefixEnd_334670 : Nat := 4983230072969 + 3 ^ 40 * 334670 * 2
def baseEnd_334670 : Nat := 152752507235831854031899

theorem tailTrace_334670 : CollatzResearch.WordTrace tailWord_334670 prefixEnd_334670 152752507235831854031899 := by
  unfold tailWord_334670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1525802212194402741325183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8137611798370147953734309 1525802212194402741325183)
  ·
    refine ⟨2288703318291604111987775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1525802212194402741325183 2288703318291604111987775)
    ·
      refine ⟨3433054977437406167981663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2288703318291604111987775 3433054977437406167981663)
      ·
        refine ⟨5149582466156109251972495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3433054977437406167981663 5149582466156109251972495)
        ·
          refine ⟨7724373699234163877958743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5149582466156109251972495 7724373699234163877958743)
          ·
            refine ⟨11586560548851245816938115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7724373699234163877958743 11586560548851245816938115)
            ·
              refine ⟨17379840823276868725407173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11586560548851245816938115 17379840823276868725407173)
              ·
                refine ⟨3258720154364412886013845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17379840823276868725407173 3258720154364412886013845)
                ·
                  refine ⟨152752507235831854031899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3258720154364412886013845 152752507235831854031899)
                  ·
                    rfl

theorem cell20_334670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_334670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334670 prefixEnd_334670 := by exact prefixLift 334670
  have htrace : WordTrace (prefixWord ++ tailWord_334670) baseStart_334670 baseEnd_334670 := by
    simpa [prefixWord, tailWord_334670, baseEnd_334670] using wordTrace_append hprefix tailTrace_334670
  have hstable : (prefixWord ++ tailWord_334670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334670).length < 2 ^ (prefixWord ++ tailWord_334670).sum := by decide
  have hdescent : baseEnd_334670 < baseStart_334670 := by decide
  rcases family_descends (prefixWord ++ tailWord_334670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334673 : List Nat := [1, 2, 2, 1, 7, 1, 6]
def baseStart_334673 : Nat := 118140960795 + 334673 * 2 ^ 59
def prefixEnd_334673 : Nat := 4983230072969 + 3 ^ 40 * 334673 * 2
def baseEnd_334673 : Nat := 16972652946397464103543

theorem tailTrace_334673 : CollatzResearch.WordTrace tailWord_334673 prefixEnd_334673 16972652946397464103543 := by
  unfold tailWord_334673
  simp only [CollatzResearch.WordTrace]
  refine ⟨12206527116544353442960673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8137684744362902295307115 12206527116544353442960673)
  ·
    refine ⟨9154895337408265082220505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12206527116544353442960673 9154895337408265082220505)
    ·
      refine ⟨6866171503056198811665379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9154895337408265082220505 6866171503056198811665379)
      ·
        refine ⟨10299257254584298217498069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6866171503056198811665379 10299257254584298217498069)
        ·
          refine ⟨241388841904319489472611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 10299257254584298217498069 241388841904319489472611)
          ·
            refine ⟨362083262856479234208917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241388841904319489472611 362083262856479234208917)
            ·
              refine ⟨16972652946397464103543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 362083262856479234208917 16972652946397464103543)
              ·
                rfl

theorem cell20_334673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 6].length) (baseStart_334673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334673 prefixEnd_334673 := by exact prefixLift 334673
  have htrace : WordTrace (prefixWord ++ tailWord_334673) baseStart_334673 baseEnd_334673 := by
    simpa [prefixWord, tailWord_334673, baseEnd_334673] using wordTrace_append hprefix tailTrace_334673
  have hstable : (prefixWord ++ tailWord_334673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334673).length < 2 ^ (prefixWord ++ tailWord_334673).sum := by decide
  have hdescent : baseEnd_334673 < baseStart_334673 := by decide
  rcases family_descends (prefixWord ++ tailWord_334673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334715 : List Nat := [1, 1, 1, 1, 1, 5, 4, 6]
def baseStart_334715 : Nat := 118140960795 + 334715 * 2 ^ 59
def prefixEnd_334715 : Nat := 4983230072969 + 3 ^ 40 * 334715 * 2
def baseEnd_334715 : Nat := 50924348820670565843905

theorem tailTrace_334715 : CollatzResearch.WordTrace tailWord_334715 prefixEnd_334715 50924348820670565843905 := by
  unfold tailWord_334715
  simp only [CollatzResearch.WordTrace]
  refine ⟨12208058982392194615989599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8138705988261463077326399 12208058982392194615989599)
  ·
    refine ⟨18312088473588291923984399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12208058982392194615989599 18312088473588291923984399)
    ·
      refine ⟨27468132710382437885976599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18312088473588291923984399 27468132710382437885976599)
      ·
        refine ⟨41202199065573656828964899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27468132710382437885976599 41202199065573656828964899)
        ·
          refine ⟨61803298598360485243447349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41202199065573656828964899 61803298598360485243447349)
          ·
            refine ⟨5794059243596295491573189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61803298598360485243447349 5794059243596295491573189)
            ·
              refine ⟨1086386108174305404669973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5794059243596295491573189 1086386108174305404669973)
              ·
                refine ⟨50924348820670565843905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1086386108174305404669973 50924348820670565843905)
                ·
                  rfl

theorem cell20_334715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 6].length) (baseStart_334715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334715 prefixEnd_334715 := by exact prefixLift 334715
  have htrace : WordTrace (prefixWord ++ tailWord_334715) baseStart_334715 baseEnd_334715 := by
    simpa [prefixWord, tailWord_334715, baseEnd_334715] using wordTrace_append hprefix tailTrace_334715
  have hstable : (prefixWord ++ tailWord_334715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334715).length < 2 ^ (prefixWord ++ tailWord_334715).sum := by decide
  have hdescent : baseEnd_334715 < baseStart_334715 := by decide
  rcases family_descends (prefixWord ++ tailWord_334715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334801 : List Nat := [1, 2, 2, 1, 2, 1, 3, 6, 2]
def baseStart_334801 : Nat := 118140960795 + 334801 * 2 ^ 59
def prefixEnd_334801 : Nat := 4983230072969 + 3 ^ 40 * 334801 * 2
def baseEnd_334801 : Nat := 152812299205377620664697

theorem tailTrace_334801 : CollatzResearch.WordTrace tailWord_334801 prefixEnd_334801 152812299205377620664697 := by
  unfold tailWord_334801
  simp only [CollatzResearch.WordTrace]
  refine ⟨12211195660080631303620257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8140797106720420869080171 12211195660080631303620257)
  ·
    refine ⟨9158396745060473477715193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12211195660080631303620257 9158396745060473477715193)
    ·
      refine ⟨6868797558795355108286395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9158396745060473477715193 6868797558795355108286395)
      ·
        refine ⟨10303196338193032662429593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6868797558795355108286395 10303196338193032662429593)
        ·
          refine ⟨7727397253644774496822195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10303196338193032662429593 7727397253644774496822195)
          ·
            refine ⟨11591095880467161745233293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7727397253644774496822195 11591095880467161745233293)
            ·
              refine ⟨4346660955175185654462485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11591095880467161745233293 4346660955175185654462485)
              ·
                refine ⟨203749732273836827552929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4346660955175185654462485 203749732273836827552929)
                ·
                  refine ⟨152812299205377620664697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203749732273836827552929 152812299205377620664697)
                  ·
                    rfl

theorem cell20_334801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 2].length) (baseStart_334801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334801 prefixEnd_334801 := by exact prefixLift 334801
  have htrace : WordTrace (prefixWord ++ tailWord_334801) baseStart_334801 baseEnd_334801 := by
    simpa [prefixWord, tailWord_334801, baseEnd_334801] using wordTrace_append hprefix tailTrace_334801
  have hstable : (prefixWord ++ tailWord_334801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334801).length < 2 ^ (prefixWord ++ tailWord_334801).sum := by decide
  have hdescent : baseEnd_334801 < baseStart_334801 := by decide
  rcases family_descends (prefixWord ++ tailWord_334801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334818 : List Nat := [3, 3, 3, 1, 1, 1, 2, 2, 4]
def baseStart_334818 : Nat := 118140960795 + 334818 * 2 ^ 59
def prefixEnd_334818 : Nat := 4983230072969 + 3 ^ 40 * 334818 * 2
def baseEnd_334818 : Nat := 152820058468601117097961

theorem tailTrace_334818 : CollatzResearch.WordTrace tailWord_334818 prefixEnd_334818 152820058468601117097961 := by
  unfold tailWord_334818
  simp only [CollatzResearch.WordTrace]
  refine ⟨3052953925254760801747277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8141210467346028804659405 3052953925254760801747277)
  ·
    refine ⟨1144857721970535300655229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3052953925254760801747277 1144857721970535300655229)
    ·
      refine ⟨429321645738950737745711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1144857721970535300655229 429321645738950737745711)
      ·
        refine ⟨643982468608426106618567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429321645738950737745711 643982468608426106618567)
        ·
          refine ⟨965973702912639159927851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 643982468608426106618567 965973702912639159927851)
          ·
            refine ⟨1448960554368958739891777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965973702912639159927851 1448960554368958739891777)
            ·
              refine ⟨1086720415776719054918833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1448960554368958739891777 1086720415776719054918833)
              ·
                refine ⟨815040311832539291189125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1086720415776719054918833 815040311832539291189125)
                ·
                  refine ⟨152820058468601117097961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 815040311832539291189125 152820058468601117097961)
                  ·
                    rfl

theorem cell20_334818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_334818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334818 prefixEnd_334818 := by exact prefixLift 334818
  have htrace : WordTrace (prefixWord ++ tailWord_334818) baseStart_334818 baseEnd_334818 := by
    simpa [prefixWord, tailWord_334818, baseEnd_334818] using wordTrace_append hprefix tailTrace_334818
  have hstable : (prefixWord ++ tailWord_334818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334818).length < 2 ^ (prefixWord ++ tailWord_334818).sum := by decide
  have hdescent : baseEnd_334818 < baseStart_334818 := by decide
  rcases family_descends (prefixWord ++ tailWord_334818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334821 : List Nat := [1, 3, 1, 6, 2, 1, 2, 4]
def baseStart_334821 : Nat := 118140960795 + 334821 * 2 ^ 59
def prefixEnd_334821 : Nat := 4983230072969 + 3 ^ 40 * 334821 * 2
def baseEnd_334821 : Nat := 50940475916782146665983

theorem tailTrace_334821 : CollatzResearch.WordTrace tailWord_334821 prefixEnd_334821 50940475916782146665983 := by
  unfold tailWord_334821
  simp only [CollatzResearch.WordTrace]
  refine ⟨12211925120008174719348317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8141283413338783146232211 12211925120008174719348317)
  ·
    refine ⟨4579471920003065519755619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12211925120008174719348317 4579471920003065519755619)
    ·
      refine ⟨6869207880004598279633429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4579471920003065519755619 6869207880004598279633429)
      ·
        refine ⟨321994119375215544357817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6869207880004598279633429 321994119375215544357817)
        ·
          refine ⟨241495589531411658268363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321994119375215544357817 241495589531411658268363)
          ·
            refine ⟨362243384297117487402545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241495589531411658268363 362243384297117487402545)
            ·
              refine ⟨271682538222838115551909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362243384297117487402545 271682538222838115551909)
              ·
                refine ⟨50940475916782146665983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 271682538222838115551909 50940475916782146665983)
                ·
                  rfl

theorem cell20_334821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 4].length) (baseStart_334821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334821 prefixEnd_334821 := by exact prefixLift 334821
  have htrace : WordTrace (prefixWord ++ tailWord_334821) baseStart_334821 baseEnd_334821 := by
    simpa [prefixWord, tailWord_334821, baseEnd_334821] using wordTrace_append hprefix tailTrace_334821
  have hstable : (prefixWord ++ tailWord_334821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334821).length < 2 ^ (prefixWord ++ tailWord_334821).sum := by decide
  have hdescent : baseEnd_334821 < baseStart_334821 := by decide
  rcases family_descends (prefixWord ++ tailWord_334821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334853 : List Nat := [1, 3, 1, 1, 2, 3, 2, 4, 3]
def baseStart_334853 : Nat := 118140960795 + 334853 * 2 ^ 59
def prefixEnd_334853 : Nat := 4983230072969 + 3 ^ 40 * 334853 * 2
def baseEnd_334853 : Nat := 152836033422296550931151

theorem tailTrace_334853 : CollatzResearch.WordTrace tailWord_334853 prefixEnd_334853 152836033422296550931151 := by
  unfold tailWord_334853
  simp only [CollatzResearch.WordTrace]
  refine ⟨12213092255892244184513213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8142061503928162789675475 12213092255892244184513213)
  ·
    refine ⟨4579909595959591569192455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12213092255892244184513213 4579909595959591569192455)
    ·
      refine ⟨6869864393939387353788683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4579909595959591569192455 6869864393939387353788683)
      ·
        refine ⟨10304796590909081030683025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6869864393939387353788683 10304796590909081030683025)
        ·
          refine ⟨7728597443181810773012269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10304796590909081030683025 7728597443181810773012269)
          ·
            refine ⟨2898224041193179039879601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7728597443181810773012269 2898224041193179039879601)
            ·
              refine ⟨2173668030894884279909701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2898224041193179039879601 2173668030894884279909701)
              ·
                refine ⟨407562755792790802483069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2173668030894884279909701 407562755792790802483069)
                ·
                  refine ⟨152836033422296550931151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 407562755792790802483069 152836033422296550931151)
                  ·
                    rfl

theorem cell20_334853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_334853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334853 prefixEnd_334853 := by exact prefixLift 334853
  have htrace : WordTrace (prefixWord ++ tailWord_334853) baseStart_334853 baseEnd_334853 := by
    simpa [prefixWord, tailWord_334853, baseEnd_334853] using wordTrace_append hprefix tailTrace_334853
  have hstable : (prefixWord ++ tailWord_334853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334853).length < 2 ^ (prefixWord ++ tailWord_334853).sum := by decide
  have hdescent : baseEnd_334853 < baseStart_334853 := by decide
  rcases family_descends (prefixWord ++ tailWord_334853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334884 : List Nat := [2, 3, 1, 4, 1, 1, 2, 6]
def baseStart_334884 : Nat := 118140960795 + 334884 * 2 ^ 59
def prefixEnd_334884 : Nat := 4983230072969 + 3 ^ 40 * 334884 * 2
def baseEnd_334884 : Nat := 50950060888999406965897

theorem tailTrace_334884 : CollatzResearch.WordTrace tailWord_334884 prefixEnd_334884 50950060888999406965897 := by
  unfold tailWord_334884
  simp only [CollatzResearch.WordTrace]
  refine ⟨6107111459389968239445853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8142815279186624319261137 6107111459389968239445853)
  ·
    refine ⟨2290166797271238089792195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6107111459389968239445853 2290166797271238089792195)
    ·
      refine ⟨3435250195906857134688293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2290166797271238089792195 3435250195906857134688293)
      ·
        refine ⟨644109411732535712754055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3435250195906857134688293 644109411732535712754055)
        ·
          refine ⟨966164117598803569131083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644109411732535712754055 966164117598803569131083)
          ·
            refine ⟨1449246176398205353696625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966164117598803569131083 1449246176398205353696625)
            ·
              refine ⟨1086934632298654015272469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1449246176398205353696625 1086934632298654015272469)
              ·
                refine ⟨50950060888999406965897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1086934632298654015272469 50950060888999406965897)
                ·
                  rfl

theorem cell20_334884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_334884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334884 prefixEnd_334884 := by exact prefixLift 334884
  have htrace : WordTrace (prefixWord ++ tailWord_334884) baseStart_334884 baseEnd_334884 := by
    simpa [prefixWord, tailWord_334884, baseEnd_334884] using wordTrace_append hprefix tailTrace_334884
  have hstable : (prefixWord ++ tailWord_334884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334884).length < 2 ^ (prefixWord ++ tailWord_334884).sum := by decide
  have hdescent : baseEnd_334884 < baseStart_334884 := by decide
  rcases family_descends (prefixWord ++ tailWord_334884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334894 : List Nat := [4, 1, 3, 1, 1, 1, 2, 5, 2]
def baseStart_334894 : Nat := 118140960795 + 334894 * 2 ^ 59
def prefixEnd_334894 : Nat := 4983230072969 + 3 ^ 40 * 334894 * 2
def baseEnd_334894 : Nat := 152854746939482630564317

theorem tailTrace_334894 : CollatzResearch.WordTrace tailWord_334894 prefixEnd_334894 152854746939482630564317 := by
  unfold tailWord_334894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1526823456092963523344467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8143058432495805457837157 1526823456092963523344467)
  ·
    refine ⟨2290235184139445285016701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1526823456092963523344467 2290235184139445285016701)
    ·
      refine ⟨858838194052291981881263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2290235184139445285016701 858838194052291981881263)
      ·
        refine ⟨1288257291078437972821895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 858838194052291981881263 1288257291078437972821895)
        ·
          refine ⟨1932385936617656959232843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1288257291078437972821895 1932385936617656959232843)
          ·
            refine ⟨2898578904926485438849265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1932385936617656959232843 2898578904926485438849265)
            ·
              refine ⟨2173934178694864079136949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2898578904926485438849265 2173934178694864079136949)
              ·
                refine ⟨203806329252643507419089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2173934178694864079136949 203806329252643507419089)
                ·
                  refine ⟨152854746939482630564317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203806329252643507419089 152854746939482630564317)
                  ·
                    rfl

theorem cell20_334894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_334894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334894 prefixEnd_334894 := by exact prefixLift 334894
  have htrace : WordTrace (prefixWord ++ tailWord_334894) baseStart_334894 baseEnd_334894 := by
    simpa [prefixWord, tailWord_334894, baseEnd_334894] using wordTrace_append hprefix tailTrace_334894
  have hstable : (prefixWord ++ tailWord_334894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334894).length < 2 ^ (prefixWord ++ tailWord_334894).sum := by decide
  have hdescent : baseEnd_334894 < baseStart_334894 := by decide
  rcases family_descends (prefixWord ++ tailWord_334894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334905 : List Nat := [1, 2, 1, 5, 2, 9]
def baseStart_334905 : Nat := 118140960795 + 334905 * 2 ^ 59
def prefixEnd_334905 : Nat := 4983230072969 + 3 ^ 40 * 334905 * 2
def baseEnd_334905 : Nat := 5661472875526499303615

theorem tailTrace_334905 : CollatzResearch.WordTrace tailWord_334905 prefixEnd_334905 5661472875526499303615 := by
  unfold tailWord_334905
  simp only [CollatzResearch.WordTrace]
  refine ⟨12214988851703857065406169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8143325901135904710270779 12214988851703857065406169)
  ·
    refine ⟨9161241638777892799054627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12214988851703857065406169 9161241638777892799054627)
    ·
      refine ⟨13741862458166839198581941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9161241638777892799054627 13741862458166839198581941)
      ·
        refine ⟨1288299605453141174867057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13741862458166839198581941 1288299605453141174867057)
        ·
          refine ⟨966224704089855881150293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1288299605453141174867057 966224704089855881150293)
          ·
            refine ⟨5661472875526499303615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 966224704089855881150293 5661472875526499303615)
            ·
              rfl

theorem cell20_334905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 9].length) (baseStart_334905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334905 prefixEnd_334905 := by exact prefixLift 334905
  have htrace : WordTrace (prefixWord ++ tailWord_334905) baseStart_334905 baseEnd_334905 := by
    simpa [prefixWord, tailWord_334905, baseEnd_334905] using wordTrace_append hprefix tailTrace_334905
  have hstable : (prefixWord ++ tailWord_334905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334905).length < 2 ^ (prefixWord ++ tailWord_334905).sum := by decide
  have hdescent : baseEnd_334905 < baseStart_334905 := by decide
  rcases family_descends (prefixWord ++ tailWord_334905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334908 : List Nat := [2, 2, 2, 2, 2, 3, 2, 2, 3]
def baseStart_334908 : Nat := 118140960795 + 334908 * 2 ^ 59
def prefixEnd_334908 : Nat := 4983230072969 + 3 ^ 40 * 334908 * 2
def baseEnd_334908 : Nat := 152861136920960804097593

theorem tailTrace_334908 : CollatzResearch.WordTrace tailWord_334908 prefixEnd_334908 152861136920960804097593 := by
  unfold tailWord_334908
  simp only [CollatzResearch.WordTrace]
  refine ⟨6107549135346494288882689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8143398847128659051843585 6107549135346494288882689)
  ·
    refine ⟨4580661851509870716662017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6107549135346494288882689 4580661851509870716662017)
    ·
      refine ⟨3435496388632403037496513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4580661851509870716662017 3435496388632403037496513)
      ·
        refine ⟨2576622291474302278122385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3435496388632403037496513 2576622291474302278122385)
        ·
          refine ⟨1932466718605726708591789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2576622291474302278122385 1932466718605726708591789)
          ·
            refine ⟨724675019477147515721921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1932466718605726708591789 724675019477147515721921)
            ·
              refine ⟨543506264607860636791441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 724675019477147515721921 543506264607860636791441)
              ·
                refine ⟨407629698455895477593581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 543506264607860636791441 407629698455895477593581)
                ·
                  refine ⟨152861136920960804097593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 407629698455895477593581 152861136920960804097593)
                  ·
                    rfl

theorem cell20_334908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_334908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334908 prefixEnd_334908 := by exact prefixLift 334908
  have htrace : WordTrace (prefixWord ++ tailWord_334908) baseStart_334908 baseEnd_334908 := by
    simpa [prefixWord, tailWord_334908, baseEnd_334908] using wordTrace_append hprefix tailTrace_334908
  have hstable : (prefixWord ++ tailWord_334908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334908).length < 2 ^ (prefixWord ++ tailWord_334908).sum := by decide
  have hdescent : baseEnd_334908 < baseStart_334908 := by decide
  rcases family_descends (prefixWord ++ tailWord_334908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334915 : List Nat := [1, 1, 1, 3, 1, 2, 5, 4, 2]
def baseStart_334915 : Nat := 118140960795 + 334915 * 2 ^ 59
def prefixEnd_334915 : Nat := 4983230072969 + 3 ^ 40 * 334915 * 2
def baseEnd_334915 : Nat := 152864331911699890864231

theorem tailTrace_334915 : CollatzResearch.WordTrace tailWord_334915 prefixEnd_334915 152864331911699890864231 := by
  unfold tailWord_334915
  simp only [CollatzResearch.WordTrace]
  refine ⟨12215353581667628773270199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8143569054445085848846799 12215353581667628773270199)
  ·
    refine ⟨18323030372501443159905299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12215353581667628773270199 18323030372501443159905299)
    ·
      refine ⟨27484545558752164739857949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18323030372501443159905299 27484545558752164739857949)
      ·
        refine ⟨10306704584532061777446731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27484545558752164739857949 10306704584532061777446731)
        ·
          refine ⟨15460056876798092666170097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10306704584532061777446731 15460056876798092666170097)
          ·
            refine ⟨11595042657598569499627573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15460056876798092666170097 11595042657598569499627573)
            ·
              refine ⟨1087035249149865890590085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11595042657598569499627573 1087035249149865890590085)
              ·
                refine ⟨203819109215599854485641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1087035249149865890590085 203819109215599854485641)
                ·
                  refine ⟨152864331911699890864231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203819109215599854485641 152864331911699890864231)
                  ·
                    rfl

theorem cell20_334915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 2].length) (baseStart_334915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334915 prefixEnd_334915 := by exact prefixLift 334915
  have htrace : WordTrace (prefixWord ++ tailWord_334915) baseStart_334915 baseEnd_334915 := by
    simpa [prefixWord, tailWord_334915, baseEnd_334915] using wordTrace_append hprefix tailTrace_334915
  have hstable : (prefixWord ++ tailWord_334915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334915).length < 2 ^ (prefixWord ++ tailWord_334915).sum := by decide
  have hdescent : baseEnd_334915 < baseStart_334915 := by decide
  rcases family_descends (prefixWord ++ tailWord_334915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334918 : List Nat := [6, 1, 1, 1, 1, 4, 1, 5]
def baseStart_334918 : Nat := 118140960795 + 334918 * 2 ^ 59
def prefixEnd_334918 : Nat := 4983230072969 + 3 ^ 40 * 334918 * 2
def baseEnd_334918 : Nat := 50955233731148404588073

theorem tailTrace_334918 : CollatzResearch.WordTrace tailWord_334918 prefixEnd_334918 50955233731148404588073 := by
  unfold tailWord_334918
  simp only [CollatzResearch.WordTrace]
  refine ⟨381733218770523758925919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8143642000437840190419605 381733218770523758925919)
  ·
    refine ⟨572599828155785638388879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 381733218770523758925919 572599828155785638388879)
    ·
      refine ⟨858899742233678457583319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 572599828155785638388879 858899742233678457583319)
      ·
        refine ⟨1288349613350517686374979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 858899742233678457583319 1288349613350517686374979)
        ·
          refine ⟨1932524420025776529562469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1288349613350517686374979 1932524420025776529562469)
          ·
            refine ⟨362348328754833099292963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1932524420025776529562469 362348328754833099292963)
            ·
              refine ⟨543522493132249648939445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362348328754833099292963 543522493132249648939445)
              ·
                refine ⟨50955233731148404588073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 543522493132249648939445 50955233731148404588073)
                ·
                  rfl

theorem cell20_334918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_334918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334918 prefixEnd_334918 := by exact prefixLift 334918
  have htrace : WordTrace (prefixWord ++ tailWord_334918) baseStart_334918 baseEnd_334918 := by
    simpa [prefixWord, tailWord_334918, baseEnd_334918] using wordTrace_append hprefix tailTrace_334918
  have hstable : (prefixWord ++ tailWord_334918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334918).length < 2 ^ (prefixWord ++ tailWord_334918).sum := by decide
  have hdescent : baseEnd_334918 < baseStart_334918 := by decide
  rcases family_descends (prefixWord ++ tailWord_334918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334929 : List Nat := [1, 2, 2, 1, 3, 1, 4, 3, 3]
def baseStart_334929 : Nat := 118140960795 + 334929 * 2 ^ 59
def prefixEnd_334929 : Nat := 4983230072969 + 3 ^ 40 * 334929 * 2
def baseEnd_334929 : Nat := 152870721893178064397507

theorem tailTrace_334929 : CollatzResearch.WordTrace tailWord_334929 prefixEnd_334929 152870721893178064397507 := by
  unfold tailWord_334929
  simp only [CollatzResearch.WordTrace]
  refine ⟨12215864203616909164279841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8143909469077939442853227 12215864203616909164279841)
  ·
    refine ⟨9161898152712681873209881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12215864203616909164279841 9161898152712681873209881)
    ·
      refine ⟨6871423614534511404907411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9161898152712681873209881 6871423614534511404907411)
      ·
        refine ⟨10307135421801767107361117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6871423614534511404907411 10307135421801767107361117)
        ·
          refine ⟨3865175783175662665260419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10307135421801767107361117 3865175783175662665260419)
          ·
            refine ⟨5797763674763493997890629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3865175783175662665260419 5797763674763493997890629)
            ·
              refine ⟨1087080689018155124604493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5797763674763493997890629 1087080689018155124604493)
              ·
                refine ⟨407655258381808171726685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1087080689018155124604493 407655258381808171726685)
                ·
                  refine ⟨152870721893178064397507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 407655258381808171726685 152870721893178064397507)
                  ·
                    rfl

theorem cell20_334929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_334929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334929 prefixEnd_334929 := by exact prefixLift 334929
  have htrace : WordTrace (prefixWord ++ tailWord_334929) baseStart_334929 baseEnd_334929 := by
    simpa [prefixWord, tailWord_334929, baseEnd_334929] using wordTrace_append hprefix tailTrace_334929
  have hstable : (prefixWord ++ tailWord_334929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334929).length < 2 ^ (prefixWord ++ tailWord_334929).sum := by decide
  have hdescent : baseEnd_334929 < baseStart_334929 := by decide
  rcases family_descends (prefixWord ++ tailWord_334929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334936 : List Nat := [2, 1, 2, 2, 1, 3, 3, 2, 4]
def baseStart_334936 : Nat := 118140960795 + 334936 * 2 ^ 59
def prefixEnd_334936 : Nat := 4983230072969 + 3 ^ 40 * 334936 * 2
def baseEnd_334936 : Nat := 152873916883917151164145

theorem tailTrace_334936 : CollatzResearch.WordTrace tailWord_334936 prefixEnd_334936 152873916883917151164145 := by
  unfold tailWord_334936
  simp only [CollatzResearch.WordTrace]
  refine ⟨6108059757295774679892331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8144079676394366239856441 6108059757295774679892331)
  ·
    refine ⟨9162089635943662019838497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6108059757295774679892331 9162089635943662019838497)
    ·
      refine ⟨6871567226957746514878873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9162089635943662019838497 6871567226957746514878873)
      ·
        refine ⟨5153675420218309886159155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6871567226957746514878873 5153675420218309886159155)
        ·
          refine ⟨7730513130327464829238733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5153675420218309886159155 7730513130327464829238733)
          ·
            refine ⟨2898942423872799310964525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7730513130327464829238733 2898942423872799310964525)
            ·
              refine ⟨1087103408952299741611697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2898942423872799310964525 1087103408952299741611697)
              ·
                refine ⟨815327556714224806208773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1087103408952299741611697 815327556714224806208773)
                ·
                  refine ⟨152873916883917151164145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 815327556714224806208773 152873916883917151164145)
                  ·
                    rfl

theorem cell20_334936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_334936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334936 prefixEnd_334936 := by exact prefixLift 334936
  have htrace : WordTrace (prefixWord ++ tailWord_334936) baseStart_334936 baseEnd_334936 := by
    simpa [prefixWord, tailWord_334936, baseEnd_334936] using wordTrace_append hprefix tailTrace_334936
  have hstable : (prefixWord ++ tailWord_334936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334936).length < 2 ^ (prefixWord ++ tailWord_334936).sum := by decide
  have hdescent : baseEnd_334936 < baseStart_334936 := by decide
  rcases family_descends (prefixWord ++ tailWord_334936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334953 : List Nat := [1, 2, 1, 1, 1, 6, 1, 5, 2]
def baseStart_334953 : Nat := 118140960795 + 334953 * 2 ^ 59
def prefixEnd_334953 : Nat := 4983230072969 + 3 ^ 40 * 334953 * 2
def baseEnd_334953 : Nat := 152881676147140647597409

theorem tailTrace_334953 : CollatzResearch.WordTrace tailWord_334953 prefixEnd_334953 152881676147140647597409 := by
  unfold tailWord_334953
  simp only [CollatzResearch.WordTrace]
  refine ⟨12216739555529961263153513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8144493037019974175435675 12216739555529961263153513)
  ·
    refine ⟨9162554666647470947365135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12216739555529961263153513 9162554666647470947365135)
    ·
      refine ⟨13743831999971206421047703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9162554666647470947365135 13743831999971206421047703)
      ·
        refine ⟨20615747999956809631571555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13743831999971206421047703 20615747999956809631571555)
        ·
          refine ⟨30923621999935214447357333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20615747999956809631571555 30923621999935214447357333)
          ·
            refine ⟨1449544781246963177219875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30923621999935214447357333 1449544781246963177219875)
            ·
              refine ⟨2174317171870444765829813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1449544781246963177219875 2174317171870444765829813)
              ·
                refine ⟨203842234862854196796545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2174317171870444765829813 203842234862854196796545)
                ·
                  refine ⟨152881676147140647597409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203842234862854196796545 152881676147140647597409)
                  ·
                    rfl

theorem cell20_334953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 2].length) (baseStart_334953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334953 prefixEnd_334953 := by exact prefixLift 334953
  have htrace : WordTrace (prefixWord ++ tailWord_334953) baseStart_334953 baseEnd_334953 := by
    simpa [prefixWord, tailWord_334953, baseEnd_334953] using wordTrace_append hprefix tailTrace_334953
  have hstable : (prefixWord ++ tailWord_334953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334953).length < 2 ^ (prefixWord ++ tailWord_334953).sum := by decide
  have hdescent : baseEnd_334953 < baseStart_334953 := by decide
  rcases family_descends (prefixWord ++ tailWord_334953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335025 : List Nat := [1, 2, 2, 5, 1, 2, 3, 2, 2]
def baseStart_335025 : Nat := 118140960795 + 335025 * 2 ^ 59
def prefixEnd_335025 : Nat := 4983230072969 + 3 ^ 40 * 335025 * 2
def baseEnd_335025 : Nat := 152914538909028397197115

theorem tailTrace_335025 : CollatzResearch.WordTrace tailWord_335025 prefixEnd_335025 152914538909028397197115 := by
  unfold tailWord_335025
  simp only [CollatzResearch.WordTrace]
  refine ⟨12219365611269117559774529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8146243740846078373183019 12219365611269117559774529)
  ·
    refine ⟨9164524208451838169830897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12219365611269117559774529 9164524208451838169830897)
    ·
      refine ⟨6873393156338878627373173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9164524208451838169830897 6873393156338878627373173)
      ·
        refine ⟨644380608406769871316235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6873393156338878627373173 644380608406769871316235)
        ·
          refine ⟨966570912610154806974353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644380608406769871316235 966570912610154806974353)
          ·
            refine ⟨724928184457616105230765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 966570912610154806974353 724928184457616105230765)
            ·
              refine ⟨271848069171606039461537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 724928184457616105230765 271848069171606039461537)
              ·
                refine ⟨203886051878704529596153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271848069171606039461537 203886051878704529596153)
                ·
                  refine ⟨152914538909028397197115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203886051878704529596153 152914538909028397197115)
                  ·
                    rfl

theorem cell20_335025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 2].length) (baseStart_335025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335025 prefixEnd_335025 := by exact prefixLift 335025
  have htrace : WordTrace (prefixWord ++ tailWord_335025) baseStart_335025 baseEnd_335025 := by
    simpa [prefixWord, tailWord_335025, baseEnd_335025] using wordTrace_append hprefix tailTrace_335025
  have hstable : (prefixWord ++ tailWord_335025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335025).length < 2 ^ (prefixWord ++ tailWord_335025).sum := by decide
  have hdescent : baseEnd_335025 < baseStart_335025 := by decide
  rcases family_descends (prefixWord ++ tailWord_335025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335036 : List Nat := [2, 2, 2, 3, 2, 2, 2, 5]
def baseStart_335036 : Nat := 118140960795 + 335036 * 2 ^ 59
def prefixEnd_335036 : Nat := 4983230072969 + 3 ^ 40 * 335036 * 2
def baseEnd_335036 : Nat := 50973186536253749276801

theorem tailTrace_335036 : CollatzResearch.WordTrace tailWord_335036 prefixEnd_335036 50973186536253749276801 := by
  unfold tailWord_335036
  simp only [CollatzResearch.WordTrace]
  refine ⟨6109883407114633219212481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8146511209486177625616641 6109883407114633219212481)
  ·
    refine ⟨4582412555335974914409361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6109883407114633219212481 4582412555335974914409361)
    ·
      refine ⟨3436809416501981185807021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4582412555335974914409361 3436809416501981185807021)
      ·
        refine ⟨1288803531188242944677633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3436809416501981185807021 1288803531188242944677633)
        ·
          refine ⟨966602648391182208508225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1288803531188242944677633 966602648391182208508225)
          ·
            refine ⟨724951986293386656381169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 966602648391182208508225 724951986293386656381169)
            ·
              refine ⟨543713989720039992285877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 724951986293386656381169 543713989720039992285877)
              ·
                refine ⟨50973186536253749276801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 543713989720039992285877 50973186536253749276801)
                ·
                  rfl

theorem cell20_335036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_335036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335036 prefixEnd_335036 := by exact prefixLift 335036
  have htrace : WordTrace (prefixWord ++ tailWord_335036) baseStart_335036 baseEnd_335036 := by
    simpa [prefixWord, tailWord_335036, baseEnd_335036] using wordTrace_append hprefix tailTrace_335036
  have hstable : (prefixWord ++ tailWord_335036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335036).length < 2 ^ (prefixWord ++ tailWord_335036).sum := by decide
  have hdescent : baseEnd_335036 < baseStart_335036 := by decide
  rcases family_descends (prefixWord ++ tailWord_335036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335074 : List Nat := [3, 3, 4, 10]
def baseStart_335074 : Nat := 118140960795 + 335074 * 2 ^ 59
def prefixEnd_335074 : Nat := 4983230072969 + 3 ^ 40 * 335074 * 2
def baseEnd_335074 : Nat := 629369974667497961167

theorem tailTrace_335074 : CollatzResearch.WordTrace tailWord_335074 prefixEnd_335074 629369974667497961167 := by
  unfold tailWord_335074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3055288197022899732077069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8147435192061065952205517 3055288197022899732077069)
  ·
    refine ⟨1145733073883587399528901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3055288197022899732077069 1145733073883587399528901)
    ·
      refine ⟨214824951353172637411669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1145733073883587399528901 214824951353172637411669)
      ·
        refine ⟨629369974667497961167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 214824951353172637411669 629369974667497961167)
        ·
          rfl

theorem cell20_335074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 10].length) (baseStart_335074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335074 prefixEnd_335074 := by exact prefixLift 335074
  have htrace : WordTrace (prefixWord ++ tailWord_335074) baseStart_335074 baseEnd_335074 := by
    simpa [prefixWord, tailWord_335074, baseEnd_335074] using wordTrace_append hprefix tailTrace_335074
  have hstable : (prefixWord ++ tailWord_335074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335074).length < 2 ^ (prefixWord ++ tailWord_335074).sum := by decide
  have hdescent : baseEnd_335074 < baseStart_335074 := by decide
  rcases family_descends (prefixWord ++ tailWord_335074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335084 : List Nat := [2, 2, 1, 1, 2, 4, 4, 2, 2]
def baseStart_335084 : Nat := 118140960795 + 335084 * 2 ^ 59
def prefixEnd_335084 : Nat := 4983230072969 + 3 ^ 40 * 335084 * 2
def baseEnd_335084 : Nat := 152941468116686414230207

theorem tailTrace_335084 : CollatzResearch.WordTrace tailWord_335084 prefixEnd_335084 152941468116686414230207 := by
  unfold tailWord_335084
  simp only [CollatzResearch.WordTrace]
  refine ⟨6110758759027685318086153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8147678345370247090781537 6110758759027685318086153)
  ·
    refine ⟨4583069069270763988564615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6110758759027685318086153 4583069069270763988564615)
    ·
      refine ⟨6874603603906145982846923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4583069069270763988564615 6874603603906145982846923)
      ·
        refine ⟨10311905405859218974270385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6874603603906145982846923 10311905405859218974270385)
        ·
          refine ⟨7733929054394414230702789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10311905405859218974270385 7733929054394414230702789)
          ·
            refine ⟨1450111697698952668256773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7733929054394414230702789 1450111697698952668256773)
            ·
              refine ⟨271895943318553625298145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1450111697698952668256773 271895943318553625298145)
              ·
                refine ⟨203921957488915218973609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271895943318553625298145 203921957488915218973609)
                ·
                  refine ⟨152941468116686414230207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203921957488915218973609 152941468116686414230207)
                  ·
                    rfl

theorem cell20_335084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_335084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335084 prefixEnd_335084 := by exact prefixLift 335084
  have htrace : WordTrace (prefixWord ++ tailWord_335084) baseStart_335084 baseEnd_335084 := by
    simpa [prefixWord, tailWord_335084, baseEnd_335084] using wordTrace_append hprefix tailTrace_335084
  have hstable : (prefixWord ++ tailWord_335084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335084).length < 2 ^ (prefixWord ++ tailWord_335084).sum := by decide
  have hdescent : baseEnd_335084 < baseStart_335084 := by decide
  rcases family_descends (prefixWord ++ tailWord_335084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335164 : List Nat := [2, 2, 2, 2, 1, 3, 2, 2, 4]
def baseStart_335164 : Nat := 118140960795 + 335164 * 2 ^ 59
def prefixEnd_335164 : Nat := 4983230072969 + 3 ^ 40 * 335164 * 2
def baseEnd_335164 : Nat := 152977982296561691563213

theorem tailTrace_335164 : CollatzResearch.WordTrace tailWord_335164 prefixEnd_335164 152977982296561691563213 := by
  unfold tailWord_335164
  simp only [CollatzResearch.WordTrace]
  refine ⟨6112217678882772149542273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8149623571843696199389697 6112217678882772149542273)
  ·
    refine ⟨4584163259162079112156705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6112217678882772149542273 4584163259162079112156705)
    ·
      refine ⟨3438122444371559334117529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4584163259162079112156705 3438122444371559334117529)
      ·
        refine ⟨2578591833278669500588147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3438122444371559334117529 2578591833278669500588147)
        ·
          refine ⟨3867887749918004250882221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2578591833278669500588147 3867887749918004250882221)
          ·
            refine ⟨1450457906219251594080833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3867887749918004250882221 1450457906219251594080833)
            ·
              refine ⟨1087843429664438695560625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1450457906219251594080833 1087843429664438695560625)
              ·
                refine ⟨815882572248329021670469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1087843429664438695560625 815882572248329021670469)
                ·
                  refine ⟨152977982296561691563213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 815882572248329021670469 152977982296561691563213)
                  ·
                    rfl

theorem cell20_335164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_335164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335164 prefixEnd_335164 := by exact prefixLift 335164
  have htrace : WordTrace (prefixWord ++ tailWord_335164) baseStart_335164 baseEnd_335164 := by
    simpa [prefixWord, tailWord_335164, baseEnd_335164] using wordTrace_append hprefix tailTrace_335164
  have hstable : (prefixWord ++ tailWord_335164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335164).length < 2 ^ (prefixWord ++ tailWord_335164).sum := by decide
  have hdescent : baseEnd_335164 < baseStart_335164 := by decide
  rcases family_descends (prefixWord ++ tailWord_335164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335190 : List Nat := [5, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_335190 : Nat := 118140960795 + 335190 * 2 ^ 59
def prefixEnd_335190 : Nat := 4983230072969 + 3 ^ 40 * 335190 * 2
def baseEnd_335190 : Nat := 152989849405021156696441

theorem tailTrace_335190 : CollatzResearch.WordTrace tailWord_335190 prefixEnd_335190 152989849405021156696441 := by
  unfold tailWord_335190
  simp only [CollatzResearch.WordTrace]
  refine ⟨764086478479459421220689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8150255770447567159687349 764086478479459421220689)
  ·
    refine ⟨573064858859594565915517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 764086478479459421220689 573064858859594565915517)
    ·
      refine ⟨214899322072347962218319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 573064858859594565915517 214899322072347962218319)
      ·
        refine ⟨322348983108521943327479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214899322072347962218319 322348983108521943327479)
        ·
          refine ⟨483523474662782914991219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322348983108521943327479 483523474662782914991219)
          ·
            refine ⟨725285211994174372486829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483523474662782914991219 725285211994174372486829)
            ·
              refine ⟨271981954497815389682561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 725285211994174372486829 271981954497815389682561)
              ·
                refine ⟨203986465873361542261921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271981954497815389682561 203986465873361542261921)
                ·
                  refine ⟨152989849405021156696441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203986465873361542261921 152989849405021156696441)
                  ·
                    rfl

theorem cell20_335190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_335190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335190 prefixEnd_335190 := by exact prefixLift 335190
  have htrace : WordTrace (prefixWord ++ tailWord_335190) baseStart_335190 baseEnd_335190 := by
    simpa [prefixWord, tailWord_335190, baseEnd_335190] using wordTrace_append hprefix tailTrace_335190
  have hstable : (prefixWord ++ tailWord_335190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335190).length < 2 ^ (prefixWord ++ tailWord_335190).sum := by decide
  have hdescent : baseEnd_335190 < baseStart_335190 := by decide
  rcases family_descends (prefixWord ++ tailWord_335190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335208 : List Nat := [2, 1, 4, 2, 4, 1, 2, 1, 3]
def baseStart_335208 : Nat := 118140960795 + 335208 * 2 ^ 59
def prefixEnd_335208 : Nat := 4983230072969 + 3 ^ 40 * 335208 * 2
def baseEnd_335208 : Nat := 152998065095493094096367

theorem tailTrace_335208 : CollatzResearch.WordTrace tailWord_335208 prefixEnd_335208 152998065095493094096367 := by
  unfold tailWord_335208
  simp only [CollatzResearch.WordTrace]
  refine ⟨6113020084803069906843139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8150693446404093209124185 6113020084803069906843139)
  ·
    refine ⟨9169530127204604860264709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6113020084803069906843139 9169530127204604860264709)
    ·
      refine ⟨1719286898850863411299633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9169530127204604860264709 1719286898850863411299633)
      ·
        refine ⟨1289465174138147558474725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1719286898850863411299633 1289465174138147558474725)
        ·
          refine ⟨241774720150902667214011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1289465174138147558474725 241774720150902667214011)
          ·
            refine ⟨362662080226354000821017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241774720150902667214011 362662080226354000821017)
            ·
              refine ⟨271996560169765500615763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362662080226354000821017 271996560169765500615763)
              ·
                refine ⟨407994840254648250923645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271996560169765500615763 407994840254648250923645)
                ·
                  refine ⟨152998065095493094096367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 407994840254648250923645 152998065095493094096367)
                  ·
                    rfl

theorem cell20_335208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 3].length) (baseStart_335208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335208 prefixEnd_335208 := by exact prefixLift 335208
  have htrace : WordTrace (prefixWord ++ tailWord_335208) baseStart_335208 baseEnd_335208 := by
    simpa [prefixWord, tailWord_335208, baseEnd_335208] using wordTrace_append hprefix tailTrace_335208
  have hstable : (prefixWord ++ tailWord_335208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335208).length < 2 ^ (prefixWord ++ tailWord_335208).sum := by decide
  have hdescent : baseEnd_335208 < baseStart_335208 := by decide
  rcases family_descends (prefixWord ++ tailWord_335208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335212 : List Nat := [2, 2, 1, 1, 5, 1, 4, 1, 3]
def baseStart_335212 : Nat := 118140960795 + 335212 * 2 ^ 59
def prefixEnd_335212 : Nat := 4983230072969 + 3 ^ 40 * 335212 * 2
def baseEnd_335212 : Nat := 152999890804486857963017

theorem tailTrace_335212 : CollatzResearch.WordTrace tailWord_335212 prefixEnd_335212 152999890804486857963017 := by
  unfold tailWord_335212
  simp only [CollatzResearch.WordTrace]
  refine ⟨6113093030795824248415945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8150790707727765664554593 6113093030795824248415945)
  ·
    refine ⟨4584819773096868186311959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6113093030795824248415945 4584819773096868186311959)
    ·
      refine ⟨6877229659645302279467939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4584819773096868186311959 6877229659645302279467939)
      ·
        refine ⟨10315844489467953419201909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6877229659645302279467939 10315844489467953419201909)
        ·
          refine ⟨967110420887620633050179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10315844489467953419201909 967110420887620633050179)
          ·
            refine ⟨1450665631331430949575269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967110420887620633050179 1450665631331430949575269)
            ·
              refine ⟨271999805874643303045363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1450665631331430949575269 271999805874643303045363)
              ·
                refine ⟨407999708811964954568045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271999805874643303045363 407999708811964954568045)
                ·
                  refine ⟨152999890804486857963017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 407999708811964954568045 152999890804486857963017)
                  ·
                    rfl

theorem cell20_335212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_335212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335212 prefixEnd_335212 := by exact prefixLift 335212
  have htrace : WordTrace (prefixWord ++ tailWord_335212) baseStart_335212 baseEnd_335212 := by
    simpa [prefixWord, tailWord_335212, baseEnd_335212] using wordTrace_append hprefix tailTrace_335212
  have hstable : (prefixWord ++ tailWord_335212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335212).length < 2 ^ (prefixWord ++ tailWord_335212).sum := by decide
  have hdescent : baseEnd_335212 < baseStart_335212 := by decide
  rcases family_descends (prefixWord ++ tailWord_335212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335223 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 6]
def baseStart_335223 : Nat := 118140960795 + 335223 * 2 ^ 59
def prefixEnd_335223 : Nat := 4983230072969 + 3 ^ 40 * 335223 * 2
def baseEnd_335223 : Nat := 153004911504219708596305

theorem tailTrace_335223 : CollatzResearch.WordTrace tailWord_335223 prefixEnd_335223 153004911504219708596305 := by
  unfold tailWord_335223
  simp only [CollatzResearch.WordTrace]
  refine ⟨12226587264551797375482323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8151058176367864916988215 12226587264551797375482323)
  ·
    refine ⟨18339880896827696063223485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12226587264551797375482323 18339880896827696063223485)
    ·
      refine ⟨6877455336310386023708807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18339880896827696063223485 6877455336310386023708807)
      ·
        refine ⟨10316183004465579035563211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6877455336310386023708807 10316183004465579035563211)
        ·
          refine ⟨15474274506698368553344817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10316183004465579035563211 15474274506698368553344817)
          ·
            refine ⟨11605705880023776415008613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15474274506698368553344817 11605705880023776415008613)
            ·
              refine ⟨2176069852504458077814115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11605705880023776415008613 2176069852504458077814115)
              ·
                refine ⟨3264104778756687116721173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2176069852504458077814115 3264104778756687116721173)
                ·
                  refine ⟨153004911504219708596305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3264104778756687116721173 153004911504219708596305)
                  ·
                    rfl

theorem cell20_335223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_335223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335223 prefixEnd_335223 := by exact prefixLift 335223
  have htrace : WordTrace (prefixWord ++ tailWord_335223) baseStart_335223 baseEnd_335223 := by
    simpa [prefixWord, tailWord_335223, baseEnd_335223] using wordTrace_append hprefix tailTrace_335223
  have hstable : (prefixWord ++ tailWord_335223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335223).length < 2 ^ (prefixWord ++ tailWord_335223).sum := by decide
  have hdescent : baseEnd_335223 < baseStart_335223 := by decide
  rcases family_descends (prefixWord ++ tailWord_335223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335257 : List Nat := [1, 2, 1, 2, 1, 6, 1, 4, 2]
def baseStart_335257 : Nat := 118140960795 + 335257 * 2 ^ 59
def prefixEnd_335257 : Nat := 4983230072969 + 3 ^ 40 * 335257 * 2
def baseEnd_335257 : Nat := 153020430030666701462833

theorem tailTrace_335257 : CollatzResearch.WordTrace tailWord_335257 prefixEnd_335257 153020430030666701462833 := by
  unfold tailWord_335257
  simp only [CollatzResearch.WordTrace]
  refine ⟨12227827346428621182220025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8151884897619080788146683 12227827346428621182220025)
  ·
    refine ⟨9170870509821465886665019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12227827346428621182220025 9170870509821465886665019)
    ·
      refine ⟨13756305764732198829997529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9170870509821465886665019 13756305764732198829997529)
      ·
        refine ⟨10317229323549149122498147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13756305764732198829997529 10317229323549149122498147)
        ·
          refine ⟨15475843985323723683747221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10317229323549149122498147 15475843985323723683747221)
          ·
            refine ⟨725430186812049547675651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15475843985323723683747221 725430186812049547675651)
            ·
              refine ⟨1088145280218074321513477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 725430186812049547675651 1088145280218074321513477)
              ·
                refine ⟨204027240040888935283777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1088145280218074321513477 204027240040888935283777)
                ·
                  refine ⟨153020430030666701462833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204027240040888935283777 153020430030666701462833)
                  ·
                    rfl

theorem cell20_335257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 2].length) (baseStart_335257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335257 prefixEnd_335257 := by exact prefixLift 335257
  have htrace : WordTrace (prefixWord ++ tailWord_335257) baseStart_335257 baseEnd_335257 := by
    simpa [prefixWord, tailWord_335257, baseEnd_335257] using wordTrace_append hprefix tailTrace_335257
  have hstable : (prefixWord ++ tailWord_335257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335257).length < 2 ^ (prefixWord ++ tailWord_335257).sum := by decide
  have hdescent : baseEnd_335257 < baseStart_335257 := by decide
  rcases family_descends (prefixWord ++ tailWord_335257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335260 : List Nat := [2, 2, 3, 4, 2, 1, 1, 5]
def baseStart_335260 : Nat := 118140960795 + 335260 * 2 ^ 59
def prefixEnd_335260 : Nat := 4983230072969 + 3 ^ 40 * 335260 * 2
def baseEnd_335260 : Nat := 51007266437470674787607

theorem tailTrace_335260 : CollatzResearch.WordTrace tailWord_335260 prefixEnd_335260 51007266437470674787607 := by
  unfold tailWord_335260
  simp only [CollatzResearch.WordTrace]
  refine ⟨6113968382708876347289617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8151957843611835129719489 6113968382708876347289617)
  ·
    refine ⟨4585476287031657260467213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6113968382708876347289617 4585476287031657260467213)
    ·
      refine ⟨1719553607636871472675205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4585476287031657260467213 1719553607636871472675205)
      ·
        refine ⟨322416301431913401126601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1719553607636871472675205 322416301431913401126601)
        ·
          refine ⟨241812226073935050844951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322416301431913401126601 241812226073935050844951)
          ·
            refine ⟨362718339110902576267427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241812226073935050844951 362718339110902576267427)
            ·
              refine ⟨544077508666353864401141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362718339110902576267427 544077508666353864401141)
              ·
                refine ⟨51007266437470674787607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 544077508666353864401141 51007266437470674787607)
                ·
                  rfl

theorem cell20_335260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 5].length) (baseStart_335260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335260 prefixEnd_335260 := by exact prefixLift 335260
  have htrace : WordTrace (prefixWord ++ tailWord_335260) baseStart_335260 baseEnd_335260 := by
    simpa [prefixWord, tailWord_335260, baseEnd_335260] using wordTrace_append hprefix tailTrace_335260
  have hstable : (prefixWord ++ tailWord_335260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335260).length < 2 ^ (prefixWord ++ tailWord_335260).sum := by decide
  have hdescent : baseEnd_335260 < baseStart_335260 := by decide
  rcases family_descends (prefixWord ++ tailWord_335260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335271 : List Nat := [1, 1, 6, 1, 1, 1, 1, 5, 3]
def baseStart_335271 : Nat := 118140960795 + 335271 * 2 ^ 59
def prefixEnd_335271 : Nat := 4983230072969 + 3 ^ 40 * 335271 * 2
def baseEnd_335271 : Nat := 153026820012144874996109

theorem tailTrace_335271 : CollatzResearch.WordTrace tailWord_335271 prefixEnd_335271 153026820012144874996109 := by
  unfold tailWord_335271
  simp only [CollatzResearch.WordTrace]
  refine ⟨12228337968377901573229667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8152225312251934382153111 12228337968377901573229667)
  ·
    refine ⟨18342506952566852359844501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12228337968377901573229667 18342506952566852359844501)
    ·
      refine ⟨859805013401571204367711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18342506952566852359844501 859805013401571204367711)
      ·
        refine ⟨1289707520102356806551567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 859805013401571204367711 1289707520102356806551567)
        ·
          refine ⟨1934561280153535209827351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1289707520102356806551567 1934561280153535209827351)
          ·
            refine ⟨2901841920230302814741027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1934561280153535209827351 2901841920230302814741027)
            ·
              refine ⟨4352762880345454222111541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2901841920230302814741027 4352762880345454222111541)
              ·
                refine ⟨408071520032386333322957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4352762880345454222111541 408071520032386333322957)
                ·
                  refine ⟨153026820012144874996109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 408071520032386333322957 153026820012144874996109)
                  ·
                    rfl

theorem cell20_335271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 3].length) (baseStart_335271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335271 prefixEnd_335271 := by exact prefixLift 335271
  have htrace : WordTrace (prefixWord ++ tailWord_335271) baseStart_335271 baseEnd_335271 := by
    simpa [prefixWord, tailWord_335271, baseEnd_335271] using wordTrace_append hprefix tailTrace_335271
  have hstable : (prefixWord ++ tailWord_335271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335271).length < 2 ^ (prefixWord ++ tailWord_335271).sum := by decide
  have hdescent : baseEnd_335271 < baseStart_335271 := by decide
  rcases family_descends (prefixWord ++ tailWord_335271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335350 : List Nat := [5, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_335350 : Nat := 118140960795 + 335350 * 2 ^ 59
def prefixEnd_335350 : Nat := 4983230072969 + 3 ^ 40 * 335350 * 2
def baseEnd_335350 : Nat := 153062877764771711362453

theorem tailTrace_335350 : CollatzResearch.WordTrace tailWord_335350 prefixEnd_335350 153062877764771711362453 := by
  unfold tailWord_335350
  simp only [CollatzResearch.WordTrace]
  refine ⟨764451208443231129084719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8154146223394465376903669 764451208443231129084719)
  ·
    refine ⟨1146676812664846693627079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 764451208443231129084719 1146676812664846693627079)
    ·
      refine ⟨1720015218997270040440619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1146676812664846693627079 1720015218997270040440619)
      ·
        refine ⟨2580022828495905060660929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1720015218997270040440619 2580022828495905060660929)
        ·
          refine ⟨1935017121371928795495697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2580022828495905060660929 1935017121371928795495697)
          ·
            refine ⟨1451262841028946596621773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1935017121371928795495697 1451262841028946596621773)
            ·
              refine ⟨544223565385854973733165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1451262841028946596621773 544223565385854973733165)
              ·
                refine ⟨204083837019695615149937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 544223565385854973733165 204083837019695615149937)
                ·
                  refine ⟨153062877764771711362453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204083837019695615149937 153062877764771711362453)
                  ·
                    rfl

theorem cell20_335350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_335350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335350 prefixEnd_335350 := by exact prefixLift 335350
  have htrace : WordTrace (prefixWord ++ tailWord_335350) baseStart_335350 baseEnd_335350 := by
    simpa [prefixWord, tailWord_335350, baseEnd_335350] using wordTrace_append hprefix tailTrace_335350
  have hstable : (prefixWord ++ tailWord_335350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335350).length < 2 ^ (prefixWord ++ tailWord_335350).sum := by decide
  have hdescent : baseEnd_335350 < baseStart_335350 := by decide
  rcases family_descends (prefixWord ++ tailWord_335350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335368 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 5]
def baseStart_335368 : Nat := 118140960795 + 335368 * 2 ^ 59
def prefixEnd_335368 : Nat := 4983230072969 + 3 ^ 40 * 335368 * 2
def baseEnd_335368 : Nat := 153071093455243648762379

theorem tailTrace_335368 : CollatzResearch.WordTrace tailWord_335368 prefixEnd_335368 153071093455243648762379 := by
  unfold tailWord_335368
  simp only [CollatzResearch.WordTrace]
  refine ⟨6115937924513243569755379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8154583899350991426340505 6115937924513243569755379)
  ·
    refine ⟨9173906886769865354633069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6115937924513243569755379 9173906886769865354633069)
    ·
      refine ⟨3440215082538699507987401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9173906886769865354633069 3440215082538699507987401)
      ·
        refine ⟨2580161311904024630990551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3440215082538699507987401 2580161311904024630990551)
        ·
          refine ⟨3870241967856036946485827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2580161311904024630990551 3870241967856036946485827)
          ·
            refine ⟨5805362951784055419728741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3870241967856036946485827 5805362951784055419728741)
            ·
              refine ⟨1088505553459510391199139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5805362951784055419728741 1088505553459510391199139)
              ·
                refine ⟨1632758330189265586798709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1088505553459510391199139 1632758330189265586798709)
                ·
                  refine ⟨153071093455243648762379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1632758330189265586798709 153071093455243648762379)
                  ·
                    rfl

theorem cell20_335368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_335368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335368 prefixEnd_335368 := by exact prefixLift 335368
  have htrace : WordTrace (prefixWord ++ tailWord_335368) baseStart_335368 baseEnd_335368 := by
    simpa [prefixWord, tailWord_335368, baseEnd_335368] using wordTrace_append hprefix tailTrace_335368
  have hstable : (prefixWord ++ tailWord_335368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335368).length < 2 ^ (prefixWord ++ tailWord_335368).sum := by decide
  have hdescent : baseEnd_335368 < baseStart_335368 := by decide
  rcases family_descends (prefixWord ++ tailWord_335368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335371 : List Nat := [1, 1, 1, 1, 8, 2, 1, 1, 4]
def baseStart_335371 : Nat := 118140960795 + 335371 * 2 ^ 59
def prefixEnd_335371 : Nat := 4983230072969 + 3 ^ 40 * 335371 * 2
def baseEnd_335371 : Nat := 153072462736988971662367

theorem tailTrace_335371 : CollatzResearch.WordTrace tailWord_335371 prefixEnd_335371 153072462736988971662367 := by
  unfold tailWord_335371
  simp only [CollatzResearch.WordTrace]
  refine ⟨12231985268015618651869967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8154656845343745767913311 12231985268015618651869967)
  ·
    refine ⟨18347977902023427977804951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12231985268015618651869967 18347977902023427977804951)
    ·
      refine ⟨27521966853035141966707427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18347977902023427977804951 27521966853035141966707427)
      ·
        refine ⟨41282950279552712950061141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27521966853035141966707427 41282950279552712950061141)
        ·
          refine ⟨483784573588508354883529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 41282950279552712950061141 483784573588508354883529)
          ·
            refine ⟨362838430191381266162647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 483784573588508354883529 362838430191381266162647)
            ·
              refine ⟨544257645287071899243971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362838430191381266162647 544257645287071899243971)
              ·
                refine ⟨816386467930607848865957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 544257645287071899243971 816386467930607848865957)
                ·
                  refine ⟨153072462736988971662367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 816386467930607848865957 153072462736988971662367)
                  ·
                    rfl

theorem cell20_335371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 4].length) (baseStart_335371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335371 prefixEnd_335371 := by exact prefixLift 335371
  have htrace : WordTrace (prefixWord ++ tailWord_335371) baseStart_335371 baseEnd_335371 := by
    simpa [prefixWord, tailWord_335371, baseEnd_335371] using wordTrace_append hprefix tailTrace_335371
  have hstable : (prefixWord ++ tailWord_335371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335371).length < 2 ^ (prefixWord ++ tailWord_335371).sum := by decide
  have hdescent : baseEnd_335371 < baseStart_335371 := by decide
  rcases family_descends (prefixWord ++ tailWord_335371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335420 : List Nat := [2, 2, 2, 2, 12]
def baseStart_335420 : Nat := 118140960795 + 335420 * 2 ^ 59
def prefixEnd_335420 : Nat := 4983230072969 + 3 ^ 40 * 335420 * 2
def baseEnd_335420 : Nat := 1890059600890896037393

theorem tailTrace_335420 : CollatzResearch.WordTrace tailWord_335420 prefixEnd_335420 1890059600890896037393 := by
  unfold tailWord_335420
  simp only [CollatzResearch.WordTrace]
  refine ⟨6116886222419050010201857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8155848296558733346935809 6116886222419050010201857)
  ·
    refine ⟨4587664666814287507651393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6116886222419050010201857 4587664666814287507651393)
    ·
      refine ⟨3440748500110715630738545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4587664666814287507651393 3440748500110715630738545)
      ·
        refine ⟨2580561375083036723053909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3440748500110715630738545 2580561375083036723053909)
        ·
          refine ⟨1890059600890896037393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2580561375083036723053909 1890059600890896037393)
          ·
            rfl

theorem cell20_335420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 12].length) (baseStart_335420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335420 prefixEnd_335420 := by exact prefixLift 335420
  have htrace : WordTrace (prefixWord ++ tailWord_335420) baseStart_335420 baseEnd_335420 := by
    simpa [prefixWord, tailWord_335420, baseEnd_335420] using wordTrace_append hprefix tailTrace_335420
  have hstable : (prefixWord ++ tailWord_335420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335420).length < 2 ^ (prefixWord ++ tailWord_335420).sum := by decide
  have hdescent : baseEnd_335420 < baseStart_335420 := by decide
  rcases family_descends (prefixWord ++ tailWord_335420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335423 : List Nat := [1, 1, 2, 2, 3, 4, 2, 2, 3]
def baseStart_335423 : Nat := 118140960795 + 335423 * 2 ^ 59
def prefixEnd_335423 : Nat := 4983230072969 + 3 ^ 40 * 335423 * 2
def baseEnd_335423 : Nat := 153096196953907901928821

theorem tailTrace_335423 : CollatzResearch.WordTrace tailWord_335423 prefixEnd_335423 153096196953907901928821 := by
  unfold tailWord_335423
  simp only [CollatzResearch.WordTrace]
  refine ⟨12233881863827231532762923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8155921242551487688508615 12233881863827231532762923)
  ·
    refine ⟨18350822795740847299144385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12233881863827231532762923 18350822795740847299144385)
    ·
      refine ⟨13763117096805635474358289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18350822795740847299144385 13763117096805635474358289)
      ·
        refine ⟨10322337822604226605768717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13763117096805635474358289 10322337822604226605768717)
        ·
          refine ⟨3870876683476584977163269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10322337822604226605768717 3870876683476584977163269)
          ·
            refine ⟨725789378151859683218113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3870876683476584977163269 725789378151859683218113)
            ·
              refine ⟨544342033613894762413585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 725789378151859683218113 544342033613894762413585)
              ·
                refine ⟨408256525210421071810189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 544342033613894762413585 408256525210421071810189)
                ·
                  refine ⟨153096196953907901928821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 408256525210421071810189 153096196953907901928821)
                  ·
                    rfl

theorem cell20_335423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 3].length) (baseStart_335423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335423 prefixEnd_335423 := by exact prefixLift 335423
  have htrace : WordTrace (prefixWord ++ tailWord_335423) baseStart_335423 baseEnd_335423 := by
    simpa [prefixWord, tailWord_335423, baseEnd_335423] using wordTrace_append hprefix tailTrace_335423
  have hstable : (prefixWord ++ tailWord_335423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335423).length < 2 ^ (prefixWord ++ tailWord_335423).sum := by decide
  have hdescent : baseEnd_335423 < baseStart_335423 := by decide
  rcases family_descends (prefixWord ++ tailWord_335423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335464 : List Nat := [2, 1, 4, 3, 1, 2, 2, 3, 2]
def baseStart_335464 : Nat := 118140960795 + 335464 * 2 ^ 59
def prefixEnd_335464 : Nat := 4983230072969 + 3 ^ 40 * 335464 * 2
def baseEnd_335464 : Nat := 153114910471093981561987

theorem tailTrace_335464 : CollatzResearch.WordTrace tailWord_335464 prefixEnd_335464 153114910471093981561987 := by
  unfold tailWord_335464
  simp only [CollatzResearch.WordTrace]
  refine ⟨6117688628339347767502723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8156918171119130356670297 6117688628339347767502723)
  ·
    refine ⟨9176532942509021651254085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6117688628339347767502723 9176532942509021651254085)
    ·
      refine ⟨1720599926720441559610141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9176532942509021651254085 1720599926720441559610141)
      ·
        refine ⟨645224972520165584853803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1720599926720441559610141 645224972520165584853803)
        ·
          refine ⟨967837458780248377280705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 645224972520165584853803 967837458780248377280705)
          ·
            refine ⟨725878094085186282960529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 967837458780248377280705 725878094085186282960529)
            ·
              refine ⟨544408570563889712220397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 725878094085186282960529 544408570563889712220397)
              ·
                refine ⟨204153213961458642082649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 544408570563889712220397 204153213961458642082649)
                ·
                  refine ⟨153114910471093981561987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204153213961458642082649 153114910471093981561987)
                  ·
                    rfl

theorem cell20_335464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 2].length) (baseStart_335464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335464 prefixEnd_335464 := by exact prefixLift 335464
  have htrace : WordTrace (prefixWord ++ tailWord_335464) baseStart_335464 baseEnd_335464 := by
    simpa [prefixWord, tailWord_335464, baseEnd_335464] using wordTrace_append hprefix tailTrace_335464
  have hstable : (prefixWord ++ tailWord_335464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335464).length < 2 ^ (prefixWord ++ tailWord_335464).sum := by decide
  have hdescent : baseEnd_335464 < baseStart_335464 := by decide
  rcases family_descends (prefixWord ++ tailWord_335464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335478 : List Nat := [5, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_335478 : Nat := 118140960795 + 335478 * 2 ^ 59
def prefixEnd_335478 : Nat := 4983230072969 + 3 ^ 40 * 335478 * 2
def baseEnd_335478 : Nat := 153121300452572155095263

theorem tailTrace_335478 : CollatzResearch.WordTrace tailWord_335478 prefixEnd_335478 153121300452572155095263 := by
  unfold tailWord_335478
  simp only [CollatzResearch.WordTrace]
  refine ⟨764742992414248495375943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8157258585751983950676725 764742992414248495375943)
  ·
    refine ⟨1147114488621372743063915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 764742992414248495375943 1147114488621372743063915)
    ·
      refine ⟨1720671732932059114595873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1147114488621372743063915 1720671732932059114595873)
      ·
        refine ⟨1290503799699044335946905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1720671732932059114595873 1290503799699044335946905)
        ·
          refine ⟨967877849774283251960179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1290503799699044335946905 967877849774283251960179)
          ·
            refine ⟨1451816774661424877940269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967877849774283251960179 1451816774661424877940269)
            ·
              refine ⟨544431290498034329227601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1451816774661424877940269 544431290498034329227601)
              ·
                refine ⟨408323467873525746920701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 544431290498034329227601 408323467873525746920701)
                ·
                  refine ⟨153121300452572155095263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 408323467873525746920701 153121300452572155095263)
                  ·
                    rfl

theorem cell20_335478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_335478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335478 prefixEnd_335478 := by exact prefixLift 335478
  have htrace : WordTrace (prefixWord ++ tailWord_335478) baseStart_335478 baseEnd_335478 := by
    simpa [prefixWord, tailWord_335478, baseEnd_335478] using wordTrace_append hprefix tailTrace_335478
  have hstable : (prefixWord ++ tailWord_335478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335478).length < 2 ^ (prefixWord ++ tailWord_335478).sum := by decide
  have hdescent : baseEnd_335478 < baseStart_335478 := by decide
  rcases family_descends (prefixWord ++ tailWord_335478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335482 : List Nat := [3, 1, 1, 1, 1, 1, 1, 8, 3]
def baseStart_335482 : Nat := 118140960795 + 335482 * 2 ^ 59
def prefixEnd_335482 : Nat := 4983230072969 + 3 ^ 40 * 335482 * 2
def baseEnd_335482 : Nat := 153123126161565918961913

theorem tailTrace_335482 : CollatzResearch.WordTrace tailWord_335482 prefixEnd_335482 153123126161565918961913 := by
  unfold tailWord_335482
  simp only [CollatzResearch.WordTrace]
  refine ⟨3059008442653371152290175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8157355847075656406107133 3059008442653371152290175)
  ·
    refine ⟨4588512663980056728435263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3059008442653371152290175 4588512663980056728435263)
    ·
      refine ⟨6882768995970085092652895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4588512663980056728435263 6882768995970085092652895)
      ·
        refine ⟨10324153493955127638979343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6882768995970085092652895 10324153493955127638979343)
        ·
          refine ⟨15486230240932691458469015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10324153493955127638979343 15486230240932691458469015)
          ·
            refine ⟨23229345361399037187703523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15486230240932691458469015 23229345361399037187703523)
            ·
              refine ⟨34844018042098555781555285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23229345361399037187703523 34844018042098555781555285)
              ·
                refine ⟨408328336430842450565101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 34844018042098555781555285 408328336430842450565101)
                ·
                  refine ⟨153123126161565918961913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 408328336430842450565101 153123126161565918961913)
                  ·
                    rfl

theorem cell20_335482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_335482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335482 prefixEnd_335482 := by exact prefixLift 335482
  have htrace : WordTrace (prefixWord ++ tailWord_335482) baseStart_335482 baseEnd_335482 := by
    simpa [prefixWord, tailWord_335482, baseEnd_335482] using wordTrace_append hprefix tailTrace_335482
  have hstable : (prefixWord ++ tailWord_335482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335482).length < 2 ^ (prefixWord ++ tailWord_335482).sum := by decide
  have hdescent : baseEnd_335482 < baseStart_335482 := by decide
  rcases family_descends (prefixWord ++ tailWord_335482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335485 : List Nat := [1, 4, 1, 1, 4, 1, 2, 4, 2]
def baseStart_335485 : Nat := 118140960795 + 335485 * 2 ^ 59
def prefixEnd_335485 : Nat := 4983230072969 + 3 ^ 40 * 335485 * 2
def baseEnd_335485 : Nat := 153124495443311241861901

theorem tailTrace_335485 : CollatzResearch.WordTrace tailWord_335485 prefixEnd_335485 153124495443311241861901 := by
  unfold tailWord_335485
  simp only [CollatzResearch.WordTrace]
  refine ⟨12236143189602616121519909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8157428793068410747679939 12236143189602616121519909)
  ·
    refine ⟨2294276848050490522784983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12236143189602616121519909 2294276848050490522784983)
    ·
      refine ⟨3441415272075735784177475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2294276848050490522784983 3441415272075735784177475)
      ·
        refine ⟨5162122908113603676266213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3441415272075735784177475 5162122908113603676266213)
        ·
          refine ⟨967898045271300689299915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5162122908113603676266213 967898045271300689299915)
          ·
            refine ⟨1451847067906951033949873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967898045271300689299915 1451847067906951033949873)
            ·
              refine ⟨1088885300930213275462405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1451847067906951033949873 1088885300930213275462405)
              ·
                refine ⟨204165993924414989149201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1088885300930213275462405 204165993924414989149201)
                ·
                  refine ⟨153124495443311241861901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204165993924414989149201 153124495443311241861901)
                  ·
                    rfl

theorem cell20_335485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_335485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335485 prefixEnd_335485 := by exact prefixLift 335485
  have htrace : WordTrace (prefixWord ++ tailWord_335485) baseStart_335485 baseEnd_335485 := by
    simpa [prefixWord, tailWord_335485, baseEnd_335485] using wordTrace_append hprefix tailTrace_335485
  have hstable : (prefixWord ++ tailWord_335485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335485).length < 2 ^ (prefixWord ++ tailWord_335485).sum := by decide
  have hdescent : baseEnd_335485 < baseStart_335485 := by decide
  rcases family_descends (prefixWord ++ tailWord_335485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335499 : List Nat := [1, 1, 1, 1, 4, 1, 7, 1, 3]
def baseStart_335499 : Nat := 118140960795 + 335499 * 2 ^ 59
def prefixEnd_335499 : Nat := 4983230072969 + 3 ^ 40 * 335499 * 2
def baseEnd_335499 : Nat := 153130885424789415395177

theorem tailTrace_335499 : CollatzResearch.WordTrace tailWord_335499 prefixEnd_335499 153130885424789415395177 := by
  unfold tailWord_335499
  simp only [CollatzResearch.WordTrace]
  refine ⟨12236653811551896512529551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8157769207701264341686367 12236653811551896512529551)
  ·
    refine ⟨18354980717327844768794327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12236653811551896512529551 18354980717327844768794327)
    ·
      refine ⟨27532471075991767153191491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18354980717327844768794327 27532471075991767153191491)
      ·
        refine ⟨41298706613987650729787237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27532471075991767153191491 41298706613987650729787237)
        ·
          refine ⟨7743507490122684511835107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41298706613987650729787237 7743507490122684511835107)
          ·
            refine ⟨11615261235184026767752661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7743507490122684511835107 11615261235184026767752661)
            ·
              refine ⟨272232685199625627369203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11615261235184026767752661 272232685199625627369203)
              ·
                refine ⟨408349027799438441053805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272232685199625627369203 408349027799438441053805)
                ·
                  refine ⟨153130885424789415395177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 408349027799438441053805 153130885424789415395177)
                  ·
                    rfl

theorem cell20_335499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 3].length) (baseStart_335499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335499 prefixEnd_335499 := by exact prefixLift 335499
  have htrace : WordTrace (prefixWord ++ tailWord_335499) baseStart_335499 baseEnd_335499 := by
    simpa [prefixWord, tailWord_335499, baseEnd_335499] using wordTrace_append hprefix tailTrace_335499
  have hstable : (prefixWord ++ tailWord_335499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335499).length < 2 ^ (prefixWord ++ tailWord_335499).sum := by decide
  have hdescent : baseEnd_335499 < baseStart_335499 := by decide
  rcases family_descends (prefixWord ++ tailWord_335499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335503 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 9]
def baseStart_335503 : Nat := 118140960795 + 335503 * 2 ^ 59
def prefixEnd_335503 : Nat := 4983230072969 + 3 ^ 40 * 335503 * 2
def baseEnd_335503 : Nat := 153132711133783179261827

theorem tailTrace_335503 : CollatzResearch.WordTrace tailWord_335503 prefixEnd_335503 153132711133783179261827 := by
  unfold tailWord_335503
  simp only [CollatzResearch.WordTrace]
  refine ⟨12236799703537405195675163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8157866469024936797116775 12236799703537405195675163)
  ·
    refine ⟨18355199555306107793512745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12236799703537405195675163 18355199555306107793512745)
    ·
      refine ⟨13766399666479580845134559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18355199555306107793512745 13766399666479580845134559)
      ·
        refine ⟨20649599499719371267701839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13766399666479580845134559 20649599499719371267701839)
        ·
          refine ⟨30974399249579056901552759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20649599499719371267701839 30974399249579056901552759)
          ·
            refine ⟨46461598874368585352329139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30974399249579056901552759 46461598874368585352329139)
            ·
              refine ⟨69692398311552878028493709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46461598874368585352329139 69692398311552878028493709)
              ·
                refine ⟨26134649366832329260685141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69692398311552878028493709 26134649366832329260685141)
                ·
                  refine ⟨153132711133783179261827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26134649366832329260685141 153132711133783179261827)
                  ·
                    rfl

theorem cell20_335503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_335503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335503 prefixEnd_335503 := by exact prefixLift 335503
  have htrace : WordTrace (prefixWord ++ tailWord_335503) baseStart_335503 baseEnd_335503 := by
    simpa [prefixWord, tailWord_335503, baseEnd_335503] using wordTrace_append hprefix tailTrace_335503
  have hstable : (prefixWord ++ tailWord_335503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335503).length < 2 ^ (prefixWord ++ tailWord_335503).sum := by decide
  have hdescent : baseEnd_335503 < baseStart_335503 := by decide
  rcases family_descends (prefixWord ++ tailWord_335503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335519 : List Nat := [1, 1, 2, 7, 1, 2, 1, 3, 2]
def baseStart_335519 : Nat := 118140960795 + 335519 * 2 ^ 59
def prefixEnd_335519 : Nat := 4983230072969 + 3 ^ 40 * 335519 * 2
def baseEnd_335519 : Nat := 153140013969758234728429

theorem tailTrace_335519 : CollatzResearch.WordTrace tailWord_335519 prefixEnd_335519 153140013969758234728429 := by
  unfold tailWord_335519
  simp only [CollatzResearch.WordTrace]
  refine ⟨12237383271479439928257611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8158255514319626618838407 12237383271479439928257611)
  ·
    refine ⟨18356074907219159892386417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12237383271479439928257611 18356074907219159892386417)
    ·
      refine ⟨13767056180414369919289813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18356074907219159892386417 13767056180414369919289813)
      ·
        refine ⟨322665379228461794983355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 13767056180414369919289813 322665379228461794983355)
        ·
          refine ⟨483998068842692692475033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322665379228461794983355 483998068842692692475033)
          ·
            refine ⟨362998551632019519356275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 483998068842692692475033 362998551632019519356275)
            ·
              refine ⟨544497827448029279034413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362998551632019519356275 544497827448029279034413)
              ·
                refine ⟨204186685293010979637905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 544497827448029279034413 204186685293010979637905)
                ·
                  refine ⟨153140013969758234728429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204186685293010979637905 153140013969758234728429)
                  ·
                    rfl

theorem cell20_335519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 2].length) (baseStart_335519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335519 prefixEnd_335519 := by exact prefixLift 335519
  have htrace : WordTrace (prefixWord ++ tailWord_335519) baseStart_335519 baseEnd_335519 := by
    simpa [prefixWord, tailWord_335519, baseEnd_335519] using wordTrace_append hprefix tailTrace_335519
  have hstable : (prefixWord ++ tailWord_335519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335519).length < 2 ^ (prefixWord ++ tailWord_335519).sum := by decide
  have hdescent : baseEnd_335519 < baseStart_335519 := by decide
  rcases family_descends (prefixWord ++ tailWord_335519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335520 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 5]
def baseStart_335520 : Nat := 118140960795 + 335520 * 2 ^ 59
def prefixEnd_335520 : Nat := 4983230072969 + 3 ^ 40 * 335520 * 2
def baseEnd_335520 : Nat := 153140470397006675695091

theorem tailTrace_335520 : CollatzResearch.WordTrace tailWord_335520 prefixEnd_335520 153140470397006675695091 := by
  unfold tailWord_335520
  simp only [CollatzResearch.WordTrace]
  refine ⟨6118709872237908549522007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8158279829650544732696009 6118709872237908549522007)
  ·
    refine ⟨9178064808356862824283011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6118709872237908549522007 9178064808356862824283011)
    ·
      refine ⟨13767097212535294236424517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9178064808356862824283011 13767097212535294236424517)
      ·
        refine ⟨2581330727350367669329597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13767097212535294236424517 2581330727350367669329597)
        ·
          refine ⟨967999022756387875998599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2581330727350367669329597 967999022756387875998599)
          ·
            refine ⟨1451998534134581813997899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967999022756387875998599 1451998534134581813997899)
            ·
              refine ⟨2177997801201872720996849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1451998534134581813997899 2177997801201872720996849)
              ·
                refine ⟨1633498350901404540747637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2177997801201872720996849 1633498350901404540747637)
                ·
                  refine ⟨153140470397006675695091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1633498350901404540747637 153140470397006675695091)
                  ·
                    rfl

theorem cell20_335520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_335520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335520 prefixEnd_335520 := by exact prefixLift 335520
  have htrace : WordTrace (prefixWord ++ tailWord_335520) baseStart_335520 baseEnd_335520 := by
    simpa [prefixWord, tailWord_335520, baseEnd_335520] using wordTrace_append hprefix tailTrace_335520
  have hstable : (prefixWord ++ tailWord_335520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335520).length < 2 ^ (prefixWord ++ tailWord_335520).sum := by decide
  have hdescent : baseEnd_335520 < baseStart_335520 := by decide
  rcases family_descends (prefixWord ++ tailWord_335520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335544 : List Nat := [2, 1, 2, 1, 2, 1, 1, 8, 2]
def baseStart_335544 : Nat := 118140960795 + 335544 * 2 ^ 59
def prefixEnd_335544 : Nat := 4983230072969 + 3 ^ 40 * 335544 * 2
def baseEnd_335544 : Nat := 153151424650969258894993

theorem tailTrace_335544 : CollatzResearch.WordTrace tailWord_335544 prefixEnd_335544 153151424650969258894993 := by
  unfold tailWord_335544
  simp only [CollatzResearch.WordTrace]
  refine ⟨6119147548194434598958843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8158863397592579465278457 6119147548194434598958843)
  ·
    refine ⟨9178721322291651898438265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6119147548194434598958843 9178721322291651898438265)
    ·
      refine ⟨6884040991718738923828699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9178721322291651898438265 6884040991718738923828699)
      ·
        refine ⟨10326061487578108385743049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6884040991718738923828699 10326061487578108385743049)
        ·
          refine ⟨7744546115683581289307287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10326061487578108385743049 7744546115683581289307287)
          ·
            refine ⟨11616819173525371933960931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7744546115683581289307287 11616819173525371933960931)
            ·
              refine ⟨17425228760288057900941397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11616819173525371933960931 17425228760288057900941397)
              ·
                refine ⟨204201899534625678526657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 17425228760288057900941397 204201899534625678526657)
                ·
                  refine ⟨153151424650969258894993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204201899534625678526657 153151424650969258894993)
                  ·
                    rfl

theorem cell20_335544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 2].length) (baseStart_335544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335544 prefixEnd_335544 := by exact prefixLift 335544
  have htrace : WordTrace (prefixWord ++ tailWord_335544) baseStart_335544 baseEnd_335544 := by
    simpa [prefixWord, tailWord_335544, baseEnd_335544] using wordTrace_append hprefix tailTrace_335544
  have hstable : (prefixWord ++ tailWord_335544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335544).length < 2 ^ (prefixWord ++ tailWord_335544).sum := by decide
  have hdescent : baseEnd_335544 < baseStart_335544 := by decide
  rcases family_descends (prefixWord ++ tailWord_335544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335596 : List Nat := [2, 2, 1, 1, 2, 2, 3, 4, 3]
def baseStart_335596 : Nat := 118140960795 + 335596 * 2 ^ 59
def prefixEnd_335596 : Nat := 4983230072969 + 3 ^ 40 * 335596 * 2
def baseEnd_335596 : Nat := 153175158867888189161447

theorem tailTrace_335596 : CollatzResearch.WordTrace tailWord_335596 prefixEnd_335596 153175158867888189161447 := by
  unfold tailWord_335596
  simp only [CollatzResearch.WordTrace]
  refine ⟨6120095846100241039405321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8160127794800321385873761 6120095846100241039405321)
  ·
    refine ⟨4590071884575180779553991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6120095846100241039405321 4590071884575180779553991)
    ·
      refine ⟨6885107826862771169330987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4590071884575180779553991 6885107826862771169330987)
      ·
        refine ⟨10327661740294156753996481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6885107826862771169330987 10327661740294156753996481)
        ·
          refine ⟨7745746305220617565497361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10327661740294156753996481 7745746305220617565497361)
          ·
            refine ⟨5809309728915463174123021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7745746305220617565497361 5809309728915463174123021)
            ·
              refine ⟨2178491148343298690296133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5809309728915463174123021 2178491148343298690296133)
              ·
                refine ⟨408467090314368504430525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2178491148343298690296133 408467090314368504430525)
                ·
                  refine ⟨153175158867888189161447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 408467090314368504430525 153175158867888189161447)
                  ·
                    rfl

theorem cell20_335596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_335596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335596 prefixEnd_335596 := by exact prefixLift 335596
  have htrace : WordTrace (prefixWord ++ tailWord_335596) baseStart_335596 baseEnd_335596 := by
    simpa [prefixWord, tailWord_335596, baseEnd_335596] using wordTrace_append hprefix tailTrace_335596
  have hstable : (prefixWord ++ tailWord_335596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335596).length < 2 ^ (prefixWord ++ tailWord_335596).sum := by decide
  have hdescent : baseEnd_335596 < baseStart_335596 := by decide
  rcases family_descends (prefixWord ++ tailWord_335596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335606 : List Nat := [5, 1, 1, 1, 1, 5, 1, 5]
def baseStart_335606 : Nat := 118140960795 + 335606 * 2 ^ 59
def prefixEnd_335606 : Nat := 4983230072969 + 3 ^ 40 * 335606 * 2
def baseEnd_335606 : Nat := 51059907713457532942691

theorem tailTrace_335606 : CollatzResearch.WordTrace tailWord_335606 prefixEnd_335606 51059907713457532942691 := by
  unfold tailWord_335606
  simp only [CollatzResearch.WordTrace]
  refine ⟨765034776385265861667167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8160370948109502524449781 765034776385265861667167)
  ·
    refine ⟨1147552164577898792500751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 765034776385265861667167 1147552164577898792500751)
    ·
      refine ⟨1721328246866848188751127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1147552164577898792500751 1721328246866848188751127)
      ·
        refine ⟨2581992370300272283126691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1721328246866848188751127 2581992370300272283126691)
        ·
          refine ⟨3872988555450408424690037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2581992370300272283126691 3872988555450408424690037)
          ·
            refine ⟨363092677073475789814691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3872988555450408424690037 363092677073475789814691)
            ·
              refine ⟨544639015610213684722037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363092677073475789814691 544639015610213684722037)
              ·
                refine ⟨51059907713457532942691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 544639015610213684722037 51059907713457532942691)
                ·
                  rfl

theorem cell20_335606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_335606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335606 prefixEnd_335606 := by exact prefixLift 335606
  have htrace : WordTrace (prefixWord ++ tailWord_335606) baseStart_335606 baseEnd_335606 := by
    simpa [prefixWord, tailWord_335606, baseEnd_335606] using wordTrace_append hprefix tailTrace_335606
  have hstable : (prefixWord ++ tailWord_335606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335606).length < 2 ^ (prefixWord ++ tailWord_335606).sum := by decide
  have hdescent : baseEnd_335606 < baseStart_335606 := by decide
  rcases family_descends (prefixWord ++ tailWord_335606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335620 : List Nat := [2, 3, 2, 2, 1, 3, 1, 2, 4]
def baseStart_335620 : Nat := 118140960795 + 335620 * 2 ^ 59
def prefixEnd_335620 : Nat := 4983230072969 + 3 ^ 40 * 335620 * 2
def baseEnd_335620 : Nat := 153186113121850772361349

theorem tailTrace_335620 : CollatzResearch.WordTrace tailWord_335620 prefixEnd_335620 153186113121850772361349 := by
  unfold tailWord_335620
  simp only [CollatzResearch.WordTrace]
  refine ⟨6120533522056767088842157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8160711362742356118456209 6120533522056767088842157)
  ·
    refine ⟨2295200070771287658315809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6120533522056767088842157 2295200070771287658315809)
    ·
      refine ⟨1721400053078465743736857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2295200070771287658315809 1721400053078465743736857)
      ·
        refine ⟨1291050039808849307802643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1721400053078465743736857 1291050039808849307802643)
        ·
          refine ⟨1936575059713273961703965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1291050039808849307802643 1936575059713273961703965)
          ·
            refine ⟨726215647392477735638987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1936575059713273961703965 726215647392477735638987)
            ·
              refine ⟨1089323471088716603458481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726215647392477735638987 1089323471088716603458481)
              ·
                refine ⟨816992603316537452593861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1089323471088716603458481 816992603316537452593861)
                ·
                  refine ⟨153186113121850772361349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 816992603316537452593861 153186113121850772361349)
                  ·
                    rfl

theorem cell20_335620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_335620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335620 prefixEnd_335620 := by exact prefixLift 335620
  have htrace : WordTrace (prefixWord ++ tailWord_335620) baseStart_335620 baseEnd_335620 := by
    simpa [prefixWord, tailWord_335620, baseEnd_335620] using wordTrace_append hprefix tailTrace_335620
  have hstable : (prefixWord ++ tailWord_335620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335620).length < 2 ^ (prefixWord ++ tailWord_335620).sum := by decide
  have hdescent : baseEnd_335620 < baseStart_335620 := by decide
  rcases family_descends (prefixWord ++ tailWord_335620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335629 : List Nat := [1, 7, 2, 1, 1, 1, 2, 3, 2]
def baseStart_335629 : Nat := 118140960795 + 335629 * 2 ^ 59
def prefixEnd_335629 : Nat := 4983230072969 + 3 ^ 40 * 335629 * 2
def baseEnd_335629 : Nat := 153190220967086741061313

theorem tailTrace_335629 : CollatzResearch.WordTrace tailWord_335629 prefixEnd_335629 153190220967086741061313 := by
  unfold tailWord_335629
  simp only [CollatzResearch.WordTrace]
  refine ⟨12241395301080928714761941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8160930200720619143174627 12241395301080928714761941)
  ·
    refine ⟨286907702369084266752233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 12241395301080928714761941 286907702369084266752233)
    ·
      refine ⟨215180776776813200064175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286907702369084266752233 215180776776813200064175)
      ·
        refine ⟨322771165165219800096263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215180776776813200064175 322771165165219800096263)
        ·
          refine ⟨484156747747829700144395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322771165165219800096263 484156747747829700144395)
          ·
            refine ⟨726235121621744550216593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484156747747829700144395 726235121621744550216593)
            ·
              refine ⟨544676341216308412662445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 726235121621744550216593 544676341216308412662445)
              ·
                refine ⟨204253627956115654748417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 544676341216308412662445 204253627956115654748417)
                ·
                  refine ⟨153190220967086741061313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204253627956115654748417 153190220967086741061313)
                  ·
                    rfl

theorem cell20_335629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_335629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335629 prefixEnd_335629 := by exact prefixLift 335629
  have htrace : WordTrace (prefixWord ++ tailWord_335629) baseStart_335629 baseEnd_335629 := by
    simpa [prefixWord, tailWord_335629, baseEnd_335629] using wordTrace_append hprefix tailTrace_335629
  have hstable : (prefixWord ++ tailWord_335629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335629).length < 2 ^ (prefixWord ++ tailWord_335629).sum := by decide
  have hdescent : baseEnd_335629 < baseStart_335629 := by decide
  rcases family_descends (prefixWord ++ tailWord_335629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335637 : List Nat := [1, 3, 2, 1, 2, 4, 2, 3, 2]
def baseStart_335637 : Nat := 118140960795 + 335637 * 2 ^ 59
def prefixEnd_335637 : Nat := 4983230072969 + 3 ^ 40 * 335637 * 2
def baseEnd_335637 : Nat := 153193872385074268794613

theorem tailTrace_335637 : CollatzResearch.WordTrace tailWord_335637 prefixEnd_335637 153193872385074268794613 := by
  unfold tailWord_335637
  simp only [CollatzResearch.WordTrace]
  refine ⟨12241687085051946081053165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8161124723367964054035443 12241687085051946081053165)
  ·
    refine ⟨4590632656894479780394937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12241687085051946081053165 4590632656894479780394937)
    ·
      refine ⟨3442974492670859835296203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4590632656894479780394937 3442974492670859835296203)
      ·
        refine ⟨5164461739006289752944305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3442974492670859835296203 5164461739006289752944305)
        ·
          refine ⟨3873346304254717314708229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5164461739006289752944305 3873346304254717314708229)
          ·
            refine ⟨726252432047759496507793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3873346304254717314708229 726252432047759496507793)
            ·
              refine ⟨544689324035819622380845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 726252432047759496507793 544689324035819622380845)
              ·
                refine ⟨204258496513432358392817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 544689324035819622380845 204258496513432358392817)
                ·
                  refine ⟨153193872385074268794613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204258496513432358392817 153193872385074268794613)
                  ·
                    rfl

theorem cell20_335637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_335637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335637 prefixEnd_335637 := by exact prefixLift 335637
  have htrace : WordTrace (prefixWord ++ tailWord_335637) baseStart_335637 baseEnd_335637 := by
    simpa [prefixWord, tailWord_335637, baseEnd_335637] using wordTrace_append hprefix tailTrace_335637
  have hstable : (prefixWord ++ tailWord_335637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335637).length < 2 ^ (prefixWord ++ tailWord_335637).sum := by decide
  have hdescent : baseEnd_335637 < baseStart_335637 := by decide
  rcases family_descends (prefixWord ++ tailWord_335637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335648 : List Nat := [2, 1, 1, 5, 1, 1, 9]
def baseStart_335648 : Nat := 118140960795 + 335648 * 2 ^ 59
def prefixEnd_335648 : Nat := 4983230072969 + 3 ^ 40 * 335648 * 2
def baseEnd_335648 : Nat := 17022099231645235491989

theorem tailTrace_335648 : CollatzResearch.WordTrace tailWord_335648 prefixEnd_335648 17022099231645235491989 := by
  unfold tailWord_335648
  simp only [CollatzResearch.WordTrace]
  refine ⟨6121044144006047479851799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8161392192008063306469065 6121044144006047479851799)
  ·
    refine ⟨9181566216009071219777699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6121044144006047479851799 9181566216009071219777699)
    ·
      refine ⟨13772349324013606829666549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9181566216009071219777699 13772349324013606829666549)
      ·
        refine ⟨1291157749126275640281239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13772349324013606829666549 1291157749126275640281239)
        ·
          refine ⟨1936736623689413460421859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1291157749126275640281239 1936736623689413460421859)
          ·
            refine ⟨2905104935534120190632789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1936736623689413460421859 2905104935534120190632789)
            ·
              refine ⟨17022099231645235491989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2905104935534120190632789 17022099231645235491989)
              ·
                rfl

theorem cell20_335648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 9].length) (baseStart_335648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335648 prefixEnd_335648 := by exact prefixLift 335648
  have htrace : WordTrace (prefixWord ++ tailWord_335648) baseStart_335648 baseEnd_335648 := by
    simpa [prefixWord, tailWord_335648, baseEnd_335648] using wordTrace_append hprefix tailTrace_335648
  have hstable : (prefixWord ++ tailWord_335648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335648).length < 2 ^ (prefixWord ++ tailWord_335648).sum := by decide
  have hdescent : baseEnd_335648 < baseStart_335648 := by decide
  rcases family_descends (prefixWord ++ tailWord_335648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335692 : List Nat := [2, 2, 1, 3, 4, 2, 1, 3, 2]
def baseStart_335692 : Nat := 118140960795 + 335692 * 2 ^ 59
def prefixEnd_335692 : Nat := 4983230072969 + 3 ^ 40 * 335692 * 2
def baseEnd_335692 : Nat := 153218975883738521961055

theorem tailTrace_335692 : CollatzResearch.WordTrace tailWord_335692 prefixEnd_335692 153218975883738521961055 := by
  unfold tailWord_335692
  simp only [CollatzResearch.WordTrace]
  refine ⟨6121846549926345237152665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8162462066568460316203553 6121846549926345237152665)
  ·
    refine ⟨4591384912444758927864499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6121846549926345237152665 4591384912444758927864499)
    ·
      refine ⟨6887077368667138391796749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4591384912444758927864499 6887077368667138391796749)
      ·
        refine ⟨2582654013250176896923781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6887077368667138391796749 2582654013250176896923781)
        ·
          refine ⟨484247627484408168173209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2582654013250176896923781 484247627484408168173209)
          ·
            refine ⟨363185720613306126129907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484247627484408168173209 363185720613306126129907)
            ·
              refine ⟨544778580919959189194861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363185720613306126129907 544778580919959189194861)
              ·
                refine ⟨204291967844984695948073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 544778580919959189194861 204291967844984695948073)
                ·
                  refine ⟨153218975883738521961055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204291967844984695948073 153218975883738521961055)
                  ·
                    rfl

theorem cell20_335692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_335692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335692 prefixEnd_335692 := by exact prefixLift 335692
  have htrace : WordTrace (prefixWord ++ tailWord_335692) baseStart_335692 baseEnd_335692 := by
    simpa [prefixWord, tailWord_335692, baseEnd_335692] using wordTrace_append hprefix tailTrace_335692
  have hstable : (prefixWord ++ tailWord_335692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335692).length < 2 ^ (prefixWord ++ tailWord_335692).sum := by decide
  have hdescent : baseEnd_335692 < baseStart_335692 := by decide
  rcases family_descends (prefixWord ++ tailWord_335692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335703 : List Nat := [1, 1, 3, 2, 5, 2, 6]
def baseStart_335703 : Nat := 118140960795 + 335703 * 2 ^ 59
def prefixEnd_335703 : Nat := 4983230072969 + 3 ^ 40 * 335703 * 2
def baseEnd_335703 : Nat := 17024888509274596954927

theorem tailTrace_335703 : CollatzResearch.WordTrace tailWord_335703 prefixEnd_335703 17024888509274596954927 := by
  unfold tailWord_335703
  simp only [CollatzResearch.WordTrace]
  refine ⟨12244094302812839352955763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8162729535208559568637175 12244094302812839352955763)
  ·
    refine ⟨18366141454219259029433645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12244094302812839352955763 18366141454219259029433645)
    ·
      refine ⟨6887303045332222136037617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18366141454219259029433645 6887303045332222136037617)
      ·
        refine ⟨5165477283999166602028213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6887303045332222136037617 5165477283999166602028213)
        ·
          refine ⟨484263495374921868940145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5165477283999166602028213 484263495374921868940145)
          ·
            refine ⟨363197621531191401705109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484263495374921868940145 363197621531191401705109)
            ·
              refine ⟨17024888509274596954927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 363197621531191401705109 17024888509274596954927)
              ·
                rfl

theorem cell20_335703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 6].length) (baseStart_335703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335703 prefixEnd_335703 := by exact prefixLift 335703
  have htrace : WordTrace (prefixWord ++ tailWord_335703) baseStart_335703 baseEnd_335703 := by
    simpa [prefixWord, tailWord_335703, baseEnd_335703] using wordTrace_append hprefix tailTrace_335703
  have hstable : (prefixWord ++ tailWord_335703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335703).length < 2 ^ (prefixWord ++ tailWord_335703).sum := by decide
  have hdescent : baseEnd_335703 < baseStart_335703 := by decide
  rcases family_descends (prefixWord ++ tailWord_335703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335713 : List Nat := [1, 2, 3, 1, 1, 1, 7, 2, 2]
def baseStart_335713 : Nat := 118140960795 + 335713 * 2 ^ 59
def prefixEnd_335713 : Nat := 4983230072969 + 3 ^ 40 * 335713 * 2
def baseEnd_335713 : Nat := 153228560855955782260969

theorem tailTrace_335713 : CollatzResearch.WordTrace tailWord_335713 prefixEnd_335713 153228560855955782260969 := by
  unfold tailWord_335713
  simp only [CollatzResearch.WordTrace]
  refine ⟨12244459032776611060819793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8162972688517740707213195 12244459032776611060819793)
  ·
    refine ⟨9183344274582458295614845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12244459032776611060819793 9183344274582458295614845)
    ·
      refine ⟨3443754102968421860855567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9183344274582458295614845 3443754102968421860855567)
      ·
        refine ⟨5165631154452632791283351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3443754102968421860855567 5165631154452632791283351)
        ·
          refine ⟨7748446731678949186925027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5165631154452632791283351 7748446731678949186925027)
          ·
            refine ⟨11622670097518423780387541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7748446731678949186925027 11622670097518423780387541)
            ·
              refine ⟨272406330410588057352833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11622670097518423780387541 272406330410588057352833)
              ·
                refine ⟨204304747807941043014625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272406330410588057352833 204304747807941043014625)
                ·
                  refine ⟨153228560855955782260969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204304747807941043014625 153228560855955782260969)
                  ·
                    rfl

theorem cell20_335713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 2].length) (baseStart_335713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335713 prefixEnd_335713 := by exact prefixLift 335713
  have htrace : WordTrace (prefixWord ++ tailWord_335713) baseStart_335713 baseEnd_335713 := by
    simpa [prefixWord, tailWord_335713, baseEnd_335713] using wordTrace_append hprefix tailTrace_335713
  have hstable : (prefixWord ++ tailWord_335713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335713).length < 2 ^ (prefixWord ++ tailWord_335713).sum := by decide
  have hdescent : baseEnd_335713 < baseStart_335713 := by decide
  rcases family_descends (prefixWord ++ tailWord_335713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335724 : List Nat := [2, 2, 1, 1, 4, 2, 1, 7]
def baseStart_335724 : Nat := 118140960795 + 335724 * 2 ^ 59
def prefixEnd_335724 : Nat := 4983230072969 + 3 ^ 40 * 335724 * 2
def baseEnd_335724 : Nat := 51077860518562877631419

theorem tailTrace_335724 : CollatzResearch.WordTrace tailWord_335724 prefixEnd_335724 51077860518562877631419 := by
  unfold tailWord_335724
  simp only [CollatzResearch.WordTrace]
  refine ⟨6122430117868379969735113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8163240157157839959646817 6122430117868379969735113)
  ·
    refine ⟨4591822588401284977301335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6122430117868379969735113 4591822588401284977301335)
    ·
      refine ⟨6887733882601927465952003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4591822588401284977301335 6887733882601927465952003)
      ·
        refine ⟨10331600823902891198928005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6887733882601927465952003 10331600823902891198928005)
        ·
          refine ⟨1937175154481792099799001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10331600823902891198928005 1937175154481792099799001)
          ·
            refine ⟨1452881365861344074849251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1937175154481792099799001 1452881365861344074849251)
            ·
              refine ⟨2179322048792016112273877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1452881365861344074849251 2179322048792016112273877)
              ·
                refine ⟨51077860518562877631419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2179322048792016112273877 51077860518562877631419)
                ·
                  rfl

theorem cell20_335724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_335724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335724 prefixEnd_335724 := by exact prefixLift 335724
  have htrace : WordTrace (prefixWord ++ tailWord_335724) baseStart_335724 baseEnd_335724 := by
    simpa [prefixWord, tailWord_335724, baseEnd_335724] using wordTrace_append hprefix tailTrace_335724
  have hstable : (prefixWord ++ tailWord_335724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335724).length < 2 ^ (prefixWord ++ tailWord_335724).sum := by decide
  have hdescent : baseEnd_335724 < baseStart_335724 := by decide
  rcases family_descends (prefixWord ++ tailWord_335724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335758 : List Nat := [4, 1, 1, 5, 2, 7]
def baseStart_335758 : Nat := 118140960795 + 335758 * 2 ^ 59
def prefixEnd_335758 : Nat := 4983230072969 + 3 ^ 40 * 335758 * 2
def baseEnd_335758 : Nat := 5675892595634652805955

theorem tailTrace_335758 : CollatzResearch.WordTrace tailWord_335758 prefixEnd_335758 5675892595634652805955 := by
  unfold tailWord_335758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1530762539701697968275991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8164066878409055830805285 1530762539701697968275991)
  ·
    refine ⟨2296143809552546952413987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1530762539701697968275991 2296143809552546952413987)
    ·
      refine ⟨3444215714328820428620981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2296143809552546952413987 3444215714328820428620981)
      ·
        refine ⟨322895223218326915183217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3444215714328820428620981 322895223218326915183217)
        ·
          refine ⟨242171417413745186387413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322895223218326915183217 242171417413745186387413)
          ·
            refine ⟨5675892595634652805955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 242171417413745186387413 5675892595634652805955)
            ·
              rfl

theorem cell20_335758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 7].length) (baseStart_335758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335758 prefixEnd_335758 := by exact prefixLift 335758
  have htrace : WordTrace (prefixWord ++ tailWord_335758) baseStart_335758 baseEnd_335758 := by
    simpa [prefixWord, tailWord_335758, baseEnd_335758] using wordTrace_append hprefix tailTrace_335758
  have hstable : (prefixWord ++ tailWord_335758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335758).length < 2 ^ (prefixWord ++ tailWord_335758).sum := by decide
  have hdescent : baseEnd_335758 < baseStart_335758 := by decide
  rcases family_descends (prefixWord ++ tailWord_335758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335768 : List Nat := [2, 1, 2, 6, 1, 1, 1, 4, 2]
def baseStart_335768 : Nat := 118140960795 + 335768 * 2 ^ 59
def prefixEnd_335768 : Nat := 4983230072969 + 3 ^ 40 * 335768 * 2
def baseEnd_335768 : Nat := 153253664354620035427411

theorem tailTrace_335768 : CollatzResearch.WordTrace tailWord_335768 prefixEnd_335768 153253664354620035427411 := by
  unfold tailWord_335768
  simp only [CollatzResearch.WordTrace]
  refine ⟨6123232523788677727035979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8164310031718236969381305 6123232523788677727035979)
  ·
    refine ⟨9184848785683016590553969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6123232523788677727035979 9184848785683016590553969)
    ·
      refine ⟨6888636589262262442915477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9184848785683016590553969 6888636589262262442915477)
      ·
        refine ⟨322904840121668552011663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6888636589262262442915477 322904840121668552011663)
        ·
          refine ⟨484357260182502828017495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322904840121668552011663 484357260182502828017495)
          ·
            refine ⟨726535890273754242026243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484357260182502828017495 726535890273754242026243)
            ·
              refine ⟨1089803835410631363039365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726535890273754242026243 1089803835410631363039365)
              ·
                refine ⟨204338219139493380569881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1089803835410631363039365 204338219139493380569881)
                ·
                  refine ⟨153253664354620035427411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204338219139493380569881 153253664354620035427411)
                  ·
                    rfl

theorem cell20_335768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 2].length) (baseStart_335768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335768 prefixEnd_335768 := by exact prefixLift 335768
  have htrace : WordTrace (prefixWord ++ tailWord_335768) baseStart_335768 baseEnd_335768 := by
    simpa [prefixWord, tailWord_335768, baseEnd_335768] using wordTrace_append hprefix tailTrace_335768
  have hstable : (prefixWord ++ tailWord_335768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335768).length < 2 ^ (prefixWord ++ tailWord_335768).sum := by decide
  have hdescent : baseEnd_335768 < baseStart_335768 := by decide
  rcases family_descends (prefixWord ++ tailWord_335768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335769 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 5]
def baseStart_335769 : Nat := 118140960795 + 335769 * 2 ^ 59
def prefixEnd_335769 : Nat := 4983230072969 + 3 ^ 40 * 335769 * 2
def baseEnd_335769 : Nat := 153254120781868476394073

theorem tailTrace_335769 : CollatzResearch.WordTrace tailWord_335769 prefixEnd_335769 153254120781868476394073 := by
  unfold tailWord_335769
  simp only [CollatzResearch.WordTrace]
  refine ⟨12246501520573732624858361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8164334347049155083238907 12246501520573732624858361)
  ·
    refine ⟨9184876140430299468643771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12246501520573732624858361 9184876140430299468643771)
    ·
      refine ⟨13777314210645449202965657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9184876140430299468643771 13777314210645449202965657)
      ·
        refine ⟨10332985657984086902224243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13777314210645449202965657 10332985657984086902224243)
        ·
          refine ⟨15499478486976130353336365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10332985657984086902224243 15499478486976130353336365)
          ·
            refine ⟨5812304432616048882501137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15499478486976130353336365 5812304432616048882501137)
            ·
              refine ⟨4359228324462036661875853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5812304432616048882501137 4359228324462036661875853)
              ·
                refine ⟨1634710621673263748203445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4359228324462036661875853 1634710621673263748203445)
                ·
                  refine ⟨153254120781868476394073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1634710621673263748203445 153254120781868476394073)
                  ·
                    rfl

theorem cell20_335769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_335769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335769 prefixEnd_335769 := by exact prefixLift 335769
  have htrace : WordTrace (prefixWord ++ tailWord_335769) baseStart_335769 baseEnd_335769 := by
    simpa [prefixWord, tailWord_335769, baseEnd_335769] using wordTrace_append hprefix tailTrace_335769
  have hstable : (prefixWord ++ tailWord_335769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335769).length < 2 ^ (prefixWord ++ tailWord_335769).sum := by decide
  have hdescent : baseEnd_335769 < baseStart_335769 := by decide
  rcases family_descends (prefixWord ++ tailWord_335769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335793 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 6]
def baseStart_335793 : Nat := 118140960795 + 335793 * 2 ^ 59
def prefixEnd_335793 : Nat := 4983230072969 + 3 ^ 40 * 335793 * 2
def baseEnd_335793 : Nat := 153265075035831059593975

theorem tailTrace_335793 : CollatzResearch.WordTrace tailWord_335793 prefixEnd_335793 153265075035831059593975 := by
  unfold tailWord_335793
  simp only [CollatzResearch.WordTrace]
  refine ⟨12247376872486784723732033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8164917914991189815821355 12247376872486784723732033)
  ·
    refine ⟨9185532654365088542799025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12247376872486784723732033 9185532654365088542799025)
    ·
      refine ⟨6889149490773816407099269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9185532654365088542799025 6889149490773816407099269)
      ·
        refine ⟨1291715529520090576331113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6889149490773816407099269 1291715529520090576331113)
        ·
          refine ⟨968786647140067932248335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1291715529520090576331113 968786647140067932248335)
          ·
            refine ⟨1453179970710101898372503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 968786647140067932248335 1453179970710101898372503)
            ·
              refine ⟨2179769956065152847558755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1453179970710101898372503 2179769956065152847558755)
              ·
                refine ⟨3269654934097729271338133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2179769956065152847558755 3269654934097729271338133)
                ·
                  refine ⟨153265075035831059593975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3269654934097729271338133 153265075035831059593975)
                  ·
                    rfl

theorem cell20_335793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_335793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335793 prefixEnd_335793 := by exact prefixLift 335793
  have htrace : WordTrace (prefixWord ++ tailWord_335793) baseStart_335793 baseEnd_335793 := by
    simpa [prefixWord, tailWord_335793, baseEnd_335793] using wordTrace_append hprefix tailTrace_335793
  have hstable : (prefixWord ++ tailWord_335793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335793).length < 2 ^ (prefixWord ++ tailWord_335793).sum := by decide
  have hdescent : baseEnd_335793 < baseStart_335793 := by decide
  rcases family_descends (prefixWord ++ tailWord_335793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335807 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 5]
def baseStart_335807 : Nat := 118140960795 + 335807 * 2 ^ 59
def prefixEnd_335807 : Nat := 4983230072969 + 3 ^ 40 * 335807 * 2
def baseEnd_335807 : Nat := 153271465017309233127251

theorem tailTrace_335807 : CollatzResearch.WordTrace tailWord_335807 prefixEnd_335807 153271465017309233127251 := by
  unfold tailWord_335807
  simp only [CollatzResearch.WordTrace]
  refine ⟨12247887494436065114741675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8165258329624043409827783 12247887494436065114741675)
  ·
    refine ⟨18371831241654097672112513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12247887494436065114741675 18371831241654097672112513)
    ·
      refine ⟨13778873431240573254084385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18371831241654097672112513 13778873431240573254084385)
      ·
        refine ⟨10334155073430429940563289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13778873431240573254084385 10334155073430429940563289)
        ·
          refine ⟨7750616305072822455422467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10334155073430429940563289 7750616305072822455422467)
          ·
            refine ⟨11625924457609233683133701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7750616305072822455422467 11625924457609233683133701)
            ·
              refine ⟨2179860835801731315587569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11625924457609233683133701 2179860835801731315587569)
              ·
                refine ⟨1634895626851298486690677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2179860835801731315587569 1634895626851298486690677)
                ·
                  refine ⟨153271465017309233127251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1634895626851298486690677 153271465017309233127251)
                  ·
                    rfl

theorem cell20_335807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_335807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335807 prefixEnd_335807 := by exact prefixLift 335807
  have htrace : WordTrace (prefixWord ++ tailWord_335807) baseStart_335807 baseEnd_335807 := by
    simpa [prefixWord, tailWord_335807, baseEnd_335807] using wordTrace_append hprefix tailTrace_335807
  have hstable : (prefixWord ++ tailWord_335807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335807).length < 2 ^ (prefixWord ++ tailWord_335807).sum := by decide
  have hdescent : baseEnd_335807 < baseStart_335807 := by decide
  rcases family_descends (prefixWord ++ tailWord_335807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335824 : List Nat := [2, 1, 1, 1, 1, 2, 7, 2, 3]
def baseStart_335824 : Nat := 118140960795 + 335824 * 2 ^ 59
def prefixEnd_335824 : Nat := 4983230072969 + 3 ^ 40 * 335824 * 2
def baseEnd_335824 : Nat := 153279224280532729560515

theorem tailTrace_335824 : CollatzResearch.WordTrace tailWord_335824 prefixEnd_335824 153279224280532729560515 := by
  unfold tailWord_335824
  simp only [CollatzResearch.WordTrace]
  refine ⟨6124253767687238509055263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8165671690249651345407017 6124253767687238509055263)
  ·
    refine ⟨9186380651530857763582895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6124253767687238509055263 9186380651530857763582895)
    ·
      refine ⟨13779570977296286645374343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9186380651530857763582895 13779570977296286645374343)
      ·
        refine ⟨20669356465944429968061515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13779570977296286645374343 20669356465944429968061515)
        ·
          refine ⟨31004034698916644952092273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20669356465944429968061515 31004034698916644952092273)
          ·
            refine ⟨23253026024187483714069205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31004034698916644952092273 23253026024187483714069205)
            ·
              refine ⟨544992797441894149548497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 23253026024187483714069205 544992797441894149548497)
              ·
                refine ⟨408744598081420612161373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 544992797441894149548497 408744598081420612161373)
                ·
                  refine ⟨153279224280532729560515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 408744598081420612161373 153279224280532729560515)
                  ·
                    rfl

theorem cell20_335824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_335824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335824 prefixEnd_335824 := by exact prefixLift 335824
  have htrace : WordTrace (prefixWord ++ tailWord_335824) baseStart_335824 baseEnd_335824 := by
    simpa [prefixWord, tailWord_335824, baseEnd_335824] using wordTrace_append hprefix tailTrace_335824
  have hstable : (prefixWord ++ tailWord_335824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335824).length < 2 ^ (prefixWord ++ tailWord_335824).sum := by decide
  have hdescent : baseEnd_335824 < baseStart_335824 := by decide
  rcases family_descends (prefixWord ++ tailWord_335824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335831 : List Nat := [1, 1, 3, 2, 1, 1, 6, 1, 4]
def baseStart_335831 : Nat := 118140960795 + 335831 * 2 ^ 59
def prefixEnd_335831 : Nat := 4983230072969 + 3 ^ 40 * 335831 * 2
def baseEnd_335831 : Nat := 153282419271271816327153

theorem tailTrace_335831 : CollatzResearch.WordTrace tailWord_335831 prefixEnd_335831 153282419271271816327153 := by
  unfold tailWord_335831
  simp only [CollatzResearch.WordTrace]
  refine ⟨12248762846349117213615347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8165841897566078142410231 12248762846349117213615347)
  ·
    refine ⟨18373144269523675820423021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12248762846349117213615347 18373144269523675820423021)
    ·
      refine ⟨6889929101071378432658633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18373144269523675820423021 6889929101071378432658633)
      ·
        refine ⟨5167446825803533824493975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6889929101071378432658633 5167446825803533824493975)
        ·
          refine ⟨7751170238705300736740963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5167446825803533824493975 7751170238705300736740963)
          ·
            refine ⟨11626755358057951105111445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7751170238705300736740963 11626755358057951105111445)
            ·
              refine ⟨545004157408966458052099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11626755358057951105111445 545004157408966458052099)
              ·
                refine ⟨817506236113449687078149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545004157408966458052099 817506236113449687078149)
                ·
                  refine ⟨153282419271271816327153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 817506236113449687078149 153282419271271816327153)
                  ·
                    rfl

theorem cell20_335831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 4].length) (baseStart_335831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335831 prefixEnd_335831 := by exact prefixLift 335831
  have htrace : WordTrace (prefixWord ++ tailWord_335831) baseStart_335831 baseEnd_335831 := by
    simpa [prefixWord, tailWord_335831, baseEnd_335831] using wordTrace_append hprefix tailTrace_335831
  have hstable : (prefixWord ++ tailWord_335831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335831).length < 2 ^ (prefixWord ++ tailWord_335831).sum := by decide
  have hdescent : baseEnd_335831 < baseStart_335831 := by decide
  rcases family_descends (prefixWord ++ tailWord_335831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335865 : List Nat := [1, 2, 1, 3, 1, 6, 1, 3, 2]
def baseStart_335865 : Nat := 118140960795 + 335865 * 2 ^ 59
def prefixEnd_335865 : Nat := 4983230072969 + 3 ^ 40 * 335865 * 2
def baseEnd_335865 : Nat := 153297937797718809193681

theorem tailTrace_335865 : CollatzResearch.WordTrace tailWord_335865 prefixEnd_335865 153297937797718809193681 := by
  unfold tailWord_335865
  simp only [CollatzResearch.WordTrace]
  refine ⟨12250002928225941020353049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8166668618817294013568699 12250002928225941020353049)
  ·
    refine ⟨9187502196169455765264787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12250002928225941020353049 9187502196169455765264787)
    ·
      refine ⟨13781253294254183647897181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9187502196169455765264787 13781253294254183647897181)
      ·
        refine ⟨5167969985345318867961443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13781253294254183647897181 5167969985345318867961443)
        ·
          refine ⟨7751954978017978301942165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5167969985345318867961443 7751954978017978301942165)
          ·
            refine ⟨363372889594592732903539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7751954978017978301942165 363372889594592732903539)
            ·
              refine ⟨545059334391889099355309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363372889594592732903539 545059334391889099355309)
              ·
                refine ⟨204397250396958412258241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 545059334391889099355309 204397250396958412258241)
                ·
                  refine ⟨153297937797718809193681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204397250396958412258241 153297937797718809193681)
                  ·
                    rfl

theorem cell20_335865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 2].length) (baseStart_335865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335865 prefixEnd_335865 := by exact prefixLift 335865
  have htrace : WordTrace (prefixWord ++ tailWord_335865) baseStart_335865 baseEnd_335865 := by
    simpa [prefixWord, tailWord_335865, baseEnd_335865] using wordTrace_append hprefix tailTrace_335865
  have hstable : (prefixWord ++ tailWord_335865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335865).length < 2 ^ (prefixWord ++ tailWord_335865).sum := by decide
  have hdescent : baseEnd_335865 < baseStart_335865 := by decide
  rcases family_descends (prefixWord ++ tailWord_335865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335878 : List Nat := [6, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_335878 : Nat := 118140960795 + 335878 * 2 ^ 59
def prefixEnd_335878 : Nat := 4983230072969 + 3 ^ 40 * 335878 * 2
def baseEnd_335878 : Nat := 153303871351948541760295

theorem tailTrace_335878 : CollatzResearch.WordTrace tailWord_335878 prefixEnd_335878 153303871351948541760295 := by
  unfold tailWord_335878
  simp only [CollatzResearch.WordTrace]
  refine ⟨382827408661838882518009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8166984718119229493717525 382827408661838882518009)
  ·
    refine ⟨287120556496379161888507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 382827408661838882518009 287120556496379161888507)
    ·
      refine ⟨430680834744568742832761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287120556496379161888507 430680834744568742832761)
      ·
        refine ⟨323010626058426557124571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 430680834744568742832761 323010626058426557124571)
        ·
          refine ⟨484515939087639835686857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323010626058426557124571 484515939087639835686857)
          ·
            refine ⟨363386954315729876765143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484515939087639835686857 363386954315729876765143)
            ·
              refine ⟨545080431473594815147715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363386954315729876765143 545080431473594815147715)
              ·
                refine ⟨817620647210392222721573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545080431473594815147715 817620647210392222721573)
                ·
                  refine ⟨153303871351948541760295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 817620647210392222721573 153303871351948541760295)
                  ·
                    rfl

theorem cell20_335878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_335878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335878 prefixEnd_335878 := by exact prefixLift 335878
  have htrace : WordTrace (prefixWord ++ tailWord_335878) baseStart_335878 baseEnd_335878 := by
    simpa [prefixWord, tailWord_335878, baseEnd_335878] using wordTrace_append hprefix tailTrace_335878
  have hstable : (prefixWord ++ tailWord_335878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335878).length < 2 ^ (prefixWord ++ tailWord_335878).sum := by decide
  have hdescent : baseEnd_335878 < baseStart_335878 := by decide
  rcases family_descends (prefixWord ++ tailWord_335878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335882 : List Nat := [3, 1, 2, 2, 4, 1, 3, 2, 2]
def baseStart_335882 : Nat := 118140960795 + 335882 * 2 ^ 59
def prefixEnd_335882 : Nat := 4983230072969 + 3 ^ 40 * 335882 * 2
def baseEnd_335882 : Nat := 153305697060942305626945

theorem tailTrace_335882 : CollatzResearch.WordTrace tailWord_335882 prefixEnd_335882 153305697060942305626945 := by
  unfold tailWord_335882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3062655742291088230930475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8167081979442901949147933 3062655742291088230930475)
  ·
    refine ⟨4593983613436632346395713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3062655742291088230930475 4593983613436632346395713)
    ·
      refine ⟨3445487710077474259796785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4593983613436632346395713 3445487710077474259796785)
      ·
        refine ⟨2584115782558105694847589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3445487710077474259796785 2584115782558105694847589)
        ·
          refine ⟨484521709229644817783923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2584115782558105694847589 484521709229644817783923)
          ·
            refine ⟨726782563844467226675885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484521709229644817783923 726782563844467226675885)
            ·
              refine ⟨272543461441675210003457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 726782563844467226675885 272543461441675210003457)
              ·
                refine ⟨204407596081256407502593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272543461441675210003457 204407596081256407502593)
                ·
                  refine ⟨153305697060942305626945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204407596081256407502593 153305697060942305626945)
                  ·
                    rfl

theorem cell20_335882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_335882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335882 prefixEnd_335882 := by exact prefixLift 335882
  have htrace : WordTrace (prefixWord ++ tailWord_335882) baseStart_335882 baseEnd_335882 := by
    simpa [prefixWord, tailWord_335882, baseEnd_335882] using wordTrace_append hprefix tailTrace_335882
  have hstable : (prefixWord ++ tailWord_335882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335882).length < 2 ^ (prefixWord ++ tailWord_335882).sum := by decide
  have hdescent : baseEnd_335882 < baseStart_335882 := by decide
  rcases family_descends (prefixWord ++ tailWord_335882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335883 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 5]
def baseStart_335883 : Nat := 118140960795 + 335883 * 2 ^ 59
def prefixEnd_335883 : Nat := 4983230072969 + 3 ^ 40 * 335883 * 2
def baseEnd_335883 : Nat := 153306153488190746593607

theorem tailTrace_335883 : CollatzResearch.WordTrace tailWord_335883 prefixEnd_335883 153306153488190746593607 := by
  unfold tailWord_335883
  simp only [CollatzResearch.WordTrace]
  refine ⟨12250659442160730094508303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8167106294773820063005535 12250659442160730094508303)
  ·
    refine ⟨18375989163241095141762455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12250659442160730094508303 18375989163241095141762455)
    ·
      refine ⟨27563983744861642712643683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18375989163241095141762455 27563983744861642712643683)
      ·
        refine ⟨41345975617292464068965525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27563983744861642712643683 41345975617292464068965525)
        ·
          refine ⟨1938092607060584253232759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41345975617292464068965525 1938092607060584253232759)
          ·
            refine ⟨2907138910590876379849139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1938092607060584253232759 2907138910590876379849139)
            ·
              refine ⟨4360708365886314569773709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2907138910590876379849139 4360708365886314569773709)
              ·
                refine ⟨1635265637207367963665141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4360708365886314569773709 1635265637207367963665141)
                ·
                  refine ⟨153306153488190746593607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1635265637207367963665141 153306153488190746593607)
                  ·
                    rfl

theorem cell20_335883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_335883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335883 prefixEnd_335883 := by exact prefixLift 335883
  have htrace : WordTrace (prefixWord ++ tailWord_335883) baseStart_335883 baseEnd_335883 := by
    simpa [prefixWord, tailWord_335883, baseEnd_335883] using wordTrace_append hprefix tailTrace_335883
  have hstable : (prefixWord ++ tailWord_335883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335883).length < 2 ^ (prefixWord ++ tailWord_335883).sum := by decide
  have hdescent : baseEnd_335883 < baseStart_335883 := by decide
  rcases family_descends (prefixWord ++ tailWord_335883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335892 : List Nat := [2, 4, 3, 2, 1, 2, 2, 1, 3]
def baseStart_335892 : Nat := 118140960795 + 335892 * 2 ^ 59
def prefixEnd_335892 : Nat := 4983230072969 + 3 ^ 40 * 335892 * 2
def baseEnd_335892 : Nat := 153310261333426715293571

theorem tailTrace_335892 : CollatzResearch.WordTrace tailWord_335892 prefixEnd_335892 153310261333426715293571 := by
  unfold tailWord_335892
  simp only [CollatzResearch.WordTrace]
  refine ⟨6125493849564062315792965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8167325132752083087723953 6125493849564062315792965)
  ·
    refine ⟨1148530096793261684211181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6125493849564062315792965 1148530096793261684211181)
    ·
      refine ⟨430698786297473131579193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1148530096793261684211181 430698786297473131579193)
      ·
        refine ⟨323024089723104848684395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 430698786297473131579193 323024089723104848684395)
        ·
          refine ⟨484536134584657273026593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323024089723104848684395 484536134584657273026593)
          ·
            refine ⟨363402100938492954769945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484536134584657273026593 363402100938492954769945)
            ·
              refine ⟨272551575703869716077459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363402100938492954769945 272551575703869716077459)
              ·
                refine ⟨408827363555804574116189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272551575703869716077459 408827363555804574116189)
                ·
                  refine ⟨153310261333426715293571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 408827363555804574116189 153310261333426715293571)
                  ·
                    rfl

theorem cell20_335892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_335892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335892 prefixEnd_335892 := by exact prefixLift 335892
  have htrace : WordTrace (prefixWord ++ tailWord_335892) baseStart_335892 baseEnd_335892 := by
    simpa [prefixWord, tailWord_335892, baseEnd_335892] using wordTrace_append hprefix tailTrace_335892
  have hstable : (prefixWord ++ tailWord_335892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335892).length < 2 ^ (prefixWord ++ tailWord_335892).sum := by decide
  have hdescent : baseEnd_335892 < baseStart_335892 := by decide
  rcases family_descends (prefixWord ++ tailWord_335892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335893 : List Nat := [1, 3, 2, 1, 5, 1, 2, 5]
def baseStart_335893 : Nat := 118140960795 + 335893 * 2 ^ 59
def prefixEnd_335893 : Nat := 4983230072969 + 3 ^ 40 * 335893 * 2
def baseEnd_335893 : Nat := 51103572586891718753411

theorem tailTrace_335893 : CollatzResearch.WordTrace tailWord_335893 prefixEnd_335893 51103572586891718753411 := by
  unfold tailWord_335893
  simp only [CollatzResearch.WordTrace]
  refine ⟨12251024172124501802372333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8167349448083001201581555 12251024172124501802372333)
  ·
    refine ⟨4594134064546688175889625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12251024172124501802372333 4594134064546688175889625)
    ·
      refine ⟨3445600548410016131917219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4594134064546688175889625 3445600548410016131917219)
      ·
        refine ⟨5168400822615024197875829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3445600548410016131917219 5168400822615024197875829)
        ·
          refine ⟨484537577120158518550859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5168400822615024197875829 484537577120158518550859)
          ·
            refine ⟨726806365680237777826289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484537577120158518550859 726806365680237777826289)
            ·
              refine ⟨545104774260178333369717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 726806365680237777826289 545104774260178333369717)
              ·
                refine ⟨51103572586891718753411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 545104774260178333369717 51103572586891718753411)
                ·
                  rfl

theorem cell20_335893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 5].length) (baseStart_335893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335893 prefixEnd_335893 := by exact prefixLift 335893
  have htrace : WordTrace (prefixWord ++ tailWord_335893) baseStart_335893 baseEnd_335893 := by
    simpa [prefixWord, tailWord_335893, baseEnd_335893] using wordTrace_append hprefix tailTrace_335893
  have hstable : (prefixWord ++ tailWord_335893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335893).length < 2 ^ (prefixWord ++ tailWord_335893).sum := by decide
  have hdescent : baseEnd_335893 < baseStart_335893 := by decide
  rcases family_descends (prefixWord ++ tailWord_335893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335934 : List Nat := [4, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_335934 : Nat := 118140960795 + 335934 * 2 ^ 59
def prefixEnd_335934 : Nat := 4983230072969 + 3 ^ 40 * 335934 * 2
def baseEnd_335934 : Nat := 153329431277861235893399

theorem tailTrace_335934 : CollatzResearch.WordTrace tailWord_335934 prefixEnd_335934 153329431277861235893399 := by
  unfold tailWord_335934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1531564945621995725576857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8168346376650643869743237 1531564945621995725576857)
  ·
    refine ⟨1148673709216496794182643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1531564945621995725576857 1148673709216496794182643)
    ·
      refine ⟨1723010563824745191273965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1148673709216496794182643 1723010563824745191273965)
      ·
        refine ⟨646128961434279446727737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1723010563824745191273965 646128961434279446727737)
        ·
          refine ⟨484596721075709585045803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 646128961434279446727737 484596721075709585045803)
          ·
            refine ⟨726895081613564377568705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484596721075709585045803 726895081613564377568705)
            ·
              refine ⟨545171311210173283176529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 726895081613564377568705 545171311210173283176529)
              ·
                refine ⟨408878483407629962382397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 545171311210173283176529 408878483407629962382397)
                ·
                  refine ⟨153329431277861235893399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 408878483407629962382397 153329431277861235893399)
                  ·
                    rfl

theorem cell20_335934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_335934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335934 prefixEnd_335934 := by exact prefixLift 335934
  have htrace : WordTrace (prefixWord ++ tailWord_335934) baseStart_335934 baseEnd_335934 := by
    simpa [prefixWord, tailWord_335934, baseEnd_335934] using wordTrace_append hprefix tailTrace_335934
  have hstable : (prefixWord ++ tailWord_335934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335934).length < 2 ^ (prefixWord ++ tailWord_335934).sum := by decide
  have hdescent : baseEnd_335934 < baseStart_335934 := by decide
  rcases family_descends (prefixWord ++ tailWord_335934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335993 : List Nat := [1, 2, 1, 3, 4, 3, 1, 2, 3]
def baseStart_335993 : Nat := 118140960795 + 335993 * 2 ^ 59
def prefixEnd_335993 : Nat := 4983230072969 + 3 ^ 40 * 335993 * 2
def baseEnd_335993 : Nat := 153356360485519252926491

theorem tailTrace_335993 : CollatzResearch.WordTrace tailWord_335993 prefixEnd_335993 153356360485519252926491 := by
  unfold tailWord_335993
  simp only [CollatzResearch.WordTrace]
  refine ⟨12254671471762218881012633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8169780981174812587341755 12254671471762218881012633)
  ·
    refine ⟨9191003603821664160759475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12254671471762218881012633 9191003603821664160759475)
    ·
      refine ⟨13786505405732496241139213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9191003603821664160759475 13786505405732496241139213)
      ·
        refine ⟨5169939527149686090427205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13786505405732496241139213 5169939527149686090427205)
        ·
          refine ⟨969363661340566141955101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5169939527149686090427205 969363661340566141955101)
          ·
            refine ⟨363511373002712303233163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 969363661340566141955101 363511373002712303233163)
            ·
              refine ⟨545267059504068454849745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363511373002712303233163 545267059504068454849745)
              ·
                refine ⟨408950294628051341137309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 545267059504068454849745 408950294628051341137309)
                ·
                  refine ⟨153356360485519252926491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 408950294628051341137309 153356360485519252926491)
                  ·
                    rfl

theorem cell20_335993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 3].length) (baseStart_335993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_335993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_335993 prefixEnd_335993 := by exact prefixLift 335993
  have htrace : WordTrace (prefixWord ++ tailWord_335993) baseStart_335993 baseEnd_335993 := by
    simpa [prefixWord, tailWord_335993, baseEnd_335993] using wordTrace_append hprefix tailTrace_335993
  have hstable : (prefixWord ++ tailWord_335993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335993).length < 2 ^ (prefixWord ++ tailWord_335993).sum := by decide
  have hdescent : baseEnd_335993 < baseStart_335993 := by decide
  rcases family_descends (prefixWord ++ tailWord_335993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336020 : List Nat := [2, 4, 2, 3, 2, 1, 2, 4]
def baseStart_336020 : Nat := 118140960795 + 336020 * 2 ^ 59
def prefixEnd_336020 : Nat := 4983230072969 + 3 ^ 40 * 336020 * 2
def baseEnd_336020 : Nat := 51122894673742386342127

theorem tailTrace_336020 : CollatzResearch.WordTrace tailWord_336020 prefixEnd_336020 51122894673742386342127 := by
  unfold tailWord_336020
  simp only [CollatzResearch.WordTrace]
  refine ⟨6127828121332201246122757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8170437495109601661497009 6127828121332201246122757)
  ·
    refine ⟨1148967772749787733648017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6127828121332201246122757 1148967772749787733648017)
    ·
      refine ⟨861725829562340800236013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1148967772749787733648017 861725829562340800236013)
      ·
        refine ⟨323147186085877800088505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 861725829562340800236013 323147186085877800088505)
        ·
          refine ⟨242360389564408350066379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323147186085877800088505 242360389564408350066379)
          ·
            refine ⟨363540584346612525099569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242360389564408350066379 363540584346612525099569)
            ·
              refine ⟨272655438259959393824677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363540584346612525099569 272655438259959393824677)
              ·
                refine ⟨51122894673742386342127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 272655438259959393824677 51122894673742386342127)
                ·
                  rfl

theorem cell20_336020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 4].length) (baseStart_336020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336020 prefixEnd_336020 := by exact prefixLift 336020
  have htrace : WordTrace (prefixWord ++ tailWord_336020) baseStart_336020 baseEnd_336020 := by
    simpa [prefixWord, tailWord_336020, baseEnd_336020] using wordTrace_append hprefix tailTrace_336020
  have hstable : (prefixWord ++ tailWord_336020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336020).length < 2 ^ (prefixWord ++ tailWord_336020).sum := by decide
  have hdescent : baseEnd_336020 < baseStart_336020 := by decide
  rcases family_descends (prefixWord ++ tailWord_336020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336024 : List Nat := [2, 1, 2, 4, 3, 2, 2, 4]
def baseStart_336024 : Nat := 118140960795 + 336024 * 2 ^ 59
def prefixEnd_336024 : Nat := 4983230072969 + 3 ^ 40 * 336024 * 2
def baseEnd_336024 : Nat := 51123503243406974297677

theorem tailTrace_336024 : CollatzResearch.WordTrace tailWord_336024 prefixEnd_336024 51123503243406974297677 := by
  unfold tailWord_336024
  simp only [CollatzResearch.WordTrace]
  refine ⟨6127901067324955587695563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8170534756433274116927417 6127901067324955587695563)
  ·
    refine ⟨9191851600987433381543345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6127901067324955587695563 9191851600987433381543345)
    ·
      refine ⟨6893888700740575036157509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9191851600987433381543345 6893888700740575036157509)
      ·
        refine ⟨1292604131388857819279533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6893888700740575036157509 1292604131388857819279533)
        ·
          refine ⟨484726549270821682229825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1292604131388857819279533 484726549270821682229825)
          ·
            refine ⟨363544911953116261672369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484726549270821682229825 363544911953116261672369)
            ·
              refine ⟨272658683964837196254277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363544911953116261672369 272658683964837196254277)
              ·
                refine ⟨51123503243406974297677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 272658683964837196254277 51123503243406974297677)
                ·
                  rfl

theorem cell20_336024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 4].length) (baseStart_336024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336024 prefixEnd_336024 := by exact prefixLift 336024
  have htrace : WordTrace (prefixWord ++ tailWord_336024) baseStart_336024 baseEnd_336024 := by
    simpa [prefixWord, tailWord_336024, baseEnd_336024] using wordTrace_append hprefix tailTrace_336024
  have hstable : (prefixWord ++ tailWord_336024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336024).length < 2 ^ (prefixWord ++ tailWord_336024).sum := by decide
  have hdescent : baseEnd_336024 < baseStart_336024 := by decide
  rcases family_descends (prefixWord ++ tailWord_336024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336028 : List Nat := [2, 2, 3, 2, 1, 1, 3, 6]
def baseStart_336028 : Nat := 118140960795 + 336028 * 2 ^ 59
def prefixEnd_336028 : Nat := 4983230072969 + 3 ^ 40 * 336028 * 2
def baseEnd_336028 : Nat := 51124111813071562253227

theorem tailTrace_336028 : CollatzResearch.WordTrace tailWord_336028 prefixEnd_336028 51124111813071562253227 := by
  unfold tailWord_336028
  simp only [CollatzResearch.WordTrace]
  refine ⟨6127974013317709929268369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8170632017756946572357825 6127974013317709929268369)
  ·
    refine ⟨4595980509988282446951277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6127974013317709929268369 4595980509988282446951277)
    ·
      refine ⟨1723492691245605917606729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4595980509988282446951277 1723492691245605917606729)
      ·
        refine ⟨1292619518434204438205047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1723492691245605917606729 1292619518434204438205047)
        ·
          refine ⟨1938929277651306657307571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1292619518434204438205047 1938929277651306657307571)
          ·
            refine ⟨2908393916476959985961357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1938929277651306657307571 2908393916476959985961357)
            ·
              refine ⟨1090647718678859994735509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2908393916476959985961357 1090647718678859994735509)
              ·
                refine ⟨51124111813071562253227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1090647718678859994735509 51124111813071562253227)
                ·
                  rfl

theorem cell20_336028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_336028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336028 prefixEnd_336028 := by exact prefixLift 336028
  have htrace : WordTrace (prefixWord ++ tailWord_336028) baseStart_336028 baseEnd_336028 := by
    simpa [prefixWord, tailWord_336028, baseEnd_336028] using wordTrace_append hprefix tailTrace_336028
  have hstable : (prefixWord ++ tailWord_336028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336028).length < 2 ^ (prefixWord ++ tailWord_336028).sum := by decide
  have hdescent : baseEnd_336028 < baseStart_336028 := by decide
  rcases family_descends (prefixWord ++ tailWord_336028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336034 : List Nat := [3, 3, 1, 3, 1, 3, 1, 3, 2]
def baseStart_336034 : Nat := 118140960795 + 336034 * 2 ^ 59
def prefixEnd_336034 : Nat := 4983230072969 + 3 ^ 40 * 336034 * 2
def baseEnd_336034 : Nat := 153375074002705332559657

theorem tailTrace_336034 : CollatzResearch.WordTrace tailWord_336034 prefixEnd_336034 153375074002705332559657 := by
  unfold tailWord_336034
  simp only [CollatzResearch.WordTrace]
  refine ⟨3064041716153420720813789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8170777909742455255503437 3064041716153420720813789)
  ·
    refine ⟨1149015643557532770305171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3064041716153420720813789 1149015643557532770305171)
    ·
      refine ⟨1723523465336299155457757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1149015643557532770305171 1723523465336299155457757)
      ·
        refine ⟨646321299501112183296659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1723523465336299155457757 646321299501112183296659)
        ·
          refine ⟨969481949251668274944989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 646321299501112183296659 969481949251668274944989)
          ·
            refine ⟨363555730969375603104371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 969481949251668274944989 363555730969375603104371)
            ·
              refine ⟨545333596454063404656557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363555730969375603104371 545333596454063404656557)
              ·
                refine ⟨204500098670273776746209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 545333596454063404656557 204500098670273776746209)
                ·
                  refine ⟨153375074002705332559657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204500098670273776746209 153375074002705332559657)
                  ·
                    rfl

theorem cell20_336034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_336034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336034 prefixEnd_336034 := by exact prefixLift 336034
  have htrace : WordTrace (prefixWord ++ tailWord_336034) baseStart_336034 baseEnd_336034 := by
    simpa [prefixWord, tailWord_336034, baseEnd_336034] using wordTrace_append hprefix tailTrace_336034
  have hstable : (prefixWord ++ tailWord_336034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336034).length < 2 ^ (prefixWord ++ tailWord_336034).sum := by decide
  have hdescent : baseEnd_336034 < baseStart_336034 := by decide
  rcases family_descends (prefixWord ++ tailWord_336034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336045 : List Nat := [1, 5, 2, 1, 2, 3, 6]
def baseStart_336045 : Nat := 118140960795 + 336045 * 2 ^ 59
def prefixEnd_336045 : Nat := 4983230072969 + 3 ^ 40 * 336045 * 2
def baseEnd_336045 : Nat := 17042232744715353688105

theorem tailTrace_336045 : CollatzResearch.WordTrace tailWord_336045 prefixEnd_336045 17042232744715353688105 := by
  unfold tailWord_336045
  simp only [CollatzResearch.WordTrace]
  refine ⟨12256568067573831761905589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8171045378382554507937059 12256568067573831761905589)
  ·
    refine ⟨1149053256335046727678649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12256568067573831761905589 1149053256335046727678649)
    ·
      refine ⟨861789942251285045758987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1149053256335046727678649 861789942251285045758987)
      ·
        refine ⟨1292684913376927568638481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 861789942251285045758987 1292684913376927568638481)
        ·
          refine ⟨969513685032695676478861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1292684913376927568638481 969513685032695676478861)
          ·
            refine ⟨363567631887260878679573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 969513685032695676478861 363567631887260878679573)
            ·
              refine ⟨17042232744715353688105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 363567631887260878679573 17042232744715353688105)
              ·
                rfl

theorem cell20_336045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 6].length) (baseStart_336045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336045 prefixEnd_336045 := by exact prefixLift 336045
  have htrace : WordTrace (prefixWord ++ tailWord_336045) baseStart_336045 baseEnd_336045 := by
    simpa [prefixWord, tailWord_336045, baseEnd_336045] using wordTrace_append hprefix tailTrace_336045
  have hstable : (prefixWord ++ tailWord_336045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336045).length < 2 ^ (prefixWord ++ tailWord_336045).sum := by decide
  have hdescent : baseEnd_336045 < baseStart_336045 := by decide
  rcases family_descends (prefixWord ++ tailWord_336045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336055 : List Nat := [1, 1, 3, 1, 4, 3, 3, 2, 2]
def baseStart_336055 : Nat := 118140960795 + 336055 * 2 ^ 59
def prefixEnd_336055 : Nat := 4983230072969 + 3 ^ 40 * 336055 * 2
def baseEnd_336055 : Nat := 153384658974922592859571

theorem tailTrace_336055 : CollatzResearch.WordTrace tailWord_336055 prefixEnd_336055 153384658974922592859571 := by
  unfold tailWord_336055
  simp only [CollatzResearch.WordTrace]
  refine ⟨12256932797537603469769619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8171288531691735646513079 12256932797537603469769619)
  ·
    refine ⟨18385399196306405204654429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12256932797537603469769619 18385399196306405204654429)
    ·
      refine ⟨6894524698614901951745411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18385399196306405204654429 6894524698614901951745411)
      ·
        refine ⟨10341787047922352927618117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6894524698614901951745411 10341787047922352927618117)
        ·
          refine ⟨1939085071485441173928397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10341787047922352927618117 1939085071485441173928397)
          ·
            refine ⟨727156901807040440223149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1939085071485441173928397 727156901807040440223149)
            ·
              refine ⟨272683838177640165083681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 727156901807040440223149 272683838177640165083681)
              ·
                refine ⟨204512878633230123812761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272683838177640165083681 204512878633230123812761)
                ·
                  refine ⟨153384658974922592859571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204512878633230123812761 153384658974922592859571)
                  ·
                    rfl

theorem cell20_336055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 2].length) (baseStart_336055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336055 prefixEnd_336055 := by exact prefixLift 336055
  have htrace : WordTrace (prefixWord ++ tailWord_336055) baseStart_336055 baseEnd_336055 := by
    simpa [prefixWord, tailWord_336055, baseEnd_336055] using wordTrace_append hprefix tailTrace_336055
  have hstable : (prefixWord ++ tailWord_336055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336055).length < 2 ^ (prefixWord ++ tailWord_336055).sum := by decide
  have hdescent : baseEnd_336055 < baseStart_336055 := by decide
  rcases family_descends (prefixWord ++ tailWord_336055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336065 : List Nat := [1, 2, 6, 1, 2, 2, 2, 1, 3]
def baseStart_336065 : Nat := 118140960795 + 336065 * 2 ^ 59
def prefixEnd_336065 : Nat := 4983230072969 + 3 ^ 40 * 336065 * 2
def baseEnd_336065 : Nat := 153389223247407002526197

theorem tailTrace_336065 : CollatzResearch.WordTrace tailWord_336065 prefixEnd_336065 153389223247407002526197 := by
  unfold tailWord_336065
  simp only [CollatzResearch.WordTrace]
  refine ⟨12257297527501375177633649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8171531685000916785089099 12257297527501375177633649)
  ·
    refine ⟨9192973145626031383225237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12257297527501375177633649 9192973145626031383225237)
    ·
      refine ⟨430920616201220221088683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9192973145626031383225237 430920616201220221088683)
      ·
        refine ⟨646380924301830331633025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430920616201220221088683 646380924301830331633025)
        ·
          refine ⟨484785693226372748724769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 646380924301830331633025 484785693226372748724769)
          ·
            refine ⟨363589269919779561543577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484785693226372748724769 363589269919779561543577)
            ·
              refine ⟨272691952439834671157683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363589269919779561543577 272691952439834671157683)
              ·
                refine ⟨409037928659752006736525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272691952439834671157683 409037928659752006736525)
                ·
                  refine ⟨153389223247407002526197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 409037928659752006736525 153389223247407002526197)
                  ·
                    rfl

theorem cell20_336065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 3].length) (baseStart_336065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336065 prefixEnd_336065 := by exact prefixLift 336065
  have htrace : WordTrace (prefixWord ++ tailWord_336065) baseStart_336065 baseEnd_336065 := by
    simpa [prefixWord, tailWord_336065, baseEnd_336065] using wordTrace_append hprefix tailTrace_336065
  have hstable : (prefixWord ++ tailWord_336065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336065).length < 2 ^ (prefixWord ++ tailWord_336065).sum := by decide
  have hdescent : baseEnd_336065 < baseStart_336065 := by decide
  rcases family_descends (prefixWord ++ tailWord_336065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336152 : List Nat := [2, 1, 2, 3, 1, 2, 4, 3, 2]
def baseStart_336152 : Nat := 118140960795 + 336152 * 2 ^ 59
def prefixEnd_336152 : Nat := 4983230072969 + 3 ^ 40 * 336152 * 2
def baseEnd_336152 : Nat := 153428932418021366625841

theorem tailTrace_336152 : CollatzResearch.WordTrace tailWord_336152 prefixEnd_336152 153428932418021366625841 := by
  unfold tailWord_336152
  simp only [CollatzResearch.WordTrace]
  refine ⟨6130235339093094518025355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8173647118790792690700473 6130235339093094518025355)
  ·
    refine ⟨9195353008639641777038033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6130235339093094518025355 9195353008639641777038033)
    ·
      refine ⟨6896514756479731332778525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9195353008639641777038033 6896514756479731332778525)
      ·
        refine ⟨2586193033679899249791947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6896514756479731332778525 2586193033679899249791947)
        ·
          refine ⟨3879289550519848874687921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2586193033679899249791947 3879289550519848874687921)
          ·
            refine ⟨2909467162889886656015941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3879289550519848874687921 2909467162889886656015941)
            ·
              refine ⟨545525093041853748002989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2909467162889886656015941 545525093041853748002989)
              ·
                refine ⟨204571909890695155501121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 545525093041853748002989 204571909890695155501121)
                ·
                  refine ⟨153428932418021366625841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204571909890695155501121 153428932418021366625841)
                  ·
                    rfl

theorem cell20_336152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 2].length) (baseStart_336152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336152 prefixEnd_336152 := by exact prefixLift 336152
  have htrace : WordTrace (prefixWord ++ tailWord_336152) baseStart_336152 baseEnd_336152 := by
    simpa [prefixWord, tailWord_336152, baseEnd_336152] using wordTrace_append hprefix tailTrace_336152
  have hstable : (prefixWord ++ tailWord_336152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336152).length < 2 ^ (prefixWord ++ tailWord_336152).sum := by decide
  have hdescent : baseEnd_336152 < baseStart_336152 := by decide
  rcases family_descends (prefixWord ++ tailWord_336152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336156 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 8]
def baseStart_336156 : Nat := 118140960795 + 336156 * 2 ^ 59
def prefixEnd_336156 : Nat := 4983230072969 + 3 ^ 40 * 336156 * 2
def baseEnd_336156 : Nat := 153430758127015130492491

theorem tailTrace_336156 : CollatzResearch.WordTrace tailWord_336156 prefixEnd_336156 153430758127015130492491 := by
  unfold tailWord_336156
  simp only [CollatzResearch.WordTrace]
  refine ⟨6130308285085848859598161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8173744380114465146130881 6130308285085848859598161)
  ·
    refine ⟨4597731213814386644698621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6130308285085848859598161 4597731213814386644698621)
    ·
      refine ⟨1724149205180394991761983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4597731213814386644698621 1724149205180394991761983)
      ·
        refine ⟨2586223807770592487642975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1724149205180394991761983 2586223807770592487642975)
        ·
          refine ⟨3879335711655888731464463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2586223807770592487642975 3879335711655888731464463)
          ·
            refine ⟨5819003567483833097196695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3879335711655888731464463 5819003567483833097196695)
            ·
              refine ⟨8728505351225749645795043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5819003567483833097196695 8728505351225749645795043)
              ·
                refine ⟨13092758026838624468692565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8728505351225749645795043 13092758026838624468692565)
                ·
                  refine ⟨153430758127015130492491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13092758026838624468692565 153430758127015130492491)
                  ·
                    rfl

theorem cell20_336156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_336156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336156 prefixEnd_336156 := by exact prefixLift 336156
  have htrace : WordTrace (prefixWord ++ tailWord_336156) baseStart_336156 baseEnd_336156 := by
    simpa [prefixWord, tailWord_336156, baseEnd_336156] using wordTrace_append hprefix tailTrace_336156
  have hstable : (prefixWord ++ tailWord_336156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336156).length < 2 ^ (prefixWord ++ tailWord_336156).sum := by decide
  have hdescent : baseEnd_336156 < baseStart_336156 := by decide
  rcases family_descends (prefixWord ++ tailWord_336156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336163 : List Nat := [1, 1, 1, 4, 2, 2, 9]
def baseStart_336163 : Nat := 118140960795 + 336163 * 2 ^ 59
def prefixEnd_336163 : Nat := 4983230072969 + 3 ^ 40 * 336163 * 2
def baseEnd_336163 : Nat := 17048217013083801917681

theorem tailTrace_336163 : CollatzResearch.WordTrace tailWord_336163 prefixEnd_336163 17048217013083801917681 := by
  unfold tailWord_336163
  simp only [CollatzResearch.WordTrace]
  refine ⟨12260871881146337914701143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8173914587430891943134095 12260871881146337914701143)
  ·
    refine ⟨18391307821719506872051715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12260871881146337914701143 18391307821719506872051715)
    ·
      refine ⟨27586961732579260308077573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18391307821719506872051715 27586961732579260308077573)
      ·
        refine ⟨5172555324858611307764545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27586961732579260308077573 5172555324858611307764545)
        ·
          refine ⟨3879416493643958480823409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5172555324858611307764545 3879416493643958480823409)
          ·
            refine ⟨2909562370232968860617557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3879416493643958480823409 2909562370232968860617557)
            ·
              refine ⟨17048217013083801917681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2909562370232968860617557 17048217013083801917681)
              ·
                rfl

theorem cell20_336163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 9].length) (baseStart_336163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336163 prefixEnd_336163 := by exact prefixLift 336163
  have htrace : WordTrace (prefixWord ++ tailWord_336163) baseStart_336163 baseEnd_336163 := by
    simpa [prefixWord, tailWord_336163, baseEnd_336163] using wordTrace_append hprefix tailTrace_336163
  have hstable : (prefixWord ++ tailWord_336163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336163).length < 2 ^ (prefixWord ++ tailWord_336163).sum := by decide
  have hdescent : baseEnd_336163 < baseStart_336163 := by decide
  rcases family_descends (prefixWord ++ tailWord_336163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336193 : List Nat := [1, 2, 5, 2, 3, 1, 2, 4]
def baseStart_336193 : Nat := 118140960795 + 336193 * 2 ^ 59
def prefixEnd_336193 : Nat := 4983230072969 + 3 ^ 40 * 336193 * 2
def baseEnd_336193 : Nat := 51149215311735815419669

theorem tailTrace_336193 : CollatzResearch.WordTrace tailWord_336193 prefixEnd_336193 51149215311735815419669 := by
  unfold tailWord_336193
  simp only [CollatzResearch.WordTrace]
  refine ⟨12261966071037653038293233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8174644047358435358862155 12261966071037653038293233)
  ·
    refine ⟨9196474553278239778719925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12261966071037653038293233 9196474553278239778719925)
    ·
      refine ⟨862169489369834979254993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9196474553278239778719925 862169489369834979254993)
      ·
        refine ⟨646627117027376234441245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 862169489369834979254993 646627117027376234441245)
        ·
          refine ⟨242485168885266087915467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 646627117027376234441245 242485168885266087915467)
          ·
            refine ⟨363727753327899131873201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242485168885266087915467 363727753327899131873201)
            ·
              refine ⟨272795814995924348904901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363727753327899131873201 272795814995924348904901)
              ·
                refine ⟨51149215311735815419669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 272795814995924348904901 51149215311735815419669)
                ·
                  rfl

theorem cell20_336193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 4].length) (baseStart_336193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336193 prefixEnd_336193 := by exact prefixLift 336193
  have htrace : WordTrace (prefixWord ++ tailWord_336193) baseStart_336193 baseEnd_336193 := by
    simpa [prefixWord, tailWord_336193, baseEnd_336193] using wordTrace_append hprefix tailTrace_336193
  have hstable : (prefixWord ++ tailWord_336193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336193).length < 2 ^ (prefixWord ++ tailWord_336193).sum := by decide
  have hdescent : baseEnd_336193 < baseStart_336193 := by decide
  rcases family_descends (prefixWord ++ tailWord_336193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336211 : List Nat := [1, 1, 1, 2, 1, 1, 4, 7, 2]
def baseStart_336211 : Nat := 118140960795 + 336211 * 2 ^ 59
def prefixEnd_336211 : Nat := 4983230072969 + 3 ^ 40 * 336211 * 2
def baseEnd_336211 : Nat := 153455861625679383658933

theorem tailTrace_336211 : CollatzResearch.WordTrace tailWord_336211 prefixEnd_336211 153455861625679383658933 := by
  unfold tailWord_336211
  simp only [CollatzResearch.WordTrace]
  refine ⟨12262622584972442112448487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8175081723314961408298991 12262622584972442112448487)
  ·
    refine ⟨18393933877458663168672731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12262622584972442112448487 18393933877458663168672731)
    ·
      refine ⟨27590900816187994753009097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18393933877458663168672731 27590900816187994753009097)
      ·
        refine ⟨20693175612140996064756823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27590900816187994753009097 20693175612140996064756823)
        ·
          refine ⟨31039763418211494097135235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20693175612140996064756823 31039763418211494097135235)
          ·
            refine ⟨46559645127317241145702853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31039763418211494097135235 46559645127317241145702853)
            ·
              refine ⟨8729933461371982714819285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46559645127317241145702853 8729933461371982714819285)
              ·
                refine ⟨204607815500905844878577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8729933461371982714819285 204607815500905844878577)
                ·
                  refine ⟨153455861625679383658933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204607815500905844878577 153455861625679383658933)
                  ·
                    rfl

theorem cell20_336211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 2].length) (baseStart_336211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336211 prefixEnd_336211 := by exact prefixLift 336211
  have htrace : WordTrace (prefixWord ++ tailWord_336211) baseStart_336211 baseEnd_336211 := by
    simpa [prefixWord, tailWord_336211, baseEnd_336211] using wordTrace_append hprefix tailTrace_336211
  have hstable : (prefixWord ++ tailWord_336211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336211).length < 2 ^ (prefixWord ++ tailWord_336211).sum := by decide
  have hdescent : baseEnd_336211 < baseStart_336211 := by decide
  rcases family_descends (prefixWord ++ tailWord_336211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336242 : List Nat := [3, 2, 1, 2, 1, 4, 1, 3, 3]
def baseStart_336242 : Nat := 118140960795 + 336242 * 2 ^ 59
def prefixEnd_336242 : Nat := 4983230072969 + 3 ^ 40 * 336242 * 2
def baseEnd_336242 : Nat := 153470010870381053625473

theorem tailTrace_336242 : CollatzResearch.WordTrace tailWord_336242 prefixEnd_336242 153470010870381053625473 := by
  unfold tailWord_336242
  simp only [CollatzResearch.WordTrace]
  refine ⟨3065938311965033601706745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8175835498573422937884653 3065938311965033601706745)
  ·
    refine ⟨2299453733973775201280059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3065938311965033601706745 2299453733973775201280059)
    ·
      refine ⟨3449180600960662801920089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2299453733973775201280059 3449180600960662801920089)
      ·
        refine ⟨2586885450720497101440067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3449180600960662801920089 2586885450720497101440067)
        ·
          refine ⟨3880328176080745652160101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2586885450720497101440067 3880328176080745652160101)
          ·
            refine ⟨727561533015139809780019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3880328176080745652160101 727561533015139809780019)
            ·
              refine ⟨1091342299522709714670029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727561533015139809780019 1091342299522709714670029)
              ·
                refine ⟨409253362321016143001261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1091342299522709714670029 409253362321016143001261)
                ·
                  refine ⟨153470010870381053625473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 409253362321016143001261 153470010870381053625473)
                  ·
                    rfl

theorem cell20_336242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_336242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336242 prefixEnd_336242 := by exact prefixLift 336242
  have htrace : WordTrace (prefixWord ++ tailWord_336242) baseStart_336242 baseEnd_336242 := by
    simpa [prefixWord, tailWord_336242, baseEnd_336242] using wordTrace_append hprefix tailTrace_336242
  have hstable : (prefixWord ++ tailWord_336242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336242).length < 2 ^ (prefixWord ++ tailWord_336242).sum := by decide
  have hdescent : baseEnd_336242 < baseStart_336242 := by decide
  rcases family_descends (prefixWord ++ tailWord_336242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336280 : List Nat := [2, 1, 2, 5, 1, 1, 1, 4, 3]
def baseStart_336280 : Nat := 118140960795 + 336280 * 2 ^ 59
def prefixEnd_336280 : Nat := 4983230072969 + 3 ^ 40 * 336280 * 2
def baseEnd_336280 : Nat := 153487355105821810358651

theorem tailTrace_336280 : CollatzResearch.WordTrace tailWord_336280 prefixEnd_336280 153487355105821810358651 := by
  unfold tailWord_336280
  simp only [CollatzResearch.WordTrace]
  refine ⟨6132569610861233448355147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8176759481148311264473529 6132569610861233448355147)
  ·
    refine ⟨9198854416291850172532721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6132569610861233448355147 9198854416291850172532721)
    ·
      refine ⟨6899140812218887629399541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9198854416291850172532721 6899140812218887629399541)
      ·
        refine ⟨646794451145520715256207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6899140812218887629399541 646794451145520715256207)
        ·
          refine ⟨970191676718281072884311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 646794451145520715256207 970191676718281072884311)
          ·
            refine ⟨1455287515077421609326467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970191676718281072884311 1455287515077421609326467)
            ·
              refine ⟨2182931272616132413989701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1455287515077421609326467 2182931272616132413989701)
              ·
                refine ⟨409299613615524827623069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2182931272616132413989701 409299613615524827623069)
                ·
                  refine ⟨153487355105821810358651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 409299613615524827623069 153487355105821810358651)
                  ·
                    rfl

theorem cell20_336280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_336280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336280 prefixEnd_336280 := by exact prefixLift 336280
  have htrace : WordTrace (prefixWord ++ tailWord_336280) baseStart_336280 baseEnd_336280 := by
    simpa [prefixWord, tailWord_336280, baseEnd_336280] using wordTrace_append hprefix tailTrace_336280
  have hstable : (prefixWord ++ tailWord_336280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336280).length < 2 ^ (prefixWord ++ tailWord_336280).sum := by decide
  have hdescent : baseEnd_336280 < baseStart_336280 := by decide
  rcases family_descends (prefixWord ++ tailWord_336280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336332 : List Nat := [2, 2, 1, 4, 3, 1, 7]
def baseStart_336332 : Nat := 118140960795 + 336332 * 2 ^ 59
def prefixEnd_336332 : Nat := 4983230072969 + 3 ^ 40 * 336332 * 2
def baseEnd_336332 : Nat := 17056787702526748958345

theorem tailTrace_336332 : CollatzResearch.WordTrace tailWord_336332 prefixEnd_336332 17056787702526748958345 := by
  unfold tailWord_336332
  simp only [CollatzResearch.WordTrace]
  refine ⟨6133517908767039888801625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8178023878356053185068833 6133517908767039888801625)
  ·
    refine ⟨4600138431575279916601219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6133517908767039888801625 4600138431575279916601219)
    ·
      refine ⟨6900207647362919874901829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4600138431575279916601219 6900207647362919874901829)
      ·
        refine ⟨1293788933880547476544093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6900207647362919874901829 1293788933880547476544093)
        ·
          refine ⟨485170850205205303704035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1293788933880547476544093 485170850205205303704035)
          ·
            refine ⟨727756275307807955556053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485170850205205303704035 727756275307807955556053)
            ·
              refine ⟨17056787702526748958345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 727756275307807955556053 17056787702526748958345)
              ·
                rfl

theorem cell20_336332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 7].length) (baseStart_336332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336332 prefixEnd_336332 := by exact prefixLift 336332
  have htrace : WordTrace (prefixWord ++ tailWord_336332) baseStart_336332 baseEnd_336332 := by
    simpa [prefixWord, tailWord_336332, baseEnd_336332] using wordTrace_append hprefix tailTrace_336332
  have hstable : (prefixWord ++ tailWord_336332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336332).length < 2 ^ (prefixWord ++ tailWord_336332).sum := by decide
  have hdescent : baseEnd_336332 < baseStart_336332 := by decide
  rcases family_descends (prefixWord ++ tailWord_336332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336342 : List Nat := [5, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_336342 : Nat := 118140960795 + 336342 * 2 ^ 59
def prefixEnd_336342 : Nat := 4983230072969 + 3 ^ 40 * 336342 * 2
def baseEnd_336342 : Nat := 153515653595225150291731

theorem tailTrace_336342 : CollatzResearch.WordTrace tailWord_336342 prefixEnd_336342 153515653595225150291731 := by
  unfold tailWord_336342
  simp only [CollatzResearch.WordTrace]
  refine ⟨766712534218615717841705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8178267031665234323644853 766712534218615717841705)
  ·
    refine ⟨575034400663961788381279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 766712534218615717841705 575034400663961788381279)
    ·
      refine ⟨862551600995942682571919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 575034400663961788381279 862551600995942682571919)
      ·
        refine ⟨1293827401493914023857879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 862551600995942682571919 1293827401493914023857879)
        ·
          refine ⟨1940741102240871035786819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1293827401493914023857879 1940741102240871035786819)
          ·
            refine ⟨2911111653361306553680229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940741102240871035786819 2911111653361306553680229)
            ·
              refine ⟨545833435005244978815043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2911111653361306553680229 545833435005244978815043)
              ·
                refine ⟨818750152507867468222565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545833435005244978815043 818750152507867468222565)
                ·
                  refine ⟨153515653595225150291731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 818750152507867468222565 153515653595225150291731)
                  ·
                    rfl

theorem cell20_336342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_336342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336342 prefixEnd_336342 := by exact prefixLift 336342
  have htrace : WordTrace (prefixWord ++ tailWord_336342) baseStart_336342 baseEnd_336342 := by
    simpa [prefixWord, tailWord_336342, baseEnd_336342] using wordTrace_append hprefix tailTrace_336342
  have hstable : (prefixWord ++ tailWord_336342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336342).length < 2 ^ (prefixWord ++ tailWord_336342).sum := by decide
  have hdescent : baseEnd_336342 < baseStart_336342 := by decide
  rcases family_descends (prefixWord ++ tailWord_336342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336353 : List Nat := [1, 2, 3, 1, 2, 2, 2, 7]
def baseStart_336353 : Nat := 118140960795 + 336353 * 2 ^ 59
def prefixEnd_336353 : Nat := 4983230072969 + 3 ^ 40 * 336353 * 2
def baseEnd_336353 : Nat := 51173558098319333641673

theorem tailTrace_336353 : CollatzResearch.WordTrace tailWord_336353 prefixEnd_336353 51173558098319333641673 := by
  unfold tailWord_336353
  simp only [CollatzResearch.WordTrace]
  refine ⟨12267801750458000364117713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8178534500305333576078475 12267801750458000364117713)
  ·
    refine ⟨9200851312843500273088285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12267801750458000364117713 9200851312843500273088285)
    ·
      refine ⟨3450319242316312602408107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9200851312843500273088285 3450319242316312602408107)
      ·
        refine ⟨5175478863474468903612161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3450319242316312602408107 5175478863474468903612161)
        ·
          refine ⟨3881609147605851677709121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5175478863474468903612161 3881609147605851677709121)
          ·
            refine ⟨2911206860704388758281841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3881609147605851677709121 2911206860704388758281841)
            ·
              refine ⟨2183405145528291568711381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2911206860704388758281841 2183405145528291568711381)
              ·
                refine ⟨51173558098319333641673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2183405145528291568711381 51173558098319333641673)
                ·
                  rfl

theorem cell20_336353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 7].length) (baseStart_336353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336353 prefixEnd_336353 := by exact prefixLift 336353
  have htrace : WordTrace (prefixWord ++ tailWord_336353) baseStart_336353 baseEnd_336353 := by
    simpa [prefixWord, tailWord_336353, baseEnd_336353] using wordTrace_append hprefix tailTrace_336353
  have hstable : (prefixWord ++ tailWord_336353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336353).length < 2 ^ (prefixWord ++ tailWord_336353).sum := by decide
  have hdescent : baseEnd_336353 < baseStart_336353 := by decide
  rcases family_descends (prefixWord ++ tailWord_336353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336390 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_336390 : Nat := 118140960795 + 336390 * 2 ^ 59
def prefixEnd_336390 : Nat := 4983230072969 + 3 ^ 40 * 336390 * 2
def baseEnd_336390 : Nat := 153537562103150316691535

theorem tailTrace_336390 : CollatzResearch.WordTrace tailWord_336390 prefixEnd_336390 153537562103150316691535 := by
  unfold tailWord_336390
  simp only [CollatzResearch.WordTrace]
  refine ⟨383410976603873615100457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8179434167549303788809749 383410976603873615100457)
  ·
    refine ⟨287558232452905211325343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 383410976603873615100457 287558232452905211325343)
    ·
      refine ⟨431337348679357816988015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287558232452905211325343 431337348679357816988015)
      ·
        refine ⟨647006023019036725482023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431337348679357816988015 647006023019036725482023)
        ·
          refine ⟨970509034528555088223035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647006023019036725482023 970509034528555088223035)
          ·
            refine ⟨1455763551792832632334553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970509034528555088223035 1455763551792832632334553)
            ·
              refine ⟨1091822663844624474250915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1455763551792832632334553 1091822663844624474250915)
              ·
                refine ⟨1637733995766936711376373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1091822663844624474250915 1637733995766936711376373)
                ·
                  refine ⟨153537562103150316691535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1637733995766936711376373 153537562103150316691535)
                  ·
                    rfl

theorem cell20_336390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_336390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336390 prefixEnd_336390 := by exact prefixLift 336390
  have htrace : WordTrace (prefixWord ++ tailWord_336390) baseStart_336390 baseEnd_336390 := by
    simpa [prefixWord, tailWord_336390, baseEnd_336390] using wordTrace_append hprefix tailTrace_336390
  have hstable : (prefixWord ++ tailWord_336390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336390).length < 2 ^ (prefixWord ++ tailWord_336390).sum := by decide
  have hdescent : baseEnd_336390 < baseStart_336390 := by decide
  rcases family_descends (prefixWord ++ tailWord_336390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336397 : List Nat := [1, 7, 1, 1, 1, 1, 3, 1, 4]
def baseStart_336397 : Nat := 118140960795 + 336397 * 2 ^ 59
def prefixEnd_336397 : Nat := 4983230072969 + 3 ^ 40 * 336397 * 2
def baseEnd_336397 : Nat := 153540757093889403458173

theorem tailTrace_336397 : CollatzResearch.WordTrace tailWord_336397 prefixEnd_336397 153540757093889403458173 := by
  unfold tailWord_336397
  simp only [CollatzResearch.WordTrace]
  refine ⟨12269406562298595878719445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8179604374865730585812963 12269406562298595878719445)
  ·
    refine ⟨287564216303873340907487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 12269406562298595878719445 287564216303873340907487)
    ·
      refine ⟨431346324455810011361231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287564216303873340907487 431346324455810011361231)
      ·
        refine ⟨647019486683715017041847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431346324455810011361231 647019486683715017041847)
        ·
          refine ⟨970529230025572525562771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647019486683715017041847 970529230025572525562771)
          ·
            refine ⟨1455793845038358788344157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970529230025572525562771 1455793845038358788344157)
            ·
              refine ⟨545922691889384545629059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1455793845038358788344157 545922691889384545629059)
              ·
                refine ⟨818884037834076818443589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545922691889384545629059 818884037834076818443589)
                ·
                  refine ⟨153540757093889403458173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 818884037834076818443589 153540757093889403458173)
                  ·
                    rfl

theorem cell20_336397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_336397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336397 prefixEnd_336397 := by exact prefixLift 336397
  have htrace : WordTrace (prefixWord ++ tailWord_336397) baseStart_336397 baseEnd_336397 := by
    simpa [prefixWord, tailWord_336397, baseEnd_336397] using wordTrace_append hprefix tailTrace_336397
  have hstable : (prefixWord ++ tailWord_336397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336397).length < 2 ^ (prefixWord ++ tailWord_336397).sum := by decide
  have hdescent : baseEnd_336397 < baseStart_336397 := by decide
  rcases family_descends (prefixWord ++ tailWord_336397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336407 : List Nat := [1, 1, 3, 6, 2, 1, 2, 1, 3]
def baseStart_336407 : Nat := 118140960795 + 336407 * 2 ^ 59
def prefixEnd_336407 : Nat := 4983230072969 + 3 ^ 40 * 336407 * 2
def baseEnd_336407 : Nat := 153545321366373813124799

theorem tailTrace_336407 : CollatzResearch.WordTrace tailWord_336407 prefixEnd_336407 153545321366373813124799 := by
  unfold tailWord_336407
  simp only [CollatzResearch.WordTrace]
  refine ⟨12269771292262367586583475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8179847528174911724388983 12269771292262367586583475)
  ·
    refine ⟨18404656938393551379875213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12269771292262367586583475 18404656938393551379875213)
    ·
      refine ⟨6901746351897581767453205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18404656938393551379875213 6901746351897581767453205)
      ·
        refine ⟨323519360245199145349369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6901746351897581767453205 323519360245199145349369)
        ·
          refine ⟨242639520183899359012027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323519360245199145349369 242639520183899359012027)
          ·
            refine ⟨363959280275849038518041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242639520183899359012027 363959280275849038518041)
            ·
              refine ⟨272969460206886778888531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363959280275849038518041 272969460206886778888531)
              ·
                refine ⟨409454190310330168332797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272969460206886778888531 409454190310330168332797)
                ·
                  refine ⟨153545321366373813124799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 409454190310330168332797 153545321366373813124799)
                  ·
                    rfl

theorem cell20_336407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 3].length) (baseStart_336407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336407 prefixEnd_336407 := by exact prefixLift 336407
  have htrace : WordTrace (prefixWord ++ tailWord_336407) baseStart_336407 baseEnd_336407 := by
    simpa [prefixWord, tailWord_336407, baseEnd_336407] using wordTrace_append hprefix tailTrace_336407
  have hstable : (prefixWord ++ tailWord_336407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336407).length < 2 ^ (prefixWord ++ tailWord_336407).sum := by decide
  have hdescent : baseEnd_336407 < baseStart_336407 := by decide
  rcases family_descends (prefixWord ++ tailWord_336407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336408 : List Nat := [2, 1, 2, 3, 3, 2, 2, 5]
def baseStart_336408 : Nat := 118140960795 + 336408 * 2 ^ 59
def prefixEnd_336408 : Nat := 4983230072969 + 3 ^ 40 * 336408 * 2
def baseEnd_336408 : Nat := 51181925931207418030487

theorem tailTrace_336408 : CollatzResearch.WordTrace tailWord_336408 prefixEnd_336408 51181925931207418030487 := by
  unfold tailWord_336408
  simp only [CollatzResearch.WordTrace]
  refine ⟨6134903882629372378684939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8179871843505829838246585 6134903882629372378684939)
  ·
    refine ⟨9202355823944058568027409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6134903882629372378684939 9202355823944058568027409)
    ·
      refine ⟨6901766867958043926020557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9202355823944058568027409 6901766867958043926020557)
      ·
        refine ⟨2588162575484266472257709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6901766867958043926020557 2588162575484266472257709)
        ·
          refine ⟨970560965806599927096641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2588162575484266472257709 970560965806599927096641)
          ·
            refine ⟨727920724354949945322481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 970560965806599927096641 727920724354949945322481)
            ·
              refine ⟨545940543266212458991861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 727920724354949945322481 545940543266212458991861)
              ·
                refine ⟨51181925931207418030487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 545940543266212458991861 51181925931207418030487)
                ·
                  rfl

theorem cell20_336408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_336408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336408 prefixEnd_336408 := by exact prefixLift 336408
  have htrace : WordTrace (prefixWord ++ tailWord_336408) baseStart_336408 baseEnd_336408 := by
    simpa [prefixWord, tailWord_336408, baseEnd_336408] using wordTrace_append hprefix tailTrace_336408
  have hstable : (prefixWord ++ tailWord_336408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336408).length < 2 ^ (prefixWord ++ tailWord_336408).sum := by decide
  have hdescent : baseEnd_336408 < baseStart_336408 := by decide
  rcases family_descends (prefixWord ++ tailWord_336408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336439 : List Nat := [1, 1, 3, 1, 2, 3, 2, 5, 2]
def baseStart_336439 : Nat := 118140960795 + 336439 * 2 ^ 59
def prefixEnd_336439 : Nat := 4983230072969 + 3 ^ 40 * 336439 * 2
def baseEnd_336439 : Nat := 153559927038323924058001

theorem tailTrace_336439 : CollatzResearch.WordTrace tailWord_336439 prefixEnd_336439 153559927038323924058001 := by
  unfold tailWord_336439
  simp only [CollatzResearch.WordTrace]
  refine ⟨12270938428146437051748371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8180625618764291367832247 12270938428146437051748371)
  ·
    refine ⟨18406407642219655577622557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12270938428146437051748371 18406407642219655577622557)
    ·
      refine ⟨6902402865832370841608459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18406407642219655577622557 6902402865832370841608459)
      ·
        refine ⟨10353604298748556262412689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6902402865832370841608459 10353604298748556262412689)
        ·
          refine ⟨7765203224061417196809517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10353604298748556262412689 7765203224061417196809517)
          ·
            refine ⟨2911951209023031448803569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7765203224061417196809517 2911951209023031448803569)
            ·
              refine ⟨2183963406767273586602677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2911951209023031448803569 2183963406767273586602677)
              ·
                refine ⟨204746569384431898744001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2183963406767273586602677 204746569384431898744001)
                ·
                  refine ⟨153559927038323924058001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204746569384431898744001 153559927038323924058001)
                  ·
                    rfl

theorem cell20_336439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 2].length) (baseStart_336439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336439 prefixEnd_336439 := by exact prefixLift 336439
  have htrace : WordTrace (prefixWord ++ tailWord_336439) baseStart_336439 baseEnd_336439 := by
    simpa [prefixWord, tailWord_336439, baseEnd_336439] using wordTrace_append hprefix tailTrace_336439
  have hstable : (prefixWord ++ tailWord_336439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336439).length < 2 ^ (prefixWord ++ tailWord_336439).sum := by decide
  have hdescent : baseEnd_336439 < baseStart_336439 := by decide
  rcases family_descends (prefixWord ++ tailWord_336439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336446 : List Nat := [4, 2, 1, 4, 9]
def baseStart_336446 : Nat := 118140960795 + 336446 * 2 ^ 59
def prefixEnd_336446 : Nat := 4983230072969 + 3 ^ 40 * 336446 * 2
def baseEnd_336446 : Nat := 1895841012704481615119

theorem tailTrace_336446 : CollatzResearch.WordTrace tailWord_336446 prefixEnd_336446 1895841012704481615119 := by
  unfold tailWord_336446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1533899217390134655906649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8180795826080718164835461 1533899217390134655906649)
  ·
    refine ⟨1150424413042600991929987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1533899217390134655906649 1150424413042600991929987)
    ·
      refine ⟨1725636619563901487894981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1150424413042600991929987 1725636619563901487894981)
      ·
        refine ⟨323556866168231528980309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1725636619563901487894981 323556866168231528980309)
        ·
          refine ⟨1895841012704481615119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 323556866168231528980309 1895841012704481615119)
          ·
            rfl

theorem cell20_336446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 9].length) (baseStart_336446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336446 prefixEnd_336446 := by exact prefixLift 336446
  have htrace : WordTrace (prefixWord ++ tailWord_336446) baseStart_336446 baseEnd_336446 := by
    simpa [prefixWord, tailWord_336446, baseEnd_336446] using wordTrace_append hprefix tailTrace_336446
  have hstable : (prefixWord ++ tailWord_336446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336446).length < 2 ^ (prefixWord ++ tailWord_336446).sum := by decide
  have hdescent : baseEnd_336446 < baseStart_336446 := by decide
  rcases family_descends (prefixWord ++ tailWord_336446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336453 : List Nat := [1, 3, 1, 1, 1, 5, 1, 4, 3]
def baseStart_336453 : Nat := 118140960795 + 336453 * 2 ^ 59
def prefixEnd_336453 : Nat := 4983230072969 + 3 ^ 40 * 336453 * 2
def baseEnd_336453 : Nat := 153566317019802097591277

theorem tailTrace_336453 : CollatzResearch.WordTrace tailWord_336453 prefixEnd_336453 153566317019802097591277 := by
  unfold tailWord_336453
  simp only [CollatzResearch.WordTrace]
  refine ⟨12271449050095717442758013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8180966033397144961838675 12271449050095717442758013)
  ·
    refine ⟨4601793393785894041034255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12271449050095717442758013 4601793393785894041034255)
    ·
      refine ⟨6902690090678841061551383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4601793393785894041034255 6902690090678841061551383)
      ·
        refine ⟨10354035136018261592327075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6902690090678841061551383 10354035136018261592327075)
        ·
          refine ⟨15531052704027392388490613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10354035136018261592327075 15531052704027392388490613)
          ·
            refine ⟨1456036191002568036420995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15531052704027392388490613 1456036191002568036420995)
            ·
              refine ⟨2184054286503852054631493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1456036191002568036420995 2184054286503852054631493)
              ·
                refine ⟨409510178719472260243405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2184054286503852054631493 409510178719472260243405)
                ·
                  refine ⟨153566317019802097591277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 409510178719472260243405 153566317019802097591277)
                  ·
                    rfl

theorem cell20_336453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_336453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336453 prefixEnd_336453 := by exact prefixLift 336453
  have htrace : WordTrace (prefixWord ++ tailWord_336453) baseStart_336453 baseEnd_336453 := by
    simpa [prefixWord, tailWord_336453, baseEnd_336453] using wordTrace_append hprefix tailTrace_336453
  have hstable : (prefixWord ++ tailWord_336453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336453).length < 2 ^ (prefixWord ++ tailWord_336453).sum := by decide
  have hdescent : baseEnd_336453 < baseStart_336453 := by decide
  rcases family_descends (prefixWord ++ tailWord_336453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336460 : List Nat := [2, 2, 1, 3, 1, 2, 2, 3, 4]
def baseStart_336460 : Nat := 118140960795 + 336460 * 2 ^ 59
def prefixEnd_336460 : Nat := 4983230072969 + 3 ^ 40 * 336460 * 2
def baseEnd_336460 : Nat := 153569512010541184357915

theorem tailTrace_336460 : CollatzResearch.WordTrace tailWord_336460 prefixEnd_336460 153569512010541184357915 := by
  unfold tailWord_336460
  simp only [CollatzResearch.WordTrace]
  refine ⟨6135852180535178819131417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8181136240713571758841889 6135852180535178819131417)
  ·
    refine ⟨4601889135401384114348563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6135852180535178819131417 4601889135401384114348563)
    ·
      refine ⟨6902833703102076171522845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4601889135401384114348563 6902833703102076171522845)
      ·
        refine ⟨2588562638663278564321067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6902833703102076171522845 2588562638663278564321067)
        ·
          refine ⟨3882843957994917846481601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2588562638663278564321067 3882843957994917846481601)
          ·
            refine ⟨2912132968496188384861201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3882843957994917846481601 2912132968496188384861201)
            ·
              refine ⟨2184099726372141288645901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2912132968496188384861201 2184099726372141288645901)
              ·
                refine ⟨819037397389552983242213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2184099726372141288645901 819037397389552983242213)
                ·
                  refine ⟨153569512010541184357915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 819037397389552983242213 153569512010541184357915)
                  ·
                    rfl

theorem cell20_336460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_336460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336460 prefixEnd_336460 := by exact prefixLift 336460
  have htrace : WordTrace (prefixWord ++ tailWord_336460) baseStart_336460 baseEnd_336460 := by
    simpa [prefixWord, tailWord_336460, baseEnd_336460] using wordTrace_append hprefix tailTrace_336460
  have hstable : (prefixWord ++ tailWord_336460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336460).length < 2 ^ (prefixWord ++ tailWord_336460).sum := by decide
  have hdescent : baseEnd_336460 < baseStart_336460 := by decide
  rcases family_descends (prefixWord ++ tailWord_336460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336474 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_336474 : Nat := 118140960795 + 336474 * 2 ^ 59
def prefixEnd_336474 : Nat := 4983230072969 + 3 ^ 40 * 336474 * 2
def baseEnd_336474 : Nat := 153575901992019357891191

theorem tailTrace_336474 : CollatzResearch.WordTrace tailWord_336474 prefixEnd_336474 153575901992019357891191 := by
  unfold tailWord_336474
  simp only [CollatzResearch.WordTrace]
  refine ⟨3068053745754909507318119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8181476655346425352848317 3068053745754909507318119)
  ·
    refine ⟨4602080618632364260977179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3068053745754909507318119 4602080618632364260977179)
    ·
      refine ⟨6903120927948546391465769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4602080618632364260977179 6903120927948546391465769)
      ·
        refine ⟨5177340695961409793599327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6903120927948546391465769 5177340695961409793599327)
        ·
          refine ⟨7766011043942114690398991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5177340695961409793599327 7766011043942114690398991)
          ·
            refine ⟨11649016565913172035598487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7766011043942114690398991 11649016565913172035598487)
            ·
              refine ⟨17473524848869758053397731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11649016565913172035598487 17473524848869758053397731)
              ·
                refine ⟨26210287273304637080096597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17473524848869758053397731 26210287273304637080096597)
                ·
                  refine ⟨153575901992019357891191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26210287273304637080096597 153575901992019357891191)
                  ·
                    rfl

theorem cell20_336474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_336474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336474 prefixEnd_336474 := by exact prefixLift 336474
  have htrace : WordTrace (prefixWord ++ tailWord_336474) baseStart_336474 baseEnd_336474 := by
    simpa [prefixWord, tailWord_336474, baseEnd_336474] using wordTrace_append hprefix tailTrace_336474
  have hstable : (prefixWord ++ tailWord_336474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336474).length < 2 ^ (prefixWord ++ tailWord_336474).sum := by decide
  have hdescent : baseEnd_336474 < baseStart_336474 := by decide
  rcases family_descends (prefixWord ++ tailWord_336474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336484 : List Nat := [2, 3, 1, 1, 2, 2, 5, 4]
def baseStart_336484 : Nat := 118140960795 + 336484 * 2 ^ 59
def prefixEnd_336484 : Nat := 4983230072969 + 3 ^ 40 * 336484 * 2
def baseEnd_336484 : Nat := 51193488754834589185939

theorem tailTrace_336484 : CollatzResearch.WordTrace tailWord_336484 prefixEnd_336484 51193488754834589185939 := by
  unfold tailWord_336484
  simp only [CollatzResearch.WordTrace]
  refine ⟨6136289856491704868568253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8181719808655606491424337 6136289856491704868568253)
  ·
    refine ⟨2301108696184389325713095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6136289856491704868568253 2301108696184389325713095)
    ·
      refine ⟨3451663044276583988569643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2301108696184389325713095 3451663044276583988569643)
      ·
        refine ⟨5177494566414875982854465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3451663044276583988569643 5177494566414875982854465)
        ·
          refine ⟨3883120924811156987140849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5177494566414875982854465 3883120924811156987140849)
          ·
            refine ⟨2912340693608367740355637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3883120924811156987140849 2912340693608367740355637)
            ·
              refine ⟨273031940025784475658341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2912340693608367740355637 273031940025784475658341)
              ·
                refine ⟨51193488754834589185939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 273031940025784475658341 51193488754834589185939)
                ·
                  rfl

theorem cell20_336484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 4].length) (baseStart_336484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336484 prefixEnd_336484 := by exact prefixLift 336484
  have htrace : WordTrace (prefixWord ++ tailWord_336484) baseStart_336484 baseEnd_336484 := by
    simpa [prefixWord, tailWord_336484, baseEnd_336484] using wordTrace_append hprefix tailTrace_336484
  have hstable : (prefixWord ++ tailWord_336484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336484).length < 2 ^ (prefixWord ++ tailWord_336484).sum := by decide
  have hdescent : baseEnd_336484 < baseStart_336484 := by decide
  rcases family_descends (prefixWord ++ tailWord_336484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336494 : List Nat := [4, 1, 2, 2, 2, 1, 1, 5, 2]
def baseStart_336494 : Nat := 118140960795 + 336494 * 2 ^ 59
def prefixEnd_336494 : Nat := 4983230072969 + 3 ^ 40 * 336494 * 2
def baseEnd_336494 : Nat := 153585030536988177224443

theorem tailTrace_336494 : CollatzResearch.WordTrace tailWord_336494 prefixEnd_336494 153585030536988177224443 := by
  unfold tailWord_336494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1534118055368397680625067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8181962961964787630000357 1534118055368397680625067)
  ·
    refine ⟨2301177083052596520937601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1534118055368397680625067 2301177083052596520937601)
    ·
      refine ⟨1725882812289447390703201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2301177083052596520937601 1725882812289447390703201)
      ·
        refine ⟨1294412109217085543027401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1725882812289447390703201 1294412109217085543027401)
        ·
          refine ⟨970809081912814157270551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1294412109217085543027401 970809081912814157270551)
          ·
            refine ⟨1456213622869221235905827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970809081912814157270551 1456213622869221235905827)
            ·
              refine ⟨2184320434303831853858741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1456213622869221235905827 2184320434303831853858741)
              ·
                refine ⟨204780040715984236299257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2184320434303831853858741 204780040715984236299257)
                ·
                  refine ⟨153585030536988177224443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204780040715984236299257 153585030536988177224443)
                  ·
                    rfl

theorem cell20_336494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_336494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336494 prefixEnd_336494 := by exact prefixLift 336494
  have htrace : WordTrace (prefixWord ++ tailWord_336494) baseStart_336494 baseEnd_336494 := by
    simpa [prefixWord, tailWord_336494, baseEnd_336494] using wordTrace_append hprefix tailTrace_336494
  have hstable : (prefixWord ++ tailWord_336494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336494).length < 2 ^ (prefixWord ++ tailWord_336494).sum := by decide
  have hdescent : baseEnd_336494 < baseStart_336494 := by decide
  rcases family_descends (prefixWord ++ tailWord_336494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336505 : List Nat := [1, 2, 1, 3, 3, 3, 7]
def baseStart_336505 : Nat := 118140960795 + 336505 * 2 ^ 59
def prefixEnd_336505 : Nat := 4983230072969 + 3 ^ 40 * 336505 * 2
def baseEnd_336505 : Nat := 17065561248524558650859

theorem tailTrace_336505 : CollatzResearch.WordTrace tailWord_336505 prefixEnd_336505 17065561248524558650859 := by
  unfold tailWord_336505
  simp only [CollatzResearch.WordTrace]
  refine ⟨12273345645907330323650969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8182230430604886882433979 12273345645907330323650969)
  ·
    refine ⟨9205009234430497742738227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12273345645907330323650969 9205009234430497742738227)
    ·
      refine ⟨13807513851645746614107341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9205009234430497742738227 13807513851645746614107341)
      ·
        refine ⟨5177817694367154980290253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13807513851645746614107341 5177817694367154980290253)
        ·
          refine ⟨1941681635387683117608845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5177817694367154980290253 1941681635387683117608845)
          ·
            refine ⟨728130613270381169103317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1941681635387683117608845 728130613270381169103317)
            ·
              refine ⟨17065561248524558650859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 728130613270381169103317 17065561248524558650859)
              ·
                rfl

theorem cell20_336505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 7].length) (baseStart_336505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336505 prefixEnd_336505 := by exact prefixLift 336505
  have htrace : WordTrace (prefixWord ++ tailWord_336505) baseStart_336505 baseEnd_336505 := by
    simpa [prefixWord, tailWord_336505, baseEnd_336505] using wordTrace_append hprefix tailTrace_336505
  have hstable : (prefixWord ++ tailWord_336505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336505).length < 2 ^ (prefixWord ++ tailWord_336505).sum := by decide
  have hdescent : baseEnd_336505 < baseStart_336505 := by decide
  rcases family_descends (prefixWord ++ tailWord_336505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336515 : List Nat := [1, 1, 1, 3, 3, 1, 4, 4, 2]
def baseStart_336515 : Nat := 118140960795 + 336515 * 2 ^ 59
def prefixEnd_336515 : Nat := 4983230072969 + 3 ^ 40 * 336515 * 2
def baseEnd_336515 : Nat := 153594615509205437524357

theorem tailTrace_336515 : CollatzResearch.WordTrace tailWord_336515 prefixEnd_336515 153594615509205437524357 := by
  unfold tailWord_336515
  simp only [CollatzResearch.WordTrace]
  refine ⟨12273710375871102031514999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8182473583914068021009999 12273710375871102031514999)
  ·
    refine ⟨18410565563806653047272499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12273710375871102031514999 18410565563806653047272499)
    ·
      refine ⟨27615848345709979570908749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18410565563806653047272499 27615848345709979570908749)
      ·
        refine ⟨10355943129641242339090781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27615848345709979570908749 10355943129641242339090781)
        ·
          refine ⟨3883478673615465877159043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10355943129641242339090781 3883478673615465877159043)
          ·
            refine ⟨5825218010423198815738565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3883478673615465877159043 5825218010423198815738565)
            ·
              refine ⟨1092228376954349777950981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5825218010423198815738565 1092228376954349777950981)
              ·
                refine ⟨204792820678940583365809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1092228376954349777950981 204792820678940583365809)
                ·
                  refine ⟨153594615509205437524357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204792820678940583365809 153594615509205437524357)
                  ·
                    rfl

theorem cell20_336515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 2].length) (baseStart_336515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336515 prefixEnd_336515 := by exact prefixLift 336515
  have htrace : WordTrace (prefixWord ++ tailWord_336515) baseStart_336515 baseEnd_336515 := by
    simpa [prefixWord, tailWord_336515, baseEnd_336515] using wordTrace_append hprefix tailTrace_336515
  have hstable : (prefixWord ++ tailWord_336515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336515).length < 2 ^ (prefixWord ++ tailWord_336515).sum := by decide
  have hdescent : baseEnd_336515 < baseStart_336515 := by decide
  rcases family_descends (prefixWord ++ tailWord_336515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336536 : List Nat := [2, 1, 2, 4, 1, 1, 1, 4, 4]
def baseStart_336536 : Nat := 118140960795 + 336536 * 2 ^ 59
def prefixEnd_336536 : Nat := 4983230072969 + 3 ^ 40 * 336536 * 2
def baseEnd_336536 : Nat := 153604200481422697824271

theorem tailTrace_336536 : CollatzResearch.WordTrace tailWord_336536 prefixEnd_336536 153604200481422697824271 := by
  unfold tailWord_336536
  simp only [CollatzResearch.WordTrace]
  refine ⟨6137238154397511309014731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8182984205863348412019641 6137238154397511309014731)
  ·
    refine ⟨9205857231596266963522097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6137238154397511309014731 9205857231596266963522097)
    ·
      refine ⟨6904392923697200222641573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9205857231596266963522097 6904392923697200222641573)
      ·
        refine ⟨1294573673193225041745295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6904392923697200222641573 1294573673193225041745295)
        ·
          refine ⟨1941860509789837562617943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1294573673193225041745295 1941860509789837562617943)
          ·
            refine ⟨2912790764684756343926915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1941860509789837562617943 2912790764684756343926915)
            ·
              refine ⟨4369186147027134515890373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2912790764684756343926915 4369186147027134515890373)
              ·
                refine ⟨819222402567587721729445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4369186147027134515890373 819222402567587721729445)
                ·
                  refine ⟨153604200481422697824271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 819222402567587721729445 153604200481422697824271)
                  ·
                    rfl

theorem cell20_336536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_336536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336536 prefixEnd_336536 := by exact prefixLift 336536
  have htrace : WordTrace (prefixWord ++ tailWord_336536) baseStart_336536 baseEnd_336536 := by
    simpa [prefixWord, tailWord_336536, baseEnd_336536] using wordTrace_append hprefix tailTrace_336536
  have hstable : (prefixWord ++ tailWord_336536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336536).length < 2 ^ (prefixWord ++ tailWord_336536).sum := by decide
  have hdescent : baseEnd_336536 < baseStart_336536 := by decide
  rcases family_descends (prefixWord ++ tailWord_336536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336566 : List Nat := [5, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_336566 : Nat := 118140960795 + 336566 * 2 ^ 59
def prefixEnd_336566 : Nat := 4983230072969 + 3 ^ 40 * 336566 * 2
def baseEnd_336566 : Nat := 153617893298875926824149

theorem tailTrace_336566 : CollatzResearch.WordTrace tailWord_336566 prefixEnd_336566 153617893298875926824149 := by
  unfold tailWord_336566
  simp only [CollatzResearch.WordTrace]
  refine ⟨767223156167896108851347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8183713665790891827747701 767223156167896108851347)
  ·
    refine ⟨1150834734251844163277021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 767223156167896108851347 1150834734251844163277021)
    ·
      refine ⟨431563025344441561228883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1150834734251844163277021 431563025344441561228883)
      ·
        refine ⟨647344538016662341843325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431563025344441561228883 647344538016662341843325)
        ·
          refine ⟨242754201756248378191247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 647344538016662341843325 242754201756248378191247)
          ·
            refine ⟨364131302634372567286871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242754201756248378191247 364131302634372567286871)
            ·
              refine ⟨546196953951558850930307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364131302634372567286871 546196953951558850930307)
              ·
                refine ⟨819295430927338276395461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 546196953951558850930307 819295430927338276395461)
                ·
                  refine ⟨153617893298875926824149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 819295430927338276395461 153617893298875926824149)
                  ·
                    rfl

theorem cell20_336566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_336566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336566 prefixEnd_336566 := by exact prefixLift 336566
  have htrace : WordTrace (prefixWord ++ tailWord_336566) baseStart_336566 baseEnd_336566 := by
    simpa [prefixWord, tailWord_336566, baseEnd_336566] using wordTrace_append hprefix tailTrace_336566
  have hstable : (prefixWord ++ tailWord_336566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336566).length < 2 ^ (prefixWord ++ tailWord_336566).sum := by decide
  have hdescent : baseEnd_336566 < baseStart_336566 := by decide
  rcases family_descends (prefixWord ++ tailWord_336566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336570 : List Nat := [3, 1, 1, 1, 2, 3, 5, 2, 2]
def baseStart_336570 : Nat := 118140960795 + 336570 * 2 ^ 59
def prefixEnd_336570 : Nat := 4983230072969 + 3 ^ 40 * 336570 * 2
def baseEnd_336570 : Nat := 153619719007869690690799

theorem tailTrace_336570 : CollatzResearch.WordTrace tailWord_336570 prefixEnd_336570 153619719007869690690799 := by
  unfold tailWord_336570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3068929097667961606191791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8183810927114564283178109 3068929097667961606191791)
  ·
    refine ⟨4603393646501942409287687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3068929097667961606191791 4603393646501942409287687)
    ·
      refine ⟨6905090469752913613931531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4603393646501942409287687 6905090469752913613931531)
      ·
        refine ⟨10357635704629370420897297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6905090469752913613931531 10357635704629370420897297)
        ·
          refine ⟨7768226778472027815672973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10357635704629370420897297 7768226778472027815672973)
          ·
            refine ⟨2913085041927010430877365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7768226778472027815672973 2913085041927010430877365)
            ·
              refine ⟨273101722680657227894753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2913085041927010430877365 273101722680657227894753)
              ·
                refine ⟨204826292010492920921065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273101722680657227894753 204826292010492920921065)
                ·
                  refine ⟨153619719007869690690799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204826292010492920921065 153619719007869690690799)
                  ·
                    rfl

theorem cell20_336570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_336570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336570 prefixEnd_336570 := by exact prefixLift 336570
  have htrace : WordTrace (prefixWord ++ tailWord_336570) baseStart_336570 baseEnd_336570 := by
    simpa [prefixWord, tailWord_336570, baseEnd_336570] using wordTrace_append hprefix tailTrace_336570
  have hstable : (prefixWord ++ tailWord_336570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336570).length < 2 ^ (prefixWord ++ tailWord_336570).sum := by decide
  have hdescent : baseEnd_336570 < baseStart_336570 := by decide
  rcases family_descends (prefixWord ++ tailWord_336570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336584 : List Nat := [2, 1, 3, 1, 2, 3, 4, 1, 3]
def baseStart_336584 : Nat := 118140960795 + 336584 * 2 ^ 59
def prefixEnd_336584 : Nat := 4983230072969 + 3 ^ 40 * 336584 * 2
def baseEnd_336584 : Nat := 153626108989347864224075

theorem tailTrace_336584 : CollatzResearch.WordTrace tailWord_336584 prefixEnd_336584 153626108989347864224075 := by
  unfold tailWord_336584
  simp only [CollatzResearch.WordTrace]
  refine ⟨6138113506310563407888403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8184151341747417877184537 6138113506310563407888403)
  ·
    refine ⟨9207170259465845111832605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6138113506310563407888403 9207170259465845111832605)
    ·
      refine ⟨3452688847299691916937227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9207170259465845111832605 3452688847299691916937227)
      ·
        refine ⟨5179033270949537875405841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3452688847299691916937227 5179033270949537875405841)
        ·
          refine ⟨3884274953212153406554381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5179033270949537875405841 3884274953212153406554381)
          ·
            refine ⟨1456603107454557527457893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3884274953212153406554381 1456603107454557527457893)
            ·
              refine ⟨273113082647729536398355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1456603107454557527457893 273113082647729536398355)
              ·
                refine ⟨409669623971594304597533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273113082647729536398355 409669623971594304597533)
                ·
                  refine ⟨153626108989347864224075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 409669623971594304597533 153626108989347864224075)
                  ·
                    rfl

theorem cell20_336584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 3].length) (baseStart_336584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336584 prefixEnd_336584 := by exact prefixLift 336584
  have htrace : WordTrace (prefixWord ++ tailWord_336584) baseStart_336584 baseEnd_336584 := by
    simpa [prefixWord, tailWord_336584, baseEnd_336584] using wordTrace_append hprefix tailTrace_336584
  have hstable : (prefixWord ++ tailWord_336584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336584).length < 2 ^ (prefixWord ++ tailWord_336584).sum := by decide
  have hdescent : baseEnd_336584 < baseStart_336584 := by decide
  rcases family_descends (prefixWord ++ tailWord_336584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336622 : List Nat := [4, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_336622 : Nat := 118140960795 + 336622 * 2 ^ 59
def prefixEnd_336622 : Nat := 4983230072969 + 3 ^ 40 * 336622 * 2
def baseEnd_336622 : Nat := 153643453224788620957253

theorem tailTrace_336622 : CollatzResearch.WordTrace tailWord_336622 prefixEnd_336622 153643453224788620957253 := by
  unfold tailWord_336622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1534701623310432413207515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8185075324322306203773413 1534701623310432413207515)
  ·
    refine ⟨2302052434965648619811273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1534701623310432413207515 2302052434965648619811273)
    ·
      refine ⟨1726539326224236464858455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2302052434965648619811273 1726539326224236464858455)
      ·
        refine ⟨2589808989336354697287683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1726539326224236464858455 2589808989336354697287683)
        ·
          refine ⟨3884713484004532045931525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2589808989336354697287683 3884713484004532045931525)
          ·
            refine ⟨728383778250849758612161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3884713484004532045931525 728383778250849758612161)
            ·
              refine ⟨546287833688137318959121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 728383778250849758612161 546287833688137318959121)
              ·
                refine ⟨409715875266102989219341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 546287833688137318959121 409715875266102989219341)
                ·
                  refine ⟨153643453224788620957253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 409715875266102989219341 153643453224788620957253)
                  ·
                    rfl

theorem cell20_336622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_336622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336622 prefixEnd_336622 := by exact prefixLift 336622
  have htrace : WordTrace (prefixWord ++ tailWord_336622) baseStart_336622 baseEnd_336622 := by
    simpa [prefixWord, tailWord_336622, baseEnd_336622] using wordTrace_append hprefix tailTrace_336622
  have hstable : (prefixWord ++ tailWord_336622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336622).length < 2 ^ (prefixWord ++ tailWord_336622).sum := by decide
  have hdescent : baseEnd_336622 < baseStart_336622 := by decide
  rcases family_descends (prefixWord ++ tailWord_336622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336633 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 8]
def baseStart_336633 : Nat := 118140960795 + 336633 * 2 ^ 59
def prefixEnd_336633 : Nat := 4983230072969 + 3 ^ 40 * 336633 * 2
def baseEnd_336633 : Nat := 153648473924521471590541

theorem tailTrace_336633 : CollatzResearch.WordTrace tailWord_336633 prefixEnd_336633 153648473924521471590541 := by
  unfold tailWord_336633
  simp only [CollatzResearch.WordTrace]
  refine ⟨12278014189443608184310553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8185342792962405456207035 12278014189443608184310553)
  ·
    refine ⟨9208510642082706138232915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12278014189443608184310553 9208510642082706138232915)
    ·
      refine ⟨13812765963124059207349373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9208510642082706138232915 13812765963124059207349373)
      ·
        refine ⟨5179787236171522202756015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13812765963124059207349373 5179787236171522202756015)
        ·
          refine ⟨7769680854257283304134023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5179787236171522202756015 7769680854257283304134023)
          ·
            refine ⟨11654521281385924956201035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7769680854257283304134023 11654521281385924956201035)
            ·
              refine ⟨17481781922078887434301553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11654521281385924956201035 17481781922078887434301553)
              ·
                refine ⟨13111336441559165575726165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17481781922078887434301553 13111336441559165575726165)
                ·
                  refine ⟨153648473924521471590541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13111336441559165575726165 153648473924521471590541)
                  ·
                    rfl

theorem cell20_336633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_336633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336633 prefixEnd_336633 := by exact prefixLift 336633
  have htrace : WordTrace (prefixWord ++ tailWord_336633) baseStart_336633 baseEnd_336633 := by
    simpa [prefixWord, tailWord_336633, baseEnd_336633] using wordTrace_append hprefix tailTrace_336633
  have hstable : (prefixWord ++ tailWord_336633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336633).length < 2 ^ (prefixWord ++ tailWord_336633).sum := by decide
  have hdescent : baseEnd_336633 < baseStart_336633 := by decide
  rcases family_descends (prefixWord ++ tailWord_336633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336636 : List Nat := [2, 2, 2, 1, 3, 4, 1, 5]
def baseStart_336636 : Nat := 118140960795 + 336636 * 2 ^ 59
def prefixEnd_336636 : Nat := 4983230072969 + 3 ^ 40 * 336636 * 2
def baseEnd_336636 : Nat := 51216614402088931496843

theorem tailTrace_336636 : CollatzResearch.WordTrace tailWord_336636 prefixEnd_336636 51216614402088931496843 := by
  unfold tailWord_336636
  simp only [CollatzResearch.WordTrace]
  refine ⟨6139061804216369848334881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8185415738955159797779841 6139061804216369848334881)
  ·
    refine ⟨4604296353162277386251161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6139061804216369848334881 4604296353162277386251161)
    ·
      refine ⟨3453222264871708039688371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4604296353162277386251161 3453222264871708039688371)
      ·
        refine ⟨5179833397307562059532557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3453222264871708039688371 5179833397307562059532557)
        ·
          refine ⟨1942437523990335772324709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5179833397307562059532557 1942437523990335772324709)
          ·
            refine ⟨364207035748187957310883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1942437523990335772324709 364207035748187957310883)
            ·
              refine ⟨546310553622281935966325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364207035748187957310883 546310553622281935966325)
              ·
                refine ⟨51216614402088931496843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 546310553622281935966325 51216614402088931496843)
                ·
                  rfl

theorem cell20_336636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 5].length) (baseStart_336636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336636 prefixEnd_336636 := by exact prefixLift 336636
  have htrace : WordTrace (prefixWord ++ tailWord_336636) baseStart_336636 baseEnd_336636 := by
    simpa [prefixWord, tailWord_336636, baseEnd_336636] using wordTrace_append hprefix tailTrace_336636
  have hstable : (prefixWord ++ tailWord_336636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336636).length < 2 ^ (prefixWord ++ tailWord_336636).sum := by decide
  have hdescent : baseEnd_336636 < baseStart_336636 := by decide
  rcases family_descends (prefixWord ++ tailWord_336636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336650 : List Nat := [3, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_336650 : Nat := 118140960795 + 336650 * 2 ^ 59
def prefixEnd_336650 : Nat := 4983230072969 + 3 ^ 40 * 336650 * 2
def baseEnd_336650 : Nat := 153656233187744968023805

theorem tailTrace_336650 : CollatzResearch.WordTrace tailWord_336650 prefixEnd_336650 153656233187744968023805 := by
  unfold tailWord_336650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3069658557595505021919851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8185756153588013391786269 3069658557595505021919851)
  ·
    refine ⟨4604487836393257532879777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3069658557595505021919851 4604487836393257532879777)
    ·
      refine ⟨3453365877294943149659833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4604487836393257532879777 3453365877294943149659833)
      ·
        refine ⟨2590024407971207362244875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3453365877294943149659833 2590024407971207362244875)
        ·
          refine ⟨3885036611956811043367313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2590024407971207362244875 3885036611956811043367313)
          ·
            refine ⟨2913777458967608282525485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3885036611956811043367313 2913777458967608282525485)
            ·
              refine ⟨1092666547112853105947057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2913777458967608282525485 1092666547112853105947057)
              ·
                refine ⟨819499910334639829460293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1092666547112853105947057 819499910334639829460293)
                ·
                  refine ⟨153656233187744968023805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 819499910334639829460293 153656233187744968023805)
                  ·
                    rfl

theorem cell20_336650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_336650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336650 prefixEnd_336650 := by exact prefixLift 336650
  have htrace : WordTrace (prefixWord ++ tailWord_336650) baseStart_336650 baseEnd_336650 := by
    simpa [prefixWord, tailWord_336650, baseEnd_336650] using wordTrace_append hprefix tailTrace_336650
  have hstable : (prefixWord ++ tailWord_336650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336650).length < 2 ^ (prefixWord ++ tailWord_336650).sum := by decide
  have hdescent : baseEnd_336650 < baseStart_336650 := by decide
  rcases family_descends (prefixWord ++ tailWord_336650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336664 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 5]
def baseStart_336664 : Nat := 118140960795 + 336664 * 2 ^ 59
def prefixEnd_336664 : Nat := 4983230072969 + 3 ^ 40 * 336664 * 2
def baseEnd_336664 : Nat := 153662623169223141557081

theorem tailTrace_336664 : CollatzResearch.WordTrace tailWord_336664 prefixEnd_336664 153662623169223141557081 := by
  unfold tailWord_336664
  simp only [CollatzResearch.WordTrace]
  refine ⟨6139572426165650239344523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8186096568220866985792697 6139572426165650239344523)
  ·
    refine ⟨9209358639248475359016785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6139572426165650239344523 9209358639248475359016785)
    ·
      refine ⟨6907018979436356519262589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9209358639248475359016785 6907018979436356519262589)
      ·
        refine ⟨2590132117288633694723471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6907018979436356519262589 2590132117288633694723471)
        ·
          refine ⟨3885198175932950542085207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2590132117288633694723471 3885198175932950542085207)
          ·
            refine ⟨5827797263899425813127811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3885198175932950542085207 5827797263899425813127811)
            ·
              refine ⟨8741695895849138719691717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5827797263899425813127811 8741695895849138719691717)
              ·
                refine ⟨1639067980471713509942197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8741695895849138719691717 1639067980471713509942197)
                ·
                  refine ⟨153662623169223141557081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1639067980471713509942197 153662623169223141557081)
                  ·
                    rfl

theorem cell20_336664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_336664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336664 prefixEnd_336664 := by exact prefixLift 336664
  have htrace : WordTrace (prefixWord ++ tailWord_336664) baseStart_336664 baseEnd_336664 := by
    simpa [prefixWord, tailWord_336664, baseEnd_336664] using wordTrace_append hprefix tailTrace_336664
  have hstable : (prefixWord ++ tailWord_336664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336664).length < 2 ^ (prefixWord ++ tailWord_336664).sum := by decide
  have hdescent : baseEnd_336664 < baseStart_336664 := by decide
  rcases family_descends (prefixWord ++ tailWord_336664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336694 : List Nat := [5, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_336694 : Nat := 118140960795 + 336694 * 2 ^ 59
def prefixEnd_336694 : Nat := 4983230072969 + 3 ^ 40 * 336694 * 2
def baseEnd_336694 : Nat := 153676315986676370556959

theorem tailTrace_336694 : CollatzResearch.WordTrace tailWord_336694 prefixEnd_336694 153676315986676370556959 := by
  unfold tailWord_336694
  simp only [CollatzResearch.WordTrace]
  refine ⟨767514940138913475142571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8186826028148410401520757 767514940138913475142571)
  ·
    refine ⟨1151272410208370212713857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 767514940138913475142571 1151272410208370212713857)
    ·
      refine ⟨863454307656277659535393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1151272410208370212713857 863454307656277659535393)
      ·
        refine ⟨647590730742208244651545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 863454307656277659535393 647590730742208244651545)
        ·
          refine ⟨485693048056656183488659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 647590730742208244651545 485693048056656183488659)
          ·
            refine ⟨728539572084984275232989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485693048056656183488659 728539572084984275232989)
            ·
              refine ⟨273202339531869103212371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 728539572084984275232989 273202339531869103212371)
              ·
                refine ⟨409803509297803654818557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273202339531869103212371 409803509297803654818557)
                ·
                  refine ⟨153676315986676370556959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 409803509297803654818557 153676315986676370556959)
                  ·
                    rfl

theorem cell20_336694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_336694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336694 prefixEnd_336694 := by exact prefixLift 336694
  have htrace : WordTrace (prefixWord ++ tailWord_336694) baseStart_336694 baseEnd_336694 := by
    simpa [prefixWord, tailWord_336694, baseEnd_336694] using wordTrace_append hprefix tailTrace_336694
  have hstable : (prefixWord ++ tailWord_336694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336694).length < 2 ^ (prefixWord ++ tailWord_336694).sum := by decide
  have hdescent : baseEnd_336694 < baseStart_336694 := by decide
  rcases family_descends (prefixWord ++ tailWord_336694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336709 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 6]
def baseStart_336709 : Nat := 118140960795 + 336709 * 2 ^ 59
def prefixEnd_336709 : Nat := 4983230072969 + 3 ^ 40 * 336709 * 2
def baseEnd_336709 : Nat := 153683162395402985056897

theorem tailTrace_336709 : CollatzResearch.WordTrace tailWord_336709 prefixEnd_336709 153683162395402985056897 := by
  unfold tailWord_336709
  simp only [CollatzResearch.WordTrace]
  refine ⟨12280786137168273164077181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8187190758112182109384787 12280786137168273164077181)
  ·
    refine ⟨4605294801438102436528943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12280786137168273164077181 4605294801438102436528943)
    ·
      refine ⟨6907942202157153654793415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4605294801438102436528943 6907942202157153654793415)
      ·
        refine ⟨10361913303235730482190123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6907942202157153654793415 10361913303235730482190123)
        ·
          refine ⟨15542869954853595723285185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10361913303235730482190123 15542869954853595723285185)
          ·
            refine ⟨11657152466140196792463889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15542869954853595723285185 11657152466140196792463889)
            ·
              refine ⟨8742864349605147594347917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11657152466140196792463889 8742864349605147594347917)
              ·
                refine ⟨3278574131101930347880469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8742864349605147594347917 3278574131101930347880469)
                ·
                  refine ⟨153683162395402985056897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3278574131101930347880469 153683162395402985056897)
                  ·
                    rfl

theorem cell20_336709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_336709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336709 prefixEnd_336709 := by exact prefixLift 336709
  have htrace : WordTrace (prefixWord ++ tailWord_336709) baseStart_336709 baseEnd_336709 := by
    simpa [prefixWord, tailWord_336709, baseEnd_336709] using wordTrace_append hprefix tailTrace_336709
  have hstable : (prefixWord ++ tailWord_336709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336709).length < 2 ^ (prefixWord ++ tailWord_336709).sum := by decide
  have hdescent : baseEnd_336709 < baseStart_336709 := by decide
  rcases family_descends (prefixWord ++ tailWord_336709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336743 : List Nat := [1, 1, 5, 1, 2, 4, 1, 1, 4]
def baseStart_336743 : Nat := 118140960795 + 336743 * 2 ^ 59
def prefixEnd_336743 : Nat := 4983230072969 + 3 ^ 40 * 336743 * 2
def baseEnd_336743 : Nat := 153698680921849977923425

theorem tailTrace_336743 : CollatzResearch.WordTrace tailWord_336743 prefixEnd_336743 153698680921849977923425 := by
  unfold tailWord_336743
  simp only [CollatzResearch.WordTrace]
  refine ⟨12282026219045096970814883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8188017479363397980543255 12282026219045096970814883)
  ·
    refine ⟨18423039328567645456222325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12282026219045096970814883 18423039328567645456222325)
    ·
      refine ⟨1727159937053216761520843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18423039328567645456222325 1727159937053216761520843)
      ·
        refine ⟨2590739905579825142281265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1727159937053216761520843 2590739905579825142281265)
        ·
          refine ⟨1943054929184868856710949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2590739905579825142281265 1943054929184868856710949)
          ·
            refine ⟨364322799222162910633303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1943054929184868856710949 364322799222162910633303)
            ·
              refine ⟨546484198833244365949955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364322799222162910633303 546484198833244365949955)
              ·
                refine ⟨819726298249866548924933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 546484198833244365949955 819726298249866548924933)
                ·
                  refine ⟨153698680921849977923425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 819726298249866548924933 153698680921849977923425)
                  ·
                    rfl

theorem cell20_336743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 4].length) (baseStart_336743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336743 prefixEnd_336743 := by exact prefixLift 336743
  have htrace : WordTrace (prefixWord ++ tailWord_336743) baseStart_336743 baseEnd_336743 := by
    simpa [prefixWord, tailWord_336743, baseEnd_336743] using wordTrace_append hprefix tailTrace_336743
  have hstable : (prefixWord ++ tailWord_336743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336743).length < 2 ^ (prefixWord ++ tailWord_336743).sum := by decide
  have hdescent : baseEnd_336743 < baseStart_336743 := by decide
  rcases family_descends (prefixWord ++ tailWord_336743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336792 : List Nat := [2, 1, 2, 15]
def baseStart_336792 : Nat := 118140960795 + 336792 * 2 ^ 59
def prefixEnd_336792 : Nat := 4983230072969 + 3 ^ 40 * 336792 * 2
def baseEnd_336792 : Nat := 632596896530961256337

theorem tailTrace_336792 : CollatzResearch.WordTrace tailWord_336792 prefixEnd_336792 632596896530961256337 := by
  unfold tailWord_336792
  simp only [CollatzResearch.WordTrace]
  refine ⟨6141906697933789169674315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8189208930578385559565753 6141906697933789169674315)
  ·
    refine ⟨9212860046900683754511473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6141906697933789169674315 9212860046900683754511473)
    ·
      refine ⟨6909645035175512815883605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9212860046900683754511473 6909645035175512815883605)
      ·
        refine ⟨632596896530961256337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 6909645035175512815883605 632596896530961256337)
        ·
          rfl

theorem cell20_336792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 15].length) (baseStart_336792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336792 prefixEnd_336792 := by exact prefixLift 336792
  have htrace : WordTrace (prefixWord ++ tailWord_336792) baseStart_336792 baseEnd_336792 := by
    simpa [prefixWord, tailWord_336792, baseEnd_336792] using wordTrace_append hprefix tailTrace_336792
  have hstable : (prefixWord ++ tailWord_336792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336792).length < 2 ^ (prefixWord ++ tailWord_336792).sum := by decide
  have hdescent : baseEnd_336792 < baseStart_336792 := by decide
  rcases family_descends (prefixWord ++ tailWord_336792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336794 : List Nat := [3, 1, 1, 4, 4, 1, 2, 2, 2]
def baseStart_336794 : Nat := 118140960795 + 336794 * 2 ^ 59
def prefixEnd_336794 : Nat := 4983230072969 + 3 ^ 40 * 336794 * 2
def baseEnd_336794 : Nat := 153721958711520467223217

theorem tailTrace_336794 : CollatzResearch.WordTrace tailWord_336794 prefixEnd_336794 153721958711520467223217 := by
  unfold tailWord_336794
  simp only [CollatzResearch.WordTrace]
  refine ⟨3070971585465083170230359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8189257561240221787280957 3070971585465083170230359)
  ·
    refine ⟨4606457378197624755345539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3070971585465083170230359 4606457378197624755345539)
    ·
      refine ⟨6909686067296437133018309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4606457378197624755345539 6909686067296437133018309)
      ·
        refine ⟨1295566137618081962440933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6909686067296437133018309 1295566137618081962440933)
        ·
          refine ⟨242918650803390367957675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1295566137618081962440933 242918650803390367957675)
          ·
            refine ⟨364377976205085551936513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242918650803390367957675 364377976205085551936513)
            ·
              refine ⟨273283482153814163952385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 364377976205085551936513 273283482153814163952385)
              ·
                refine ⟨204962611615360622964289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273283482153814163952385 204962611615360622964289)
                ·
                  refine ⟨153721958711520467223217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204962611615360622964289 153721958711520467223217)
                  ·
                    rfl

theorem cell20_336794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_336794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336794 prefixEnd_336794 := by exact prefixLift 336794
  have htrace : WordTrace (prefixWord ++ tailWord_336794) baseStart_336794 baseEnd_336794 := by
    simpa [prefixWord, tailWord_336794, baseEnd_336794] using wordTrace_append hprefix tailTrace_336794
  have hstable : (prefixWord ++ tailWord_336794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336794).length < 2 ^ (prefixWord ++ tailWord_336794).sum := by decide
  have hdescent : baseEnd_336794 < baseStart_336794 := by decide
  rcases family_descends (prefixWord ++ tailWord_336794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336823 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 6]
def baseStart_336823 : Nat := 118140960795 + 336823 * 2 ^ 59
def prefixEnd_336823 : Nat := 4983230072969 + 3 ^ 40 * 336823 * 2
def baseEnd_336823 : Nat := 153735195101725255256431

theorem tailTrace_336823 : CollatzResearch.WordTrace tailWord_336823 prefixEnd_336823 153735195101725255256431 := by
  unfold tailWord_336823
  simp only [CollatzResearch.WordTrace]
  refine ⟨12284944058755270633727123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8189962705836847089151415 12284944058755270633727123)
  ·
    refine ⟨18427416088132905950590685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12284944058755270633727123 18427416088132905950590685)
    ·
      refine ⟨6910281033049839731471507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18427416088132905950590685 6910281033049839731471507)
      ·
        refine ⟨10365421549574759597207261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6910281033049839731471507 10365421549574759597207261)
        ·
          refine ⟨3887033081090534848952723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10365421549574759597207261 3887033081090534848952723)
          ·
            refine ⟨5830549621635802273429085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3887033081090534848952723 5830549621635802273429085)
            ·
              refine ⟨2186456108113425852535907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5830549621635802273429085 2186456108113425852535907)
              ·
                refine ⟨3279684162170138778803861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2186456108113425852535907 3279684162170138778803861)
                ·
                  refine ⟨153735195101725255256431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3279684162170138778803861 153735195101725255256431)
                  ·
                    rfl

theorem cell20_336823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_336823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336823 prefixEnd_336823 := by exact prefixLift 336823
  have htrace : WordTrace (prefixWord ++ tailWord_336823) baseStart_336823 baseEnd_336823 := by
    simpa [prefixWord, tailWord_336823, baseEnd_336823] using wordTrace_append hprefix tailTrace_336823
  have hstable : (prefixWord ++ tailWord_336823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336823).length < 2 ^ (prefixWord ++ tailWord_336823).sum := by decide
  have hdescent : baseEnd_336823 < baseStart_336823 := by decide
  rcases family_descends (prefixWord ++ tailWord_336823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336850 : List Nat := [3, 2, 2, 3, 1, 1, 3, 2, 3]
def baseStart_336850 : Nat := 118140960795 + 336850 * 2 ^ 59
def prefixEnd_336850 : Nat := 4983230072969 + 3 ^ 40 * 336850 * 2
def baseEnd_336850 : Nat := 153747518637433161356321

theorem tailTrace_336850 : CollatzResearch.WordTrace tailWord_336850 prefixEnd_336850 153747518637433161356321 := by
  unfold tailWord_336850
  simp only [CollatzResearch.WordTrace]
  refine ⟨3071482207414363561240001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8190619219771636163306669 3071482207414363561240001)
  ·
    refine ⟨2303611655560772670930001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3071482207414363561240001 2303611655560772670930001)
    ·
      refine ⟨1727708741670579503197501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2303611655560772670930001 1727708741670579503197501)
      ·
        refine ⟨647890778126467313699063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1727708741670579503197501 647890778126467313699063)
        ·
          refine ⟨971836167189700970548595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647890778126467313699063 971836167189700970548595)
          ·
            refine ⟨1457754250784551455822893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971836167189700970548595 1457754250784551455822893)
            ·
              refine ⟨546657844044206795933585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1457754250784551455822893 546657844044206795933585)
              ·
                refine ⟨409993383033155096950189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 546657844044206795933585 409993383033155096950189)
                ·
                  refine ⟨153747518637433161356321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 409993383033155096950189 153747518637433161356321)
                  ·
                    rfl

theorem cell20_336850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_336850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336850 prefixEnd_336850 := by exact prefixLift 336850
  have htrace : WordTrace (prefixWord ++ tailWord_336850) baseStart_336850 baseEnd_336850 := by
    simpa [prefixWord, tailWord_336850, baseEnd_336850] using wordTrace_append hprefix tailTrace_336850
  have hstable : (prefixWord ++ tailWord_336850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336850).length < 2 ^ (prefixWord ++ tailWord_336850).sum := by decide
  have hdescent : baseEnd_336850 < baseStart_336850 := by decide
  rcases family_descends (prefixWord ++ tailWord_336850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336857 : List Nat := [1, 2, 1, 2, 5, 1, 2, 4, 2]
def baseStart_336857 : Nat := 118140960795 + 336857 * 2 ^ 59
def prefixEnd_336857 : Nat := 4983230072969 + 3 ^ 40 * 336857 * 2
def baseEnd_336857 : Nat := 153750713628172248122959

theorem tailTrace_336857 : CollatzResearch.WordTrace tailWord_336857 prefixEnd_336857 153750713628172248122959 := by
  unfold tailWord_336857
  simp only [CollatzResearch.WordTrace]
  refine ⟨12286184140632094440464825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8190789427088062960309883 12286184140632094440464825)
  ·
    refine ⟨9214638105474070830348619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12286184140632094440464825 9214638105474070830348619)
    ·
      refine ⟨13821957158211106245522929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9214638105474070830348619 13821957158211106245522929)
      ·
        refine ⟨10366467868658329684142197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13821957158211106245522929 10366467868658329684142197)
        ·
          refine ⟨971856362686718407888331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10366467868658329684142197 971856362686718407888331)
          ·
            refine ⟨1457784544030077611832497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971856362686718407888331 1457784544030077611832497)
            ·
              refine ⟨1093338408022558208874373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1457784544030077611832497 1093338408022558208874373)
              ·
                refine ⟨205000951504229664163945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1093338408022558208874373 205000951504229664163945)
                ·
                  refine ⟨153750713628172248122959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205000951504229664163945 153750713628172248122959)
                  ·
                    rfl

theorem cell20_336857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 2].length) (baseStart_336857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336857 prefixEnd_336857 := by exact prefixLift 336857
  have htrace : WordTrace (prefixWord ++ tailWord_336857) baseStart_336857 baseEnd_336857 := by
    simpa [prefixWord, tailWord_336857, baseEnd_336857] using wordTrace_append hprefix tailTrace_336857
  have hstable : (prefixWord ++ tailWord_336857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336857).length < 2 ^ (prefixWord ++ tailWord_336857).sum := by decide
  have hdescent : baseEnd_336857 < baseStart_336857 := by decide
  rcases family_descends (prefixWord ++ tailWord_336857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336892 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 5]
def baseStart_336892 : Nat := 118140960795 + 336892 * 2 ^ 59
def prefixEnd_336892 : Nat := 4983230072969 + 3 ^ 40 * 336892 * 2
def baseEnd_336892 : Nat := 153766688581867681956149

theorem tailTrace_336892 : CollatzResearch.WordTrace tailWord_336892 prefixEnd_336892 153766688581867681956149 := by
  unfold tailWord_336892
  simp only [CollatzResearch.WordTrace]
  refine ⟨6143730347752647708994465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8191640463670196945325953 6143730347752647708994465)
  ·
    refine ⟨4607797760814485781745849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6143730347752647708994465 4607797760814485781745849)
    ·
      refine ⟨3455848320610864336309387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4607797760814485781745849 3455848320610864336309387)
      ·
        refine ⟨5183772480916296504464081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3455848320610864336309387 5183772480916296504464081)
        ·
          refine ⟨3887829360687222378348061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5183772480916296504464081 3887829360687222378348061)
          ·
            refine ⟨1457936010257708391880523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3887829360687222378348061 1457936010257708391880523)
            ·
              refine ⟨2186904015386562587820785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457936010257708391880523 2186904015386562587820785)
              ·
                refine ⟨1640178011539921940865589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2186904015386562587820785 1640178011539921940865589)
                ·
                  refine ⟨153766688581867681956149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1640178011539921940865589 153766688581867681956149)
                  ·
                    rfl

theorem cell20_336892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_336892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336892 prefixEnd_336892 := by exact prefixLift 336892
  have htrace : WordTrace (prefixWord ++ tailWord_336892) baseStart_336892 baseEnd_336892 := by
    simpa [prefixWord, tailWord_336892, baseEnd_336892] using wordTrace_append hprefix tailTrace_336892
  have hstable : (prefixWord ++ tailWord_336892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336892).length < 2 ^ (prefixWord ++ tailWord_336892).sum := by decide
  have hdescent : baseEnd_336892 < baseStart_336892 := by decide
  rcases family_descends (prefixWord ++ tailWord_336892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336898 : List Nat := [3, 4, 1, 3, 2, 1, 6]
def baseStart_336898 : Nat := 118140960795 + 336898 * 2 ^ 59
def prefixEnd_336898 : Nat := 4983230072969 + 3 ^ 40 * 336898 * 2
def baseEnd_336898 : Nat := 17085491905039814195125

theorem tailTrace_336898 : CollatzResearch.WordTrace tailWord_336898 prefixEnd_336898 17085491905039814195125 := by
  unfold tailWord_336898
  simp only [CollatzResearch.WordTrace]
  refine ⟨3071919883370889610676837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8191786355655705628471565 3071919883370889610676837)
  ·
    refine ⟨575984978132041802001907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3071919883370889610676837 575984978132041802001907)
    ·
      refine ⟨863977467198062703002861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 575984978132041802001907 863977467198062703002861)
      ·
        refine ⟨323991550199273513626073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 863977467198062703002861 323991550199273513626073)
        ·
          refine ⟨242993662649455135219555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323991550199273513626073 242993662649455135219555)
          ·
            refine ⟨364490493974182702829333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242993662649455135219555 364490493974182702829333)
            ·
              refine ⟨17085491905039814195125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 364490493974182702829333 17085491905039814195125)
              ·
                rfl

theorem cell20_336898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 6].length) (baseStart_336898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336898 prefixEnd_336898 := by exact prefixLift 336898
  have htrace : WordTrace (prefixWord ++ tailWord_336898) baseStart_336898 baseEnd_336898 := by
    simpa [prefixWord, tailWord_336898, baseEnd_336898] using wordTrace_append hprefix tailTrace_336898
  have hstable : (prefixWord ++ tailWord_336898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336898).length < 2 ^ (prefixWord ++ tailWord_336898).sum := by decide
  have hdescent : baseEnd_336898 < baseStart_336898 := by decide
  rcases family_descends (prefixWord ++ tailWord_336898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336944 : List Nat := [2, 1, 1, 1, 2, 4, 1, 8]
def baseStart_336944 : Nat := 118140960795 + 336944 * 2 ^ 59
def prefixEnd_336944 : Nat := 4983230072969 + 3 ^ 40 * 336944 * 2
def baseEnd_336944 : Nat := 51263474266262204074201

theorem tailTrace_336944 : CollatzResearch.WordTrace tailWord_336944 prefixEnd_336944 51263474266262204074201 := by
  unfold tailWord_336944
  simp only [CollatzResearch.WordTrace]
  refine ⟨6144678645658454149440943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8192904860877938865921257 6144678645658454149440943)
  ·
    refine ⟨9217017968487681224161415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6144678645658454149440943 9217017968487681224161415)
    ·
      refine ⟨13825526952731521836242123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9217017968487681224161415 13825526952731521836242123)
      ·
        refine ⟨20738290429097282754363185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13825526952731521836242123 20738290429097282754363185)
        ·
          refine ⟨15553717821822962065772389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20738290429097282754363185 15553717821822962065772389)
          ·
            refine ⟨2916322091591805387332323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15553717821822962065772389 2916322091591805387332323)
            ·
              refine ⟨4374483137387708080998485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2916322091591805387332323 4374483137387708080998485)
              ·
                refine ⟨51263474266262204074201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4374483137387708080998485 51263474266262204074201)
                ·
                  rfl

theorem cell20_336944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_336944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336944 prefixEnd_336944 := by exact prefixLift 336944
  have htrace : WordTrace (prefixWord ++ tailWord_336944) baseStart_336944 baseEnd_336944 := by
    simpa [prefixWord, tailWord_336944, baseEnd_336944] using wordTrace_append hprefix tailTrace_336944
  have hstable : (prefixWord ++ tailWord_336944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336944).length < 2 ^ (prefixWord ++ tailWord_336944).sum := by decide
  have hdescent : baseEnd_336944 < baseStart_336944 := by decide
  rcases family_descends (prefixWord ++ tailWord_336944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336961 : List Nat := [1, 2, 5, 1, 3, 8]
def baseStart_336961 : Nat := 118140960795 + 336961 * 2 ^ 59
def prefixEnd_336961 : Nat := 4983230072969 + 3 ^ 40 * 336961 * 2
def baseEnd_336961 : Nat := 5696228965259633653921

theorem tailTrace_336961 : CollatzResearch.WordTrace tailWord_336961 prefixEnd_336961 5696228965259633653921 := by
  unfold tailWord_336961
  simp only [CollatzResearch.WordTrace]
  refine ⟨12289977332255320202250737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8193318221503546801500491 12289977332255320202250737)
  ·
    refine ⟨9217482999191490151688053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12289977332255320202250737 9217482999191490151688053)
    ·
      refine ⟨864139031174202201720755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9217482999191490151688053 864139031174202201720755)
      ·
        refine ⟨1296208546761303302581133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 864139031174202201720755 1296208546761303302581133)
        ·
          refine ⟨486078205035488738467925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1296208546761303302581133 486078205035488738467925)
          ·
            refine ⟨5696228965259633653921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 486078205035488738467925 5696228965259633653921)
            ·
              rfl

theorem cell20_336961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 8].length) (baseStart_336961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336961 prefixEnd_336961 := by exact prefixLift 336961
  have htrace : WordTrace (prefixWord ++ tailWord_336961) baseStart_336961 baseEnd_336961 := by
    simpa [prefixWord, tailWord_336961, baseEnd_336961] using wordTrace_append hprefix tailTrace_336961
  have hstable : (prefixWord ++ tailWord_336961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336961).length < 2 ^ (prefixWord ++ tailWord_336961).sum := by decide
  have hdescent : baseEnd_336961 < baseStart_336961 := by decide
  rcases family_descends (prefixWord ++ tailWord_336961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336978 : List Nat := [3, 2, 2, 1, 3, 3, 1, 5]
def baseStart_336978 : Nat := 118140960795 + 336978 * 2 ^ 59
def prefixEnd_336978 : Nat := 4983230072969 + 3 ^ 40 * 336978 * 2
def baseEnd_336978 : Nat := 51268647108411201696377

theorem tailTrace_336978 : CollatzResearch.WordTrace tailWord_336978 prefixEnd_336978 51268647108411201696377 := by
  unfold tailWord_336978
  simp only [CollatzResearch.WordTrace]
  refine ⟨3072649343298433026404897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8193731582129154737079725 3072649343298433026404897)
  ·
    refine ⟨2304487007473824769803673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3072649343298433026404897 2304487007473824769803673)
    ·
      refine ⟨1728365255605368577352755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2304487007473824769803673 1728365255605368577352755)
      ·
        refine ⟨2592547883408052866029133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1728365255605368577352755 2592547883408052866029133)
        ·
          refine ⟨972205456278019824760925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2592547883408052866029133 972205456278019824760925)
          ·
            refine ⟨364577046104257434285347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 972205456278019824760925 364577046104257434285347)
            ·
              refine ⟨546865569156386151428021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364577046104257434285347 546865569156386151428021)
              ·
                refine ⟨51268647108411201696377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 546865569156386151428021 51268647108411201696377)
                ·
                  rfl

theorem cell20_336978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_336978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_336978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_336978 prefixEnd_336978 := by exact prefixLift 336978
  have htrace : WordTrace (prefixWord ++ tailWord_336978) baseStart_336978 baseEnd_336978 := by
    simpa [prefixWord, tailWord_336978, baseEnd_336978] using wordTrace_append hprefix tailTrace_336978
  have hstable : (prefixWord ++ tailWord_336978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336978).length < 2 ^ (prefixWord ++ tailWord_336978).sum := by decide
  have hdescent : baseEnd_336978 < baseStart_336978 := by decide
  rcases family_descends (prefixWord ++ tailWord_336978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337020 : List Nat := [2, 2, 2, 1, 1, 3, 9]
def baseStart_337020 : Nat := 118140960795 + 337020 * 2 ^ 59
def prefixEnd_337020 : Nat := 4983230072969 + 3 ^ 40 * 337020 * 2
def baseEnd_337020 : Nat := 17091679029963125076551

theorem tailTrace_337020 : CollatzResearch.WordTrace tailWord_337020 prefixEnd_337020 17091679029963125076551 := by
  unfold tailWord_337020
  simp only [CollatzResearch.WordTrace]
  refine ⟨6146064619520786639324257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8194752826027715519099009 6146064619520786639324257)
  ·
    refine ⟨4609548464640589979493193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6146064619520786639324257 4609548464640589979493193)
    ·
      refine ⟨3457161348480442484619895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4609548464640589979493193 3457161348480442484619895)
      ·
        refine ⟨5185742022720663726929843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3457161348480442484619895 5185742022720663726929843)
        ·
          refine ⟨7778613034080995590394765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5185742022720663726929843 7778613034080995590394765)
          ·
            refine ⟨2916979887780373346398037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7778613034080995590394765 2916979887780373346398037)
            ·
              refine ⟨17091679029963125076551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2916979887780373346398037 17091679029963125076551)
              ·
                rfl

theorem cell20_337020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 9].length) (baseStart_337020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337020 prefixEnd_337020 := by exact prefixLift 337020
  have htrace : WordTrace (prefixWord ++ tailWord_337020) baseStart_337020 baseEnd_337020 := by
    simpa [prefixWord, tailWord_337020, baseEnd_337020] using wordTrace_append hprefix tailTrace_337020
  have hstable : (prefixWord ++ tailWord_337020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337020).length < 2 ^ (prefixWord ++ tailWord_337020).sum := by decide
  have hdescent : baseEnd_337020 < baseStart_337020 := by decide
  rcases family_descends (prefixWord ++ tailWord_337020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337054 : List Nat := [4, 3, 1, 1, 2, 2, 1, 6]
def baseStart_337054 : Nat := 118140960795 + 337054 * 2 ^ 59
def prefixEnd_337054 : Nat := 4983230072969 + 3 ^ 40 * 337054 * 2
def baseEnd_337054 : Nat := 51280209932038372851829

theorem tailTrace_337054 : CollatzResearch.WordTrace tailWord_337054 prefixEnd_337054 51280209932038372851829 := by
  unfold tailWord_337054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1536671165114799635673277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8195579547278931390257477 1536671165114799635673277)
  ·
    refine ⟨576251686918049863377479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1536671165114799635673277 576251686918049863377479)
    ·
      refine ⟨864377530377074795066219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 576251686918049863377479 864377530377074795066219)
      ·
        refine ⟨1296566295565612192599329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 864377530377074795066219 1296566295565612192599329)
        ·
          refine ⟨972424721674209144449497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1296566295565612192599329 972424721674209144449497)
          ·
            refine ⟨729318541255656858337123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 972424721674209144449497 729318541255656858337123)
            ·
              refine ⟨1093977811883485287505685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 729318541255656858337123 1093977811883485287505685)
              ·
                refine ⟨51280209932038372851829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1093977811883485287505685 51280209932038372851829)
                ·
                  rfl

theorem cell20_337054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_337054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337054 prefixEnd_337054 := by exact prefixLift 337054
  have htrace : WordTrace (prefixWord ++ tailWord_337054) baseStart_337054 baseEnd_337054 := by
    simpa [prefixWord, tailWord_337054, baseEnd_337054] using wordTrace_append hprefix tailTrace_337054
  have hstable : (prefixWord ++ tailWord_337054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337054).length < 2 ^ (prefixWord ++ tailWord_337054).sum := by decide
  have hdescent : baseEnd_337054 < baseStart_337054 := by decide
  rcases family_descends (prefixWord ++ tailWord_337054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337068 : List Nat := [2, 2, 1, 1, 1, 1, 1, 9, 2]
def baseStart_337068 : Nat := 118140960795 + 337068 * 2 ^ 59
def prefixEnd_337068 : Nat := 4983230072969 + 3 ^ 40 * 337068 * 2
def baseEnd_337068 : Nat := 153847019777593292088763

theorem tailTrace_337068 : CollatzResearch.WordTrace tailWord_337068 prefixEnd_337068 153847019777593292088763 := by
  unfold tailWord_337068
  simp only [CollatzResearch.WordTrace]
  refine ⟨6146939971433838738197929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8195919961911784984263905 6146939971433838738197929)
  ·
    refine ⟨4610204978575379053648447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6146939971433838738197929 4610204978575379053648447)
    ·
      refine ⟨6915307467863068580472671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4610204978575379053648447 6915307467863068580472671)
      ·
        refine ⟨10372961201794602870709007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6915307467863068580472671 10372961201794602870709007)
        ·
          refine ⟨15559441802691904306063511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10372961201794602870709007 15559441802691904306063511)
          ·
            refine ⟨23339162704037856459095267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15559441802691904306063511 23339162704037856459095267)
            ·
              refine ⟨35008744056056784688642901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23339162704037856459095267 35008744056056784688642901)
              ·
                refine ⟨205129359703457722785017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 35008744056056784688642901 205129359703457722785017)
                ·
                  refine ⟨153847019777593292088763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205129359703457722785017 153847019777593292088763)
                  ·
                    rfl

theorem cell20_337068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_337068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337068 prefixEnd_337068 := by exact prefixLift 337068
  have htrace : WordTrace (prefixWord ++ tailWord_337068) baseStart_337068 baseEnd_337068 := by
    simpa [prefixWord, tailWord_337068, baseEnd_337068] using wordTrace_append hprefix tailTrace_337068
  have hstable : (prefixWord ++ tailWord_337068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337068).length < 2 ^ (prefixWord ++ tailWord_337068).sum := by decide
  have hdescent : baseEnd_337068 < baseStart_337068 := by decide
  rcases family_descends (prefixWord ++ tailWord_337068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337082 : List Nat := [3, 1, 1, 1, 2, 2, 1, 6, 3]
def baseStart_337082 : Nat := 118140960795 + 337082 * 2 ^ 59
def prefixEnd_337082 : Nat := 4983230072969 + 3 ^ 40 * 337082 * 2
def baseEnd_337082 : Nat := 153853409759071465622039

theorem tailTrace_337082 : CollatzResearch.WordTrace tailWord_337082 prefixEnd_337082 153853409759071465622039 := by
  unfold tailWord_337082
  simp only [CollatzResearch.WordTrace]
  refine ⟨3073597641204239466851375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8196260376544638578270333 3073597641204239466851375)
  ·
    refine ⟨4610396461806359200277063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3073597641204239466851375 4610396461806359200277063)
    ·
      refine ⟨6915594692709538800415595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4610396461806359200277063 6915594692709538800415595)
      ·
        refine ⟨10373392039064308200623393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6915594692709538800415595 10373392039064308200623393)
        ·
          refine ⟨7780044029298231150467545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10373392039064308200623393 7780044029298231150467545)
          ·
            refine ⟨5835033021973673362850659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7780044029298231150467545 5835033021973673362850659)
            ·
              refine ⟨8752549532960510044275989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5835033021973673362850659 8752549532960510044275989)
              ·
                refine ⟨410275759357523908325437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8752549532960510044275989 410275759357523908325437)
                ·
                  refine ⟨153853409759071465622039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 410275759357523908325437 153853409759071465622039)
                  ·
                    rfl

theorem cell20_337082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_337082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337082 prefixEnd_337082 := by exact prefixLift 337082
  have htrace : WordTrace (prefixWord ++ tailWord_337082) baseStart_337082 baseEnd_337082 := by
    simpa [prefixWord, tailWord_337082, baseEnd_337082] using wordTrace_append hprefix tailTrace_337082
  have hstable : (prefixWord ++ tailWord_337082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337082).length < 2 ^ (prefixWord ++ tailWord_337082).sum := by decide
  have hdescent : baseEnd_337082 < baseStart_337082 := by decide
  rcases family_descends (prefixWord ++ tailWord_337082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337092 : List Nat := [2, 3, 3, 1, 3, 1, 2, 5]
def baseStart_337092 : Nat := 118140960795 + 337092 * 2 ^ 59
def prefixEnd_337092 : Nat := 4983230072969 + 3 ^ 40 * 337092 * 2
def baseEnd_337092 : Nat := 51285991343851958429555

theorem tailTrace_337092 : CollatzResearch.WordTrace tailWord_337092 prefixEnd_337092 51285991343851958429555 := by
  unfold tailWord_337092
  simp only [CollatzResearch.WordTrace]
  refine ⟨6147377647390364787634765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8196503529853819716846353 6147377647390364787634765)
  ·
    refine ⟨2305266617771386795363037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6147377647390364787634765 2305266617771386795363037)
    ·
      refine ⟨864474981664270048261139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2305266617771386795363037 864474981664270048261139)
      ·
        refine ⟨1296712472496405072391709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 864474981664270048261139 1296712472496405072391709)
        ·
          refine ⟨486267177186151902146891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1296712472496405072391709 486267177186151902146891)
          ·
            refine ⟨729400765779227853220337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486267177186151902146891 729400765779227853220337)
            ·
              refine ⟨547050574334420889915253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 729400765779227853220337 547050574334420889915253)
              ·
                refine ⟨51285991343851958429555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 547050574334420889915253 51285991343851958429555)
                ·
                  rfl

theorem cell20_337092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_337092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337092 prefixEnd_337092 := by exact prefixLift 337092
  have htrace : WordTrace (prefixWord ++ tailWord_337092) baseStart_337092 baseEnd_337092 := by
    simpa [prefixWord, tailWord_337092, baseEnd_337092] using wordTrace_append hprefix tailTrace_337092
  have hstable : (prefixWord ++ tailWord_337092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337092).length < 2 ^ (prefixWord ++ tailWord_337092).sum := by decide
  have hdescent : baseEnd_337092 < baseStart_337092 := by decide
  rcases family_descends (prefixWord ++ tailWord_337092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337096 : List Nat := [2, 1, 3, 1, 2, 1, 3, 7]
def baseStart_337096 : Nat := 118140960795 + 337096 * 2 ^ 59
def prefixEnd_337096 : Nat := 4983230072969 + 3 ^ 40 * 337096 * 2
def baseEnd_337096 : Nat := 51286599913516546385105

theorem tailTrace_337096 : CollatzResearch.WordTrace tailWord_337096 prefixEnd_337096 51286599913516546385105 := by
  unfold tailWord_337096
  simp only [CollatzResearch.WordTrace]
  refine ⟨6147450593383119129207571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8196600791177492172276761 6147450593383119129207571)
  ·
    refine ⟨9221175890074678693811357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6147450593383119129207571 9221175890074678693811357)
    ·
      refine ⟨3457940958778004510179259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9221175890074678693811357 3457940958778004510179259)
      ·
        refine ⟨5186911438167006765268889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3457940958778004510179259 5186911438167006765268889)
        ·
          refine ⟨3890183578625255073951667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5186911438167006765268889 3890183578625255073951667)
          ·
            refine ⟨5835275367937882610927501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3890183578625255073951667 5835275367937882610927501)
            ·
              refine ⟨2188228262976705979097813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5835275367937882610927501 2188228262976705979097813)
              ·
                refine ⟨51286599913516546385105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2188228262976705979097813 51286599913516546385105)
                ·
                  rfl

theorem cell20_337096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_337096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337096 prefixEnd_337096 := by exact prefixLift 337096
  have htrace : WordTrace (prefixWord ++ tailWord_337096) baseStart_337096 baseEnd_337096 := by
    simpa [prefixWord, tailWord_337096, baseEnd_337096] using wordTrace_append hprefix tailTrace_337096
  have hstable : (prefixWord ++ tailWord_337096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337096).length < 2 ^ (prefixWord ++ tailWord_337096).sum := by decide
  have hdescent : baseEnd_337096 < baseStart_337096 := by decide
  rcases family_descends (prefixWord ++ tailWord_337096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337103 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 7]
def baseStart_337103 : Nat := 118140960795 + 337103 * 2 ^ 59
def prefixEnd_337103 : Nat := 4983230072969 + 3 ^ 40 * 337103 * 2
def baseEnd_337103 : Nat := 153862994731288725921953

theorem tailTrace_337103 : CollatzResearch.WordTrace tailWord_337103 prefixEnd_337103 153862994731288725921953 := by
  unfold tailWord_337103
  simp only [CollatzResearch.WordTrace]
  refine ⟨12295156497740878453919963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8196770998493918969279975 12295156497740878453919963)
  ·
    refine ⟨18442734746611317680879945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12295156497740878453919963 18442734746611317680879945)
    ·
      refine ⟨13832051059958488260659959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18442734746611317680879945 13832051059958488260659959)
      ·
        refine ⟨20748076589937732390989939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13832051059958488260659959 20748076589937732390989939)
        ·
          refine ⟨31122114884906598586484909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20748076589937732390989939 31122114884906598586484909)
          ·
            refine ⟨11670793081839974469931841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31122114884906598586484909 11670793081839974469931841)
            ·
              refine ⟨8753094811379980852448881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11670793081839974469931841 8753094811379980852448881)
              ·
                refine ⟨6564821108534985639336661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8753094811379980852448881 6564821108534985639336661)
                ·
                  refine ⟨153862994731288725921953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6564821108534985639336661 153862994731288725921953)
                  ·
                    rfl

theorem cell20_337103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_337103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337103 prefixEnd_337103 := by exact prefixLift 337103
  have htrace : WordTrace (prefixWord ++ tailWord_337103) baseStart_337103 baseEnd_337103 := by
    simpa [prefixWord, tailWord_337103, baseEnd_337103] using wordTrace_append hprefix tailTrace_337103
  have hstable : (prefixWord ++ tailWord_337103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337103).length < 2 ^ (prefixWord ++ tailWord_337103).sum := by decide
  have hdescent : baseEnd_337103 < baseStart_337103 := by decide
  rcases family_descends (prefixWord ++ tailWord_337103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337151 : List Nat := [1, 1, 2, 2, 1, 7, 1, 5]
def baseStart_337151 : Nat := 118140960795 + 337151 * 2 ^ 59
def prefixEnd_337151 : Nat := 4983230072969 + 3 ^ 40 * 337151 * 2
def baseEnd_337151 : Nat := 51294967746404630773919

theorem tailTrace_337151 : CollatzResearch.WordTrace tailWord_337151 prefixEnd_337151 51294967746404630773919 := by
  unfold tailWord_337151
  simp only [CollatzResearch.WordTrace]
  refine ⟨12296907201566982651667307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8197938134377988434444871 12296907201566982651667307)
  ·
    refine ⟨18445360802350473977500961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12296907201566982651667307 18445360802350473977500961)
    ·
      refine ⟨13834020601762855483125721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18445360802350473977500961 13834020601762855483125721)
      ·
        refine ⟨10375515451322141612344291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13834020601762855483125721 10375515451322141612344291)
        ·
          refine ⟨15563273176983212418516437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10375515451322141612344291 15563273176983212418516437)
          ·
            refine ⟨364764215085544041058979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 15563273176983212418516437 364764215085544041058979)
            ·
              refine ⟨547146322628316061588469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364764215085544041058979 547146322628316061588469)
              ·
                refine ⟨51294967746404630773919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 547146322628316061588469 51294967746404630773919)
                ·
                  rfl

theorem cell20_337151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 5].length) (baseStart_337151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337151 prefixEnd_337151 := by exact prefixLift 337151
  have htrace : WordTrace (prefixWord ++ tailWord_337151) baseStart_337151 baseEnd_337151 := by
    simpa [prefixWord, tailWord_337151, baseEnd_337151] using wordTrace_append hprefix tailTrace_337151
  have hstable : (prefixWord ++ tailWord_337151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337151).length < 2 ^ (prefixWord ++ tailWord_337151).sum := by decide
  have hdescent : baseEnd_337151 < baseStart_337151 := by decide
  rcases family_descends (prefixWord ++ tailWord_337151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337179 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 5]
def baseStart_337179 : Nat := 118140960795 + 337179 * 2 ^ 59
def prefixEnd_337179 : Nat := 4983230072969 + 3 ^ 40 * 337179 * 2
def baseEnd_337179 : Nat := 153897683202170239388309

theorem tailTrace_337179 : CollatzResearch.WordTrace tailWord_337179 prefixEnd_337179 153897683202170239388309 := by
  unfold tailWord_337179
  simp only [CollatzResearch.WordTrace]
  refine ⟨12297928445465543433686591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8198618963643695622457727 12297928445465543433686591)
  ·
    refine ⟨18446892668198315150529887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12297928445465543433686591 18446892668198315150529887)
    ·
      refine ⟨27670339002297472725794831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18446892668198315150529887 27670339002297472725794831)
      ·
        refine ⟨41505508503446209088692247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27670339002297472725794831 41505508503446209088692247)
        ·
          refine ⟨62258262755169313633038371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41505508503446209088692247 62258262755169313633038371)
          ·
            refine ⟨93387394132753970449557557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62258262755169313633038371 93387394132753970449557557)
            ·
              refine ⟨8755068199945684729646021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93387394132753970449557557 8755068199945684729646021)
              ·
                refine ⟨1641575287489815886808629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8755068199945684729646021 1641575287489815886808629)
                ·
                  refine ⟨153897683202170239388309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1641575287489815886808629 153897683202170239388309)
                  ·
                    rfl

theorem cell20_337179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_337179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337179 prefixEnd_337179 := by exact prefixLift 337179
  have htrace : WordTrace (prefixWord ++ tailWord_337179) baseStart_337179 baseEnd_337179 := by
    simpa [prefixWord, tailWord_337179, baseEnd_337179] using wordTrace_append hprefix tailTrace_337179
  have hstable : (prefixWord ++ tailWord_337179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337179).length < 2 ^ (prefixWord ++ tailWord_337179).sum := by decide
  have hdescent : baseEnd_337179 < baseStart_337179 := by decide
  rcases family_descends (prefixWord ++ tailWord_337179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337192 : List Nat := [2, 1, 5, 1, 2, 3, 1, 2, 3]
def baseStart_337192 : Nat := 118140960795 + 337192 * 2 ^ 59
def prefixEnd_337192 : Nat := 4983230072969 + 3 ^ 40 * 337192 * 2
def baseEnd_337192 : Nat := 153903616756399971954923

theorem tailTrace_337192 : CollatzResearch.WordTrace tailWord_337192 prefixEnd_337192 153903616756399971954923 := by
  unfold tailWord_337192
  simp only [CollatzResearch.WordTrace]
  refine ⟨6149201297209223326954915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8198935062945631102606553 6149201297209223326954915)
  ·
    refine ⟨9223801945813834990432373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6149201297209223326954915 9223801945813834990432373)
    ·
      refine ⟨864731432420047030353035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9223801945813834990432373 864731432420047030353035)
      ·
        refine ⟨1297097148630070545529553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 864731432420047030353035 1297097148630070545529553)
        ·
          refine ⟨972822861472552909147165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1297097148630070545529553 972822861472552909147165)
          ·
            refine ⟨364808573052207340930187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 972822861472552909147165 364808573052207340930187)
            ·
              refine ⟨547212859578311011395281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364808573052207340930187 547212859578311011395281)
              ·
                refine ⟨410409644683733258546461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 547212859578311011395281 410409644683733258546461)
                ·
                  refine ⟨153903616756399971954923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 410409644683733258546461 153903616756399971954923)
                  ·
                    rfl

theorem cell20_337192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 3].length) (baseStart_337192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337192 prefixEnd_337192 := by exact prefixLift 337192
  have htrace : WordTrace (prefixWord ++ tailWord_337192) baseStart_337192 baseEnd_337192 := by
    simpa [prefixWord, tailWord_337192, baseEnd_337192] using wordTrace_append hprefix tailTrace_337192
  have hstable : (prefixWord ++ tailWord_337192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337192).length < 2 ^ (prefixWord ++ tailWord_337192).sum := by decide
  have hdescent : baseEnd_337192 < baseStart_337192 := by decide
  rcases family_descends (prefixWord ++ tailWord_337192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337203 : List Nat := [1, 1, 1, 2, 5, 2, 1, 3, 4]
def baseStart_337203 : Nat := 118140960795 + 337203 * 2 ^ 59
def prefixEnd_337203 : Nat := 4983230072969 + 3 ^ 40 * 337203 * 2
def baseEnd_337203 : Nat := 153908637456132822588211

theorem tailTrace_337203 : CollatzResearch.WordTrace tailWord_337203 prefixEnd_337203 153908637456132822588211 := by
  unfold tailWord_337203
  simp only [CollatzResearch.WordTrace]
  refine ⟨12298803797378595532560263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8199202531585730355040175 12298803797378595532560263)
  ·
    refine ⟨18448205696067893298840395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12298803797378595532560263 18448205696067893298840395)
    ·
      refine ⟨27672308544101839948260593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18448205696067893298840395 27672308544101839948260593)
      ·
        refine ⟨20754231408076379961195445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27672308544101839948260593 20754231408076379961195445)
        ·
          refine ⟨1945709194507160621362073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20754231408076379961195445 1945709194507160621362073)
          ·
            refine ⟨1459281895880370466021555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1945709194507160621362073 1459281895880370466021555)
            ·
              refine ⟨2188922843820555699032333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1459281895880370466021555 2188922843820555699032333)
              ·
                refine ⟨820846066432708387137125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2188922843820555699032333 820846066432708387137125)
                ·
                  refine ⟨153908637456132822588211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 820846066432708387137125 153908637456132822588211)
                  ·
                    rfl

theorem cell20_337203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 4].length) (baseStart_337203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337203 prefixEnd_337203 := by exact prefixLift 337203
  have htrace : WordTrace (prefixWord ++ tailWord_337203) baseStart_337203 baseEnd_337203 := by
    simpa [prefixWord, tailWord_337203, baseEnd_337203] using wordTrace_append hprefix tailTrace_337203
  have hstable : (prefixWord ++ tailWord_337203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337203).length < 2 ^ (prefixWord ++ tailWord_337203).sum := by decide
  have hdescent : baseEnd_337203 < baseStart_337203 := by decide
  rcases family_descends (prefixWord ++ tailWord_337203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337210 : List Nat := [3, 1, 1, 1, 4, 1, 2, 7]
def baseStart_337210 : Nat := 118140960795 + 337210 * 2 ^ 59
def prefixEnd_337210 : Nat := 4983230072969 + 3 ^ 40 * 337210 * 2
def baseEnd_337210 : Nat := 51303944148957303118283

theorem tailTrace_337210 : CollatzResearch.WordTrace tailWord_337210 prefixEnd_337210 51303944148957303118283 := by
  unfold tailWord_337210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3074764777088308932016271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8199372738902157152043389 3074764777088308932016271)
  ·
    refine ⟨4612147165632463398024407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3074764777088308932016271 4612147165632463398024407)
    ·
      refine ⟨6918220748448695097036611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4612147165632463398024407 6918220748448695097036611)
      ·
        refine ⟨10377331122673042645554917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6918220748448695097036611 10377331122673042645554917)
        ·
          refine ⟨1945749585501195496041547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10377331122673042645554917 1945749585501195496041547)
          ·
            refine ⟨2918624378251793244062321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1945749585501195496041547 2918624378251793244062321)
            ·
              refine ⟨2188968283688844933046741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2918624378251793244062321 2188968283688844933046741)
              ·
                refine ⟨51303944148957303118283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2188968283688844933046741 51303944148957303118283)
                ·
                  rfl

theorem cell20_337210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_337210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337210 prefixEnd_337210 := by exact prefixLift 337210
  have htrace : WordTrace (prefixWord ++ tailWord_337210) baseStart_337210 baseEnd_337210 := by
    simpa [prefixWord, tailWord_337210, baseEnd_337210] using wordTrace_append hprefix tailTrace_337210
  have hstable : (prefixWord ++ tailWord_337210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337210).length < 2 ^ (prefixWord ++ tailWord_337210).sum := by decide
  have hdescent : baseEnd_337210 < baseStart_337210 := by decide
  rcases family_descends (prefixWord ++ tailWord_337210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337237 : List Nat := [1, 3, 2, 2, 3, 1, 3, 3, 2]
def baseStart_337237 : Nat := 118140960795 + 337237 * 2 ^ 59
def prefixEnd_337237 : Nat := 4983230072969 + 3 ^ 40 * 337237 * 2
def baseEnd_337237 : Nat := 153924155982579815454739

theorem tailTrace_337237 : CollatzResearch.WordTrace tailWord_337237 prefixEnd_337237 153924155982579815454739 := by
  unfold tailWord_337237
  simp only [CollatzResearch.WordTrace]
  refine ⟨12300043879255419339297965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8200029252836946226198643 12300043879255419339297965)
  ·
    refine ⟨4612516454720782252236737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12300043879255419339297965 4612516454720782252236737)
    ·
      refine ⟨3459387341040586689177553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4612516454720782252236737 3459387341040586689177553)
      ·
        refine ⟨2594540505780440016883165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3459387341040586689177553 2594540505780440016883165)
        ·
          refine ⟨972952689667665006331187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2594540505780440016883165 972952689667665006331187)
          ·
            refine ⟨1459429034501497509496781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972952689667665006331187 1459429034501497509496781)
            ·
              refine ⟨547285887938061566061293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1459429034501497509496781 547285887938061566061293)
              ·
                refine ⟨205232207976773087272985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 547285887938061566061293 205232207976773087272985)
                ·
                  refine ⟨153924155982579815454739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205232207976773087272985 153924155982579815454739)
                  ·
                    rfl

theorem cell20_337237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_337237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337237 prefixEnd_337237 := by exact prefixLift 337237
  have htrace : WordTrace (prefixWord ++ tailWord_337237) baseStart_337237 baseEnd_337237 := by
    simpa [prefixWord, tailWord_337237, baseEnd_337237] using wordTrace_append hprefix tailTrace_337237
  have hstable : (prefixWord ++ tailWord_337237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337237).length < 2 ^ (prefixWord ++ tailWord_337237).sum := by decide
  have hdescent : baseEnd_337237 < baseStart_337237 := by decide
  rcases family_descends (prefixWord ++ tailWord_337237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337248 : List Nat := [2, 1, 1, 3, 4, 1, 8]
def baseStart_337248 : Nat := 118140960795 + 337248 * 2 ^ 59
def prefixEnd_337248 : Nat := 4983230072969 + 3 ^ 40 * 337248 * 2
def baseEnd_337248 : Nat := 17103241853590296232003

theorem tailTrace_337248 : CollatzResearch.WordTrace tailWord_337248 prefixEnd_337248 17103241853590296232003 := by
  unfold tailWord_337248
  simp only [CollatzResearch.WordTrace]
  refine ⟨6150222541107784108974199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8200296721477045478632265 6150222541107784108974199)
  ·
    refine ⟨9225333811661676163461299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6150222541107784108974199 9225333811661676163461299)
    ·
      refine ⟨13838000717492514245191949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9225333811661676163461299 13838000717492514245191949)
      ·
        refine ⟨5189250269059692841946981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13838000717492514245191949 5189250269059692841946981)
        ·
          refine ⟨972984425448692407865059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5189250269059692841946981 972984425448692407865059)
          ·
            refine ⟨1459476638173038611797589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972984425448692407865059 1459476638173038611797589)
            ·
              refine ⟨17103241853590296232003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1459476638173038611797589 17103241853590296232003)
              ·
                rfl

theorem cell20_337248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 8].length) (baseStart_337248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337248 prefixEnd_337248 := by exact prefixLift 337248
  have htrace : WordTrace (prefixWord ++ tailWord_337248) baseStart_337248 baseEnd_337248 := by
    simpa [prefixWord, tailWord_337248, baseEnd_337248] using wordTrace_append hprefix tailTrace_337248
  have hstable : (prefixWord ++ tailWord_337248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337248).length < 2 ^ (prefixWord ++ tailWord_337248).sum := by decide
  have hdescent : baseEnd_337248 < baseStart_337248 := by decide
  rcases family_descends (prefixWord ++ tailWord_337248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337282 : List Nat := [3, 4, 2, 1, 1, 1, 2, 6]
def baseStart_337282 : Nat := 118140960795 + 337282 * 2 ^ 59
def prefixEnd_337282 : Nat := 4983230072969 + 3 ^ 40 * 337282 * 2
def baseEnd_337282 : Nat := 51314898402919886318185

theorem tailTrace_337282 : CollatzResearch.WordTrace tailWord_337282 prefixEnd_337282 51314898402919886318185 := by
  unfold tailWord_337282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3075421291023098006171525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8201123442728261349790733 3075421291023098006171525)
  ·
    refine ⟨576641492066830876157161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3075421291023098006171525 576641492066830876157161)
    ·
      refine ⟨432481119050123157117871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 576641492066830876157161 432481119050123157117871)
      ·
        refine ⟨648721678575184735676807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432481119050123157117871 648721678575184735676807)
        ·
          refine ⟨973082517862777103515211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648721678575184735676807 973082517862777103515211)
          ·
            refine ⟨1459623776794165655272817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 973082517862777103515211 1459623776794165655272817)
            ·
              refine ⟨1094717832595624241454613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1459623776794165655272817 1094717832595624241454613)
              ·
                refine ⟨51314898402919886318185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1094717832595624241454613 51314898402919886318185)
                ·
                  rfl

theorem cell20_337282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_337282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337282 prefixEnd_337282 := by exact prefixLift 337282
  have htrace : WordTrace (prefixWord ++ tailWord_337282) baseStart_337282 baseEnd_337282 := by
    simpa [prefixWord, tailWord_337282, baseEnd_337282] using wordTrace_append hprefix tailTrace_337282
  have hstable : (prefixWord ++ tailWord_337282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337282).length < 2 ^ (prefixWord ++ tailWord_337282).sum := by decide
  have hdescent : baseEnd_337282 < baseStart_337282 := by decide
  rcases family_descends (prefixWord ++ tailWord_337282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337324 : List Nat := [2, 2, 1, 1, 1, 1, 7, 5]
def baseStart_337324 : Nat := 118140960795 + 337324 * 2 ^ 59
def prefixEnd_337324 : Nat := 4983230072969 + 3 ^ 40 * 337324 * 2
def baseEnd_337324 : Nat := 51321288384398059851461

theorem tailTrace_337324 : CollatzResearch.WordTrace tailWord_337324 prefixEnd_337324 51321288384398059851461 := by
  unfold tailWord_337324
  simp only [CollatzResearch.WordTrace]
  refine ⟨6151608514970116598857513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8202144686626822131810017 6151608514970116598857513)
  ·
    refine ⟨4613706386227587449143135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6151608514970116598857513 4613706386227587449143135)
    ·
      refine ⟨6920559579341381173714703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4613706386227587449143135 6920559579341381173714703)
      ·
        refine ⟨10380839369012071760572055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6920559579341381173714703 10380839369012071760572055)
        ·
          refine ⟨15571259053518107640858083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10380839369012071760572055 15571259053518107640858083)
          ·
            refine ⟨23356888580277161461287125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15571259053518107640858083 23356888580277161461287125)
            ·
              refine ⟨547427076100245971748917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 23356888580277161461287125 547427076100245971748917)
              ·
                refine ⟨51321288384398059851461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 547427076100245971748917 51321288384398059851461)
                ·
                  rfl

theorem cell20_337324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_337324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337324 prefixEnd_337324 := by exact prefixLift 337324
  have htrace : WordTrace (prefixWord ++ tailWord_337324) baseStart_337324 baseEnd_337324 := by
    simpa [prefixWord, tailWord_337324, baseEnd_337324] using wordTrace_append hprefix tailTrace_337324
  have hstable : (prefixWord ++ tailWord_337324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337324).length < 2 ^ (prefixWord ++ tailWord_337324).sum := by decide
  have hdescent : baseEnd_337324 < baseStart_337324 := by decide
  rcases family_descends (prefixWord ++ tailWord_337324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337341 : List Nat := [1, 4, 1, 2, 2, 1, 5, 4]
def baseStart_337341 : Nat := 118140960795 + 337341 * 2 ^ 59
def prefixEnd_337341 : Nat := 4983230072969 + 3 ^ 40 * 337341 * 2
def baseEnd_337341 : Nat := 51323874805472558662549

theorem tailTrace_337341 : CollatzResearch.WordTrace tailWord_337341 prefixEnd_337341 51323874805472558662549 := by
  unfold tailWord_337341
  simp only [CollatzResearch.WordTrace]
  refine ⟨12303837070878645101083877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8202558047252430067389251 12303837070878645101083877)
  ·
    refine ⟨2306969450789745956453227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12303837070878645101083877 2306969450789745956453227)
    ·
      refine ⟨3460454176184618934679841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2306969450789745956453227 3460454176184618934679841)
      ·
        refine ⟨2595340632138464201009881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3460454176184618934679841 2595340632138464201009881)
        ·
          refine ⟨1946505474103848150757411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2595340632138464201009881 1946505474103848150757411)
          ·
            refine ⟨2919758211155772226136117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1946505474103848150757411 2919758211155772226136117)
            ·
              refine ⟨273727332295853646200261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2919758211155772226136117 273727332295853646200261)
              ·
                refine ⟨51323874805472558662549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 273727332295853646200261 51323874805472558662549)
                ·
                  rfl

theorem cell20_337341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 4].length) (baseStart_337341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337341 prefixEnd_337341 := by exact prefixLift 337341
  have htrace : WordTrace (prefixWord ++ tailWord_337341) baseStart_337341 baseEnd_337341 := by
    simpa [prefixWord, tailWord_337341, baseEnd_337341] using wordTrace_append hprefix tailTrace_337341
  have hstable : (prefixWord ++ tailWord_337341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337341).length < 2 ^ (prefixWord ++ tailWord_337341).sum := by decide
  have hdescent : baseEnd_337341 < baseStart_337341 := by decide
  rcases family_descends (prefixWord ++ tailWord_337341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337393 : List Nat := [1, 2, 2, 2, 3, 2, 2, 2, 4]
def baseStart_337393 : Nat := 118140960795 + 337393 * 2 ^ 59
def prefixEnd_337393 : Nat := 4983230072969 + 3 ^ 40 * 337393 * 2
def baseEnd_337393 : Nat := 153995358633336606254101

theorem tailTrace_337393 : CollatzResearch.WordTrace tailWord_337393 prefixEnd_337393 153995358633336606254101 := by
  unfold tailWord_337393
  simp only [CollatzResearch.WordTrace]
  refine ⟨12305733666690257981976833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8203822444460171987984555 12305733666690257981976833)
  ·
    refine ⟨9229300250017693486482625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12305733666690257981976833 9229300250017693486482625)
    ·
      refine ⟨6921975187513270114861969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9229300250017693486482625 6921975187513270114861969)
      ·
        refine ⟨5191481390634952586146477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6921975187513270114861969 5191481390634952586146477)
        ·
          refine ⟨1946805521488107219804929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5191481390634952586146477 1946805521488107219804929)
          ·
            refine ⟨1460104141116080414853697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1946805521488107219804929 1460104141116080414853697)
            ·
              refine ⟨1095078105837060311140273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1460104141116080414853697 1095078105837060311140273)
              ·
                refine ⟨821308579377795233355205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1095078105837060311140273 821308579377795233355205)
                ·
                  refine ⟨153995358633336606254101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 821308579377795233355205 153995358633336606254101)
                  ·
                    rfl

theorem cell20_337393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_337393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337393 prefixEnd_337393 := by exact prefixLift 337393
  have htrace : WordTrace (prefixWord ++ tailWord_337393) baseStart_337393 baseEnd_337393 := by
    simpa [prefixWord, tailWord_337393, baseEnd_337393] using wordTrace_append hprefix tailTrace_337393
  have hstable : (prefixWord ++ tailWord_337393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337393).length < 2 ^ (prefixWord ++ tailWord_337393).sum := by decide
  have hdescent : baseEnd_337393 < baseStart_337393 := by decide
  rcases family_descends (prefixWord ++ tailWord_337393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337400 : List Nat := [2, 1, 2, 1, 1, 6, 1, 6]
def baseStart_337400 : Nat := 118140960795 + 337400 * 2 ^ 59
def prefixEnd_337400 : Nat := 4983230072969 + 3 ^ 40 * 337400 * 2
def baseEnd_337400 : Nat := 51332851208025231006913

theorem tailTrace_337400 : CollatzResearch.WordTrace tailWord_337400 prefixEnd_337400 51332851208025231006913 := by
  unfold tailWord_337400
  simp only [CollatzResearch.WordTrace]
  refine ⟨6152994488832449088740827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8203992651776598784987769 6152994488832449088740827)
  ·
    refine ⟨9229491733248673633111241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6152994488832449088740827 9229491733248673633111241)
    ·
      refine ⟨6922118799936505224833431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9229491733248673633111241 6922118799936505224833431)
      ·
        refine ⟨10383178199904757837250147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6922118799936505224833431 10383178199904757837250147)
        ·
          refine ⟨15574767299857136755875221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10383178199904757837250147 15574767299857136755875221)
          ·
            refine ⟨730067217180803285431651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15574767299857136755875221 730067217180803285431651)
            ·
              refine ⟨1095100825771204928147477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730067217180803285431651 1095100825771204928147477)
              ·
                refine ⟨51332851208025231006913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1095100825771204928147477 51332851208025231006913)
                ·
                  rfl

theorem cell20_337400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_337400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337400 prefixEnd_337400 := by exact prefixLift 337400
  have htrace : WordTrace (prefixWord ++ tailWord_337400) baseStart_337400 baseEnd_337400 := by
    simpa [prefixWord, tailWord_337400, baseEnd_337400] using wordTrace_append hprefix tailTrace_337400
  have hstable : (prefixWord ++ tailWord_337400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337400).length < 2 ^ (prefixWord ++ tailWord_337400).sum := by decide
  have hdescent : baseEnd_337400 < baseStart_337400 := by decide
  rcases family_descends (prefixWord ++ tailWord_337400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337427 : List Nat := [1, 1, 1, 2, 1, 7, 3, 2, 2]
def baseStart_337427 : Nat := 118140960795 + 337427 * 2 ^ 59
def prefixEnd_337427 : Nat := 4983230072969 + 3 ^ 40 * 337427 * 2
def baseEnd_337427 : Nat := 154010877159783599120629

theorem tailTrace_337427 : CollatzResearch.WordTrace tailWord_337427 prefixEnd_337427 154010877159783599120629 := by
  unfold tailWord_337427
  simp only [CollatzResearch.WordTrace]
  refine ⟨12306973748567081788714535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8204649165711387859143023 12306973748567081788714535)
  ·
    refine ⟨18460460622850622683071803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12306973748567081788714535 18460460622850622683071803)
    ·
      refine ⟨27690690934275934024607705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18460460622850622683071803 27690690934275934024607705)
      ·
        refine ⟨20768018200706950518455779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27690690934275934024607705 20768018200706950518455779)
        ·
          refine ⟨31152027301060425777683669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20768018200706950518455779 31152027301060425777683669)
          ·
            refine ⟨730125639868603729164461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 31152027301060425777683669 730125639868603729164461)
            ·
              refine ⟨273797114950726398436673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 730125639868603729164461 273797114950726398436673)
              ·
                refine ⟨205347836213044798827505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273797114950726398436673 205347836213044798827505)
                ·
                  refine ⟨154010877159783599120629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205347836213044798827505 154010877159783599120629)
                  ·
                    rfl

theorem cell20_337427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 2].length) (baseStart_337427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337427 prefixEnd_337427 := by exact prefixLift 337427
  have htrace : WordTrace (prefixWord ++ tailWord_337427) baseStart_337427 baseEnd_337427 := by
    simpa [prefixWord, tailWord_337427, baseEnd_337427] using wordTrace_append hprefix tailTrace_337427
  have hstable : (prefixWord ++ tailWord_337427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337427).length < 2 ^ (prefixWord ++ tailWord_337427).sum := by decide
  have hdescent : baseEnd_337427 < baseStart_337427 := by decide
  rcases family_descends (prefixWord ++ tailWord_337427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337441 : List Nat := [1, 2, 3, 2, 2, 2, 4, 1, 3]
def baseStart_337441 : Nat := 118140960795 + 337441 * 2 ^ 59
def prefixEnd_337441 : Nat := 4983230072969 + 3 ^ 40 * 337441 * 2
def baseEnd_337441 : Nat := 154017267141261772653905

theorem tailTrace_337441 : CollatzResearch.WordTrace tailWord_337441 prefixEnd_337441 154017267141261772653905 := by
  unfold tailWord_337441
  simp only [CollatzResearch.WordTrace]
  refine ⟨12307484370516362179724177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8204989580344241453149451 12307484370516362179724177)
  ·
    refine ⟨9230613277887271634793133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12307484370516362179724177 9230613277887271634793133)
    ·
      refine ⟨3461479979207726863047425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9230613277887271634793133 3461479979207726863047425)
      ·
        refine ⟨2596109984405795147285569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3461479979207726863047425 2596109984405795147285569)
        ·
          refine ⟨1947082488304346360464177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2596109984405795147285569 1947082488304346360464177)
          ·
            refine ⟨1460311866228259770348133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1947082488304346360464177 1460311866228259770348133)
            ·
              refine ⟨273808474917798706940275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1460311866228259770348133 273808474917798706940275)
              ·
                refine ⟨410712712376698060410413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273808474917798706940275 410712712376698060410413)
                ·
                  refine ⟨154017267141261772653905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 410712712376698060410413 154017267141261772653905)
                  ·
                    rfl

theorem cell20_337441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 3].length) (baseStart_337441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337441 prefixEnd_337441 := by exact prefixLift 337441
  have htrace : WordTrace (prefixWord ++ tailWord_337441) baseStart_337441 baseEnd_337441 := by
    simpa [prefixWord, tailWord_337441, baseEnd_337441] using wordTrace_append hprefix tailTrace_337441
  have hstable : (prefixWord ++ tailWord_337441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337441).length < 2 ^ (prefixWord ++ tailWord_337441).sum := by decide
  have hdescent : baseEnd_337441 < baseStart_337441 := by decide
  rcases family_descends (prefixWord ++ tailWord_337441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337478 : List Nat := [6, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_337478 : Nat := 118140960795 + 337478 * 2 ^ 59
def prefixEnd_337478 : Nat := 4983230072969 + 3 ^ 40 * 337478 * 2
def baseEnd_337478 : Nat := 154034154949454088420421

theorem tailTrace_337478 : CollatzResearch.WordTrace tailWord_337478 prefixEnd_337478 154034154949454088420421 := by
  unfold tailWord_337478
  simp only [CollatzResearch.WordTrace]
  refine ⟨384651058480697421838159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8205889247588211665880725 384651058480697421838159)
  ·
    refine ⟨576976587721046132757239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 384651058480697421838159 576976587721046132757239)
    ·
      refine ⟨865464881581569199135859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 576976587721046132757239 865464881581569199135859)
      ·
        refine ⟨1298197322372353798703789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 865464881581569199135859 1298197322372353798703789)
        ·
          refine ⟨486823995889632674513921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1298197322372353798703789 486823995889632674513921)
          ·
            refine ⟨365117996917224505885441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 486823995889632674513921 365117996917224505885441)
            ·
              refine ⟨273838497687918379414081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365117996917224505885441 273838497687918379414081)
              ·
                refine ⟨205378873265938784560561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273838497687918379414081 205378873265938784560561)
                ·
                  refine ⟨154034154949454088420421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205378873265938784560561 154034154949454088420421)
                  ·
                    rfl

theorem cell20_337478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_337478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337478 prefixEnd_337478 := by exact prefixLift 337478
  have htrace : WordTrace (prefixWord ++ tailWord_337478) baseStart_337478 baseEnd_337478 := by
    simpa [prefixWord, tailWord_337478, baseEnd_337478] using wordTrace_append hprefix tailTrace_337478
  have hstable : (prefixWord ++ tailWord_337478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337478).length < 2 ^ (prefixWord ++ tailWord_337478).sum := by decide
  have hdescent : baseEnd_337478 < baseStart_337478 := by decide
  rcases family_descends (prefixWord ++ tailWord_337478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337479 : List Nat := [1, 1, 4, 1, 5, 1, 2, 2, 3]
def baseStart_337479 : Nat := 118140960795 + 337479 * 2 ^ 59
def prefixEnd_337479 : Nat := 4983230072969 + 3 ^ 40 * 337479 * 2
def baseEnd_337479 : Nat := 154034611376702529387083

theorem tailTrace_337479 : CollatzResearch.WordTrace tailWord_337479 prefixEnd_337479 154034611376702529387083 := by
  unfold tailWord_337479
  simp only [CollatzResearch.WordTrace]
  refine ⟨12308870344378694669607491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8205913562919129779738327 12308870344378694669607491)
  ·
    refine ⟨18463305516568042004411237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12308870344378694669607491 18463305516568042004411237)
    ·
      refine ⟨3461869784356507875827107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18463305516568042004411237 3461869784356507875827107)
      ·
        refine ⟨5192804676534761813740661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3461869784356507875827107 5192804676534761813740661)
        ·
          refine ⟨486825438425133920038187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5192804676534761813740661 486825438425133920038187)
          ·
            refine ⟨730238157637700880057281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486825438425133920038187 730238157637700880057281)
            ·
              refine ⟨547678618228275660042961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 730238157637700880057281 547678618228275660042961)
              ·
                refine ⟨410758963671206745032221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 547678618228275660042961 410758963671206745032221)
                ·
                  refine ⟨154034611376702529387083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 410758963671206745032221 154034611376702529387083)
                  ·
                    rfl

theorem cell20_337479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 3].length) (baseStart_337479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337479 prefixEnd_337479 := by exact prefixLift 337479
  have htrace : WordTrace (prefixWord ++ tailWord_337479) baseStart_337479 baseEnd_337479 := by
    simpa [prefixWord, tailWord_337479, baseEnd_337479] using wordTrace_append hprefix tailTrace_337479
  have hstable : (prefixWord ++ tailWord_337479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337479).length < 2 ^ (prefixWord ++ tailWord_337479).sum := by decide
  have hdescent : baseEnd_337479 < baseStart_337479 := by decide
  rcases family_descends (prefixWord ++ tailWord_337479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337507 : List Nat := [1, 1, 1, 5, 1, 4, 1, 2, 4]
def baseStart_337507 : Nat := 118140960795 + 337507 * 2 ^ 59
def prefixEnd_337507 : Nat := 4983230072969 + 3 ^ 40 * 337507 * 2
def baseEnd_337507 : Nat := 154047391339658876453635

theorem tailTrace_337507 : CollatzResearch.WordTrace tailWord_337507 prefixEnd_337507 154047391339658876453635 := by
  unfold tailWord_337507
  simp only [CollatzResearch.WordTrace]
  refine ⟨12309891588277255451626775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8206594392184836967751183 12309891588277255451626775)
  ·
    refine ⟨18464837382415883177440163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12309891588277255451626775 18464837382415883177440163)
    ·
      refine ⟨27697256073623824766160245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18464837382415883177440163 27697256073623824766160245)
      ·
        refine ⟨2596617756902233571827523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27697256073623824766160245 2596617756902233571827523)
        ·
          refine ⟨3894926635353350357741285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2596617756902233571827523 3894926635353350357741285)
          ·
            refine ⟨730298744128753192076491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3894926635353350357741285 730298744128753192076491)
            ·
              refine ⟨1095448116193129788114737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730298744128753192076491 1095448116193129788114737)
              ·
                refine ⟨821586087144847341086053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1095448116193129788114737 821586087144847341086053)
                ·
                  refine ⟨154047391339658876453635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 821586087144847341086053 154047391339658876453635)
                  ·
                    rfl

theorem cell20_337507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 4].length) (baseStart_337507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337507 prefixEnd_337507 := by exact prefixLift 337507
  have htrace : WordTrace (prefixWord ++ tailWord_337507) baseStart_337507 baseEnd_337507 := by
    simpa [prefixWord, tailWord_337507, baseEnd_337507] using wordTrace_append hprefix tailTrace_337507
  have hstable : (prefixWord ++ tailWord_337507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337507).length < 2 ^ (prefixWord ++ tailWord_337507).sum := by decide
  have hdescent : baseEnd_337507 < baseStart_337507 := by decide
  rcases family_descends (prefixWord ++ tailWord_337507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337569 : List Nat := [1, 2, 3, 3, 2, 1, 4, 4]
def baseStart_337569 : Nat := 118140960795 + 337569 * 2 ^ 59
def prefixEnd_337569 : Nat := 4983230072969 + 3 ^ 40 * 337569 * 2
def baseEnd_337569 : Nat := 51358563276354072128905

theorem tailTrace_337569 : CollatzResearch.WordTrace tailWord_337569 prefixEnd_337569 51358563276354072128905 := by
  unfold tailWord_337569
  simp only [CollatzResearch.WordTrace]
  refine ⟨12312152914052640040383761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8208101942701760026922507 12312152914052640040383761)
  ·
    refine ⟨9234114685539480030287821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12312152914052640040383761 9234114685539480030287821)
    ·
      refine ⟨3462793007077305011357933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9234114685539480030287821 3462793007077305011357933)
      ·
        refine ⟨1298547377653989379259225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3462793007077305011357933 1298547377653989379259225)
        ·
          refine ⟨973910533240492034444419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1298547377653989379259225 973910533240492034444419)
          ·
            refine ⟨1460865799860738051666629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 973910533240492034444419 1460865799860738051666629)
            ·
              refine ⟨273912337473888384687493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1460865799860738051666629 273912337473888384687493)
              ·
                refine ⟨51358563276354072128905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 273912337473888384687493 51358563276354072128905)
                ·
                  rfl

theorem cell20_337569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 4].length) (baseStart_337569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337569 prefixEnd_337569 := by exact prefixLift 337569
  have htrace : WordTrace (prefixWord ++ tailWord_337569) baseStart_337569 baseEnd_337569 := by
    simpa [prefixWord, tailWord_337569, baseEnd_337569] using wordTrace_append hprefix tailTrace_337569
  have hstable : (prefixWord ++ tailWord_337569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337569).length < 2 ^ (prefixWord ++ tailWord_337569).sum := by decide
  have hdescent : baseEnd_337569 < baseStart_337569 := by decide
  rcases family_descends (prefixWord ++ tailWord_337569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337597 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 5]
def baseStart_337597 : Nat := 118140960795 + 337597 * 2 ^ 59
def prefixEnd_337597 : Nat := 4983230072969 + 3 ^ 40 * 337597 * 2
def baseEnd_337597 : Nat := 154088469792018563453267

theorem tailTrace_337597 : CollatzResearch.WordTrace tailWord_337597 prefixEnd_337597 154088469792018563453267 := by
  unfold tailWord_337597
  simp only [CollatzResearch.WordTrace]
  refine ⟨12313174157951200822403045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8208782771967467214935363 12313174157951200822403045)
  ·
    refine ⟨2308720154615850154200571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12313174157951200822403045 2308720154615850154200571)
    ·
      refine ⟨3463080231923775231300857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2308720154615850154200571 3463080231923775231300857)
      ·
        refine ⟨2597310173942831423475643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3463080231923775231300857 2597310173942831423475643)
        ·
          refine ⟨3895965260914247135213465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2597310173942831423475643 3895965260914247135213465)
          ·
            refine ⟨2921973945685685351410099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3895965260914247135213465 2921973945685685351410099)
            ·
              refine ⟨4382960918528528027115149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2921973945685685351410099 4382960918528528027115149)
              ·
                refine ⟨1643610344448198010168181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4382960918528528027115149 1643610344448198010168181)
                ·
                  refine ⟨154088469792018563453267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1643610344448198010168181 154088469792018563453267)
                  ·
                    rfl

theorem cell20_337597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_337597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337597 prefixEnd_337597 := by exact prefixLift 337597
  have htrace : WordTrace (prefixWord ++ tailWord_337597) baseStart_337597 baseEnd_337597 := by
    simpa [prefixWord, tailWord_337597, baseEnd_337597] using wordTrace_append hprefix tailTrace_337597
  have hstable : (prefixWord ++ tailWord_337597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337597).length < 2 ^ (prefixWord ++ tailWord_337597).sum := by decide
  have hdescent : baseEnd_337597 < baseStart_337597 := by decide
  rcases family_descends (prefixWord ++ tailWord_337597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337606 : List Nat := [6, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_337606 : Nat := 118140960795 + 337606 * 2 ^ 59
def prefixEnd_337606 : Nat := 4983230072969 + 3 ^ 40 * 337606 * 2
def baseEnd_337606 : Nat := 154092577637254532153231

theorem tailTrace_337606 : CollatzResearch.WordTrace tailWord_337606 prefixEnd_337606 154092577637254532153231 := by
  unfold tailWord_337606
  simp only [CollatzResearch.WordTrace]
  refine ⟨384796950466206104983771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8209001609945730239653781 384796950466206104983771)
  ·
    refine ⟨577195425699309157475657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 384796950466206104983771 577195425699309157475657)
    ·
      refine ⟨432896569274481868106743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 577195425699309157475657 432896569274481868106743)
      ·
        refine ⟨649344853911722802160115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432896569274481868106743 649344853911722802160115)
        ·
          refine ⟨974017280867584203240173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 649344853911722802160115 974017280867584203240173)
          ·
            refine ⟨365256480325344076215065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 974017280867584203240173 365256480325344076215065)
            ·
              refine ⟨273942360244008057161299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365256480325344076215065 273942360244008057161299)
              ·
                refine ⟨410913540366012085741949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273942360244008057161299 410913540366012085741949)
                ·
                  refine ⟨154092577637254532153231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 410913540366012085741949 154092577637254532153231)
                  ·
                    rfl

theorem cell20_337606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_337606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337606 prefixEnd_337606 := by exact prefixLift 337606
  have htrace : WordTrace (prefixWord ++ tailWord_337606) baseStart_337606 baseEnd_337606 := by
    simpa [prefixWord, tailWord_337606, baseEnd_337606] using wordTrace_append hprefix tailTrace_337606
  have hstable : (prefixWord ++ tailWord_337606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337606).length < 2 ^ (prefixWord ++ tailWord_337606).sum := by decide
  have hdescent : baseEnd_337606 < baseStart_337606 := by decide
  rcases family_descends (prefixWord ++ tailWord_337606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337610 : List Nat := [3, 1, 2, 1, 5, 2, 2, 1, 3]
def baseStart_337610 : Nat := 118140960795 + 337610 * 2 ^ 59
def prefixEnd_337610 : Nat := 4983230072969 + 3 ^ 40 * 337610 * 2
def baseEnd_337610 : Nat := 154094403346248296019881

theorem tailTrace_337610 : CollatzResearch.WordTrace tailWord_337610 prefixEnd_337610 154094403346248296019881 := by
  unfold tailWord_337610
  simp only [CollatzResearch.WordTrace]
  refine ⟨3078412076726026010656571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8209098871269402695084189 3078412076726026010656571)
  ·
    refine ⟨4617618115089039015984857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3078412076726026010656571 4617618115089039015984857)
    ·
      refine ⟨3463213586316779261988643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4617618115089039015984857 3463213586316779261988643)
      ·
        refine ⟨5194820379475168892982965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3463213586316779261988643 5194820379475168892982965)
        ·
          refine ⟨487014410575797083717153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5194820379475168892982965 487014410575797083717153)
          ·
            refine ⟨365260807931847812787865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 487014410575797083717153 365260807931847812787865)
            ·
              refine ⟨273945605948885859590899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365260807931847812787865 273945605948885859590899)
              ·
                refine ⟨410918408923328789386349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273945605948885859590899 410918408923328789386349)
                ·
                  refine ⟨154094403346248296019881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 410918408923328789386349 154094403346248296019881)
                  ·
                    rfl

theorem cell20_337610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_337610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337610 prefixEnd_337610 := by exact prefixLift 337610
  have htrace : WordTrace (prefixWord ++ tailWord_337610) baseStart_337610 baseEnd_337610 := by
    simpa [prefixWord, tailWord_337610, baseEnd_337610] using wordTrace_append hprefix tailTrace_337610
  have hstable : (prefixWord ++ tailWord_337610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337610).length < 2 ^ (prefixWord ++ tailWord_337610).sum := by decide
  have hdescent : baseEnd_337610 < baseStart_337610 := by decide
  rcases family_descends (prefixWord ++ tailWord_337610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337614 : List Nat := [4, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_337614 : Nat := 118140960795 + 337614 * 2 ^ 59
def prefixEnd_337614 : Nat := 4983230072969 + 3 ^ 40 * 337614 * 2
def baseEnd_337614 : Nat := 154096229055242059886531

theorem tailTrace_337614 : CollatzResearch.WordTrace tailWord_337614 prefixEnd_337614 154096229055242059886531 := by
  unfold tailWord_337614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1539224274861201590721487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8209196132593075150514597 1539224274861201590721487)
  ·
    refine ⟨2308836412291802386082231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1539224274861201590721487 2308836412291802386082231)
    ·
      refine ⟨3463254618437703579123347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2308836412291802386082231 3463254618437703579123347)
      ·
        refine ⟨5194881927656555368685021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3463254618437703579123347 5194881927656555368685021)
        ·
          refine ⟨1948080722871208263256883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5194881927656555368685021 1948080722871208263256883)
          ·
            refine ⟨2922121084306812394885325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1948080722871208263256883 2922121084306812394885325)
            ·
              refine ⟨1095795406615054648081997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2922121084306812394885325 1095795406615054648081997)
              ·
                refine ⟨410923277480645493030749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1095795406615054648081997 410923277480645493030749)
                ·
                  refine ⟨154096229055242059886531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 410923277480645493030749 154096229055242059886531)
                  ·
                    rfl

theorem cell20_337614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_337614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337614 prefixEnd_337614 := by exact prefixLift 337614
  have htrace : WordTrace (prefixWord ++ tailWord_337614) baseStart_337614 baseEnd_337614 := by
    simpa [prefixWord, tailWord_337614, baseEnd_337614] using wordTrace_append hprefix tailTrace_337614
  have hstable : (prefixWord ++ tailWord_337614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337614).length < 2 ^ (prefixWord ++ tailWord_337614).sum := by decide
  have hdescent : baseEnd_337614 < baseStart_337614 := by decide
  rcases family_descends (prefixWord ++ tailWord_337614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337649 : List Nat := [1, 2, 2, 2, 2, 11]
def baseStart_337649 : Nat := 118140960795 + 337649 * 2 ^ 59
def prefixEnd_337649 : Nat := 4983230072969 + 3 ^ 40 * 337649 * 2
def baseEnd_337649 : Nat := 5707859407738425693323

theorem tailTrace_337649 : CollatzResearch.WordTrace tailWord_337649 prefixEnd_337649 5707859407738425693323 := by
  unfold tailWord_337649
  simp only [CollatzResearch.WordTrace]
  refine ⟨12315070753762813703296001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8210047169175209135530667 12315070753762813703296001)
  ·
    refine ⟨9236303065322110277472001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12315070753762813703296001 9236303065322110277472001)
    ·
      refine ⟨6927227298991582708104001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9236303065322110277472001 6927227298991582708104001)
      ·
        refine ⟨5195420474243687031078001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6927227298991582708104001 5195420474243687031078001)
        ·
          refine ⟨3896565355682765273308501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5195420474243687031078001 3896565355682765273308501)
          ·
            refine ⟨5707859407738425693323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3896565355682765273308501 5707859407738425693323)
            ·
              rfl

theorem cell20_337649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 11].length) (baseStart_337649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337649 prefixEnd_337649 := by exact prefixLift 337649
  have htrace : WordTrace (prefixWord ++ tailWord_337649) baseStart_337649 baseEnd_337649 := by
    simpa [prefixWord, tailWord_337649, baseEnd_337649] using wordTrace_append hprefix tailTrace_337649
  have hstable : (prefixWord ++ tailWord_337649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337649).length < 2 ^ (prefixWord ++ tailWord_337649).sum := by decide
  have hdescent : baseEnd_337649 < baseStart_337649 := by decide
  rcases family_descends (prefixWord ++ tailWord_337649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337662 : List Nat := [4, 2, 2, 1, 3, 2, 1, 5]
def baseStart_337662 : Nat := 118140960795 + 337662 * 2 ^ 59
def prefixEnd_337662 : Nat := 4983230072969 + 3 ^ 40 * 337662 * 2
def baseEnd_337662 : Nat := 51372712521055742095445

theorem tailTrace_337662 : CollatzResearch.WordTrace tailWord_337662 prefixEnd_337662 51372712521055742095445 := by
  unfold tailWord_337662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1539443112839464615439905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8210363268477144615679493 1539443112839464615439905)
  ·
    refine ⟨1154582334629598461579929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1539443112839464615439905 1154582334629598461579929)
    ·
      refine ⟨865936750972198846184947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1154582334629598461579929 865936750972198846184947)
      ·
        refine ⟨1298905126458298269277421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 865936750972198846184947 1298905126458298269277421)
        ·
          refine ⟨487089422421861850979033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1298905126458298269277421 487089422421861850979033)
          ·
            refine ⟨365317066816396388234275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 487089422421861850979033 365317066816396388234275)
            ·
              refine ⟨547975600224594582351413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365317066816396388234275 547975600224594582351413)
              ·
                refine ⟨51372712521055742095445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 547975600224594582351413 51372712521055742095445)
                ·
                  rfl

theorem cell20_337662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_337662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337662 prefixEnd_337662 := by exact prefixLift 337662
  have htrace : WordTrace (prefixWord ++ tailWord_337662) baseStart_337662 baseEnd_337662 := by
    simpa [prefixWord, tailWord_337662, baseEnd_337662] using wordTrace_append hprefix tailTrace_337662
  have hstable : (prefixWord ++ tailWord_337662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337662).length < 2 ^ (prefixWord ++ tailWord_337662).sum := by decide
  have hdescent : baseEnd_337662 < baseStart_337662 := by decide
  rcases family_descends (prefixWord ++ tailWord_337662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337704 : List Nat := [2, 1, 5, 1, 1, 3, 7]
def baseStart_337704 : Nat := 118140960795 + 337704 * 2 ^ 59
def prefixEnd_337704 : Nat := 4983230072969 + 3 ^ 40 * 337704 * 2
def baseEnd_337704 : Nat := 17126367500844638542907

theorem tailTrace_337704 : CollatzResearch.WordTrace tailWord_337704 prefixEnd_337704 17126367500844638542907 := by
  unfold tailWord_337704
  simp only [CollatzResearch.WordTrace]
  refine ⟨6158538384281779048274083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8211384512375705397698777 6158538384281779048274083)
  ·
    refine ⟨9237807576422668572411125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6158538384281779048274083 9237807576422668572411125)
    ·
      refine ⟨866044460289625178663543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9237807576422668572411125 866044460289625178663543)
      ·
        refine ⟨1299066690434437767995315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866044460289625178663543 1299066690434437767995315)
        ·
          refine ⟨1948600035651656651992973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1299066690434437767995315 1948600035651656651992973)
          ·
            refine ⟨730725013369371244497365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1948600035651656651992973 730725013369371244497365)
            ·
              refine ⟨17126367500844638542907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 730725013369371244497365 17126367500844638542907)
              ·
                rfl

theorem cell20_337704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 7].length) (baseStart_337704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337704 prefixEnd_337704 := by exact prefixLift 337704
  have htrace : WordTrace (prefixWord ++ tailWord_337704) baseStart_337704 baseEnd_337704 := by
    simpa [prefixWord, tailWord_337704, baseEnd_337704] using wordTrace_append hprefix tailTrace_337704
  have hstable : (prefixWord ++ tailWord_337704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337704).length < 2 ^ (prefixWord ++ tailWord_337704).sum := by decide
  have hdescent : baseEnd_337704 < baseStart_337704 := by decide
  rcases family_descends (prefixWord ++ tailWord_337704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337714 : List Nat := [3, 2, 1, 1, 3, 2, 2, 4, 2]
def baseStart_337714 : Nat := 118140960795 + 337714 * 2 ^ 59
def prefixEnd_337714 : Nat := 4983230072969 + 3 ^ 40 * 337714 * 2
def baseEnd_337714 : Nat := 154141871780086156552789

theorem tailTrace_337714 : CollatzResearch.WordTrace tailWord_337714 prefixEnd_337714 154141871780086156552789 := by
  unfold tailWord_337714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3079360374631832451103049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8211627665684886536274797 3079360374631832451103049)
  ·
    refine ⟨2309520280973874338327287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3079360374631832451103049 2309520280973874338327287)
    ·
      refine ⟨3464280421460811507490931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2309520280973874338327287 3464280421460811507490931)
      ·
        refine ⟨5196420632191217261236397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3464280421460811507490931 5196420632191217261236397)
        ·
          refine ⟨1948657737071706472963649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5196420632191217261236397 1948657737071706472963649)
          ·
            refine ⟨1461493302803779854722737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1948657737071706472963649 1461493302803779854722737)
            ·
              refine ⟨1096119977102834891042053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1461493302803779854722737 1096119977102834891042053)
              ·
                refine ⟨205522495706781542070385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1096119977102834891042053 205522495706781542070385)
                ·
                  refine ⟨154141871780086156552789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205522495706781542070385 154141871780086156552789)
                  ·
                    rfl

theorem cell20_337714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_337714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337714 prefixEnd_337714 := by exact prefixLift 337714
  have htrace : WordTrace (prefixWord ++ tailWord_337714) baseStart_337714 baseEnd_337714 := by
    simpa [prefixWord, tailWord_337714, baseEnd_337714] using wordTrace_append hprefix tailTrace_337714
  have hstable : (prefixWord ++ tailWord_337714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337714).length < 2 ^ (prefixWord ++ tailWord_337714).sum := by decide
  have hdescent : baseEnd_337714 < baseStart_337714 := by decide
  rcases family_descends (prefixWord ++ tailWord_337714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337749 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 5]
def baseStart_337749 : Nat := 118140960795 + 337749 * 2 ^ 59
def prefixEnd_337749 : Nat := 4983230072969 + 3 ^ 40 * 337749 * 2
def baseEnd_337749 : Nat := 154157846733781590385979

theorem tailTrace_337749 : CollatzResearch.WordTrace tailWord_337749 prefixEnd_337749 154157846733781590385979 := by
  unfold tailWord_337749
  simp only [CollatzResearch.WordTrace]
  refine ⟨12318718053400530781936301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8212478702267020521290867 12318718053400530781936301)
  ·
    refine ⟨4619519270025199043226113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12318718053400530781936301 4619519270025199043226113)
    ·
      refine ⟨3464639452518899282419585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4619519270025199043226113 3464639452518899282419585)
      ·
        refine ⟨2598479589389174461814689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3464639452518899282419585 2598479589389174461814689)
        ·
          refine ⟨1948859692041880846361017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2598479589389174461814689 1948859692041880846361017)
          ·
            refine ⟨1461644769031410634770763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1948859692041880846361017 1461644769031410634770763)
            ·
              refine ⟨2192467153547115952156145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1461644769031410634770763 2192467153547115952156145)
              ·
                refine ⟨1644350365160336964117109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2192467153547115952156145 1644350365160336964117109)
                ·
                  refine ⟨154157846733781590385979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1644350365160336964117109 154157846733781590385979)
                  ·
                    rfl

theorem cell20_337749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_337749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337749 prefixEnd_337749 := by exact prefixLift 337749
  have htrace : WordTrace (prefixWord ++ tailWord_337749) baseStart_337749 baseEnd_337749 := by
    simpa [prefixWord, tailWord_337749, baseEnd_337749] using wordTrace_append hprefix tailTrace_337749
  have hstable : (prefixWord ++ tailWord_337749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337749).length < 2 ^ (prefixWord ++ tailWord_337749).sum := by decide
  have hdescent : baseEnd_337749 < baseStart_337749 := by decide
  rcases family_descends (prefixWord ++ tailWord_337749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337773 : List Nat := [1, 5, 1, 1, 1, 1, 5, 1, 4]
def baseStart_337773 : Nat := 118140960795 + 337773 * 2 ^ 59
def prefixEnd_337773 : Nat := 4983230072969 + 3 ^ 40 * 337773 * 2
def baseEnd_337773 : Nat := 154168800987744173585881

theorem tailTrace_337773 : CollatzResearch.WordTrace tailWord_337773 prefixEnd_337773 154168800987744173585881 := by
  unfold tailWord_337773
  simp only [CollatzResearch.WordTrace]
  refine ⟨12319593405313582880809973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8213062270209055253873315 12319593405313582880809973)
  ·
    refine ⟨1154961881748148395075935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12319593405313582880809973 1154961881748148395075935)
    ·
      refine ⟨1732442822622222592613903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1154961881748148395075935 1732442822622222592613903)
      ·
        refine ⟨2598664233933333888920855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1732442822622222592613903 2598664233933333888920855)
        ·
          refine ⟨3897996350900000833381283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2598664233933333888920855 3897996350900000833381283)
          ·
            refine ⟨5846994526350001250071925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3897996350900000833381283 5846994526350001250071925)
            ·
              refine ⟨548155736845312617194243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5846994526350001250071925 548155736845312617194243)
              ·
                refine ⟨822233605267968925791365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548155736845312617194243 822233605267968925791365)
                ·
                  refine ⟨154168800987744173585881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 822233605267968925791365 154168800987744173585881)
                  ·
                    rfl

theorem cell20_337773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_337773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337773 prefixEnd_337773 := by exact prefixLift 337773
  have htrace : WordTrace (prefixWord ++ tailWord_337773) baseStart_337773 baseEnd_337773 := by
    simpa [prefixWord, tailWord_337773, baseEnd_337773] using wordTrace_append hprefix tailTrace_337773
  have hstable : (prefixWord ++ tailWord_337773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337773).length < 2 ^ (prefixWord ++ tailWord_337773).sum := by decide
  have hdescent : baseEnd_337773 < baseStart_337773 := by decide
  rcases family_descends (prefixWord ++ tailWord_337773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337801 : List Nat := [1, 2, 1, 1, 5, 1, 1, 8]
def baseStart_337801 : Nat := 118140960795 + 337801 * 2 ^ 59
def prefixEnd_337801 : Nat := 4983230072969 + 3 ^ 40 * 337801 * 2
def baseEnd_337801 : Nat := 51393860316900173550811

theorem tailTrace_337801 : CollatzResearch.WordTrace tailWord_337801 prefixEnd_337801 51393860316900173550811 := by
  unfold tailWord_337801
  simp only [CollatzResearch.WordTrace]
  refine ⟨12320614649212143662829257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8213743099474762441886171 12320614649212143662829257)
  ·
    refine ⟨9240460986909107747121943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12320614649212143662829257 9240460986909107747121943)
    ·
      refine ⟨13860691480363661620682915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9240460986909107747121943 13860691480363661620682915)
      ·
        refine ⟨20791037220545492431024373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13860691480363661620682915 20791037220545492431024373)
        ·
          refine ⟨1949159739426139915408535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20791037220545492431024373 1949159739426139915408535)
          ·
            refine ⟨2923739609139209873112803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1949159739426139915408535 2923739609139209873112803)
            ·
              refine ⟨4385609413708814809669205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923739609139209873112803 4385609413708814809669205)
              ·
                refine ⟨51393860316900173550811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4385609413708814809669205 51393860316900173550811)
                ·
                  rfl

theorem cell20_337801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 8].length) (baseStart_337801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337801 prefixEnd_337801 := by exact prefixLift 337801
  have htrace : WordTrace (prefixWord ++ tailWord_337801) baseStart_337801 baseEnd_337801 := by
    simpa [prefixWord, tailWord_337801, baseEnd_337801] using wordTrace_append hprefix tailTrace_337801
  have hstable : (prefixWord ++ tailWord_337801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337801).length < 2 ^ (prefixWord ++ tailWord_337801).sum := by decide
  have hdescent : baseEnd_337801 < baseStart_337801 := by decide
  rcases family_descends (prefixWord ++ tailWord_337801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337814 : List Nat := [5, 3, 1, 1, 2, 8]
def baseStart_337814 : Nat := 118140960795 + 337814 * 2 ^ 59
def prefixEnd_337814 : Nat := 4983230072969 + 3 ^ 40 * 337814 * 2
def baseEnd_337814 : Nat := 5710648685367787156261

theorem tailTrace_337814 : CollatzResearch.WordTrace tailWord_337814 prefixEnd_337814 5710648685367787156261 := by
  unfold tailWord_337814
  simp only [CollatzResearch.WordTrace]
  refine ⟨770068049885315430190781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8214059198776697922034997 770068049885315430190781)
  ·
    refine ⟨288775518706993286321543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 770068049885315430190781 288775518706993286321543)
    ·
      refine ⟨433163278060489929482315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288775518706993286321543 433163278060489929482315)
      ·
        refine ⟨649744917090734894223473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433163278060489929482315 649744917090734894223473)
        ·
          refine ⟨487308687818051170667605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 649744917090734894223473 487308687818051170667605)
          ·
            refine ⟨5710648685367787156261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 487308687818051170667605 5710648685367787156261)
            ·
              rfl

theorem cell20_337814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 8].length) (baseStart_337814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337814 prefixEnd_337814 := by exact prefixLift 337814
  have htrace : WordTrace (prefixWord ++ tailWord_337814) baseStart_337814 baseEnd_337814 := by
    simpa [prefixWord, tailWord_337814, baseEnd_337814] using wordTrace_append hprefix tailTrace_337814
  have hstable : (prefixWord ++ tailWord_337814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337814).length < 2 ^ (prefixWord ++ tailWord_337814).sum := by decide
  have hdescent : baseEnd_337814 < baseStart_337814 := by decide
  rcases family_descends (prefixWord ++ tailWord_337814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337828 : List Nat := [2, 3, 1, 2, 1, 4, 1, 4, 2]
def baseStart_337828 : Nat := 118140960795 + 337828 * 2 ^ 59
def prefixEnd_337828 : Nat := 4983230072969 + 3 ^ 40 * 337828 * 2
def baseEnd_337828 : Nat := 154193904486408426752323

theorem tailTrace_337828 : CollatzResearch.WordTrace tailWord_337828 prefixEnd_337828 154193904486408426752323 := by
  unfold tailWord_337828
  simp only [CollatzResearch.WordTrace]
  refine ⟨6160799710057163637031069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8214399613409551516041425 6160799710057163637031069)
  ·
    refine ⟨2310299891271436363886651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6160799710057163637031069 2310299891271436363886651)
    ·
      refine ⟨3465449836907154545829977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2310299891271436363886651 3465449836907154545829977)
      ·
        refine ⟨2599087377680365909372483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3465449836907154545829977 2599087377680365909372483)
        ·
          refine ⟨3898631066520548864058725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2599087377680365909372483 3898631066520548864058725)
          ·
            refine ⟨730993324972602912011011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3898631066520548864058725 730993324972602912011011)
            ·
              refine ⟨1096489987458904368016517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730993324972602912011011 1096489987458904368016517)
              ·
                refine ⟨205591872648544569003097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1096489987458904368016517 205591872648544569003097)
                ·
                  refine ⟨154193904486408426752323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205591872648544569003097 154193904486408426752323)
                  ·
                    rfl

theorem cell20_337828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_337828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337828 prefixEnd_337828 := by exact prefixLift 337828
  have htrace : WordTrace (prefixWord ++ tailWord_337828) baseStart_337828 baseEnd_337828 := by
    simpa [prefixWord, tailWord_337828, baseEnd_337828] using wordTrace_append hprefix tailTrace_337828
  have hstable : (prefixWord ++ tailWord_337828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337828).length < 2 ^ (prefixWord ++ tailWord_337828).sum := by decide
  have hdescent : baseEnd_337828 < baseStart_337828 := by decide
  rcases family_descends (prefixWord ++ tailWord_337828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337852 : List Nat := [2, 2, 2, 5, 1, 1, 3, 4]
def baseStart_337852 : Nat := 118140960795 + 337852 * 2 ^ 59
def prefixEnd_337852 : Nat := 4983230072969 + 3 ^ 40 * 337852 * 2
def baseEnd_337852 : Nat := 51401619580123669984075

theorem tailTrace_337852 : CollatzResearch.WordTrace tailWord_337852 prefixEnd_337852 51401619580123669984075 := by
  unfold tailWord_337852
  simp only [CollatzResearch.WordTrace]
  refine ⟨6161237386013689686467905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8214983181351586248623873 6161237386013689686467905)
  ·
    refine ⟨4620928039510267264850929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6161237386013689686467905 4620928039510267264850929)
    ·
      refine ⟨3465696029632700448638197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4620928039510267264850929 3465696029632700448638197)
      ·
        refine ⟨324909002778065667059831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3465696029632700448638197 324909002778065667059831)
        ·
          refine ⟨487363504167098500589747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324909002778065667059831 487363504167098500589747)
          ·
            refine ⟨731045256250647750884621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487363504167098500589747 731045256250647750884621)
            ·
              refine ⟨274141971093992906581733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 731045256250647750884621 274141971093992906581733)
              ·
                refine ⟨51401619580123669984075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 274141971093992906581733 51401619580123669984075)
                ·
                  rfl

theorem cell20_337852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 4].length) (baseStart_337852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337852 prefixEnd_337852 := by exact prefixLift 337852
  have htrace : WordTrace (prefixWord ++ tailWord_337852) baseStart_337852 baseEnd_337852 := by
    simpa [prefixWord, tailWord_337852, baseEnd_337852] using wordTrace_append hprefix tailTrace_337852
  have hstable : (prefixWord ++ tailWord_337852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337852).length < 2 ^ (prefixWord ++ tailWord_337852).sum := by decide
  have hdescent : baseEnd_337852 < baseStart_337852 := by decide
  rcases family_descends (prefixWord ++ tailWord_337852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337856 : List Nat := [2, 1, 1, 2, 3, 2, 5, 4]
def baseStart_337856 : Nat := 118140960795 + 337856 * 2 ^ 59
def prefixEnd_337856 : Nat := 4983230072969 + 3 ^ 40 * 337856 * 2
def baseEnd_337856 : Nat := 51402228149788257939625

theorem tailTrace_337856 : CollatzResearch.WordTrace tailWord_337856 prefixEnd_337856 51402228149788257939625 := by
  unfold tailWord_337856
  simp only [CollatzResearch.WordTrace]
  refine ⟨6161310332006444028040711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8215080442675258704054281 6161310332006444028040711)
  ·
    refine ⟨9241965498009666042061067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6161310332006444028040711 9241965498009666042061067)
    ·
      refine ⟨13862948247014499063091601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9241965498009666042061067 13862948247014499063091601)
      ·
        refine ⟨10397211185260874297318701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13862948247014499063091601 10397211185260874297318701)
        ·
          refine ⟨3898954194472827861494513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10397211185260874297318701 3898954194472827861494513)
          ·
            refine ⟨2924215645854620896120885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3898954194472827861494513 2924215645854620896120885)
            ·
              refine ⟨274145216798870709011333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2924215645854620896120885 274145216798870709011333)
              ·
                refine ⟨51402228149788257939625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 274145216798870709011333 51402228149788257939625)
                ·
                  rfl

theorem cell20_337856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 4].length) (baseStart_337856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337856 prefixEnd_337856 := by exact prefixLift 337856
  have htrace : WordTrace (prefixWord ++ tailWord_337856) baseStart_337856 baseEnd_337856 := by
    simpa [prefixWord, tailWord_337856, baseEnd_337856] using wordTrace_append hprefix tailTrace_337856
  have hstable : (prefixWord ++ tailWord_337856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337856).length < 2 ^ (prefixWord ++ tailWord_337856).sum := by decide
  have hdescent : baseEnd_337856 < baseStart_337856 := by decide
  rcases family_descends (prefixWord ++ tailWord_337856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337870 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_337870 : Nat := 118140960795 + 337870 * 2 ^ 59
def prefixEnd_337870 : Nat := 4983230072969 + 3 ^ 40 * 337870 * 2
def baseEnd_337870 : Nat := 154213074430842947352151

theorem tailTrace_337870 : CollatzResearch.WordTrace tailWord_337870 prefixEnd_337870 154213074430842947352151 := by
  unfold tailWord_337870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1540391410745271055886383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8215420857308112298060709 1540391410745271055886383)
  ·
    refine ⟨2310587116117906583829575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1540391410745271055886383 2310587116117906583829575)
    ·
      refine ⟨3465880674176859875744363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2310587116117906583829575 3465880674176859875744363)
      ·
        refine ⟨5198821011265289813616545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3465880674176859875744363 5198821011265289813616545)
        ·
          refine ⟨3899115758448967360212409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5198821011265289813616545 3899115758448967360212409)
          ·
            refine ⟨2924336818836725520159307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3899115758448967360212409 2924336818836725520159307)
            ·
              refine ⟨4386505228255088280238961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2924336818836725520159307 4386505228255088280238961)
              ·
                refine ⟨3289878921191316210179221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4386505228255088280238961 3289878921191316210179221)
                ·
                  refine ⟨154213074430842947352151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3289878921191316210179221 154213074430842947352151)
                  ·
                    rfl

theorem cell20_337870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_337870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337870 prefixEnd_337870 := by exact prefixLift 337870
  have htrace : WordTrace (prefixWord ++ tailWord_337870) baseStart_337870 baseEnd_337870 := by
    simpa [prefixWord, tailWord_337870, baseEnd_337870] using wordTrace_append hprefix tailTrace_337870
  have hstable : (prefixWord ++ tailWord_337870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337870).length < 2 ^ (prefixWord ++ tailWord_337870).sum := by decide
  have hdescent : baseEnd_337870 < baseStart_337870 := by decide
  rcases family_descends (prefixWord ++ tailWord_337870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337887 : List Nat := [1, 1, 2, 3, 4, 2, 2, 1, 4]
def baseStart_337887 : Nat := 118140960795 + 337887 * 2 ^ 59
def prefixEnd_337887 : Nat := 4983230072969 + 3 ^ 40 * 337887 * 2
def baseEnd_337887 : Nat := 154220833694066443785415

theorem tailTrace_337887 : CollatzResearch.WordTrace tailWord_337887 prefixEnd_337887 154220833694066443785415 := by
  unfold tailWord_337887
  simp only [CollatzResearch.WordTrace]
  refine ⟨12323751326900580350459915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8215834217933720233639943 12323751326900580350459915)
  ·
    refine ⟨18485626990350870525689873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12323751326900580350459915 18485626990350870525689873)
    ·
      refine ⟨13864220242763152894267405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18485626990350870525689873 13864220242763152894267405)
      ·
        refine ⟨5199082591036182335350277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13864220242763152894267405 5199082591036182335350277)
        ·
          refine ⟨974827985819284187878177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5199082591036182335350277 974827985819284187878177)
          ·
            refine ⟨731120989364463140908633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 974827985819284187878177 731120989364463140908633)
            ·
              refine ⟨548340742023347355681475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 731120989364463140908633 548340742023347355681475)
              ·
                refine ⟨822511113035021033522213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548340742023347355681475 822511113035021033522213)
                ·
                  refine ⟨154220833694066443785415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 822511113035021033522213 154220833694066443785415)
                  ·
                    rfl

theorem cell20_337887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 4].length) (baseStart_337887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337887 prefixEnd_337887 := by exact prefixLift 337887
  have htrace : WordTrace (prefixWord ++ tailWord_337887) baseStart_337887 baseEnd_337887 := by
    simpa [prefixWord, tailWord_337887, baseEnd_337887] using wordTrace_append hprefix tailTrace_337887
  have hstable : (prefixWord ++ tailWord_337887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337887).length < 2 ^ (prefixWord ++ tailWord_337887).sum := by decide
  have hdescent : baseEnd_337887 < baseStart_337887 := by decide
  rcases family_descends (prefixWord ++ tailWord_337887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337918 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_337918 : Nat := 118140960795 + 337918 * 2 ^ 59
def prefixEnd_337918 : Nat := 4983230072969 + 3 ^ 40 * 337918 * 2
def baseEnd_337918 : Nat := 154234982938768113751955

theorem tailTrace_337918 : CollatzResearch.WordTrace tailWord_337918 prefixEnd_337918 154234982938768113751955 := by
  unfold tailWord_337918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1540610248723534080604801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8216587993192181763225605 1540610248723534080604801)
  ·
    refine ⟨1155457686542650560453601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1540610248723534080604801 1155457686542650560453601)
    ·
      refine ⟨866593264906987920340201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1155457686542650560453601 866593264906987920340201)
      ·
        refine ⟨649944948680240940255151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 866593264906987920340201 649944948680240940255151)
        ·
          refine ⟨974917423020361410382727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 649944948680240940255151 974917423020361410382727)
          ·
            refine ⟨1462376134530542115574091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 974917423020361410382727 1462376134530542115574091)
            ·
              refine ⟨2193564201795813173361137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462376134530542115574091 2193564201795813173361137)
              ·
                refine ⟨1645173151346859880020853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2193564201795813173361137 1645173151346859880020853)
                ·
                  refine ⟨154234982938768113751955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1645173151346859880020853 154234982938768113751955)
                  ·
                    rfl

theorem cell20_337918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_337918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_337918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_337918 prefixEnd_337918 := by exact prefixLift 337918
  have htrace : WordTrace (prefixWord ++ tailWord_337918) baseStart_337918 baseEnd_337918 := by
    simpa [prefixWord, tailWord_337918, baseEnd_337918] using wordTrace_append hprefix tailTrace_337918
  have hstable : (prefixWord ++ tailWord_337918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337918).length < 2 ^ (prefixWord ++ tailWord_337918).sum := by decide
  have hdescent : baseEnd_337918 < baseStart_337918 := by decide
  rcases family_descends (prefixWord ++ tailWord_337918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338008 : List Nat := [2, 1, 2, 2, 1, 6, 1, 5]
def baseStart_338008 : Nat := 118140960795 + 338008 * 2 ^ 59
def prefixEnd_338008 : Nat := 4983230072969 + 3 ^ 40 * 338008 * 2
def baseEnd_338008 : Nat := 51425353797042600250529

theorem tailTrace_338008 : CollatzResearch.WordTrace tailWord_338008 prefixEnd_338008 51425353797042600250529 := by
  unfold tailWord_338008
  simp only [CollatzResearch.WordTrace]
  refine ⟨6164082279731109007807339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8218776372974812010409785 6164082279731109007807339)
  ·
    refine ⟨9246123419596663511711009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6164082279731109007807339 9246123419596663511711009)
    ·
      refine ⟨6934592564697497633783257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9246123419596663511711009 6934592564697497633783257)
      ·
        refine ⟨5200944423523123225337443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6934592564697497633783257 5200944423523123225337443)
        ·
          refine ⟨7801416635284684838006165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5200944423523123225337443 7801416635284684838006165)
          ·
            refine ⟨365691404778969601781539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7801416635284684838006165 365691404778969601781539)
            ·
              refine ⟨548537107168454402672309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365691404778969601781539 548537107168454402672309)
              ·
                refine ⟨51425353797042600250529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 548537107168454402672309 51425353797042600250529)
                ·
                  rfl

theorem cell20_338008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 5].length) (baseStart_338008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338008 prefixEnd_338008 := by exact prefixLift 338008
  have htrace : WordTrace (prefixWord ++ tailWord_338008) baseStart_338008 baseEnd_338008 := by
    simpa [prefixWord, tailWord_338008, baseEnd_338008] using wordTrace_append hprefix tailTrace_338008
  have hstable : (prefixWord ++ tailWord_338008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338008).length < 2 ^ (prefixWord ++ tailWord_338008).sum := by decide
  have hdescent : baseEnd_338008 < baseStart_338008 := by decide
  rcases family_descends (prefixWord ++ tailWord_338008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338018 : List Nat := [3, 3, 2, 2, 2, 1, 1, 2, 4]
def baseStart_338018 : Nat := 118140960795 + 338018 * 2 ^ 59
def prefixEnd_338018 : Nat := 4983230072969 + 3 ^ 40 * 338018 * 2
def baseEnd_338018 : Nat := 154280625663612210418213

theorem tailTrace_338018 : CollatzResearch.WordTrace tailWord_338018 prefixEnd_338018 154280625663612210418213 := by
  unfold tailWord_338018
  simp only [CollatzResearch.WordTrace]
  refine ⟨3082132322356497430869677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8219019526283993148985805 3082132322356497430869677)
  ·
    refine ⟨1155799620883686536576129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3082132322356497430869677 1155799620883686536576129)
    ·
      refine ⟨866849715662764902432097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1155799620883686536576129 866849715662764902432097)
      ·
        refine ⟨650137286747073676824073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 866849715662764902432097 650137286747073676824073)
        ·
          refine ⟨487602965060305257618055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 650137286747073676824073 487602965060305257618055)
          ·
            refine ⟨731404447590457886427083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487602965060305257618055 731404447590457886427083)
            ·
              refine ⟨1097106671385686829640625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731404447590457886427083 1097106671385686829640625)
              ·
                refine ⟨822830003539265122230469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1097106671385686829640625 822830003539265122230469)
                ·
                  refine ⟨154280625663612210418213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 822830003539265122230469 154280625663612210418213)
                  ·
                    rfl

theorem cell20_338018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_338018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338018 prefixEnd_338018 := by exact prefixLift 338018
  have htrace : WordTrace (prefixWord ++ tailWord_338018) baseStart_338018 baseEnd_338018 := by
    simpa [prefixWord, tailWord_338018, baseEnd_338018] using wordTrace_append hprefix tailTrace_338018
  have hstable : (prefixWord ++ tailWord_338018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338018).length < 2 ^ (prefixWord ++ tailWord_338018).sum := by decide
  have hdescent : baseEnd_338018 < baseStart_338018 := by decide
  rcases family_descends (prefixWord ++ tailWord_338018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338039 : List Nat := [1, 1, 3, 1, 1, 5, 1, 5, 2]
def baseStart_338039 : Nat := 118140960795 + 338039 * 2 ^ 59
def prefixEnd_338039 : Nat := 4983230072969 + 3 ^ 40 * 338039 * 2
def baseEnd_338039 : Nat := 154290210635829470718127

theorem tailTrace_338039 : CollatzResearch.WordTrace tailWord_338039 prefixEnd_338039 154290210635829470718127 := by
  unfold tailWord_338039
  simp only [CollatzResearch.WordTrace]
  refine ⟨12329295222349910309993171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8219530148233273539995447 12329295222349910309993171)
  ·
    refine ⟨18493942833524865464989757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12329295222349910309993171 18493942833524865464989757)
    ·
      refine ⟨6935228562571824549371159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18493942833524865464989757 6935228562571824549371159)
      ·
        refine ⟨10402842843857736824056739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6935228562571824549371159 10402842843857736824056739)
        ·
          refine ⟨15604264265786605236085109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10402842843857736824056739 15604264265786605236085109)
          ·
            refine ⟨1462899774917494240882979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15604264265786605236085109 1462899774917494240882979)
            ·
              refine ⟨2194349662376241361324469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462899774917494240882979 2194349662376241361324469)
              ·
                refine ⟨205720280847772627624169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2194349662376241361324469 205720280847772627624169)
                ·
                  refine ⟨154290210635829470718127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205720280847772627624169 154290210635829470718127)
                  ·
                    rfl

theorem cell20_338039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 2].length) (baseStart_338039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338039 prefixEnd_338039 := by exact prefixLift 338039
  have htrace : WordTrace (prefixWord ++ tailWord_338039) baseStart_338039 baseEnd_338039 := by
    simpa [prefixWord, tailWord_338039, baseEnd_338039] using wordTrace_append hprefix tailTrace_338039
  have hstable : (prefixWord ++ tailWord_338039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338039).length < 2 ^ (prefixWord ++ tailWord_338039).sum := by decide
  have hdescent : baseEnd_338039 < baseStart_338039 := by decide
  rcases family_descends (prefixWord ++ tailWord_338039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338049 : List Nat := [1, 2, 4, 2, 3, 2, 1, 2, 3]
def baseStart_338049 : Nat := 118140960795 + 338049 * 2 ^ 59
def prefixEnd_338049 : Nat := 4983230072969 + 3 ^ 40 * 338049 * 2
def baseEnd_338049 : Nat := 154294774908313880384753

theorem tailTrace_338049 : CollatzResearch.WordTrace tailWord_338049 prefixEnd_338049 154294774908313880384753 := by
  unfold tailWord_338049
  simp only [CollatzResearch.WordTrace]
  refine ⟨12329659952313682017857201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8219773301542454678571467 12329659952313682017857201)
  ·
    refine ⟨9247244964235261513392901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12329659952313682017857201 9247244964235261513392901)
    ·
      refine ⟨1733858430794111533761169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9247244964235261513392901 1733858430794111533761169)
      ·
        refine ⟨1300393823095583650320877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1733858430794111533761169 1300393823095583650320877)
        ·
          refine ⟨487647683660843868870329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1300393823095583650320877 487647683660843868870329)
          ·
            refine ⟨365735762745632901652747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 487647683660843868870329 365735762745632901652747)
            ·
              refine ⟨548603644118449352479121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365735762745632901652747 548603644118449352479121)
              ·
                refine ⟨411452733088837014359341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 548603644118449352479121 411452733088837014359341)
                ·
                  refine ⟨154294774908313880384753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 411452733088837014359341 154294774908313880384753)
                  ·
                    rfl

theorem cell20_338049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 3].length) (baseStart_338049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338049 prefixEnd_338049 := by exact prefixLift 338049
  have htrace : WordTrace (prefixWord ++ tailWord_338049) baseStart_338049 baseEnd_338049 := by
    simpa [prefixWord, tailWord_338049, baseEnd_338049] using wordTrace_append hprefix tailTrace_338049
  have hstable : (prefixWord ++ tailWord_338049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338049).length < 2 ^ (prefixWord ++ tailWord_338049).sum := by decide
  have hdescent : baseEnd_338049 < baseStart_338049 := by decide
  rcases family_descends (prefixWord ++ tailWord_338049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338053 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 5]
def baseStart_338053 : Nat := 118140960795 + 338053 * 2 ^ 59
def prefixEnd_338053 : Nat := 4983230072969 + 3 ^ 40 * 338053 * 2
def baseEnd_338053 : Nat := 154296600617307644251403

theorem tailTrace_338053 : CollatzResearch.WordTrace tailWord_338053 prefixEnd_338053 154296600617307644251403 := by
  unfold tailWord_338053
  simp only [CollatzResearch.WordTrace]
  refine ⟨12329805844299190701002813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8219870562866127134001875 12329805844299190701002813)
  ·
    refine ⟨4623677191612196512876055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12329805844299190701002813 4623677191612196512876055)
    ·
      refine ⟨6935515787418294769314083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4623677191612196512876055 6935515787418294769314083)
      ·
        refine ⟨10403273681127442153971125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6935515787418294769314083 10403273681127442153971125)
        ·
          refine ⟨975306907605697701934793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10403273681127442153971125 975306907605697701934793)
          ·
            refine ⟨731480180704273276451095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 975306907605697701934793 731480180704273276451095)
            ·
              refine ⟨1097220271056409914676643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731480180704273276451095 1097220271056409914676643)
              ·
                refine ⟨1645830406584614872014965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1097220271056409914676643 1645830406584614872014965)
                ·
                  refine ⟨154296600617307644251403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1645830406584614872014965 154296600617307644251403)
                  ·
                    rfl

theorem cell20_338053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_338053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338053 prefixEnd_338053 := by exact prefixLift 338053
  have htrace : WordTrace (prefixWord ++ tailWord_338053) baseStart_338053 baseEnd_338053 := by
    simpa [prefixWord, tailWord_338053, baseEnd_338053] using wordTrace_append hprefix tailTrace_338053
  have hstable : (prefixWord ++ tailWord_338053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338053).length < 2 ^ (prefixWord ++ tailWord_338053).sum := by decide
  have hdescent : baseEnd_338053 < baseStart_338053 := by decide
  rcases family_descends (prefixWord ++ tailWord_338053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338056 : List Nat := [2, 1, 3, 4, 1, 1, 2, 4, 2]
def baseStart_338056 : Nat := 118140960795 + 338056 * 2 ^ 59
def prefixEnd_338056 : Nat := 4983230072969 + 3 ^ 40 * 338056 * 2
def baseEnd_338056 : Nat := 154297969899052967151391

theorem tailTrace_338056 : CollatzResearch.WordTrace tailWord_338056 prefixEnd_338056 154297969899052967151391 := by
  unfold tailWord_338056
  simp only [CollatzResearch.WordTrace]
  refine ⟨6164957631644161106681011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8219943508858881475574681 6164957631644161106681011)
  ·
    refine ⟨9247436447466241660021517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6164957631644161106681011 9247436447466241660021517)
    ·
      refine ⟨3467788667799840622508069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9247436447466241660021517 3467788667799840622508069)
      ·
        refine ⟨650210375212470116720263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3467788667799840622508069 650210375212470116720263)
        ·
          refine ⟨975315562818705175080395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650210375212470116720263 975315562818705175080395)
          ·
            refine ⟨1462973344228057762620593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975315562818705175080395 1462973344228057762620593)
            ·
              refine ⟨1097230008171043321965445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1462973344228057762620593 1097230008171043321965445)
              ·
                refine ⟨205730626532070622868521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1097230008171043321965445 205730626532070622868521)
                ·
                  refine ⟨154297969899052967151391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205730626532070622868521 154297969899052967151391)
                  ·
                    rfl

theorem cell20_338056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 2].length) (baseStart_338056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338056 prefixEnd_338056 := by exact prefixLift 338056
  have htrace : WordTrace (prefixWord ++ tailWord_338056) baseStart_338056 baseEnd_338056 := by
    simpa [prefixWord, tailWord_338056, baseEnd_338056] using wordTrace_append hprefix tailTrace_338056
  have hstable : (prefixWord ++ tailWord_338056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338056).length < 2 ^ (prefixWord ++ tailWord_338056).sum := by decide
  have hdescent : baseEnd_338056 < baseStart_338056 := by decide
  rcases family_descends (prefixWord ++ tailWord_338056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338084 : List Nat := [2, 3, 1, 2, 4, 1, 1, 6]
def baseStart_338084 : Nat := 118140960795 + 338084 * 2 ^ 59
def prefixEnd_338084 : Nat := 4983230072969 + 3 ^ 40 * 338084 * 2
def baseEnd_338084 : Nat := 51436916620669771405981

theorem tailTrace_338084 : CollatzResearch.WordTrace tailWord_338084 prefixEnd_338084 51436916620669771405981 := by
  unfold tailWord_338084
  simp only [CollatzResearch.WordTrace]
  refine ⟨6165468253593441497690653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8220624338124588663587537 6165468253593441497690653)
  ·
    refine ⟨2312050595097540561633995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6165468253593441497690653 2312050595097540561633995)
    ·
      refine ⟨3468075892646310842450993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2312050595097540561633995 3468075892646310842450993)
      ·
        refine ⟨2601056919484733131838245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3468075892646310842450993 2601056919484733131838245)
        ·
          refine ⟨487698172403387462219671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2601056919484733131838245 487698172403387462219671)
          ·
            refine ⟨731547258605081193329507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487698172403387462219671 731547258605081193329507)
            ·
              refine ⟨1097320887907621789994261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731547258605081193329507 1097320887907621789994261)
              ·
                refine ⟨51436916620669771405981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1097320887907621789994261 51436916620669771405981)
                ·
                  rfl

theorem cell20_338084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_338084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338084 prefixEnd_338084 := by exact prefixLift 338084
  have htrace : WordTrace (prefixWord ++ tailWord_338084) baseStart_338084 baseEnd_338084 := by
    simpa [prefixWord, tailWord_338084, baseEnd_338084] using wordTrace_append hprefix tailTrace_338084
  have hstable : (prefixWord ++ tailWord_338084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338084).length < 2 ^ (prefixWord ++ tailWord_338084).sum := by decide
  have hdescent : baseEnd_338084 < baseStart_338084 := by decide
  rcases family_descends (prefixWord ++ tailWord_338084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338090 : List Nat := [3, 1, 5, 1, 2, 2, 1, 3, 2]
def baseStart_338090 : Nat := 118140960795 + 338090 * 2 ^ 59
def prefixEnd_338090 : Nat := 4983230072969 + 3 ^ 40 * 338090 * 2
def baseEnd_338090 : Nat := 154313488425499960017919

theorem tailTrace_338090 : CollatzResearch.WordTrace tailWord_338090 prefixEnd_338090 154313488425499960017919 := by
  unfold tailWord_338090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3082788836291286505024931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8220770230110097346733149 3082788836291286505024931)
  ·
    refine ⟨4624183254436929757537397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3082788836291286505024931 4624183254436929757537397)
    ·
      refine ⟨433517180103462164769131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4624183254436929757537397 433517180103462164769131)
      ·
        refine ⟨650275770155193247153697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433517180103462164769131 650275770155193247153697)
        ·
          refine ⟨487706827616394935365273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 650275770155193247153697 487706827616394935365273)
          ·
            refine ⟨365780120712296201523955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 487706827616394935365273 365780120712296201523955)
            ·
              refine ⟨548670181068444302285933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365780120712296201523955 548670181068444302285933)
              ·
                refine ⟨205751317900666613357225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 548670181068444302285933 205751317900666613357225)
                ·
                  refine ⟨154313488425499960017919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205751317900666613357225 154313488425499960017919)
                  ·
                    rfl

theorem cell20_338090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_338090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338090 prefixEnd_338090 := by exact prefixLift 338090
  have htrace : WordTrace (prefixWord ++ tailWord_338090) baseStart_338090 baseEnd_338090 := by
    simpa [prefixWord, tailWord_338090, baseEnd_338090] using wordTrace_append hprefix tailTrace_338090
  have hstable : (prefixWord ++ tailWord_338090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338090).length < 2 ^ (prefixWord ++ tailWord_338090).sum := by decide
  have hdescent : baseEnd_338090 < baseStart_338090 := by decide
  rcases family_descends (prefixWord ++ tailWord_338090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338101 : List Nat := [1, 3, 3, 4, 1, 2, 6]
def baseStart_338101 : Nat := 118140960795 + 338101 * 2 ^ 59
def prefixEnd_338101 : Nat := 4983230072969 + 3 ^ 40 * 338101 * 2
def baseEnd_338101 : Nat := 17146501013914756739023

theorem tailTrace_338101 : CollatzResearch.WordTrace tailWord_338101 prefixEnd_338101 17146501013914756739023 := by
  unfold tailWord_338101
  simp only [CollatzResearch.WordTrace]
  refine ⟨12331556548125294898750157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8221037698750196599166771 12331556548125294898750157)
  ·
    refine ⟨4624333705546985587031309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12331556548125294898750157 4624333705546985587031309)
    ·
      refine ⟨1734125139580119595136741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4624333705546985587031309 1734125139580119595136741)
      ·
        refine ⟨325148463671272424088139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1734125139580119595136741 325148463671272424088139)
        ·
          refine ⟨487722695506908636132209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325148463671272424088139 487722695506908636132209)
          ·
            refine ⟨365792021630181477099157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 487722695506908636132209 365792021630181477099157)
            ·
              refine ⟨17146501013914756739023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 365792021630181477099157 17146501013914756739023)
              ·
                rfl

theorem cell20_338101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 6].length) (baseStart_338101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338101 prefixEnd_338101 := by exact prefixLift 338101
  have htrace : WordTrace (prefixWord ++ tailWord_338101) baseStart_338101 baseEnd_338101 := by
    simpa [prefixWord, tailWord_338101, baseEnd_338101] using wordTrace_append hprefix tailTrace_338101
  have hstable : (prefixWord ++ tailWord_338101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338101).length < 2 ^ (prefixWord ++ tailWord_338101).sum := by decide
  have hdescent : baseEnd_338101 < baseStart_338101 := by decide
  rcases family_descends (prefixWord ++ tailWord_338101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338170 : List Nat := [3, 1, 1, 1, 1, 5, 4, 2, 2]
def baseStart_338170 : Nat := 118140960795 + 338170 * 2 ^ 59
def prefixEnd_338170 : Nat := 4983230072969 + 3 ^ 40 * 338170 * 2
def baseEnd_338170 : Nat := 154350002605375237350925

theorem tailTrace_338170 : CollatzResearch.WordTrace tailWord_338170 prefixEnd_338170 154350002605375237350925 := by
  unfold tailWord_338170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3083518296218829920752991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8222715456583546455341309 3083518296218829920752991)
  ·
    refine ⟨4625277444328244881129487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3083518296218829920752991 4625277444328244881129487)
    ·
      refine ⟨6937916166492367321694231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4625277444328244881129487 6937916166492367321694231)
      ·
        refine ⟨10406874249738550982541347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6937916166492367321694231 10406874249738550982541347)
        ·
          refine ⟨15610311374607826473812021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10406874249738550982541347 15610311374607826473812021)
          ·
            refine ⟨1463466691369483731919877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15610311374607826473812021 1463466691369483731919877)
            ·
              refine ⟨274400004631778199734977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1463466691369483731919877 274400004631778199734977)
              ·
                refine ⟨205800003473833649801233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274400004631778199734977 205800003473833649801233)
                ·
                  refine ⟨154350002605375237350925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205800003473833649801233 154350002605375237350925)
                  ·
                    rfl

theorem cell20_338170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_338170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338170 prefixEnd_338170 := by exact prefixLift 338170
  have htrace : WordTrace (prefixWord ++ tailWord_338170) baseStart_338170 baseEnd_338170 := by
    simpa [prefixWord, tailWord_338170, baseEnd_338170] using wordTrace_append hprefix tailTrace_338170
  have hstable : (prefixWord ++ tailWord_338170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338170).length < 2 ^ (prefixWord ++ tailWord_338170).sum := by decide
  have hdescent : baseEnd_338170 < baseStart_338170 := by decide
  rcases family_descends (prefixWord ++ tailWord_338170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338208 : List Nat := [2, 1, 1, 5, 2, 2, 2, 3, 2]
def baseStart_338208 : Nat := 118140960795 + 338208 * 2 ^ 59
def prefixEnd_338208 : Nat := 4983230072969 + 3 ^ 40 * 338208 * 2
def baseEnd_338208 : Nat := 154367346840815994084103

theorem tailTrace_338208 : CollatzResearch.WordTrace tailWord_338208 prefixEnd_338208 154367346840815994084103 := by
  unfold tailWord_338208
  simp only [CollatzResearch.WordTrace]
  refine ⟨6167729579368826086447639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8223639439158434781930185 6167729579368826086447639)
  ·
    refine ⟨9251594369053239129671459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6167729579368826086447639 9251594369053239129671459)
    ·
      refine ⟨13877391553579858694507189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9251594369053239129671459 13877391553579858694507189)
      ·
        refine ⟨1301005458148111752610049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13877391553579858694507189 1301005458148111752610049)
        ·
          refine ⟨975754093611083814457537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1301005458148111752610049 975754093611083814457537)
          ·
            refine ⟨731815570208312860843153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 975754093611083814457537 731815570208312860843153)
            ·
              refine ⟨548861677656234645632365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 731815570208312860843153 548861677656234645632365)
              ·
                refine ⟨205823129121087992112137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 548861677656234645632365 205823129121087992112137)
                ·
                  refine ⟨154367346840815994084103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205823129121087992112137 154367346840815994084103)
                  ·
                    rfl

theorem cell20_338208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 2].length) (baseStart_338208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338208 prefixEnd_338208 := by exact prefixLift 338208
  have htrace : WordTrace (prefixWord ++ tailWord_338208) baseStart_338208 baseEnd_338208 := by
    simpa [prefixWord, tailWord_338208, baseEnd_338208] using wordTrace_append hprefix tailTrace_338208
  have hstable : (prefixWord ++ tailWord_338208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338208).length < 2 ^ (prefixWord ++ tailWord_338208).sum := by decide
  have hdescent : baseEnd_338208 < baseStart_338208 := by decide
  rcases family_descends (prefixWord ++ tailWord_338208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338218 : List Nat := [3, 1, 4, 2, 3, 1, 1, 2, 3]
def baseStart_338218 : Nat := 118140960795 + 338218 * 2 ^ 59
def prefixEnd_338218 : Nat := 4983230072969 + 3 ^ 40 * 338218 * 2
def baseEnd_338218 : Nat := 154371911113300403750729

theorem tailTrace_338218 : CollatzResearch.WordTrace tailWord_338218 prefixEnd_338218 154371911113300403750729 := by
  unfold tailWord_338218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3083955972175355970189827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8223882592467615920506205 3083955972175355970189827)
  ·
    refine ⟨4625933958263033955284741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3083955972175355970189827 4625933958263033955284741)
    ·
      refine ⟨867362617174318866615889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4625933958263033955284741 867362617174318866615889)
      ·
        refine ⟨650521962880739149961917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 867362617174318866615889 650521962880739149961917)
        ·
          refine ⟨243945736080277181235719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 650521962880739149961917 243945736080277181235719)
          ·
            refine ⟨365918604120415771853579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243945736080277181235719 365918604120415771853579)
            ·
              refine ⟨548877906180623657780369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365918604120415771853579 548877906180623657780369)
              ·
                refine ⟨411658429635467743335277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 548877906180623657780369 411658429635467743335277)
                ·
                  refine ⟨154371911113300403750729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 411658429635467743335277 154371911113300403750729)
                  ·
                    rfl

theorem cell20_338218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_338218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338218 prefixEnd_338218 := by exact prefixLift 338218
  have htrace : WordTrace (prefixWord ++ tailWord_338218) baseStart_338218 baseEnd_338218 := by
    simpa [prefixWord, tailWord_338218, baseEnd_338218] using wordTrace_append hprefix tailTrace_338218
  have hstable : (prefixWord ++ tailWord_338218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338218).length < 2 ^ (prefixWord ++ tailWord_338218).sum := by decide
  have hdescent : baseEnd_338218 < baseStart_338218 := by decide
  rcases family_descends (prefixWord ++ tailWord_338218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338229 : List Nat := [1, 3, 3, 1, 2, 1, 1, 6, 2]
def baseStart_338229 : Nat := 118140960795 + 338229 * 2 ^ 59
def prefixEnd_338229 : Nat := 4983230072969 + 3 ^ 40 * 338229 * 2
def baseEnd_338229 : Nat := 154376931813033254384017

theorem tailTrace_338229 : CollatzResearch.WordTrace tailWord_338229 prefixEnd_338229 154376931813033254384017 := by
  unfold tailWord_338229
  simp only [CollatzResearch.WordTrace]
  refine ⟨12336225091661572759409741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8224150061107715172939827 12336225091661572759409741)
  ·
    refine ⟨4626084409373089784778653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12336225091661572759409741 4626084409373089784778653)
    ·
      refine ⟨1734781653514908669291995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4626084409373089784778653 1734781653514908669291995)
      ·
        refine ⟨2602172480272363003937993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1734781653514908669291995 2602172480272363003937993)
        ·
          refine ⟨1951629360204272252953495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2602172480272363003937993 1951629360204272252953495)
          ·
            refine ⟨2927444040306408379430243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1951629360204272252953495 2927444040306408379430243)
            ·
              refine ⟨4391166060459612569145365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2927444040306408379430243 4391166060459612569145365)
              ·
                refine ⟨205835909084044339178689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4391166060459612569145365 205835909084044339178689)
                ·
                  refine ⟨154376931813033254384017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205835909084044339178689 154376931813033254384017)
                  ·
                    rfl

theorem cell20_338229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_338229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338229 prefixEnd_338229 := by exact prefixLift 338229
  have htrace : WordTrace (prefixWord ++ tailWord_338229) baseStart_338229 baseEnd_338229 := by
    simpa [prefixWord, tailWord_338229, baseEnd_338229] using wordTrace_append hprefix tailTrace_338229
  have hstable : (prefixWord ++ tailWord_338229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338229).length < 2 ^ (prefixWord ++ tailWord_338229).sum := by decide
  have hdescent : baseEnd_338229 < baseStart_338229 := by decide
  rcases family_descends (prefixWord ++ tailWord_338229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338257 : List Nat := [1, 2, 2, 1, 4, 3, 1, 6]
def baseStart_338257 : Nat := 118140960795 + 338257 * 2 ^ 59
def prefixEnd_338257 : Nat := 4983230072969 + 3 ^ 40 * 338257 * 2
def baseEnd_338257 : Nat := 51463237258663200483523

theorem tailTrace_338257 : CollatzResearch.WordTrace tailWord_338257 prefixEnd_338257 51463237258663200483523 := by
  unfold tailWord_338257
  simp only [CollatzResearch.WordTrace]
  refine ⟨12337246335560133541429025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8224830890373422360952683 12337246335560133541429025)
  ·
    refine ⟨9252934751670100156071769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12337246335560133541429025 9252934751670100156071769)
    ·
      refine ⟨6939701063752575117053827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9252934751670100156071769 6939701063752575117053827)
      ·
        refine ⟨10409551595628862675580741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6939701063752575117053827 10409551595628862675580741)
        ·
          refine ⟨1951790924180411751671389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10409551595628862675580741 1951790924180411751671389)
          ·
            refine ⟨731921596567654406876771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1951790924180411751671389 731921596567654406876771)
            ·
              refine ⟨1097882394851481610315157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731921596567654406876771 1097882394851481610315157)
              ·
                refine ⟨51463237258663200483523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1097882394851481610315157 51463237258663200483523)
                ·
                  rfl

theorem cell20_338257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 6].length) (baseStart_338257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338257 prefixEnd_338257 := by exact prefixLift 338257
  have htrace : WordTrace (prefixWord ++ tailWord_338257) baseStart_338257 baseEnd_338257 := by
    simpa [prefixWord, tailWord_338257, baseEnd_338257] using wordTrace_append hprefix tailTrace_338257
  have hstable : (prefixWord ++ tailWord_338257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338257).length < 2 ^ (prefixWord ++ tailWord_338257).sum := by decide
  have hdescent : baseEnd_338257 < baseStart_338257 := by decide
  rcases family_descends (prefixWord ++ tailWord_338257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338271 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 6]
def baseStart_338271 : Nat := 118140960795 + 338271 * 2 ^ 59
def prefixEnd_338271 : Nat := 4983230072969 + 3 ^ 40 * 338271 * 2
def baseEnd_338271 : Nat := 154396101757467774983845

theorem tailTrace_338271 : CollatzResearch.WordTrace tailWord_338271 prefixEnd_338271 154396101757467774983845 := by
  unfold tailWord_338271
  simp only [CollatzResearch.WordTrace]
  refine ⟨12337756957509413932438667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8225171305006275954959111 12337756957509413932438667)
  ·
    refine ⟨18506635436264120898658001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12337756957509413932438667 18506635436264120898658001)
    ·
      refine ⟨13879976577198090673993501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18506635436264120898658001 13879976577198090673993501)
      ·
        refine ⟨5204991216449284002747563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13879976577198090673993501 5204991216449284002747563)
        ·
          refine ⟨7807486824673926004121345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5204991216449284002747563 7807486824673926004121345)
          ·
            refine ⟨5855615118505444503091009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7807486824673926004121345 5855615118505444503091009)
            ·
              refine ⟨4391711338879083377318257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5855615118505444503091009 4391711338879083377318257)
              ·
                refine ⟨3293783504159312532988693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4391711338879083377318257 3293783504159312532988693)
                ·
                  refine ⟨154396101757467774983845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3293783504159312532988693 154396101757467774983845)
                  ·
                    rfl

theorem cell20_338271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_338271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338271 prefixEnd_338271 := by exact prefixLift 338271
  have htrace : WordTrace (prefixWord ++ tailWord_338271) baseStart_338271 baseEnd_338271 := by
    simpa [prefixWord, tailWord_338271, baseEnd_338271] using wordTrace_append hprefix tailTrace_338271
  have hstable : (prefixWord ++ tailWord_338271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338271).length < 2 ^ (prefixWord ++ tailWord_338271).sum := by decide
  have hdescent : baseEnd_338271 < baseStart_338271 := by decide
  rcases family_descends (prefixWord ++ tailWord_338271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338274 : List Nat := [3, 3, 2, 1, 1, 4, 6]
def baseStart_338274 : Nat := 118140960795 + 338274 * 2 ^ 59
def prefixEnd_338274 : Nat := 4983230072969 + 3 ^ 40 * 338274 * 2
def baseEnd_338274 : Nat := 17155274559912566431537

theorem tailTrace_338274 : CollatzResearch.WordTrace tailWord_338274 prefixEnd_338274 17155274559912566431537 := by
  unfold tailWord_338274
  simp only [CollatzResearch.WordTrace]
  refine ⟨3084466594124636361199469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8225244250999030296531917 3084466594124636361199469)
  ·
    refine ⟨1156674972796738635449801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3084466594124636361199469 1156674972796738635449801)
    ·
      refine ⟨867506229597553976587351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1156674972796738635449801 867506229597553976587351)
      ·
        refine ⟨1301259344396330964881027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 867506229597553976587351 1301259344396330964881027)
        ·
          refine ⟨1951889016594496447321541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1301259344396330964881027 1951889016594496447321541)
          ·
            refine ⟨365979190611468083872789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1951889016594496447321541 365979190611468083872789)
            ·
              refine ⟨17155274559912566431537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 365979190611468083872789 17155274559912566431537)
              ·
                rfl

theorem cell20_338274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 6].length) (baseStart_338274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338274 prefixEnd_338274 := by exact prefixLift 338274
  have htrace : WordTrace (prefixWord ++ tailWord_338274) baseStart_338274 baseEnd_338274 := by
    simpa [prefixWord, tailWord_338274, baseEnd_338274] using wordTrace_append hprefix tailTrace_338274
  have hstable : (prefixWord ++ tailWord_338274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338274).length < 2 ^ (prefixWord ++ tailWord_338274).sum := by decide
  have hdescent : baseEnd_338274 < baseStart_338274 := by decide
  rcases family_descends (prefixWord ++ tailWord_338274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338284 : List Nat := [2, 2, 1, 1, 7, 1, 1, 1, 4]
def baseStart_338284 : Nat := 118140960795 + 338284 * 2 ^ 59
def prefixEnd_338284 : Nat := 4983230072969 + 3 ^ 40 * 338284 * 2
def baseEnd_338284 : Nat := 154402035311697507550459

theorem tailTrace_338284 : CollatzResearch.WordTrace tailWord_338284 prefixEnd_338284 154402035311697507550459 := by
  unfold tailWord_338284
  simp only [CollatzResearch.WordTrace]
  refine ⟨6169115553231158576330953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8225487404308211435107937 6169115553231158576330953)
  ·
    refine ⟨4626836664923368932248215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6169115553231158576330953 4626836664923368932248215)
    ·
      refine ⟨6940254997385053398372323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4626836664923368932248215 6940254997385053398372323)
      ·
        refine ⟨10410382496077580097558485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6940254997385053398372323 10410382496077580097558485)
        ·
          refine ⟨243993339751818283536527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 10410382496077580097558485 243993339751818283536527)
          ·
            refine ⟨365990009627727425304791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243993339751818283536527 365990009627727425304791)
            ·
              refine ⟨548985014441591137957187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365990009627727425304791 548985014441591137957187)
              ·
                refine ⟨823477521662386706935781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548985014441591137957187 823477521662386706935781)
                ·
                  refine ⟨154402035311697507550459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 823477521662386706935781 154402035311697507550459)
                  ·
                    rfl

theorem cell20_338284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_338284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338284 prefixEnd_338284 := by exact prefixLift 338284
  have htrace : WordTrace (prefixWord ++ tailWord_338284) baseStart_338284 baseEnd_338284 := by
    simpa [prefixWord, tailWord_338284, baseEnd_338284] using wordTrace_append hprefix tailTrace_338284
  have hstable : (prefixWord ++ tailWord_338284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338284).length < 2 ^ (prefixWord ++ tailWord_338284).sum := by decide
  have hdescent : baseEnd_338284 < baseStart_338284 := by decide
  rcases family_descends (prefixWord ++ tailWord_338284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338288 : List Nat := [2, 1, 1, 1, 4, 3, 3, 1, 4]
def baseStart_338288 : Nat := 118140960795 + 338288 * 2 ^ 59
def prefixEnd_338288 : Nat := 4983230072969 + 3 ^ 40 * 338288 * 2
def baseEnd_338288 : Nat := 154403861020691271417109

theorem tailTrace_338288 : CollatzResearch.WordTrace tailWord_338288 prefixEnd_338288 154403861020691271417109 := by
  unfold tailWord_338288
  simp only [CollatzResearch.WordTrace]
  refine ⟨6169188499223912917903759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8225584665631883890538345 6169188499223912917903759)
  ·
    refine ⟨9253782748835869376855639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6169188499223912917903759 9253782748835869376855639)
    ·
      refine ⟨13880674123253804065283459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9253782748835869376855639 13880674123253804065283459)
      ·
        refine ⟨20821011184880706097925189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13880674123253804065283459 20821011184880706097925189)
        ·
          refine ⟨3903939597165132393360973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20821011184880706097925189 3903939597165132393360973)
          ·
            refine ⟨1463977348936924647510365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3903939597165132393360973 1463977348936924647510365)
            ·
              refine ⟨548991505851346742816387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1463977348936924647510365 548991505851346742816387)
              ·
                refine ⟨823487258777020114224581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548991505851346742816387 823487258777020114224581)
                ·
                  refine ⟨154403861020691271417109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 823487258777020114224581 154403861020691271417109)
                  ·
                    rfl

theorem cell20_338288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_338288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338288 prefixEnd_338288 := by exact prefixLift 338288
  have htrace : WordTrace (prefixWord ++ tailWord_338288) baseStart_338288 baseEnd_338288 := by
    simpa [prefixWord, tailWord_338288, baseEnd_338288] using wordTrace_append hprefix tailTrace_338288
  have hstable : (prefixWord ++ tailWord_338288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338288).length < 2 ^ (prefixWord ++ tailWord_338288).sum := by decide
  have hdescent : baseEnd_338288 < baseStart_338288 := by decide
  rcases family_descends (prefixWord ++ tailWord_338288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338309 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 6]
def baseStart_338309 : Nat := 118140960795 + 338309 * 2 ^ 59
def prefixEnd_338309 : Nat := 4983230072969 + 3 ^ 40 * 338309 * 2
def baseEnd_338309 : Nat := 154413445992908531717023

theorem tailTrace_338309 : CollatzResearch.WordTrace tailWord_338309 prefixEnd_338309 154413445992908531717023 := by
  unfold tailWord_338309
  simp only [CollatzResearch.WordTrace]
  refine ⟨12339142931371746422321981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8226095287581164281547987 12339142931371746422321981)
  ·
    refine ⟨4627178599264404908370743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12339142931371746422321981 4627178599264404908370743)
    ·
      refine ⟨6940767898896607362556115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4627178599264404908370743 6940767898896607362556115)
      ·
        refine ⟨10411151848344911043834173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6940767898896607362556115 10411151848344911043834173)
        ·
          refine ⟨3904181943129341641437815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10411151848344911043834173 3904181943129341641437815)
          ·
            refine ⟨5856272914694012462156723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3904181943129341641437815 5856272914694012462156723)
            ·
              refine ⟨8784409372041018693235085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5856272914694012462156723 8784409372041018693235085)
              ·
                refine ⟨3294153514515382009963157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8784409372041018693235085 3294153514515382009963157)
                ·
                  refine ⟨154413445992908531717023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3294153514515382009963157 154413445992908531717023)
                  ·
                    rfl

theorem cell20_338309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_338309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338309 prefixEnd_338309 := by exact prefixLift 338309
  have htrace : WordTrace (prefixWord ++ tailWord_338309) baseStart_338309 baseEnd_338309 := by
    simpa [prefixWord, tailWord_338309, baseEnd_338309] using wordTrace_append hprefix tailTrace_338309
  have hstable : (prefixWord ++ tailWord_338309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338309).length < 2 ^ (prefixWord ++ tailWord_338309).sum := by decide
  have hdescent : baseEnd_338309 < baseStart_338309 := by decide
  rcases family_descends (prefixWord ++ tailWord_338309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338333 : List Nat := [1, 4, 2, 1, 4, 8]
def baseStart_338333 : Nat := 118140960795 + 338333 * 2 ^ 59
def prefixEnd_338333 : Nat := 4983230072969 + 3 ^ 40 * 338333 * 2
def baseEnd_338333 : Nat := 5719422231365596848775

theorem tailTrace_338333 : CollatzResearch.WordTrace tailWord_338333 prefixEnd_338333 5719422231365596848775 := by
  unfold tailWord_338333
  simp only [CollatzResearch.WordTrace]
  refine ⟨12340018283284798521195653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8226678855523199014130435 12340018283284798521195653)
  ·
    refine ⟨2313753428115899722724185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12340018283284798521195653 2313753428115899722724185)
    ·
      refine ⟨1735315071086924792043139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2313753428115899722724185 1735315071086924792043139)
      ·
        refine ⟨2602972606630387188064709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1735315071086924792043139 2602972606630387188064709)
        ·
          refine ⟨488057363743197597762133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2602972606630387188064709 488057363743197597762133)
          ·
            refine ⟨5719422231365596848775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 488057363743197597762133 5719422231365596848775)
            ·
              rfl

theorem cell20_338333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 8].length) (baseStart_338333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338333 prefixEnd_338333 := by exact prefixLift 338333
  have htrace : WordTrace (prefixWord ++ tailWord_338333) baseStart_338333 baseEnd_338333 := by
    simpa [prefixWord, tailWord_338333, baseEnd_338333] using wordTrace_append hprefix tailTrace_338333
  have hstable : (prefixWord ++ tailWord_338333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338333).length < 2 ^ (prefixWord ++ tailWord_338333).sum := by decide
  have hdescent : baseEnd_338333 < baseStart_338333 := by decide
  rcases family_descends (prefixWord ++ tailWord_338333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338340 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 5]
def baseStart_338340 : Nat := 118140960795 + 338340 * 2 ^ 59
def prefixEnd_338340 : Nat := 4983230072969 + 3 ^ 40 * 338340 * 2
def baseEnd_338340 : Nat := 154427595237610201683563

theorem tailTrace_338340 : CollatzResearch.WordTrace tailWord_338340 prefixEnd_338340 154427595237610201683563 := by
  unfold tailWord_338340
  simp only [CollatzResearch.WordTrace]
  refine ⟨6170136797129719358350237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8226849062839625811133649 6170136797129719358350237)
  ·
    refine ⟨2313801298923644759381339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6170136797129719358350237 2313801298923644759381339)
    ·
      refine ⟨3470701948385467139072009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2313801298923644759381339 3470701948385467139072009)
      ·
        refine ⟨2603026461289100354304007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3470701948385467139072009 2603026461289100354304007)
        ·
          refine ⟨3904539691933650531456011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2603026461289100354304007 3904539691933650531456011)
          ·
            refine ⟨5856809537900475797184017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3904539691933650531456011 5856809537900475797184017)
            ·
              refine ⟨4392607153425356847888013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5856809537900475797184017 4392607153425356847888013)
              ·
                refine ⟨1647227682534508817958005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4392607153425356847888013 1647227682534508817958005)
                ·
                  refine ⟨154427595237610201683563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1647227682534508817958005 154427595237610201683563)
                  ·
                    rfl

theorem cell20_338340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_338340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338340 prefixEnd_338340 := by exact prefixLift 338340
  have htrace : WordTrace (prefixWord ++ tailWord_338340) baseStart_338340 baseEnd_338340 := by
    simpa [prefixWord, tailWord_338340, baseEnd_338340] using wordTrace_append hprefix tailTrace_338340
  have hstable : (prefixWord ++ tailWord_338340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338340).length < 2 ^ (prefixWord ++ tailWord_338340).sum := by decide
  have hdescent : baseEnd_338340 < baseStart_338340 := by decide
  rcases family_descends (prefixWord ++ tailWord_338340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338364 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 6]
def baseStart_338364 : Nat := 118140960795 + 338364 * 2 ^ 59
def prefixEnd_338364 : Nat := 4983230072969 + 3 ^ 40 * 338364 * 2
def baseEnd_338364 : Nat := 154438549491572784883465

theorem tailTrace_338364 : CollatzResearch.WordTrace tailWord_338364 prefixEnd_338364 154438549491572784883465 := by
  unfold tailWord_338364
  simp only [CollatzResearch.WordTrace]
  refine ⟨6170574473086245407787073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8227432630781660543716097 6170574473086245407787073)
  ·
    refine ⟨4627930854814684055840305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6170574473086245407787073 4627930854814684055840305)
    ·
      refine ⟨3470948141111013041880229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4627930854814684055840305 3470948141111013041880229)
      ·
        refine ⟨650802776458314945352543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3470948141111013041880229 650802776458314945352543)
        ·
          refine ⟨976204164687472418028815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650802776458314945352543 976204164687472418028815)
          ·
            refine ⟨1464306247031208627043223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976204164687472418028815 1464306247031208627043223)
            ·
              refine ⟨2196459370546812940564835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1464306247031208627043223 2196459370546812940564835)
              ·
                refine ⟨3294689055820219410847253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2196459370546812940564835 3294689055820219410847253)
                ·
                  refine ⟨154438549491572784883465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3294689055820219410847253 154438549491572784883465)
                  ·
                    rfl

theorem cell20_338364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_338364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338364 prefixEnd_338364 := by exact prefixLift 338364
  have htrace : WordTrace (prefixWord ++ tailWord_338364) baseStart_338364 baseEnd_338364 := by
    simpa [prefixWord, tailWord_338364, baseEnd_338364] using wordTrace_append hprefix tailTrace_338364
  have hstable : (prefixWord ++ tailWord_338364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338364).length < 2 ^ (prefixWord ++ tailWord_338364).sum := by decide
  have hdescent : baseEnd_338364 < baseStart_338364 := by decide
  rcases family_descends (prefixWord ++ tailWord_338364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338378 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_338378 : Nat := 118140960795 + 338378 * 2 ^ 59
def prefixEnd_338378 : Nat := 4983230072969 + 3 ^ 40 * 338378 * 2
def baseEnd_338378 : Nat := 154444939473050958416741

theorem tailTrace_338378 : CollatzResearch.WordTrace tailWord_338378 prefixEnd_338378 154444939473050958416741 := by
  unfold tailWord_338378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3085414892030442801645947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8227773045414514137722525 3085414892030442801645947)
  ·
    refine ⟨4628122338045664202468921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3085414892030442801645947 4628122338045664202468921)
    ·
      refine ⟨3471091753534248151851691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4628122338045664202468921 3471091753534248151851691)
      ·
        refine ⟨5206637630301372227777537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3471091753534248151851691 5206637630301372227777537)
        ·
          refine ⟨3904978222726029170833153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5206637630301372227777537 3904978222726029170833153)
          ·
            refine ⟨2928733667044521878124865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3904978222726029170833153 2928733667044521878124865)
            ·
              refine ⟨2196550250283391408593649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2928733667044521878124865 2196550250283391408593649)
              ·
                refine ⟨1647412687712543556445237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2196550250283391408593649 1647412687712543556445237)
                ·
                  refine ⟨154444939473050958416741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1647412687712543556445237 154444939473050958416741)
                  ·
                    rfl

theorem cell20_338378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_338378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338378 prefixEnd_338378 := by exact prefixLift 338378
  have htrace : WordTrace (prefixWord ++ tailWord_338378) baseStart_338378 baseEnd_338378 := by
    simpa [prefixWord, tailWord_338378, baseEnd_338378] using wordTrace_append hprefix tailTrace_338378
  have hstable : (prefixWord ++ tailWord_338378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338378).length < 2 ^ (prefixWord ++ tailWord_338378).sum := by decide
  have hdescent : baseEnd_338378 < baseStart_338378 := by decide
  rcases family_descends (prefixWord ++ tailWord_338378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338436 : List Nat := [2, 3, 2, 3, 1, 1, 3, 3, 2]
def baseStart_338436 : Nat := 118140960795 + 338436 * 2 ^ 59
def prefixEnd_338436 : Nat := 4983230072969 + 3 ^ 40 * 338436 * 2
def baseEnd_338436 : Nat := 154471412253460534483171

theorem tailTrace_338436 : CollatzResearch.WordTrace tailWord_338436 prefixEnd_338436 154471412253460534483171 := by
  unfold tailWord_338436
  simp only [CollatzResearch.WordTrace]
  refine ⟨6171887500955823556097581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8229183334607764741463441 6171887500955823556097581)
  ·
    refine ⟨2314457812858433833536593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6171887500955823556097581 2314457812858433833536593)
    ·
      refine ⟨1735843359643825375152445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2314457812858433833536593 1735843359643825375152445)
      ·
        refine ⟨650941259866434515682167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1735843359643825375152445 650941259866434515682167)
        ·
          refine ⟨976411889799651773523251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650941259866434515682167 976411889799651773523251)
          ·
            refine ⟨1464617834699477660284877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976411889799651773523251 1464617834699477660284877)
            ·
              refine ⟨549231688012304122606829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1464617834699477660284877 549231688012304122606829)
              ·
                refine ⟨205961883004614045977561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 549231688012304122606829 205961883004614045977561)
                ·
                  refine ⟨154471412253460534483171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205961883004614045977561 154471412253460534483171)
                  ·
                    rfl

theorem cell20_338436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_338436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338436 prefixEnd_338436 := by exact prefixLift 338436
  have htrace : WordTrace (prefixWord ++ tailWord_338436) baseStart_338436 baseEnd_338436 := by
    simpa [prefixWord, tailWord_338436, baseEnd_338436] using wordTrace_append hprefix tailTrace_338436
  have hstable : (prefixWord ++ tailWord_338436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338436).length < 2 ^ (prefixWord ++ tailWord_338436).sum := by decide
  have hdescent : baseEnd_338436 < baseStart_338436 := by decide
  rcases family_descends (prefixWord ++ tailWord_338436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338464 : List Nat := [2, 1, 1, 6, 2, 1, 2, 5]
def baseStart_338464 : Nat := 118140960795 + 338464 * 2 ^ 59
def prefixEnd_338464 : Nat := 4983230072969 + 3 ^ 40 * 338464 * 2
def baseEnd_338464 : Nat := 51494730738805627183241

theorem tailTrace_338464 : CollatzResearch.WordTrace tailWord_338464 prefixEnd_338464 51494730738805627183241 := by
  unfold tailWord_338464
  simp only [CollatzResearch.WordTrace]
  refine ⟨6172398122905103947107223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8229864163873471929476297 6172398122905103947107223)
  ·
    refine ⟨9258597184357655920660835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6172398122905103947107223 9258597184357655920660835)
    ·
      refine ⟨13887895776536483880991253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9258597184357655920660835 13887895776536483880991253)
      ·
        refine ⟨650995114525147681921465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13887895776536483880991253 650995114525147681921465)
        ·
          refine ⟨488246335893860761441099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 650995114525147681921465 488246335893860761441099)
          ·
            refine ⟨732369503840791142161649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488246335893860761441099 732369503840791142161649)
            ·
              refine ⟨549277127880593356621237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 732369503840791142161649 549277127880593356621237)
              ·
                refine ⟨51494730738805627183241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 549277127880593356621237 51494730738805627183241)
                ·
                  rfl

theorem cell20_338464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_338464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338464 prefixEnd_338464 := by exact prefixLift 338464
  have htrace : WordTrace (prefixWord ++ tailWord_338464) baseStart_338464 baseEnd_338464 := by
    simpa [prefixWord, tailWord_338464, baseEnd_338464] using wordTrace_append hprefix tailTrace_338464
  have hstable : (prefixWord ++ tailWord_338464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338464).length < 2 ^ (prefixWord ++ tailWord_338464).sum := by decide
  have hdescent : baseEnd_338464 < baseStart_338464 := by decide
  rcases family_descends (prefixWord ++ tailWord_338464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338502 : List Nat := [6, 1, 1, 1, 2, 9]
def baseStart_338502 : Nat := 118140960795 + 338502 * 2 ^ 59
def prefixEnd_338502 : Nat := 4983230072969 + 3 ^ 40 * 338502 * 2
def baseEnd_338502 : Nat := 5722279127846579195663

theorem tailTrace_338502 : CollatzResearch.WordTrace tailWord_338502 prefixEnd_338502 5722279127846579195663 := by
  unfold tailWord_338502
  simp only [CollatzResearch.WordTrace]
  refine ⟨385818194364766887003055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8230788146448360256065173 385818194364766887003055)
  ·
    refine ⟨578727291547150330504583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 385818194364766887003055 578727291547150330504583)
    ·
      refine ⟨868090937320725495756875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 578727291547150330504583 868090937320725495756875)
      ·
        refine ⟨1302136405981088243635313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 868090937320725495756875 1302136405981088243635313)
        ·
          refine ⟨976602304485816182726485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1302136405981088243635313 976602304485816182726485)
          ·
            refine ⟨5722279127846579195663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 976602304485816182726485 5722279127846579195663)
            ·
              rfl

theorem cell20_338502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 9].length) (baseStart_338502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338502 prefixEnd_338502 := by exact prefixLift 338502
  have htrace : WordTrace (prefixWord ++ tailWord_338502) baseStart_338502 baseEnd_338502 := by
    simpa [prefixWord, tailWord_338502, baseEnd_338502] using wordTrace_append hprefix tailTrace_338502
  have hstable : (prefixWord ++ tailWord_338502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338502).length < 2 ^ (prefixWord ++ tailWord_338502).sum := by decide
  have hdescent : baseEnd_338502 < baseStart_338502 := by decide
  rcases family_descends (prefixWord ++ tailWord_338502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338506 : List Nat := [3, 1, 2, 1, 1, 12]
def baseStart_338506 : Nat := 118140960795 + 338506 * 2 ^ 59
def prefixEnd_338506 : Nat := 4983230072969 + 3 ^ 40 * 338506 * 2
def baseEnd_338506 : Nat := 5722346746698200079613

theorem tailTrace_338506 : CollatzResearch.WordTrace tailWord_338506 prefixEnd_338506 5722346746698200079613 := by
  unfold tailWord_338506
  simp only [CollatzResearch.WordTrace]
  refine ⟨3086582027914512266810843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8230885407772032711495581 3086582027914512266810843)
  ·
    refine ⟨4629873041871768400216265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3086582027914512266810843 4629873041871768400216265)
    ·
      refine ⟨3472404781403826300162199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4629873041871768400216265 3472404781403826300162199)
      ·
        refine ⟨5208607172105739450243299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3472404781403826300162199 5208607172105739450243299)
        ·
          refine ⟨7812910758158609175364949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5208607172105739450243299 7812910758158609175364949)
          ·
            refine ⟨5722346746698200079613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 7812910758158609175364949 5722346746698200079613)
            ·
              rfl

theorem cell20_338506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 12].length) (baseStart_338506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338506 prefixEnd_338506 := by exact prefixLift 338506
  have htrace : WordTrace (prefixWord ++ tailWord_338506) baseStart_338506 baseEnd_338506 := by
    simpa [prefixWord, tailWord_338506, baseEnd_338506] using wordTrace_append hprefix tailTrace_338506
  have hstable : (prefixWord ++ tailWord_338506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338506).length < 2 ^ (prefixWord ++ tailWord_338506).sum := by decide
  have hdescent : baseEnd_338506 < baseStart_338506 := by decide
  rcases family_descends (prefixWord ++ tailWord_338506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338564 : List Nat := [2, 3, 2, 1, 3, 3, 1, 2, 3]
def baseStart_338564 : Nat := 118140960795 + 338564 * 2 ^ 59
def prefixEnd_338564 : Nat := 4983230072969 + 3 ^ 40 * 338564 * 2
def baseEnd_338564 : Nat := 154529834941260978215981

theorem tailTrace_338564 : CollatzResearch.WordTrace tailWord_338564 prefixEnd_338564 154529834941260978215981 := by
  unfold tailWord_338564
  simp only [CollatzResearch.WordTrace]
  refine ⟨6174221772723962486427373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8232295696965283315236497 6174221772723962486427373)
  ·
    refine ⟨2315333164771485932410265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6174221772723962486427373 2315333164771485932410265)
    ·
      refine ⟨1736499873578614449307699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2315333164771485932410265 1736499873578614449307699)
      ·
        refine ⟨2604749810367921673961549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1736499873578614449307699 2604749810367921673961549)
        ·
          refine ⟨976781178887970627735581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2604749810367921673961549 976781178887970627735581)
          ·
            refine ⟨366292942082988985400843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 976781178887970627735581 366292942082988985400843)
            ·
              refine ⟨549439413124483478101265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366292942082988985400843 549439413124483478101265)
              ·
                refine ⟨412079559843362608575949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 549439413124483478101265 412079559843362608575949)
                ·
                  refine ⟨154529834941260978215981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 412079559843362608575949 154529834941260978215981)
                  ·
                    rfl

theorem cell20_338564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_338564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338564 prefixEnd_338564 := by exact prefixLift 338564
  have htrace : WordTrace (prefixWord ++ tailWord_338564) baseStart_338564 baseEnd_338564 := by
    simpa [prefixWord, tailWord_338564, baseEnd_338564] using wordTrace_append hprefix tailTrace_338564
  have hstable : (prefixWord ++ tailWord_338564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338564).length < 2 ^ (prefixWord ++ tailWord_338564).sum := by decide
  have hdescent : baseEnd_338564 < baseStart_338564 := by decide
  rcases family_descends (prefixWord ++ tailWord_338564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338585 : List Nat := [1, 2, 1, 2, 1, 2, 7, 1, 3]
def baseStart_338585 : Nat := 118140960795 + 338585 * 2 ^ 59
def prefixEnd_338585 : Nat := 4983230072969 + 3 ^ 40 * 338585 * 2
def baseEnd_338585 : Nat := 154539419913478238515895

theorem tailTrace_338585 : CollatzResearch.WordTrace tailWord_338585 prefixEnd_338585 154539419913478238515895 := by
  unfold tailWord_338585
  simp only [CollatzResearch.WordTrace]
  refine ⟨12349209478371845559369209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8232806318914563706246139 12349209478371845559369209)
  ·
    refine ⟨9261907108778884169526907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12349209478371845559369209 9261907108778884169526907)
    ·
      refine ⟨13892860663168326254290361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9261907108778884169526907 13892860663168326254290361)
      ·
        refine ⟨10419645497376244690717771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13892860663168326254290361 10419645497376244690717771)
        ·
          refine ⟨15629468246064367036076657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10419645497376244690717771 15629468246064367036076657)
          ·
            refine ⟨11722101184548275277057493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15629468246064367036076657 11722101184548275277057493)
            ·
              refine ⟨274736746512850201806035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11722101184548275277057493 274736746512850201806035)
              ·
                refine ⟨412105119769275302709053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274736746512850201806035 412105119769275302709053)
                ·
                  refine ⟨154539419913478238515895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 412105119769275302709053 154539419913478238515895)
                  ·
                    rfl

theorem cell20_338585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 3].length) (baseStart_338585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338585 prefixEnd_338585 := by exact prefixLift 338585
  have htrace : WordTrace (prefixWord ++ tailWord_338585) baseStart_338585 baseEnd_338585 := by
    simpa [prefixWord, tailWord_338585, baseEnd_338585] using wordTrace_append hprefix tailTrace_338585
  have hstable : (prefixWord ++ tailWord_338585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338585).length < 2 ^ (prefixWord ++ tailWord_338585).sum := by decide
  have hdescent : baseEnd_338585 < baseStart_338585 := by decide
  rcases family_descends (prefixWord ++ tailWord_338585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338665 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 7]
def baseStart_338665 : Nat := 118140960795 + 338665 * 2 ^ 59
def prefixEnd_338665 : Nat := 4983230072969 + 3 ^ 40 * 338665 * 2
def baseEnd_338665 : Nat := 154575934093353515848901

theorem tailTrace_338665 : CollatzResearch.WordTrace tailWord_338665 prefixEnd_338665 154575934093353515848901 := by
  unfold tailWord_338665
  simp only [CollatzResearch.WordTrace]
  refine ⟨12352127318082019222281449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8234751545388012814854299 12352127318082019222281449)
  ·
    refine ⟨9264095488561514416711087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12352127318082019222281449 9264095488561514416711087)
    ·
      refine ⟨13896143232842271625066631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9264095488561514416711087 13896143232842271625066631)
      ·
        refine ⟨20844214849263407437599947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13896143232842271625066631 20844214849263407437599947)
        ·
          refine ⟨31266322273895111156399921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20844214849263407437599947 31266322273895111156399921)
          ·
            refine ⟨23449741705421333367299941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31266322273895111156399921 23449741705421333367299941)
            ·
              refine ⟨4396826569766500006368739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23449741705421333367299941 4396826569766500006368739)
              ·
                refine ⟨6595239854649750009553109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4396826569766500006368739 6595239854649750009553109)
                ·
                  refine ⟨154575934093353515848901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6595239854649750009553109 154575934093353515848901)
                  ·
                    rfl

theorem cell20_338665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_338665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338665 prefixEnd_338665 := by exact prefixLift 338665
  have htrace : WordTrace (prefixWord ++ tailWord_338665) baseStart_338665 baseEnd_338665 := by
    simpa [prefixWord, tailWord_338665, baseEnd_338665] using wordTrace_append hprefix tailTrace_338665
  have hstable : (prefixWord ++ tailWord_338665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338665).length < 2 ^ (prefixWord ++ tailWord_338665).sum := by decide
  have hdescent : baseEnd_338665 < baseStart_338665 := by decide
  rcases family_descends (prefixWord ++ tailWord_338665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338668 : List Nat := [2, 2, 1, 1, 2, 2, 1, 7, 2]
def baseStart_338668 : Nat := 118140960795 + 338668 * 2 ^ 59
def prefixEnd_338668 : Nat := 4983230072969 + 3 ^ 40 * 338668 * 2
def baseEnd_338668 : Nat := 154577303375098838748889

theorem tailTrace_338668 : CollatzResearch.WordTrace tailWord_338668 prefixEnd_338668 154577303375098838748889 := by
  unfold tailWord_338668
  simp only [CollatzResearch.WordTrace]
  refine ⟨6176118368535575367320329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8234824491380767156427105 6176118368535575367320329)
  ·
    refine ⟨4632088776401681525490247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6176118368535575367320329 4632088776401681525490247)
    ·
      refine ⟨6948133164602522288235371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4632088776401681525490247 6948133164602522288235371)
      ·
        refine ⟨10422199746903783432353057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6948133164602522288235371 10422199746903783432353057)
        ·
          refine ⟨7816649810177837574264793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10422199746903783432353057 7816649810177837574264793)
          ·
            refine ⟨5862487357633378180698595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7816649810177837574264793 5862487357633378180698595)
            ·
              refine ⟨8793731036450067271047893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5862487357633378180698595 8793731036450067271047893)
              ·
                refine ⟨206103071166798451665185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8793731036450067271047893 206103071166798451665185)
                ·
                  refine ⟨154577303375098838748889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206103071166798451665185 154577303375098838748889)
                  ·
                    rfl

theorem cell20_338668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_338668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338668 prefixEnd_338668 := by exact prefixLift 338668
  have htrace : WordTrace (prefixWord ++ tailWord_338668) baseStart_338668 baseEnd_338668 := by
    simpa [prefixWord, tailWord_338668, baseEnd_338668] using wordTrace_append hprefix tailTrace_338668
  have hstable : (prefixWord ++ tailWord_338668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338668).length < 2 ^ (prefixWord ++ tailWord_338668).sum := by decide
  have hdescent : baseEnd_338668 < baseStart_338668 := by decide
  rcases family_descends (prefixWord ++ tailWord_338668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338677 : List Nat := [1, 3, 6, 1, 1, 2, 2, 2, 2]
def baseStart_338677 : Nat := 118140960795 + 338677 * 2 ^ 59
def prefixEnd_338677 : Nat := 4983230072969 + 3 ^ 40 * 338677 * 2
def baseEnd_338677 : Nat := 154581411220334807448853

theorem tailTrace_338677 : CollatzResearch.WordTrace tailWord_338677 prefixEnd_338677 154581411220334807448853 := by
  unfold tailWord_338677
  simp only [CollatzResearch.WordTrace]
  refine ⟨12352564994038545271718285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8235043329359030181145523 12352564994038545271718285)
  ·
    refine ⟨4632211872764454476894357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12352564994038545271718285 4632211872764454476894357)
    ·
      refine ⟨217134931535833803604423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4632211872764454476894357 217134931535833803604423)
      ·
        refine ⟨325702397303750705406635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217134931535833803604423 325702397303750705406635)
        ·
          refine ⟨488553595955626058109953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325702397303750705406635 488553595955626058109953)
          ·
            refine ⟨366415196966719543582465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488553595955626058109953 366415196966719543582465)
            ·
              refine ⟨274811397725039657686849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366415196966719543582465 274811397725039657686849)
              ·
                refine ⟨206108548293779743265137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274811397725039657686849 206108548293779743265137)
                ·
                  refine ⟨154581411220334807448853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206108548293779743265137 154581411220334807448853)
                  ·
                    rfl

theorem cell20_338677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_338677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338677 prefixEnd_338677 := by exact prefixLift 338677
  have htrace : WordTrace (prefixWord ++ tailWord_338677) baseStart_338677 baseEnd_338677 := by
    simpa [prefixWord, tailWord_338677, baseEnd_338677] using wordTrace_append hprefix tailTrace_338677
  have hstable : (prefixWord ++ tailWord_338677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338677).length < 2 ^ (prefixWord ++ tailWord_338677).sum := by decide
  have hdescent : baseEnd_338677 < baseStart_338677 := by decide
  rcases family_descends (prefixWord ++ tailWord_338677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338682 : List Nat := [3, 1, 1, 1, 1, 3, 3, 4, 3]
def baseStart_338682 : Nat := 118140960795 + 338682 * 2 ^ 59
def prefixEnd_338682 : Nat := 4983230072969 + 3 ^ 40 * 338682 * 2
def baseEnd_338682 : Nat := 154583693356577012282165

theorem tailTrace_338682 : CollatzResearch.WordTrace tailWord_338682 prefixEnd_338682 154583693356577012282165 := by
  unfold tailWord_338682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3088186839755107781412575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8235164906013620750433533 3088186839755107781412575)
  ·
    refine ⟨4632280259632661672118863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3088186839755107781412575 4632280259632661672118863)
    ·
      refine ⟨6948420389448992508178295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4632280259632661672118863 6948420389448992508178295)
      ·
        refine ⟨10422630584173488762267443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6948420389448992508178295 10422630584173488762267443)
        ·
          refine ⟨15633945876260233143401165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10422630584173488762267443 15633945876260233143401165)
          ·
            refine ⟨5862729703597587428775437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15633945876260233143401165 5862729703597587428775437)
            ·
              refine ⟨2198523638849095285790789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5862729703597587428775437 2198523638849095285790789)
              ·
                refine ⟨412223182284205366085773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2198523638849095285790789 412223182284205366085773)
                ·
                  refine ⟨154583693356577012282165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 412223182284205366085773 154583693356577012282165)
                  ·
                    rfl

theorem cell20_338682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_338682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338682 prefixEnd_338682 := by exact prefixLift 338682
  have htrace : WordTrace (prefixWord ++ tailWord_338682) baseStart_338682 baseEnd_338682 := by
    simpa [prefixWord, tailWord_338682, baseEnd_338682] using wordTrace_append hprefix tailTrace_338682
  have hstable : (prefixWord ++ tailWord_338682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338682).length < 2 ^ (prefixWord ++ tailWord_338682).sum := by decide
  have hdescent : baseEnd_338682 < baseStart_338682 := by decide
  rcases family_descends (prefixWord ++ tailWord_338682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338689 : List Nat := [1, 2, 4, 1, 1, 1, 1, 5, 4]
def baseStart_338689 : Nat := 118140960795 + 338689 * 2 ^ 59
def prefixEnd_338689 : Nat := 4983230072969 + 3 ^ 40 * 338689 * 2
def baseEnd_338689 : Nat := 154586888347316099048803

theorem tailTrace_338689 : CollatzResearch.WordTrace tailWord_338689 prefixEnd_338689 154586888347316099048803 := by
  unfold tailWord_338689
  simp only [CollatzResearch.WordTrace]
  refine ⟨12353002669995071321155121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8235335113330047547436747 12353002669995071321155121)
  ·
    refine ⟨9264752002496303490866341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12353002669995071321155121 9264752002496303490866341)
    ·
      refine ⟨1737141000468056904537439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9264752002496303490866341 1737141000468056904537439)
      ·
        refine ⟨2605711500702085356806159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1737141000468056904537439 2605711500702085356806159)
        ·
          refine ⟨3908567251053128035209239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2605711500702085356806159 3908567251053128035209239)
          ·
            refine ⟨5862850876579692052813859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3908567251053128035209239 5862850876579692052813859)
            ·
              refine ⟨8794276314869538079220789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5862850876579692052813859 8794276314869538079220789)
              ·
                refine ⟨824463404519019194926949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8794276314869538079220789 824463404519019194926949)
                ·
                  refine ⟨154586888347316099048803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 824463404519019194926949 154586888347316099048803)
                  ·
                    rfl

theorem cell20_338689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_338689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338689 prefixEnd_338689 := by exact prefixLift 338689
  have htrace : WordTrace (prefixWord ++ tailWord_338689) baseStart_338689 baseEnd_338689 := by
    simpa [prefixWord, tailWord_338689, baseEnd_338689] using wordTrace_append hprefix tailTrace_338689
  have hstable : (prefixWord ++ tailWord_338689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338689).length < 2 ^ (prefixWord ++ tailWord_338689).sum := by decide
  have hdescent : baseEnd_338689 < baseStart_338689 := by decide
  rcases family_descends (prefixWord ++ tailWord_338689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338730 : List Nat := [3, 1, 4, 3, 1, 1, 7]
def baseStart_338730 : Nat := 118140960795 + 338730 * 2 ^ 59
def prefixEnd_338730 : Nat := 4983230072969 + 3 ^ 40 * 338730 * 2
def baseEnd_338730 : Nat := 17178400207166908742441

theorem tailTrace_338730 : CollatzResearch.WordTrace tailWord_338730 prefixEnd_338730 17178400207166908742441 := by
  unfold tailWord_338730
  simp only [CollatzResearch.WordTrace]
  refine ⟨3088624515711633830849411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8236332041897690215598429 3088624515711633830849411)
  ·
    refine ⟨4632936773567450746274117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3088624515711633830849411 4632936773567450746274117)
    ·
      refine ⟨868675645043897014926397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4632936773567450746274117 868675645043897014926397)
      ·
        refine ⟨325753366891461380597399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 868675645043897014926397 325753366891461380597399)
        ·
          refine ⟨488630050337192070896099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325753366891461380597399 488630050337192070896099)
          ·
            refine ⟨732945075505788106344149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488630050337192070896099 732945075505788106344149)
            ·
              refine ⟨17178400207166908742441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 732945075505788106344149 17178400207166908742441)
              ·
                rfl

theorem cell20_338730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 7].length) (baseStart_338730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338730 prefixEnd_338730 := by exact prefixLift 338730
  have htrace : WordTrace (prefixWord ++ tailWord_338730) baseStart_338730 baseEnd_338730 := by
    simpa [prefixWord, tailWord_338730, baseEnd_338730] using wordTrace_append hprefix tailTrace_338730
  have hstable : (prefixWord ++ tailWord_338730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338730).length < 2 ^ (prefixWord ++ tailWord_338730).sum := by decide
  have hdescent : baseEnd_338730 < baseStart_338730 := by decide
  rcases family_descends (prefixWord ++ tailWord_338730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338744 : List Nat := [2, 1, 2, 1, 3, 2, 1, 6, 2]
def baseStart_338744 : Nat := 118140960795 + 338744 * 2 ^ 59
def prefixEnd_338744 : Nat := 4983230072969 + 3 ^ 40 * 338744 * 2
def baseEnd_338744 : Nat := 154611991845980352215245

theorem tailTrace_338744 : CollatzResearch.WordTrace tailWord_338744 prefixEnd_338744 154611991845980352215245 := by
  unfold tailWord_338744
  simp only [CollatzResearch.WordTrace]
  refine ⟨6177504342397907857203643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8236672456530543809604857 6177504342397907857203643)
  ·
    refine ⟨9266256513596861785805465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6177504342397907857203643 9266256513596861785805465)
    ·
      refine ⟨6949692385197646339354099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9266256513596861785805465 6949692385197646339354099)
      ·
        refine ⟨10424538577796469509031149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6949692385197646339354099 10424538577796469509031149)
        ·
          refine ⟨3909201966673676065886681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10424538577796469509031149 3909201966673676065886681)
          ·
            refine ⟨2931901475005257049415011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3909201966673676065886681 2931901475005257049415011)
            ·
              refine ⟨4397852212507885574122517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2931901475005257049415011 4397852212507885574122517)
              ·
                refine ⟨206149322461307136286993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4397852212507885574122517 206149322461307136286993)
                ·
                  refine ⟨154611991845980352215245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206149322461307136286993 154611991845980352215245)
                  ·
                    rfl

theorem cell20_338744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 2].length) (baseStart_338744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338744 prefixEnd_338744 := by exact prefixLift 338744
  have htrace : WordTrace (prefixWord ++ tailWord_338744) baseStart_338744 baseEnd_338744 := by
    simpa [prefixWord, tailWord_338744, baseEnd_338744] using wordTrace_append hprefix tailTrace_338744
  have hstable : (prefixWord ++ tailWord_338744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338744).length < 2 ^ (prefixWord ++ tailWord_338744).sum := by decide
  have hdescent : baseEnd_338744 < baseStart_338744 := by decide
  rcases family_descends (prefixWord ++ tailWord_338744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338796 : List Nat := [2, 2, 1, 1, 4, 1, 2, 4, 3]
def baseStart_338796 : Nat := 118140960795 + 338796 * 2 ^ 59
def prefixEnd_338796 : Nat := 4983230072969 + 3 ^ 40 * 338796 * 2
def baseEnd_338796 : Nat := 154635726062899282481699

theorem tailTrace_338796 : CollatzResearch.WordTrace tailWord_338796 prefixEnd_338796 154635726062899282481699 := by
  unfold tailWord_338796
  simp only [CollatzResearch.WordTrace]
  refine ⟨6178452640303714297650121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8237936853738285730200161 6178452640303714297650121)
  ·
    refine ⟨4633839480227785723237591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6178452640303714297650121 4633839480227785723237591)
    ·
      refine ⟨6950759220341678584856387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4633839480227785723237591 6950759220341678584856387)
      ·
        refine ⟨10426138830512517877284581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6950759220341678584856387 10426138830512517877284581)
        ·
          refine ⟨1954901030721097101990859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10426138830512517877284581 1954901030721097101990859)
          ·
            refine ⟨2932351546081645652986289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1954901030721097101990859 2932351546081645652986289)
            ·
              refine ⟨2199263659561234239739717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2932351546081645652986289 2199263659561234239739717)
              ·
                refine ⟨412361936167731419951197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2199263659561234239739717 412361936167731419951197)
                ·
                  refine ⟨154635726062899282481699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 412361936167731419951197 154635726062899282481699)
                  ·
                    rfl

theorem cell20_338796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_338796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338796 prefixEnd_338796 := by exact prefixLift 338796
  have htrace : WordTrace (prefixWord ++ tailWord_338796) baseStart_338796 baseEnd_338796 := by
    simpa [prefixWord, tailWord_338796, baseEnd_338796] using wordTrace_append hprefix tailTrace_338796
  have hstable : (prefixWord ++ tailWord_338796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338796).length < 2 ^ (prefixWord ++ tailWord_338796).sum := by decide
  have hdescent : baseEnd_338796 < baseStart_338796 := by decide
  rcases family_descends (prefixWord ++ tailWord_338796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338803 : List Nat := [1, 1, 1, 2, 2, 1, 7, 1, 4]
def baseStart_338803 : Nat := 118140960795 + 338803 * 2 ^ 59
def prefixEnd_338803 : Nat := 4983230072969 + 3 ^ 40 * 338803 * 2
def baseEnd_338803 : Nat := 154638921053638369248337

theorem tailTrace_338803 : CollatzResearch.WordTrace tailWord_338803 prefixEnd_338803 154638921053638369248337 := by
  unfold tailWord_338803
  simp only [CollatzResearch.WordTrace]
  refine ⟨12357160591582068790805063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8238107061054712527203375 12357160591582068790805063)
  ·
    refine ⟨18535740887373103186207595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12357160591582068790805063 18535740887373103186207595)
    ·
      refine ⟨27803611331059654779311393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18535740887373103186207595 27803611331059654779311393)
      ·
        refine ⟨20852708498294741084483545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27803611331059654779311393 20852708498294741084483545)
        ·
          refine ⟨15639531373721055813362659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20852708498294741084483545 15639531373721055813362659)
          ·
            refine ⟨23459297060581583720043989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15639531373721055813362659 23459297060581583720043989)
            ·
              refine ⟨549827274857380868438531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 23459297060581583720043989 549827274857380868438531)
              ·
                refine ⟨824740912286071302657797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 549827274857380868438531 824740912286071302657797)
                ·
                  refine ⟨154638921053638369248337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 824740912286071302657797 154638921053638369248337)
                  ·
                    rfl

theorem cell20_338803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 4].length) (baseStart_338803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338803 prefixEnd_338803 := by exact prefixLift 338803
  have htrace : WordTrace (prefixWord ++ tailWord_338803) baseStart_338803 baseEnd_338803 := by
    simpa [prefixWord, tailWord_338803, baseEnd_338803] using wordTrace_append hprefix tailTrace_338803
  have hstable : (prefixWord ++ tailWord_338803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338803).length < 2 ^ (prefixWord ++ tailWord_338803).sum := by decide
  have hdescent : baseEnd_338803 < baseStart_338803 := by decide
  rcases family_descends (prefixWord ++ tailWord_338803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338806 : List Nat := [5, 1, 1, 3, 1, 2, 2, 5]
def baseStart_338806 : Nat := 118140960795 + 338806 * 2 ^ 59
def prefixEnd_338806 : Nat := 4983230072969 + 3 ^ 40 * 338806 * 2
def baseEnd_338806 : Nat := 51546763445127897382775

theorem tailTrace_338806 : CollatzResearch.WordTrace tailWord_338806 prefixEnd_338806 51546763445127897382775 := by
  unfold tailWord_338806
  simp only [CollatzResearch.WordTrace]
  refine ⟨772329375660700018947767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8238180007047466868776181 772329375660700018947767)
  ·
    refine ⟨1158494063491050028421651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 772329375660700018947767 1158494063491050028421651)
    ·
      refine ⟨1737741095236575042632477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1158494063491050028421651 1737741095236575042632477)
      ·
        refine ⟨651652910713715640987179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1737741095236575042632477 651652910713715640987179)
        ·
          refine ⟨977479366070573461480769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651652910713715640987179 977479366070573461480769)
          ·
            refine ⟨733109524552930096110577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 977479366070573461480769 733109524552930096110577)
            ·
              refine ⟨549832143414697572082933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733109524552930096110577 549832143414697572082933)
              ·
                refine ⟨51546763445127897382775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 549832143414697572082933 51546763445127897382775)
                ·
                  rfl

theorem cell20_338806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_338806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338806 prefixEnd_338806 := by exact prefixLift 338806
  have htrace : WordTrace (prefixWord ++ tailWord_338806) baseStart_338806 baseEnd_338806 := by
    simpa [prefixWord, tailWord_338806, baseEnd_338806] using wordTrace_append hprefix tailTrace_338806
  have hstable : (prefixWord ++ tailWord_338806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338806).length < 2 ^ (prefixWord ++ tailWord_338806).sum := by decide
  have hdescent : baseEnd_338806 < baseStart_338806 := by decide
  rcases family_descends (prefixWord ++ tailWord_338806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338813 : List Nat := [1, 4, 1, 1, 2, 1, 6, 1, 3]
def baseStart_338813 : Nat := 118140960795 + 338813 * 2 ^ 59
def prefixEnd_338813 : Nat := 4983230072969 + 3 ^ 40 * 338813 * 2
def baseEnd_338813 : Nat := 154643485326122778914963

theorem tailTrace_338813 : CollatzResearch.WordTrace tailWord_338813 prefixEnd_338813 154643485326122778914963 := by
  unfold tailWord_338813
  simp only [CollatzResearch.WordTrace]
  refine ⟨12357525321545840498669093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8238350214363893665779395 12357525321545840498669093)
  ·
    refine ⟨2317035997789845093500455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12357525321545840498669093 2317035997789845093500455)
    ·
      refine ⟨3475553996684767640250683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2317035997789845093500455 3475553996684767640250683)
      ·
        refine ⟨5213330995027151460376025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3475553996684767640250683 5213330995027151460376025)
        ·
          refine ⟨3909998246270363595282019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5213330995027151460376025 3909998246270363595282019)
          ·
            refine ⟨5864997369405545392923029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3909998246270363595282019 5864997369405545392923029)
            ·
              refine ⟨274921751690884940293267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5864997369405545392923029 274921751690884940293267)
              ·
                refine ⟨412382627536327410439901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274921751690884940293267 412382627536327410439901)
                ·
                  refine ⟨154643485326122778914963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 412382627536327410439901 154643485326122778914963)
                  ·
                    rfl

theorem cell20_338813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_338813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338813 prefixEnd_338813 := by exact prefixLift 338813
  have htrace : WordTrace (prefixWord ++ tailWord_338813) baseStart_338813 baseEnd_338813 := by
    simpa [prefixWord, tailWord_338813, baseEnd_338813] using wordTrace_append hprefix tailTrace_338813
  have hstable : (prefixWord ++ tailWord_338813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338813).length < 2 ^ (prefixWord ++ tailWord_338813).sum := by decide
  have hdescent : baseEnd_338813 < baseStart_338813 := by decide
  rcases family_descends (prefixWord ++ tailWord_338813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338861 : List Nat := [1, 5, 2, 3, 1, 2, 1, 5]
def baseStart_338861 : Nat := 118140960795 + 338861 * 2 ^ 59
def prefixEnd_338861 : Nat := 4983230072969 + 3 ^ 40 * 338861 * 2
def baseEnd_338861 : Nat := 51555131278015981771589

theorem tailTrace_338861 : CollatzResearch.WordTrace tailWord_338861 prefixEnd_338861 51555131278015981771589 := by
  unfold tailWord_338861
  simp only [CollatzResearch.WordTrace]
  refine ⟨12359276025371944696416437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8239517350247963130944291 12359276025371944696416437)
  ·
    refine ⟨1158682127378619815289041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12359276025371944696416437 1158682127378619815289041)
    ·
      refine ⟨869011595533964861466781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1158682127378619815289041 869011595533964861466781)
      ·
        refine ⟨325879348325236823050043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 869011595533964861466781 325879348325236823050043)
        ·
          refine ⟨488819022487855234575065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325879348325236823050043 488819022487855234575065)
          ·
            refine ⟨366614266865891425931299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488819022487855234575065 366614266865891425931299)
            ·
              refine ⟨549921400298837138896949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366614266865891425931299 549921400298837138896949)
              ·
                refine ⟨51555131278015981771589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 549921400298837138896949 51555131278015981771589)
                ·
                  rfl

theorem cell20_338861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 5].length) (baseStart_338861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338861 prefixEnd_338861 := by exact prefixLift 338861
  have htrace : WordTrace (prefixWord ++ tailWord_338861) baseStart_338861 baseEnd_338861 := by
    simpa [prefixWord, tailWord_338861, baseEnd_338861] using wordTrace_append hprefix tailTrace_338861
  have hstable : (prefixWord ++ tailWord_338861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338861).length < 2 ^ (prefixWord ++ tailWord_338861).sum := by decide
  have hdescent : baseEnd_338861 < baseStart_338861 := by decide
  rcases family_descends (prefixWord ++ tailWord_338861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338868 : List Nat := [2, 5, 2, 1, 1, 1, 2, 3, 3]
def baseStart_338868 : Nat := 118140960795 + 338868 * 2 ^ 59
def prefixEnd_338868 : Nat := 4983230072969 + 3 ^ 40 * 338868 * 2
def baseEnd_338868 : Nat := 154668588824787032081405

theorem tailTrace_338868 : CollatzResearch.WordTrace tailWord_338868 prefixEnd_338868 154668588824787032081405 := by
  unfold tailWord_338868
  simp only [CollatzResearch.WordTrace]
  refine ⟨6179765668173292445960629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8239687557564389927947505 6179765668173292445960629)
  ·
    refine ⟨579353031391246166808809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6179765668173292445960629 579353031391246166808809)
    ·
      refine ⟨434514773543434625106607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 579353031391246166808809 434514773543434625106607)
      ·
        refine ⟨651772160315151937659911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434514773543434625106607 651772160315151937659911)
        ·
          refine ⟨977658240472727906489867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651772160315151937659911 977658240472727906489867)
          ·
            refine ⟨1466487360709091859734801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977658240472727906489867 1466487360709091859734801)
            ·
              refine ⟨1099865520531818894801101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1466487360709091859734801 1099865520531818894801101)
              ·
                refine ⟨412449570199432085550413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1099865520531818894801101 412449570199432085550413)
                ·
                  refine ⟨154668588824787032081405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 412449570199432085550413 154668588824787032081405)
                  ·
                    rfl

theorem cell20_338868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_338868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338868 prefixEnd_338868 := by exact prefixLift 338868
  have htrace : WordTrace (prefixWord ++ tailWord_338868) baseStart_338868 baseEnd_338868 := by
    simpa [prefixWord, tailWord_338868, baseEnd_338868] using wordTrace_append hprefix tailTrace_338868
  have hstable : (prefixWord ++ tailWord_338868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338868).length < 2 ^ (prefixWord ++ tailWord_338868).sum := by decide
  have hdescent : baseEnd_338868 < baseStart_338868 := by decide
  rcases family_descends (prefixWord ++ tailWord_338868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338872 : List Nat := [2, 1, 2, 1, 2, 4, 2, 3, 3]
def baseStart_338872 : Nat := 118140960795 + 338872 * 2 ^ 59
def prefixEnd_338872 : Nat := 4983230072969 + 3 ^ 40 * 338872 * 2
def baseEnd_338872 : Nat := 154670414533780795948055

theorem tailTrace_338872 : CollatzResearch.WordTrace tailWord_338872 prefixEnd_338872 154670414533780795948055 := by
  unfold tailWord_338872
  simp only [CollatzResearch.WordTrace]
  refine ⟨6179838614166046787533435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8239784818888062383377913 6179838614166046787533435)
  ·
    refine ⟨9269757921249070181300153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6179838614166046787533435 9269757921249070181300153)
    ·
      refine ⟨6952318440936802635975115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9269757921249070181300153 6952318440936802635975115)
      ·
        refine ⟨10428477661405203953962673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6952318440936802635975115 10428477661405203953962673)
        ·
          refine ⟨7821358246053902965472005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10428477661405203953962673 7821358246053902965472005)
          ·
            refine ⟨1466504671135106806026001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7821358246053902965472005 1466504671135106806026001)
            ·
              refine ⟨1099878503351330104519501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1466504671135106806026001 1099878503351330104519501)
              ·
                refine ⟨412454438756748789194813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1099878503351330104519501 412454438756748789194813)
                ·
                  refine ⟨154670414533780795948055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 412454438756748789194813 154670414533780795948055)
                  ·
                    rfl

theorem cell20_338872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_338872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338872 prefixEnd_338872 := by exact prefixLift 338872
  have htrace : WordTrace (prefixWord ++ tailWord_338872) baseStart_338872 baseEnd_338872 := by
    simpa [prefixWord, tailWord_338872, baseEnd_338872] using wordTrace_append hprefix tailTrace_338872
  have hstable : (prefixWord ++ tailWord_338872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338872).length < 2 ^ (prefixWord ++ tailWord_338872).sum := by decide
  have hdescent : baseEnd_338872 < baseStart_338872 := by decide
  rcases family_descends (prefixWord ++ tailWord_338872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338927 : List Nat := [1, 1, 2, 1, 4, 4, 3, 1, 3]
def baseStart_338927 : Nat := 118140960795 + 338927 * 2 ^ 59
def prefixEnd_338927 : Nat := 4983230072969 + 3 ^ 40 * 338927 * 2
def baseEnd_338927 : Nat := 154695518032445049114497

theorem tailTrace_338927 : CollatzResearch.WordTrace tailWord_338927 prefixEnd_338927 154695518032445049114497 := by
  unfold tailWord_338927
  simp only [CollatzResearch.WordTrace]
  refine ⟨12361683243132837968319035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8241122162088558645546023 12361683243132837968319035)
  ·
    refine ⟨18542524864699256952478553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12361683243132837968319035 18542524864699256952478553)
    ·
      refine ⟨13906893648524442714358915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18542524864699256952478553 13906893648524442714358915)
      ·
        refine ⟨20860340472786664071538373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13906893648524442714358915 20860340472786664071538373)
        ·
          refine ⟨3911313838647499513413445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20860340472786664071538373 3911313838647499513413445)
          ·
            refine ⟨733371344746406158765021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3911313838647499513413445 733371344746406158765021)
            ·
              refine ⟨275014254279902309536883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 733371344746406158765021 275014254279902309536883)
              ·
                refine ⟨412521381419853464305325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275014254279902309536883 412521381419853464305325)
                ·
                  refine ⟨154695518032445049114497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 412521381419853464305325 154695518032445049114497)
                  ·
                    rfl

theorem cell20_338927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 3].length) (baseStart_338927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338927 prefixEnd_338927 := by exact prefixLift 338927
  have htrace : WordTrace (prefixWord ++ tailWord_338927) baseStart_338927 baseEnd_338927 := by
    simpa [prefixWord, tailWord_338927, baseEnd_338927] using wordTrace_append hprefix tailTrace_338927
  have hstable : (prefixWord ++ tailWord_338927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338927).length < 2 ^ (prefixWord ++ tailWord_338927).sum := by decide
  have hdescent : baseEnd_338927 < baseStart_338927 := by decide
  rcases family_descends (prefixWord ++ tailWord_338927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338934 : List Nat := [5, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_338934 : Nat := 118140960795 + 338934 * 2 ^ 59
def prefixEnd_338934 : Nat := 4983230072969 + 3 ^ 40 * 338934 * 2
def baseEnd_338934 : Nat := 154698713023184135881135

theorem tailTrace_338934 : CollatzResearch.WordTrace tailWord_338934 prefixEnd_338934 154698713023184135881135 := by
  unfold tailWord_338934
  simp only [CollatzResearch.WordTrace]
  refine ⟨772621159631717385238991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8241292369404985442549237 772621159631717385238991)
  ·
    refine ⟨1158931739447576077858487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 772621159631717385238991 1158931739447576077858487)
    ·
      refine ⟨1738397609171364116787731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1158931739447576077858487 1738397609171364116787731)
      ·
        refine ⟨2607596413757046175181597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1738397609171364116787731 2607596413757046175181597)
        ·
          refine ⟨977848655158892315693099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2607596413757046175181597 977848655158892315693099)
          ·
            refine ⟨1466772982738338473539649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977848655158892315693099 1466772982738338473539649)
            ·
              refine ⟨1100079737053753855154737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1466772982738338473539649 1100079737053753855154737)
              ·
                refine ⟨825059802790315391366053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1100079737053753855154737 825059802790315391366053)
                ·
                  refine ⟨154698713023184135881135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 825059802790315391366053 154698713023184135881135)
                  ·
                    rfl

theorem cell20_338934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_338934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338934 prefixEnd_338934 := by exact prefixLift 338934
  have htrace : WordTrace (prefixWord ++ tailWord_338934) baseStart_338934 baseEnd_338934 := by
    simpa [prefixWord, tailWord_338934, baseEnd_338934] using wordTrace_append hprefix tailTrace_338934
  have hstable : (prefixWord ++ tailWord_338934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338934).length < 2 ^ (prefixWord ++ tailWord_338934).sum := by decide
  have hdescent : baseEnd_338934 < baseStart_338934 := by decide
  rcases family_descends (prefixWord ++ tailWord_338934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338969 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 5]
def baseStart_338969 : Nat := 118140960795 + 338969 * 2 ^ 59
def prefixEnd_338969 : Nat := 4983230072969 + 3 ^ 40 * 338969 * 2
def baseEnd_338969 : Nat := 154714687976879569714325

theorem tailTrace_338969 : CollatzResearch.WordTrace tailWord_338969 prefixEnd_338969 154714687976879569714325 := by
  unfold tailWord_338969
  simp only [CollatzResearch.WordTrace]
  refine ⟨12363215108980679141347961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8242143405987119427565307 12363215108980679141347961)
  ·
    refine ⟨9272411331735509356010971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12363215108980679141347961 9272411331735509356010971)
    ·
      refine ⟨13908616997603264034016457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9272411331735509356010971 13908616997603264034016457)
      ·
        refine ⟨10431462748202448025512343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13908616997603264034016457 10431462748202448025512343)
        ·
          refine ⟨15647194122303672038268515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10431462748202448025512343 15647194122303672038268515)
          ·
            refine ⟨23470791183455508057402773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15647194122303672038268515 23470791183455508057402773)
            ·
              refine ⟨1100193336724476940190755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23470791183455508057402773 1100193336724476940190755)
              ·
                refine ⟨1650290005086715410286133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1100193336724476940190755 1650290005086715410286133)
                ·
                  refine ⟨154714687976879569714325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1650290005086715410286133 154714687976879569714325)
                  ·
                    rfl

theorem cell20_338969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_338969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_338969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_338969 prefixEnd_338969 := by exact prefixLift 338969
  have htrace : WordTrace (prefixWord ++ tailWord_338969) baseStart_338969 baseEnd_338969 := by
    simpa [prefixWord, tailWord_338969, baseEnd_338969] using wordTrace_append hprefix tailTrace_338969
  have hstable : (prefixWord ++ tailWord_338969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338969).length < 2 ^ (prefixWord ++ tailWord_338969).sum := by decide
  have hdescent : baseEnd_338969 < baseStart_338969 := by decide
  rcases family_descends (prefixWord ++ tailWord_338969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339000 : List Nat := [2, 1, 2, 1, 5, 1, 2, 6]
def baseStart_339000 : Nat := 118140960795 + 339000 * 2 ^ 59
def prefixEnd_339000 : Nat := 4983230072969 + 3 ^ 40 * 339000 * 2
def baseEnd_339000 : Nat := 51576279073860413226955

theorem tailTrace_339000 : CollatzResearch.WordTrace tailWord_339000 prefixEnd_339000 51576279073860413226955 := by
  unfold tailWord_339000
  simp only [CollatzResearch.WordTrace]
  refine ⟨6182172885934185717863227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8242897181245580957150969 6182172885934185717863227)
  ·
    refine ⟨9273259328901278576794841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6182172885934185717863227 9273259328901278576794841)
    ·
      refine ⟨6954944496675958932596131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9273259328901278576794841 6954944496675958932596131)
      ·
        refine ⟨10432416745013938398894197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6954944496675958932596131 10432416745013938398894197)
        ·
          refine ⟨978039069845056724896331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10432416745013938398894197 978039069845056724896331)
          ·
            refine ⟨1467058604767585087344497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978039069845056724896331 1467058604767585087344497)
            ·
              refine ⟨1100293953575688815508373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1467058604767585087344497 1100293953575688815508373)
              ·
                refine ⟨51576279073860413226955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1100293953575688815508373 51576279073860413226955)
                ·
                  rfl

theorem cell20_339000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_339000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339000 prefixEnd_339000 := by exact prefixLift 339000
  have htrace : WordTrace (prefixWord ++ tailWord_339000) baseStart_339000 baseEnd_339000 := by
    simpa [prefixWord, tailWord_339000, baseEnd_339000] using wordTrace_append hprefix tailTrace_339000
  have hstable : (prefixWord ++ tailWord_339000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339000).length < 2 ^ (prefixWord ++ tailWord_339000).sum := by decide
  have hdescent : baseEnd_339000 < baseStart_339000 := by decide
  rcases family_descends (prefixWord ++ tailWord_339000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339030 : List Nat := [5, 2, 2, 1, 3, 1, 1, 5]
def baseStart_339030 : Nat := 118140960795 + 339030 * 2 ^ 59
def prefixEnd_339030 : Nat := 4983230072969 + 3 ^ 40 * 339030 * 2
def baseEnd_339030 : Nat := 51580843346344822893581

theorem tailTrace_339030 : CollatzResearch.WordTrace tailWord_339030 prefixEnd_339030 51580843346344822893581 := by
  unfold tailWord_339030
  simp only [CollatzResearch.WordTrace]
  refine ⟨772839997609980409957409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8243626641173124372879029 772839997609980409957409)
  ·
    refine ⟨579629998207485307468057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 772839997609980409957409 579629998207485307468057)
    ·
      refine ⟨434722498655613980601043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 579629998207485307468057 434722498655613980601043)
      ·
        refine ⟨652083747983420970901565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434722498655613980601043 652083747983420970901565)
        ·
          refine ⟨244531405493782864088087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 652083747983420970901565 244531405493782864088087)
          ·
            refine ⟨366797108240674296132131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244531405493782864088087 366797108240674296132131)
            ·
              refine ⟨550195662361011444198197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366797108240674296132131 550195662361011444198197)
              ·
                refine ⟨51580843346344822893581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 550195662361011444198197 51580843346344822893581)
                ·
                  rfl

theorem cell20_339030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_339030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339030 prefixEnd_339030 := by exact prefixLift 339030
  have htrace : WordTrace (prefixWord ++ tailWord_339030) baseStart_339030 baseEnd_339030 := by
    simpa [prefixWord, tailWord_339030, baseEnd_339030] using wordTrace_append hprefix tailTrace_339030
  have hstable : (prefixWord ++ tailWord_339030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339030).length < 2 ^ (prefixWord ++ tailWord_339030).sum := by decide
  have hdescent : baseEnd_339030 < baseStart_339030 := by decide
  rcases family_descends (prefixWord ++ tailWord_339030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339062 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_339062 : Nat := 118140960795 + 339062 * 2 ^ 59
def prefixEnd_339062 : Nat := 4983230072969 + 3 ^ 40 * 339062 * 2
def baseEnd_339062 : Nat := 154757135710984579613945

theorem tailTrace_339062 : CollatzResearch.WordTrace tailWord_339062 prefixEnd_339062 154757135710984579613945 := by
  unfold tailWord_339062
  simp only [CollatzResearch.WordTrace]
  refine ⟨772912943602734751530215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8244404731762504016322293 772912943602734751530215)
  ·
    refine ⟨1159369415404102127295323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 772912943602734751530215 1159369415404102127295323)
    ·
      refine ⟨1739054123106153190942985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1159369415404102127295323 1739054123106153190942985)
      ·
        refine ⟨1304290592329614893207239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1739054123106153190942985 1304290592329614893207239)
        ·
          refine ⟨1956435888494422339810859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1304290592329614893207239 1956435888494422339810859)
          ·
            refine ⟨2934653832741633509716289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1956435888494422339810859 2934653832741633509716289)
            ·
              refine ⟨2200990374556225132287217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2934653832741633509716289 2200990374556225132287217)
              ·
                refine ⟨1650742780917168849215413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2200990374556225132287217 1650742780917168849215413)
                ·
                  refine ⟨154757135710984579613945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1650742780917168849215413 154757135710984579613945)
                  ·
                    rfl

theorem cell20_339062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_339062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339062 prefixEnd_339062 := by exact prefixLift 339062
  have htrace : WordTrace (prefixWord ++ tailWord_339062) baseStart_339062 baseEnd_339062 := by
    simpa [prefixWord, tailWord_339062, baseEnd_339062] using wordTrace_append hprefix tailTrace_339062
  have hstable : (prefixWord ++ tailWord_339062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339062).length < 2 ^ (prefixWord ++ tailWord_339062).sum := by decide
  have hdescent : baseEnd_339062 < baseStart_339062 := by decide
  rcases family_descends (prefixWord ++ tailWord_339062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339065 : List Nat := [1, 2, 1, 3, 5, 1, 2, 3, 2]
def baseStart_339065 : Nat := 118140960795 + 339065 * 2 ^ 59
def prefixEnd_339065 : Nat := 4983230072969 + 3 ^ 40 * 339065 * 2
def baseEnd_339065 : Nat := 154758504992729902513933

theorem tailTrace_339065 : CollatzResearch.WordTrace tailWord_339065 prefixEnd_339065 154758504992729902513933 := by
  unfold tailWord_339065
  simp only [CollatzResearch.WordTrace]
  refine ⟨12366716516632887536842649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8244477677755258357895099 12366716516632887536842649)
  ·
    refine ⟨9275037387474665652631987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12366716516632887536842649 9275037387474665652631987)
    ·
      refine ⟨13912556081211998478947981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9275037387474665652631987 13912556081211998478947981)
      ·
        refine ⟨5217208530454499429605493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13912556081211998478947981 5217208530454499429605493)
        ·
          refine ⟨489113299730109321525515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5217208530454499429605493 489113299730109321525515)
          ·
            refine ⟨733669949595163982288273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489113299730109321525515 733669949595163982288273)
            ·
              refine ⟨550252462196372986716205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733669949595163982288273 550252462196372986716205)
              ·
                refine ⟨206344673323639870018577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 550252462196372986716205 206344673323639870018577)
                ·
                  refine ⟨154758504992729902513933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206344673323639870018577 154758504992729902513933)
                  ·
                    rfl

theorem cell20_339065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 2].length) (baseStart_339065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339065 prefixEnd_339065 := by exact prefixLift 339065
  have htrace : WordTrace (prefixWord ++ tailWord_339065) baseStart_339065 baseEnd_339065 := by
    simpa [prefixWord, tailWord_339065, baseEnd_339065] using wordTrace_append hprefix tailTrace_339065
  have hstable : (prefixWord ++ tailWord_339065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339065).length < 2 ^ (prefixWord ++ tailWord_339065).sum := by decide
  have hdescent : baseEnd_339065 < baseStart_339065 := by decide
  rcases family_descends (prefixWord ++ tailWord_339065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339076 : List Nat := [2, 3, 2, 1, 2, 3, 7]
def baseStart_339076 : Nat := 118140960795 + 339076 * 2 ^ 59
def prefixEnd_339076 : Nat := 4983230072969 + 3 ^ 40 * 339076 * 2
def baseEnd_339076 : Nat := 17195947299162528127469

theorem tailTrace_339076 : CollatzResearch.WordTrace tailWord_339076 prefixEnd_339076 17195947299162528127469 := by
  unfold tailWord_339076
  simp only [CollatzResearch.WordTrace]
  refine ⟨6183558859796518207746541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8244745146395357610328721 6183558859796518207746541)
  ·
    refine ⟨2318834572423694327904953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6183558859796518207746541 2318834572423694327904953)
    ·
      refine ⟨1739125929317770745928715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2318834572423694327904953 1739125929317770745928715)
      ·
        refine ⟨2608688893976656118893073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1739125929317770745928715 2608688893976656118893073)
        ·
          refine ⟨1956516670482492089169805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2608688893976656118893073 1956516670482492089169805)
          ·
            refine ⟨733693751430934533438677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1956516670482492089169805 733693751430934533438677)
            ·
              refine ⟨17195947299162528127469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 733693751430934533438677 17195947299162528127469)
              ·
                rfl

theorem cell20_339076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 7].length) (baseStart_339076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339076 prefixEnd_339076 := by exact prefixLift 339076
  have htrace : WordTrace (prefixWord ++ tailWord_339076) baseStart_339076 baseEnd_339076 := by
    simpa [prefixWord, tailWord_339076, baseEnd_339076] using wordTrace_append hprefix tailTrace_339076
  have hstable : (prefixWord ++ tailWord_339076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339076).length < 2 ^ (prefixWord ++ tailWord_339076).sum := by decide
  have hdescent : baseEnd_339076 < baseStart_339076 := by decide
  rcases family_descends (prefixWord ++ tailWord_339076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339086 : List Nat := [4, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_339086 : Nat := 118140960795 + 339086 * 2 ^ 59
def prefixEnd_339086 : Nat := 4983230072969 + 3 ^ 40 * 339086 * 2
def baseEnd_339086 : Nat := 154768089964947162813847

theorem tailTrace_339086 : CollatzResearch.WordTrace tailWord_339086 prefixEnd_339086 154768089964947162813847 := by
  unfold tailWord_339086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1545935306194601015419639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8244988299704538748904741 1545935306194601015419639)
  ·
    refine ⟨2318902959291901523129459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1545935306194601015419639 2318902959291901523129459)
    ·
      refine ⟨3478354438937852284694189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2318902959291901523129459 3478354438937852284694189)
      ·
        refine ⟨1304382914601694606760321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3478354438937852284694189 1304382914601694606760321)
        ·
          refine ⟨978287185951270955070241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1304382914601694606760321 978287185951270955070241)
          ·
            refine ⟨733715389463453216302681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 978287185951270955070241 733715389463453216302681)
            ·
              refine ⟨550286542097589912227011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733715389463453216302681 550286542097589912227011)
              ·
                refine ⟨825429813146384868340517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550286542097589912227011 825429813146384868340517)
                ·
                  refine ⟨154768089964947162813847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 825429813146384868340517 154768089964947162813847)
                  ·
                    rfl

theorem cell20_339086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_339086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339086 prefixEnd_339086 := by exact prefixLift 339086
  have htrace : WordTrace (prefixWord ++ tailWord_339086) baseStart_339086 baseEnd_339086 := by
    simpa [prefixWord, tailWord_339086, baseEnd_339086] using wordTrace_append hprefix tailTrace_339086
  have hstable : (prefixWord ++ tailWord_339086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339086).length < 2 ^ (prefixWord ++ tailWord_339086).sum := by decide
  have hdescent : baseEnd_339086 < baseStart_339086 := by decide
  rcases family_descends (prefixWord ++ tailWord_339086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339135 : List Nat := [1, 1, 2, 2, 2, 2, 10]
def baseStart_339135 : Nat := 118140960795 + 339135 * 2 ^ 59
def prefixEnd_339135 : Nat := 4983230072969 + 3 ^ 40 * 339135 * 2
def baseEnd_339135 : Nat := 17198939433346752242257

theorem tailTrace_339135 : CollatzResearch.WordTrace tailWord_339135 prefixEnd_339135 17198939433346752242257 := by
  unfold tailWord_339135
  simp only [CollatzResearch.WordTrace]
  refine ⟨12369269626379289491890859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8246179750919526327927239 12369269626379289491890859)
  ·
    refine ⟨18553904439568934237836289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12369269626379289491890859 18553904439568934237836289)
    ·
      refine ⟨13915428329676700678377217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18553904439568934237836289 13915428329676700678377217)
      ·
        refine ⟨10436571247257525508782913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13915428329676700678377217 10436571247257525508782913)
        ·
          refine ⟨7827428435443144131587185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10436571247257525508782913 7827428435443144131587185)
          ·
            refine ⟨5870571326582358098690389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7827428435443144131587185 5870571326582358098690389)
            ·
              refine ⟨17198939433346752242257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5870571326582358098690389 17198939433346752242257)
              ·
                rfl

theorem cell20_339135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 10].length) (baseStart_339135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339135 prefixEnd_339135 := by exact prefixLift 339135
  have htrace : WordTrace (prefixWord ++ tailWord_339135) baseStart_339135 baseEnd_339135 := by
    simpa [prefixWord, tailWord_339135, baseEnd_339135] using wordTrace_append hprefix tailTrace_339135
  have hstable : (prefixWord ++ tailWord_339135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339135).length < 2 ^ (prefixWord ++ tailWord_339135).sum := by decide
  have hdescent : baseEnd_339135 < baseStart_339135 := by decide
  rcases family_descends (prefixWord ++ tailWord_339135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339196 : List Nat := [2, 2, 2, 1, 5, 2, 2, 2, 2]
def baseStart_339196 : Nat := 118140960795 + 339196 * 2 ^ 59
def prefixEnd_339196 : Nat := 4983230072969 + 3 ^ 40 * 339196 * 2
def baseEnd_339196 : Nat := 154818296962275669146731

theorem tailTrace_339196 : CollatzResearch.WordTrace tailWord_339196 prefixEnd_339196 154818296962275669146731 := by
  unfold tailWord_339196
  simp only [CollatzResearch.WordTrace]
  refine ⟨6185747239579148454930721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8247662986105531273240961 6185747239579148454930721)
  ·
    refine ⟨4639310429684361341198041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6185747239579148454930721 4639310429684361341198041)
    ·
      refine ⟨3479482822263271005898531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4639310429684361341198041 3479482822263271005898531)
      ·
        refine ⟨5219224233394906508847797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3479482822263271005898531 5219224233394906508847797)
        ·
          refine ⟨489302271880772485204481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5219224233394906508847797 489302271880772485204481)
          ·
            refine ⟨366976703910579363903361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 489302271880772485204481 366976703910579363903361)
            ·
              refine ⟨275232527932934522927521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366976703910579363903361 275232527932934522927521)
              ·
                refine ⟨206424395949700892195641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275232527932934522927521 206424395949700892195641)
                ·
                  refine ⟨154818296962275669146731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206424395949700892195641 154818296962275669146731)
                  ·
                    rfl

theorem cell20_339196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_339196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339196 prefixEnd_339196 := by exact prefixLift 339196
  have htrace : WordTrace (prefixWord ++ tailWord_339196) baseStart_339196 baseEnd_339196 := by
    simpa [prefixWord, tailWord_339196, baseEnd_339196] using wordTrace_append hprefix tailTrace_339196
  have hstable : (prefixWord ++ tailWord_339196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339196).length < 2 ^ (prefixWord ++ tailWord_339196).sum := by decide
  have hdescent : baseEnd_339196 < baseStart_339196 := by decide
  rcases family_descends (prefixWord ++ tailWord_339196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339214 : List Nat := [4, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_339214 : Nat := 118140960795 + 339214 * 2 ^ 59
def prefixEnd_339214 : Nat := 4983230072969 + 3 ^ 40 * 339214 * 2
def baseEnd_339214 : Nat := 154826512652747606546657

theorem tailTrace_339214 : CollatzResearch.WordTrace tailWord_339214 prefixEnd_339214 154826512652747606546657 := by
  unfold tailWord_339214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1546518874136635748002087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8248100662062057322677797 1546518874136635748002087)
  ·
    refine ⟨2319778311204953622003131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1546518874136635748002087 2319778311204953622003131)
    ·
      refine ⟨3479667466807430433004697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2319778311204953622003131 3479667466807430433004697)
      ·
        refine ⟨2609750600105572824753523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3479667466807430433004697 2609750600105572824753523)
        ·
          refine ⟨3914625900158359237130285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2609750600105572824753523 3914625900158359237130285)
          ·
            refine ⟨1467984712559384713923857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3914625900158359237130285 1467984712559384713923857)
            ·
              refine ⟨1100988534419538535442893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1467984712559384713923857 1100988534419538535442893)
              ·
                refine ⟨412870700407326950791085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1100988534419538535442893 412870700407326950791085)
                ·
                  refine ⟨154826512652747606546657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 412870700407326950791085 154826512652747606546657)
                  ·
                    rfl

theorem cell20_339214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_339214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339214 prefixEnd_339214 := by exact prefixLift 339214
  have htrace : WordTrace (prefixWord ++ tailWord_339214) baseStart_339214 baseEnd_339214 := by
    simpa [prefixWord, tailWord_339214, baseEnd_339214] using wordTrace_append hprefix tailTrace_339214
  have hstable : (prefixWord ++ tailWord_339214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339214).length < 2 ^ (prefixWord ++ tailWord_339214).sum := by decide
  have hdescent : baseEnd_339214 < baseStart_339214 := by decide
  rcases family_descends (prefixWord ++ tailWord_339214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339245 : List Nat := [1, 5, 3, 1, 1, 2, 7]
def baseStart_339245 : Nat := 118140960795 + 339245 * 2 ^ 59
def prefixEnd_339245 : Nat := 4983230072969 + 3 ^ 40 * 339245 * 2
def baseEnd_339245 : Nat := 17204517988605475168133

theorem tailTrace_339245 : CollatzResearch.WordTrace tailWord_339245 prefixEnd_339245 17204517988605475168133 := by
  unfold tailWord_339245
  simp only [CollatzResearch.WordTrace]
  refine ⟨12373281655980778278395189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8248854437320518852263459 12373281655980778278395189)
  ·
    refine ⟨1159995155248197963599549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12373281655980778278395189 1159995155248197963599549)
    ·
      refine ⟨434998183218074236349831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1159995155248197963599549 434998183218074236349831)
      ·
        refine ⟨652497274827111354524747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434998183218074236349831 652497274827111354524747)
        ·
          refine ⟨978745912240667031787121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652497274827111354524747 978745912240667031787121)
          ·
            refine ⟨734059434180500273840341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 978745912240667031787121 734059434180500273840341)
            ·
              refine ⟨17204517988605475168133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 734059434180500273840341 17204517988605475168133)
              ·
                rfl

theorem cell20_339245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 7].length) (baseStart_339245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339245 prefixEnd_339245 := by exact prefixLift 339245
  have htrace : WordTrace (prefixWord ++ tailWord_339245) baseStart_339245 baseEnd_339245 := by
    simpa [prefixWord, tailWord_339245, baseEnd_339245] using wordTrace_append hprefix tailTrace_339245
  have hstable : (prefixWord ++ tailWord_339245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339245).length < 2 ^ (prefixWord ++ tailWord_339245).sum := by decide
  have hdescent : baseEnd_339245 < baseStart_339245 := by decide
  rcases family_descends (prefixWord ++ tailWord_339245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339252 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 5]
def baseStart_339252 : Nat := 118140960795 + 339252 * 2 ^ 59
def prefixEnd_339252 : Nat := 4983230072969 + 3 ^ 40 * 339252 * 2
def baseEnd_339252 : Nat := 154843856888188363279835

theorem tailTrace_339252 : CollatzResearch.WordTrace tailWord_339252 prefixEnd_339252 154843856888188363279835 := by
  unfold tailWord_339252
  simp only [CollatzResearch.WordTrace]
  refine ⟨6186768483477709236950005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8249024644636945649266673 6186768483477709236950005)
  ·
    refine ⟨580009545326035240964063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6186768483477709236950005 580009545326035240964063)
    ·
      refine ⟨870014317989052861446095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 580009545326035240964063 870014317989052861446095)
      ·
        refine ⟨1305021476983579292169143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 870014317989052861446095 1305021476983579292169143)
        ·
          refine ⟨1957532215475368938253715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1305021476983579292169143 1957532215475368938253715)
          ·
            refine ⟨2936298323213053407380573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1957532215475368938253715 2936298323213053407380573)
            ·
              refine ⟨1101111871204895027767715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2936298323213053407380573 1101111871204895027767715)
              ·
                refine ⟨1651667806807342541651573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101111871204895027767715 1651667806807342541651573)
                ·
                  refine ⟨154843856888188363279835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1651667806807342541651573 154843856888188363279835)
                  ·
                    rfl

theorem cell20_339252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_339252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339252 prefixEnd_339252 := by exact prefixLift 339252
  have htrace : WordTrace (prefixWord ++ tailWord_339252) baseStart_339252 baseEnd_339252 := by
    simpa [prefixWord, tailWord_339252, baseEnd_339252] using wordTrace_append hprefix tailTrace_339252
  have hstable : (prefixWord ++ tailWord_339252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339252).length < 2 ^ (prefixWord ++ tailWord_339252).sum := by decide
  have hdescent : baseEnd_339252 < baseStart_339252 := by decide
  rcases family_descends (prefixWord ++ tailWord_339252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339273 : List Nat := [1, 2, 1, 1, 2, 3, 2, 5, 3]
def baseStart_339273 : Nat := 118140960795 + 339273 * 2 ^ 59
def prefixEnd_339273 : Nat := 4983230072969 + 3 ^ 40 * 339273 * 2
def baseEnd_339273 : Nat := 154853441860405623579749

theorem tailTrace_339273 : CollatzResearch.WordTrace tailWord_339273 prefixEnd_339273 154853441860405623579749 := by
  unfold tailWord_339273
  simp only [CollatzResearch.WordTrace]
  refine ⟨12374302899879339060414473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8249535266586226040276315 12374302899879339060414473)
  ·
    refine ⟨9280727174909504295310855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12374302899879339060414473 9280727174909504295310855)
    ·
      refine ⟨13921090762364256442966283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9280727174909504295310855 13921090762364256442966283)
      ·
        refine ⟨20881636143546384664449425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13921090762364256442966283 20881636143546384664449425)
        ·
          refine ⟨15661227107659788498337069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20881636143546384664449425 15661227107659788498337069)
          ·
            refine ⟨5872960165372420686876401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15661227107659788498337069 5872960165372420686876401)
            ·
              refine ⟨4404720124029315515157301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5872960165372420686876401 4404720124029315515157301)
              ·
                refine ⟨412942511627748329545997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4404720124029315515157301 412942511627748329545997)
                ·
                  refine ⟨154853441860405623579749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 412942511627748329545997 154853441860405623579749)
                  ·
                    rfl

theorem cell20_339273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_339273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339273 prefixEnd_339273 := by exact prefixLift 339273
  have htrace : WordTrace (prefixWord ++ tailWord_339273) baseStart_339273 baseEnd_339273 := by
    simpa [prefixWord, tailWord_339273, baseEnd_339273] using wordTrace_append hprefix tailTrace_339273
  have hstable : (prefixWord ++ tailWord_339273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339273).length < 2 ^ (prefixWord ++ tailWord_339273).sum := by decide
  have hdescent : baseEnd_339273 < baseStart_339273 := by decide
  rcases family_descends (prefixWord ++ tailWord_339273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339280 : List Nat := [2, 1, 1, 1, 1, 5, 1, 4, 4]
def baseStart_339280 : Nat := 118140960795 + 339280 * 2 ^ 59
def prefixEnd_339280 : Nat := 4983230072969 + 3 ^ 40 * 339280 * 2
def baseEnd_339280 : Nat := 154856636851144710346387

theorem tailTrace_339280 : CollatzResearch.WordTrace tailWord_339280 prefixEnd_339280 154856636851144710346387 := by
  unfold tailWord_339280
  simp only [CollatzResearch.WordTrace]
  refine ⟨6187279105426989627959647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8249705473902652837279529 6187279105426989627959647)
  ·
    refine ⟨9280918658140484441939471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6187279105426989627959647 9280918658140484441939471)
    ·
      refine ⟨13921377987210726662909207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9280918658140484441939471 13921377987210726662909207)
      ·
        refine ⟨20882066980816089994363811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13921377987210726662909207 20882066980816089994363811)
        ·
          refine ⟨31323100471224134991545717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20882066980816089994363811 31323100471224134991545717)
          ·
            refine ⟨2936540669177262655457411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31323100471224134991545717 2936540669177262655457411)
            ·
              refine ⟨4404811003765893983186117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2936540669177262655457411 4404811003765893983186117)
              ·
                refine ⟨825902063206105121847397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4404811003765893983186117 825902063206105121847397)
                ·
                  refine ⟨154856636851144710346387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 825902063206105121847397 154856636851144710346387)
                  ·
                    rfl

theorem cell20_339280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_339280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339280 prefixEnd_339280 := by exact prefixLift 339280
  have htrace : WordTrace (prefixWord ++ tailWord_339280) baseStart_339280 baseEnd_339280 := by
    simpa [prefixWord, tailWord_339280, baseEnd_339280] using wordTrace_append hprefix tailTrace_339280
  have hstable : (prefixWord ++ tailWord_339280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339280).length < 2 ^ (prefixWord ++ tailWord_339280).sum := by decide
  have hdescent : baseEnd_339280 < baseStart_339280 := by decide
  rcases family_descends (prefixWord ++ tailWord_339280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339310 : List Nat := [4, 1, 2, 4, 2, 1, 1, 1, 4]
def baseStart_339310 : Nat := 118140960795 + 339310 * 2 ^ 59
def prefixEnd_339310 : Nat := 4983230072969 + 3 ^ 40 * 339310 * 2
def baseEnd_339310 : Nat := 154870329668597939346265

theorem tailTrace_339310 : CollatzResearch.WordTrace tailWord_339310 prefixEnd_339310 154870329668597939346265 := by
  unfold tailWord_339310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1546956550093161797438923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8250434933830196253007589 1546956550093161797438923)
  ·
    refine ⟨2320434825139742696158385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1546956550093161797438923 2320434825139742696158385)
    ·
      refine ⟨1740326118854807022118789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2320434825139742696158385 1740326118854807022118789)
      ·
        refine ⟨326311147285276316647273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1740326118854807022118789 326311147285276316647273)
        ·
          refine ⟨244733360463957237485455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326311147285276316647273 244733360463957237485455)
          ·
            refine ⟨367100040695935856228183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244733360463957237485455 367100040695935856228183)
            ·
              refine ⟨550650061043903784342275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367100040695935856228183 550650061043903784342275)
              ·
                refine ⟨825975091565855676513413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550650061043903784342275 825975091565855676513413)
                ·
                  refine ⟨154870329668597939346265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 825975091565855676513413 154870329668597939346265)
                  ·
                    rfl

theorem cell20_339310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_339310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339310 prefixEnd_339310 := by exact prefixLift 339310
  have htrace : WordTrace (prefixWord ++ tailWord_339310) baseStart_339310 baseEnd_339310 := by
    simpa [prefixWord, tailWord_339310, baseEnd_339310] using wordTrace_append hprefix tailTrace_339310
  have hstable : (prefixWord ++ tailWord_339310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339310).length < 2 ^ (prefixWord ++ tailWord_339310).sum := by decide
  have hdescent : baseEnd_339310 < baseStart_339310 := by decide
  rcases family_descends (prefixWord ++ tailWord_339310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339311 : List Nat := [1, 1, 2, 1, 3, 1, 4, 4, 3]
def baseStart_339311 : Nat := 118140960795 + 339311 * 2 ^ 59
def prefixEnd_339311 : Nat := 4983230072969 + 3 ^ 40 * 339311 * 2
def baseEnd_339311 : Nat := 154870786095846380312927

theorem tailTrace_339311 : CollatzResearch.WordTrace tailWord_339311 prefixEnd_339311 154870786095846380312927 := by
  unfold tailWord_339311
  simp only [CollatzResearch.WordTrace]
  refine ⟨12375688873741671550297787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8250459249161114366865191 12375688873741671550297787)
  ·
    refine ⟨18563533310612507325446681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12375688873741671550297787 18563533310612507325446681)
    ·
      refine ⟨13922649982959380494085011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18563533310612507325446681 13922649982959380494085011)
      ·
        refine ⟨20883974974439070741127517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13922649982959380494085011 20883974974439070741127517)
        ·
          refine ⟨7831490615414651527922819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20883974974439070741127517 7831490615414651527922819)
          ·
            refine ⟨11747235923121977291884229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7831490615414651527922819 11747235923121977291884229)
            ·
              refine ⟨2202606735585370742228293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11747235923121977291884229 2202606735585370742228293)
              ·
                refine ⟨412988762922257014167805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2202606735585370742228293 412988762922257014167805)
                ·
                  refine ⟨154870786095846380312927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 412988762922257014167805 154870786095846380312927)
                  ·
                    rfl

theorem cell20_339311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 3].length) (baseStart_339311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339311 prefixEnd_339311 := by exact prefixLift 339311
  have htrace : WordTrace (prefixWord ++ tailWord_339311) baseStart_339311 baseEnd_339311 := by
    simpa [prefixWord, tailWord_339311, baseEnd_339311] using wordTrace_append hprefix tailTrace_339311
  have hstable : (prefixWord ++ tailWord_339311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339311).length < 2 ^ (prefixWord ++ tailWord_339311).sum := by decide
  have hdescent : baseEnd_339311 < baseStart_339311 := by decide
  rcases family_descends (prefixWord ++ tailWord_339311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339408 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 7]
def baseStart_339408 : Nat := 118140960795 + 339408 * 2 ^ 59
def prefixEnd_339408 : Nat := 4983230072969 + 3 ^ 40 * 339408 * 2
def baseEnd_339408 : Nat := 154915059538945154079197

theorem tailTrace_339408 : CollatzResearch.WordTrace tailWord_339408 prefixEnd_339408 154915059538945154079197 := by
  unfold tailWord_339408
  simp only [CollatzResearch.WordTrace]
  refine ⟨6189613377195128558289439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8252817836260171411052585 6189613377195128558289439)
  ·
    refine ⟨9284420065792692837434159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6189613377195128558289439 9284420065792692837434159)
    ·
      refine ⟨13926630098689039256151239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9284420065792692837434159 13926630098689039256151239)
      ·
        refine ⟨20889945148033558884226859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13926630098689039256151239 20889945148033558884226859)
        ·
          refine ⟨31334917722050338326340289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20889945148033558884226859 31334917722050338326340289)
          ·
            refine ⟨23501188291537753744755217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31334917722050338326340289 23501188291537753744755217)
            ·
              refine ⟨17625891218653315308566413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23501188291537753744755217 17625891218653315308566413)
              ·
                refine ⟨6609709206994993240712405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17625891218653315308566413 6609709206994993240712405)
                ·
                  refine ⟨154915059538945154079197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6609709206994993240712405 154915059538945154079197)
                  ·
                    rfl

theorem cell20_339408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_339408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339408 prefixEnd_339408 := by exact prefixLift 339408
  have htrace : WordTrace (prefixWord ++ tailWord_339408) baseStart_339408 baseEnd_339408 := by
    simpa [prefixWord, tailWord_339408, baseEnd_339408] using wordTrace_append hprefix tailTrace_339408
  have hstable : (prefixWord ++ tailWord_339408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339408).length < 2 ^ (prefixWord ++ tailWord_339408).sum := by decide
  have hdescent : baseEnd_339408 < baseStart_339408 := by decide
  rcases family_descends (prefixWord ++ tailWord_339408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339421 : List Nat := [1, 4, 3, 1, 1, 4, 1, 2, 3]
def baseStart_339421 : Nat := 118140960795 + 339421 * 2 ^ 59
def prefixEnd_339421 : Nat := 4983230072969 + 3 ^ 40 * 339421 * 2
def baseEnd_339421 : Nat := 154920993093174886645811

theorem tailTrace_339421 : CollatzResearch.WordTrace tailWord_339421 prefixEnd_339421 154920993093174886645811 := by
  unfold tailWord_339421
  simp only [CollatzResearch.WordTrace]
  refine ⟨12379700903343160336802117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8253133935562106891201411 12379700903343160336802117)
  ·
    refine ⟨2321193919376842563150397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12379700903343160336802117 2321193919376842563150397)
    ·
      refine ⟨870447719766315961181399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2321193919376842563150397 870447719766315961181399)
      ·
        refine ⟨1305671579649473941772099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 870447719766315961181399 1305671579649473941772099)
        ·
          refine ⟨1958507369474210912658149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1305671579649473941772099 1958507369474210912658149)
          ·
            refine ⟨367220131776414546123403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1958507369474210912658149 367220131776414546123403)
            ·
              refine ⟨550830197664621819185105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367220131776414546123403 550830197664621819185105)
              ·
                refine ⟨413122648248466364388829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 550830197664621819185105 413122648248466364388829)
                ·
                  refine ⟨154920993093174886645811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 413122648248466364388829 154920993093174886645811)
                  ·
                    rfl

theorem cell20_339421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_339421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339421 prefixEnd_339421 := by exact prefixLift 339421
  have htrace : WordTrace (prefixWord ++ tailWord_339421) baseStart_339421 baseEnd_339421 := by
    simpa [prefixWord, tailWord_339421, baseEnd_339421] using wordTrace_append hprefix tailTrace_339421
  have hstable : (prefixWord ++ tailWord_339421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339421).length < 2 ^ (prefixWord ++ tailWord_339421).sum := by decide
  have hdescent : baseEnd_339421 < baseStart_339421 := by decide
  rcases family_descends (prefixWord ++ tailWord_339421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339425 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 5]
def baseStart_339425 : Nat := 118140960795 + 339425 * 2 ^ 59
def prefixEnd_339425 : Nat := 4983230072969 + 3 ^ 40 * 339425 * 2
def baseEnd_339425 : Nat := 154922818802168650512461

theorem tailTrace_339425 : CollatzResearch.WordTrace tailWord_339425 prefixEnd_339425 154922818802168650512461 := by
  unfold tailWord_339425
  simp only [CollatzResearch.WordTrace]
  refine ⟨12379846795328669019947729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8253231196885779346631819 12379846795328669019947729)
  ·
    refine ⟨9284885096496501764960797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12379846795328669019947729 9284885096496501764960797)
    ·
      refine ⟨3481831911186188161860299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9284885096496501764960797 3481831911186188161860299)
      ·
        refine ⟨5222747866779282242790449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3481831911186188161860299 5222747866779282242790449)
        ·
          refine ⟨3917060900084461682092837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5222747866779282242790449 3917060900084461682092837)
          ·
            refine ⟨734448918765836565392407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3917060900084461682092837 734448918765836565392407)
            ·
              refine ⟨1101673378148754848088611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 734448918765836565392407 1101673378148754848088611)
              ·
                refine ⟨1652510067223132272132917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101673378148754848088611 1652510067223132272132917)
                ·
                  refine ⟨154922818802168650512461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1652510067223132272132917 154922818802168650512461)
                  ·
                    rfl

theorem cell20_339425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_339425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339425 prefixEnd_339425 := by exact prefixLift 339425
  have htrace : WordTrace (prefixWord ++ tailWord_339425) baseStart_339425 baseEnd_339425 := by
    simpa [prefixWord, tailWord_339425, baseEnd_339425] using wordTrace_append hprefix tailTrace_339425
  have hstable : (prefixWord ++ tailWord_339425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339425).length < 2 ^ (prefixWord ++ tailWord_339425).sum := by decide
  have hdescent : baseEnd_339425 < baseStart_339425 := by decide
  rcases family_descends (prefixWord ++ tailWord_339425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339463 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 5]
def baseStart_339463 : Nat := 118140960795 + 339463 * 2 ^ 59
def prefixEnd_339463 : Nat := 4983230072969 + 3 ^ 40 * 339463 * 2
def baseEnd_339463 : Nat := 154940163037609407245639

theorem tailTrace_339463 : CollatzResearch.WordTrace tailWord_339463 prefixEnd_339463 154940163037609407245639 := by
  unfold tailWord_339463
  simp only [CollatzResearch.WordTrace]
  refine ⟨12381232769191001509831043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8254155179460667673220695 12381232769191001509831043)
  ·
    refine ⟨18571849153786502264746565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12381232769191001509831043 18571849153786502264746565)
    ·
      refine ⟨3482221716334969174639981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18571849153786502264746565 3482221716334969174639981)
      ·
        refine ⟨1305833143625613440489993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3482221716334969174639981 1305833143625613440489993)
        ·
          refine ⟨979374857719210080367495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1305833143625613440489993 979374857719210080367495)
          ·
            refine ⟨1469062286578815120551243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979374857719210080367495 1469062286578815120551243)
            ·
              refine ⟨2203593429868222680826865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1469062286578815120551243 2203593429868222680826865)
              ·
                refine ⟨1652695072401167010620149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2203593429868222680826865 1652695072401167010620149)
                ·
                  refine ⟨154940163037609407245639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1652695072401167010620149 154940163037609407245639)
                  ·
                    rfl

theorem cell20_339463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 5].length) (baseStart_339463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339463 prefixEnd_339463 := by exact prefixLift 339463
  have htrace : WordTrace (prefixWord ++ tailWord_339463) baseStart_339463 baseEnd_339463 := by
    simpa [prefixWord, tailWord_339463, baseEnd_339463] using wordTrace_append hprefix tailTrace_339463
  have hstable : (prefixWord ++ tailWord_339463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339463).length < 2 ^ (prefixWord ++ tailWord_339463).sum := by decide
  have hdescent : baseEnd_339463 < baseStart_339463 := by decide
  rcases family_descends (prefixWord ++ tailWord_339463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339466 : List Nat := [3, 1, 2, 2, 2, 2, 3, 3, 2]
def baseStart_339466 : Nat := 118140960795 + 339466 * 2 ^ 59
def prefixEnd_339466 : Nat := 4983230072969 + 3 ^ 40 * 339466 * 2
def baseEnd_339466 : Nat := 154941532319354730145627

theorem tailTrace_339466 : CollatzResearch.WordTrace tailWord_339466 prefixEnd_339466 154941532319354730145627 := by
  unfold tailWord_339466
  simp only [CollatzResearch.WordTrace]
  refine ⟨3095335547045033255547563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8254228125453422014793501 3095335547045033255547563)
  ·
    refine ⟨4643003320567549883321345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3095335547045033255547563 4643003320567549883321345)
    ·
      refine ⟨3482252490425662412491009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4643003320567549883321345 3482252490425662412491009)
      ·
        refine ⟨2611689367819246809368257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3482252490425662412491009 2611689367819246809368257)
        ·
          refine ⟨1958767025864435107026193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2611689367819246809368257 1958767025864435107026193)
          ·
            refine ⟨1469075269398326330269645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1958767025864435107026193 1469075269398326330269645)
            ·
              refine ⟨550903226024372373851117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1469075269398326330269645 550903226024372373851117)
              ·
                refine ⟨206588709759139640194169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 550903226024372373851117 206588709759139640194169)
                ·
                  refine ⟨154941532319354730145627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206588709759139640194169 154941532319354730145627)
                  ·
                    rfl

theorem cell20_339466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_339466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339466 prefixEnd_339466 := by exact prefixLift 339466
  have htrace : WordTrace (prefixWord ++ tailWord_339466) baseStart_339466 baseEnd_339466 := by
    simpa [prefixWord, tailWord_339466, baseEnd_339466] using wordTrace_append hprefix tailTrace_339466
  have hstable : (prefixWord ++ tailWord_339466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339466).length < 2 ^ (prefixWord ++ tailWord_339466).sum := by decide
  have hdescent : baseEnd_339466 < baseStart_339466 := by decide
  rcases family_descends (prefixWord ++ tailWord_339466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339469 : List Nat := [1, 7, 1, 1, 3, 1, 6]
def baseStart_339469 : Nat := 118140960795 + 339469 * 2 ^ 59
def prefixEnd_339469 : Nat := 4983230072969 + 3 ^ 40 * 339469 * 2
def baseEnd_339469 : Nat := 17215877955677783671735

theorem tailTrace_339469 : CollatzResearch.WordTrace tailWord_339469 prefixEnd_339469 17215877955677783671735 := by
  unfold tailWord_339469
  simp only [CollatzResearch.WordTrace]
  refine ⟨12381451607169264534549461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8254301071446176356366307 12381451607169264534549461)
  ·
    refine ⟨290190272043029637528503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 12381451607169264534549461 290190272043029637528503)
    ·
      refine ⟨435285408064544456292755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290190272043029637528503 435285408064544456292755)
      ·
        refine ⟨652928112096816684439133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435285408064544456292755 652928112096816684439133)
        ·
          refine ⟨244848042036306256664675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 652928112096816684439133 244848042036306256664675)
          ·
            refine ⟨367272063054459384997013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244848042036306256664675 367272063054459384997013)
            ·
              refine ⟨17215877955677783671735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 367272063054459384997013 17215877955677783671735)
              ·
                rfl

theorem cell20_339469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 6].length) (baseStart_339469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339469 prefixEnd_339469 := by exact prefixLift 339469
  have htrace : WordTrace (prefixWord ++ tailWord_339469) baseStart_339469 baseEnd_339469 := by
    simpa [prefixWord, tailWord_339469, baseEnd_339469] using wordTrace_append hprefix tailTrace_339469
  have hstable : (prefixWord ++ tailWord_339469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339469).length < 2 ^ (prefixWord ++ tailWord_339469).sum := by decide
  have hdescent : baseEnd_339469 < baseStart_339469 := by decide
  rcases family_descends (prefixWord ++ tailWord_339469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339477 : List Nat := [1, 3, 2, 1, 3, 2, 8]
def baseStart_339477 : Nat := 118140960795 + 339477 * 2 ^ 59
def prefixEnd_339477 : Nat := 4983230072969 + 3 ^ 40 * 339477 * 2
def baseEnd_339477 : Nat := 17216283668787508975435

theorem tailTrace_339477 : CollatzResearch.WordTrace tailWord_339477 prefixEnd_339477 17216283668787508975435 := by
  unfold tailWord_339477
  simp only [CollatzResearch.WordTrace]
  refine ⟨12381743391140281900840685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8254495594093521267227123 12381743391140281900840685)
  ·
    refine ⟨4643153771677605712815257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12381743391140281900840685 4643153771677605712815257)
    ·
      refine ⟨3482365328758204284611443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4643153771677605712815257 3482365328758204284611443)
      ·
        refine ⟨5223547993137306426917165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3482365328758204284611443 5223547993137306426917165)
        ·
          refine ⟨1958830497426489910093937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5223547993137306426917165 1958830497426489910093937)
          ·
            refine ⟨1469122873069867432570453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1958830497426489910093937 1469122873069867432570453)
            ·
              refine ⟨17216283668787508975435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1469122873069867432570453 17216283668787508975435)
              ·
                rfl

theorem cell20_339477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 8].length) (baseStart_339477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339477 prefixEnd_339477 := by exact prefixLift 339477
  have htrace : WordTrace (prefixWord ++ tailWord_339477) baseStart_339477 baseEnd_339477 := by
    simpa [prefixWord, tailWord_339477, baseEnd_339477] using wordTrace_append hprefix tailTrace_339477
  have hstable : (prefixWord ++ tailWord_339477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339477).length < 2 ^ (prefixWord ++ tailWord_339477).sum := by decide
  have hdescent : baseEnd_339477 < baseStart_339477 := by decide
  rcases family_descends (prefixWord ++ tailWord_339477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339487 : List Nat := [1, 1, 2, 4, 1, 1, 2, 6, 2]
def baseStart_339487 : Nat := 118140960795 + 339487 * 2 ^ 59
def prefixEnd_339487 : Nat := 4983230072969 + 3 ^ 40 * 339487 * 2
def baseEnd_339487 : Nat := 154951117291571990445541

theorem tailTrace_339487 : CollatzResearch.WordTrace tailWord_339487 prefixEnd_339487 154951117291571990445541 := by
  unfold tailWord_339487
  simp only [CollatzResearch.WordTrace]
  refine ⟨12382108121104053608704715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8254738747402702405803143 12382108121104053608704715)
  ·
    refine ⟨18573162181656080413057073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12382108121104053608704715 18573162181656080413057073)
    ·
      refine ⟨13929871636242060309792805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18573162181656080413057073 13929871636242060309792805)
      ·
        refine ⟨2611850931795386308086151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13929871636242060309792805 2611850931795386308086151)
        ·
          refine ⟨3917776397693079462129227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2611850931795386308086151 3917776397693079462129227)
          ·
            refine ⟨5876664596539619193193841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3917776397693079462129227 5876664596539619193193841)
            ·
              refine ⟨4407498447404714394895381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5876664596539619193193841 4407498447404714394895381)
              ·
                refine ⟨206601489722095987260721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4407498447404714394895381 206601489722095987260721)
                ·
                  refine ⟨154951117291571990445541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206601489722095987260721 154951117291571990445541)
                  ·
                    rfl

theorem cell20_339487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 2].length) (baseStart_339487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339487 prefixEnd_339487 := by exact prefixLift 339487
  have htrace : WordTrace (prefixWord ++ tailWord_339487) baseStart_339487 baseEnd_339487 := by
    simpa [prefixWord, tailWord_339487, baseEnd_339487] using wordTrace_append hprefix tailTrace_339487
  have hstable : (prefixWord ++ tailWord_339487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339487).length < 2 ^ (prefixWord ++ tailWord_339487).sum := by decide
  have hdescent : baseEnd_339487 < baseStart_339487 := by decide
  rcases family_descends (prefixWord ++ tailWord_339487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339525 : List Nat := [1, 3, 1, 1, 1, 4, 2, 5, 2]
def baseStart_339525 : Nat := 118140960795 + 339525 * 2 ^ 59
def prefixEnd_339525 : Nat := 4983230072969 + 3 ^ 40 * 339525 * 2
def baseEnd_339525 : Nat := 154968461527012747178719

theorem tailTrace_339525 : CollatzResearch.WordTrace tailWord_339525 prefixEnd_339525 154968461527012747178719 := by
  unfold tailWord_339525
  simp only [CollatzResearch.WordTrace]
  refine ⟨12383494094966386098588029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8255662729977590732392019 12383494094966386098588029)
  ·
    refine ⟨4643810285612394786970511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12383494094966386098588029 4643810285612394786970511)
    ·
      refine ⟨6965715428418592180455767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4643810285612394786970511 6965715428418592180455767)
      ·
        refine ⟨10448573142627888270683651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6965715428418592180455767 10448573142627888270683651)
        ·
          refine ⟨15672859713941832406025477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10448573142627888270683651 15672859713941832406025477)
          ·
            refine ⟨2938661196364093576129777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15672859713941832406025477 2938661196364093576129777)
            ·
              refine ⟨2203995897273070182097333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2938661196364093576129777 2203995897273070182097333)
              ·
                refine ⟨206624615369350329571625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2203995897273070182097333 206624615369350329571625)
                ·
                  refine ⟨154968461527012747178719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206624615369350329571625 154968461527012747178719)
                  ·
                    rfl

theorem cell20_339525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_339525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339525 prefixEnd_339525 := by exact prefixLift 339525
  have htrace : WordTrace (prefixWord ++ tailWord_339525) baseStart_339525 baseEnd_339525 := by
    simpa [prefixWord, tailWord_339525, baseEnd_339525] using wordTrace_append hprefix tailTrace_339525
  have hstable : (prefixWord ++ tailWord_339525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339525).length < 2 ^ (prefixWord ++ tailWord_339525).sum := by decide
  have hdescent : baseEnd_339525 < baseStart_339525 := by decide
  rcases family_descends (prefixWord ++ tailWord_339525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339591 : List Nat := [1, 1, 4, 2, 1, 4, 7]
def baseStart_339591 : Nat := 118140960795 + 339591 * 2 ^ 59
def prefixEnd_339591 : Nat := 4983230072969 + 3 ^ 40 * 339591 * 2
def baseEnd_339591 : Nat := 17222065080601094553161

theorem tailTrace_339591 : CollatzResearch.WordTrace tailWord_339591 prefixEnd_339591 17222065080601094553161 := by
  unfold tailWord_339591
  simp only [CollatzResearch.WordTrace]
  refine ⟨12385901312727279370490627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8257267541818186246993751 12385901312727279370490627)
  ·
    refine ⟨18578851969090919055735941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12385901312727279370490627 18578851969090919055735941)
    ·
      refine ⟨3483534744204547322950489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18578851969090919055735941 3483534744204547322950489)
      ·
        refine ⟨2612651058153410492212867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3483534744204547322950489 2612651058153410492212867)
        ·
          refine ⟨3918976587230115738319301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2612651058153410492212867 3918976587230115738319301)
          ·
            refine ⟨734808110105646700934869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3918976587230115738319301 734808110105646700934869)
            ·
              refine ⟨17222065080601094553161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 734808110105646700934869 17222065080601094553161)
              ·
                rfl

theorem cell20_339591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 7].length) (baseStart_339591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339591 prefixEnd_339591 := by exact prefixLift 339591
  have htrace : WordTrace (prefixWord ++ tailWord_339591) baseStart_339591 baseEnd_339591 := by
    simpa [prefixWord, tailWord_339591, baseEnd_339591] using wordTrace_append hprefix tailTrace_339591
  have hstable : (prefixWord ++ tailWord_339591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339591).length < 2 ^ (prefixWord ++ tailWord_339591).sum := by decide
  have hdescent : baseEnd_339591 < baseStart_339591 := by decide
  rcases family_descends (prefixWord ++ tailWord_339591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339594 : List Nat := [3, 1, 2, 3, 2, 1, 3, 2, 3]
def baseStart_339594 : Nat := 118140960795 + 339594 * 2 ^ 59
def prefixEnd_339594 : Nat := 4983230072969 + 3 ^ 40 * 339594 * 2
def baseEnd_339594 : Nat := 154999955007155173878437

theorem tailTrace_339594 : CollatzResearch.WordTrace tailWord_339594 prefixEnd_339594 154999955007155173878437 := by
  unfold tailWord_339594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3096502682929102720712459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8257340487810940588566557 3096502682929102720712459)
  ·
    refine ⟨4644754024393654081068689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3096502682929102720712459 4644754024393654081068689)
    ·
      refine ⟨3483565518295240560801517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4644754024393654081068689 3483565518295240560801517)
      ·
        refine ⟨1306337069360715210300569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3483565518295240560801517 1306337069360715210300569)
        ·
          refine ⟨979752802020536407725427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1306337069360715210300569 979752802020536407725427)
          ·
            refine ⟨1469629203030804611588141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979752802020536407725427 1469629203030804611588141)
            ·
              refine ⟨551110951136551729345553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1469629203030804611588141 551110951136551729345553)
              ·
                refine ⟨413333213352413797009165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 551110951136551729345553 413333213352413797009165)
                ·
                  refine ⟨154999955007155173878437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 413333213352413797009165 154999955007155173878437)
                  ·
                    rfl

theorem cell20_339594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_339594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339594 prefixEnd_339594 := by exact prefixLift 339594
  have htrace : WordTrace (prefixWord ++ tailWord_339594) baseStart_339594 baseEnd_339594 := by
    simpa [prefixWord, tailWord_339594, baseEnd_339594] using wordTrace_append hprefix tailTrace_339594
  have hstable : (prefixWord ++ tailWord_339594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339594).length < 2 ^ (prefixWord ++ tailWord_339594).sum := by decide
  have hdescent : baseEnd_339594 < baseStart_339594 := by decide
  rcases family_descends (prefixWord ++ tailWord_339594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339643 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 6]
def baseStart_339643 : Nat := 118140960795 + 339643 * 2 ^ 59
def prefixEnd_339643 : Nat := 4983230072969 + 3 ^ 40 * 339643 * 2
def baseEnd_339643 : Nat := 155022319942328781244903

theorem tailTrace_339643 : CollatzResearch.WordTrace tailWord_339643 prefixEnd_339643 155022319942328781244903 := by
  unfold tailWord_339643
  simp only [CollatzResearch.WordTrace]
  refine ⟨12387797908538892251383583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8258531939025928167589055 12387797908538892251383583)
  ·
    refine ⟨18581696862808338377075375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12387797908538892251383583 18581696862808338377075375)
    ·
      refine ⟨27872545294212507565613063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18581696862808338377075375 27872545294212507565613063)
      ·
        refine ⟨41808817941318761348419595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27872545294212507565613063 41808817941318761348419595)
        ·
          refine ⟨62713226911978142022629393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41808817941318761348419595 62713226911978142022629393)
          ·
            refine ⟨47034920183983606516972045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62713226911978142022629393 47034920183983606516972045)
            ·
              refine ⟨17638095068993852443864517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47034920183983606516972045 17638095068993852443864517)
              ·
                refine ⟨3307142825436347333224597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17638095068993852443864517 3307142825436347333224597)
                ·
                  refine ⟨155022319942328781244903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3307142825436347333224597 155022319942328781244903)
                  ·
                    rfl

theorem cell20_339643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_339643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339643 prefixEnd_339643 := by exact prefixLift 339643
  have htrace : WordTrace (prefixWord ++ tailWord_339643) baseStart_339643 baseEnd_339643 := by
    simpa [prefixWord, tailWord_339643, baseEnd_339643] using wordTrace_append hprefix tailTrace_339643
  have hstable : (prefixWord ++ tailWord_339643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339643).length < 2 ^ (prefixWord ++ tailWord_339643).sum := by decide
  have hdescent : baseEnd_339643 < baseStart_339643 := by decide
  rcases family_descends (prefixWord ++ tailWord_339643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339646 : List Nat := [4, 2, 1, 1, 2, 4, 6]
def baseStart_339646 : Nat := 118140960795 + 339646 * 2 ^ 59
def prefixEnd_339646 : Nat := 4983230072969 + 3 ^ 40 * 339646 * 2
def baseEnd_339646 : Nat := 17224854358230456016099

theorem tailTrace_339646 : CollatzResearch.WordTrace tailWord_339646 prefixEnd_339646 17224854358230456016099 := by
  unfold tailWord_339646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1548488415941002970467849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8258604885018682509161861 1548488415941002970467849)
  ·
    refine ⟨1161366311955752227850887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1548488415941002970467849 1161366311955752227850887)
    ·
      refine ⟨1742049467933628341776331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1161366311955752227850887 1742049467933628341776331)
      ·
        refine ⟨2613074201900442512664497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1742049467933628341776331 2613074201900442512664497)
        ·
          refine ⟨1959805651425331884498373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2613074201900442512664497 1959805651425331884498373)
          ·
            refine ⟨367463559642249728343445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1959805651425331884498373 367463559642249728343445)
            ·
              refine ⟨17224854358230456016099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 367463559642249728343445 17224854358230456016099)
              ·
                rfl

theorem cell20_339646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 6].length) (baseStart_339646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339646 prefixEnd_339646 := by exact prefixLift 339646
  have htrace : WordTrace (prefixWord ++ tailWord_339646) baseStart_339646 baseEnd_339646 := by
    simpa [prefixWord, tailWord_339646, baseEnd_339646] using wordTrace_append hprefix tailTrace_339646
  have hstable : (prefixWord ++ tailWord_339646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339646).length < 2 ^ (prefixWord ++ tailWord_339646).sum := by decide
  have hdescent : baseEnd_339646 < baseStart_339646 := by decide
  rcases family_descends (prefixWord ++ tailWord_339646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339656 : List Nat := [2, 1, 3, 1, 2, 2, 5, 2, 2]
def baseStart_339656 : Nat := 118140960795 + 339656 * 2 ^ 59
def prefixEnd_339656 : Nat := 4983230072969 + 3 ^ 40 * 339656 * 2
def baseEnd_339656 : Nat := 155028253496558513811517

theorem tailTrace_339656 : CollatzResearch.WordTrace tailWord_339656 prefixEnd_339656 155028253496558513811517 := by
  unfold tailWord_339656
  simp only [CollatzResearch.WordTrace]
  refine ⟨6194136028745897735803411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8258848038327863647737881 6194136028745897735803411)
  ·
    refine ⟨9291204043118846603705117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6194136028745897735803411 9291204043118846603705117)
    ·
      refine ⟨3484201516169567476389419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9291204043118846603705117 3484201516169567476389419)
      ·
        refine ⟨5226302274254351214584129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3484201516169567476389419 5226302274254351214584129)
        ·
          refine ⟨3919726705690763410938097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5226302274254351214584129 3919726705690763410938097)
          ·
            refine ⟨2939795029268072558203573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3919726705690763410938097 2939795029268072558203573)
            ·
              refine ⟨275605783993881802331585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2939795029268072558203573 275605783993881802331585)
              ·
                refine ⟨206704337995411351748689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275605783993881802331585 206704337995411351748689)
                ·
                  refine ⟨155028253496558513811517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206704337995411351748689 155028253496558513811517)
                  ·
                    rfl

theorem cell20_339656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 2].length) (baseStart_339656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339656 prefixEnd_339656 := by exact prefixLift 339656
  have htrace : WordTrace (prefixWord ++ tailWord_339656) baseStart_339656 baseEnd_339656 := by
    simpa [prefixWord, tailWord_339656, baseEnd_339656] using wordTrace_append hprefix tailTrace_339656
  have hstable : (prefixWord ++ tailWord_339656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339656).length < 2 ^ (prefixWord ++ tailWord_339656).sum := by decide
  have hdescent : baseEnd_339656 < baseStart_339656 := by decide
  rcases family_descends (prefixWord ++ tailWord_339656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339722 : List Nat := [3, 1, 2, 2, 1, 5, 1, 5]
def baseStart_339722 : Nat := 118140960795 + 339722 * 2 ^ 59
def prefixEnd_339722 : Nat := 4983230072969 + 3 ^ 40 * 339722 * 2
def baseEnd_339722 : Nat := 51686125898318539203749

theorem tailTrace_339722 : CollatzResearch.WordTrace tailWord_339722 prefixEnd_339722 51686125898318539203749 := by
  unfold tailWord_339722
  simp only [CollatzResearch.WordTrace]
  refine ⟨3097669818813172185877355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8260452850168459162339613 3097669818813172185877355)
  ·
    refine ⟨4646504728219758278816033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3097669818813172185877355 4646504728219758278816033)
    ·
      refine ⟨3484878546164818709112025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4646504728219758278816033 3484878546164818709112025)
      ·
        refine ⟨2613658909623614031834019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3484878546164818709112025 2613658909623614031834019)
        ·
          refine ⟨3920488364435421047751029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2613658909623614031834019 3920488364435421047751029)
          ·
            refine ⟨367545784165820723226659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3920488364435421047751029 367545784165820723226659)
            ·
              refine ⟨551318676248731084839989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367545784165820723226659 551318676248731084839989)
              ·
                refine ⟨51686125898318539203749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 551318676248731084839989 51686125898318539203749)
                ·
                  rfl

theorem cell20_339722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_339722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339722 prefixEnd_339722 := by exact prefixLift 339722
  have htrace : WordTrace (prefixWord ++ tailWord_339722) baseStart_339722 baseEnd_339722 := by
    simpa [prefixWord, tailWord_339722, baseEnd_339722] using wordTrace_append hprefix tailTrace_339722
  have hstable : (prefixWord ++ tailWord_339722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339722).length < 2 ^ (prefixWord ++ tailWord_339722).sum := by decide
  have hdescent : baseEnd_339722 < baseStart_339722 := by decide
  rcases family_descends (prefixWord ++ tailWord_339722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339763 : List Nat := [1, 1, 1, 2, 8, 1, 1, 2, 3]
def baseStart_339763 : Nat := 118140960795 + 339763 * 2 ^ 59
def prefixEnd_339763 : Nat := 4983230072969 + 3 ^ 40 * 339763 * 2
def baseEnd_339763 : Nat := 155077091212141697244413

theorem tailTrace_339763 : CollatzResearch.WordTrace tailWord_339763 prefixEnd_339763 155077091212141697244413 := by
  unfold tailWord_339763
  simp only [CollatzResearch.WordTrace]
  refine ⟨12392174668104152745751943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8261449778736101830501295 12392174668104152745751943)
  ·
    refine ⟨18588262002156229118627915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12392174668104152745751943 18588262002156229118627915)
    ·
      refine ⟨27882393003234343677941873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18588262002156229118627915 27882393003234343677941873)
      ·
        refine ⟨20911794752425757758456405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27882393003234343677941873 20911794752425757758456405)
        ·
          refine ⟨245060094754989348731911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 20911794752425757758456405 245060094754989348731911)
          ·
            refine ⟨367590142132484023097867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245060094754989348731911 367590142132484023097867)
            ·
              refine ⟨551385213198726034646801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367590142132484023097867 551385213198726034646801)
              ·
                refine ⟨413538909899044525985101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 551385213198726034646801 413538909899044525985101)
                ·
                  refine ⟨155077091212141697244413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 413538909899044525985101 155077091212141697244413)
                  ·
                    rfl

theorem cell20_339763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 3].length) (baseStart_339763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339763 prefixEnd_339763 := by exact prefixLift 339763
  have htrace : WordTrace (prefixWord ++ tailWord_339763) baseStart_339763 baseEnd_339763 := by
    simpa [prefixWord, tailWord_339763, baseEnd_339763] using wordTrace_append hprefix tailTrace_339763
  have hstable : (prefixWord ++ tailWord_339763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339763).length < 2 ^ (prefixWord ++ tailWord_339763).sum := by decide
  have hdescent : baseEnd_339763 < baseStart_339763 := by decide
  rcases family_descends (prefixWord ++ tailWord_339763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339784 : List Nat := [2, 1, 3, 1, 1, 5, 3, 1, 3]
def baseStart_339784 : Nat := 118140960795 + 339784 * 2 ^ 59
def prefixEnd_339784 : Nat := 4983230072969 + 3 ^ 40 * 339784 * 2
def baseEnd_339784 : Nat := 155086676184358957544327

theorem tailTrace_339784 : CollatzResearch.WordTrace tailWord_339784 prefixEnd_339784 155086676184358957544327 := by
  unfold tailWord_339784
  simp only [CollatzResearch.WordTrace]
  refine ⟨6196470300514036666133203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8261960400685382221510937 6196470300514036666133203)
  ·
    refine ⟨9294705450771054999199805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6196470300514036666133203 9294705450771054999199805)
    ·
      refine ⟨3485514544039145624699927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9294705450771054999199805 3485514544039145624699927)
      ·
        refine ⟨5228271816058718437049891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3485514544039145624699927 5228271816058718437049891)
        ·
          refine ⟨7842407724088077655574837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5228271816058718437049891 7842407724088077655574837)
          ·
            refine ⟨735225724133257280210141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7842407724088077655574837 735225724133257280210141)
            ·
              refine ⟨275709646549971480078803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 735225724133257280210141 275709646549971480078803)
              ·
                refine ⟨413564469824957220118205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275709646549971480078803 413564469824957220118205)
                ·
                  refine ⟨155086676184358957544327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 413564469824957220118205 155086676184358957544327)
                  ·
                    rfl

theorem cell20_339784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 3].length) (baseStart_339784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339784 prefixEnd_339784 := by exact prefixLift 339784
  have htrace : WordTrace (prefixWord ++ tailWord_339784) baseStart_339784 baseEnd_339784 := by
    simpa [prefixWord, tailWord_339784, baseEnd_339784] using wordTrace_append hprefix tailTrace_339784
  have hstable : (prefixWord ++ tailWord_339784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339784).length < 2 ^ (prefixWord ++ tailWord_339784).sum := by decide
  have hdescent : baseEnd_339784 < baseStart_339784 := by decide
  rcases family_descends (prefixWord ++ tailWord_339784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339804 : List Nat := [2, 2, 4, 2, 3, 1, 1, 3, 2]
def baseStart_339804 : Nat := 118140960795 + 339804 * 2 ^ 59
def prefixEnd_339804 : Nat := 4983230072969 + 3 ^ 40 * 339804 * 2
def baseEnd_339804 : Nat := 155095804729327776877579

theorem tailTrace_339804 : CollatzResearch.WordTrace tailWord_339804 prefixEnd_339804 155095804729327776877579 := by
  unfold tailWord_339804
  simp only [CollatzResearch.WordTrace]
  refine ⟨6196835030477808373997233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8262446707303744498662977 6196835030477808373997233)
  ·
    refine ⟨4647626272858356280497925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6196835030477808373997233 4647626272858356280497925)
    ·
      refine ⟨871429926160941802593361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4647626272858356280497925 871429926160941802593361)
      ·
        refine ⟨653572444620706351945021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 871429926160941802593361 653572444620706351945021)
        ·
          refine ⟨245089666732764881979383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 653572444620706351945021 245089666732764881979383)
          ·
            refine ⟨367634500099147322969075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245089666732764881979383 367634500099147322969075)
            ·
              refine ⟨551451750148720984453613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367634500099147322969075 551451750148720984453613)
              ·
                refine ⟨206794406305770369170105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 551451750148720984453613 206794406305770369170105)
                ·
                  refine ⟨155095804729327776877579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206794406305770369170105 155095804729327776877579)
                  ·
                    rfl

theorem cell20_339804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_339804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339804 prefixEnd_339804 := by exact prefixLift 339804
  have htrace : WordTrace (prefixWord ++ tailWord_339804) baseStart_339804 baseEnd_339804 := by
    simpa [prefixWord, tailWord_339804, baseEnd_339804] using wordTrace_append hprefix tailTrace_339804
  have hstable : (prefixWord ++ tailWord_339804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339804).length < 2 ^ (prefixWord ++ tailWord_339804).sum := by decide
  have hdescent : baseEnd_339804 < baseStart_339804 := by decide
  rcases family_descends (prefixWord ++ tailWord_339804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339808 : List Nat := [2, 1, 1, 3, 3, 4, 1, 3, 2]
def baseStart_339808 : Nat := 118140960795 + 339808 * 2 ^ 59
def prefixEnd_339808 : Nat := 4983230072969 + 3 ^ 40 * 339808 * 2
def baseEnd_339808 : Nat := 155097630438321540744229

theorem tailTrace_339808 : CollatzResearch.WordTrace tailWord_339808 prefixEnd_339808 155097630438321540744229 := by
  unfold tailWord_339808
  simp only [CollatzResearch.WordTrace]
  refine ⟨6196907976470562715570039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8262543968627416954093385 6196907976470562715570039)
  ·
    refine ⟨9295361964705844073355059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6196907976470562715570039 9295361964705844073355059)
    ·
      refine ⟨13943042947058766110032589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9295361964705844073355059 13943042947058766110032589)
      ·
        refine ⟨5228641105147037291262221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13943042947058766110032589 5228641105147037291262221)
        ·
          refine ⟨1960740414430138984223333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5228641105147037291262221 1960740414430138984223333)
          ·
            refine ⟨367638827705651059541875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1960740414430138984223333 367638827705651059541875)
            ·
              refine ⟨551458241558476589312813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367638827705651059541875 551458241558476589312813)
              ·
                refine ⟨206796840584428720992305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 551458241558476589312813 206796840584428720992305)
                ·
                  refine ⟨155097630438321540744229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206796840584428720992305 155097630438321540744229)
                  ·
                    rfl

theorem cell20_339808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 2].length) (baseStart_339808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_339808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_339808 prefixEnd_339808 := by exact prefixLift 339808
  have htrace : WordTrace (prefixWord ++ tailWord_339808) baseStart_339808 baseEnd_339808 := by
    simpa [prefixWord, tailWord_339808, baseEnd_339808] using wordTrace_append hprefix tailTrace_339808
  have hstable : (prefixWord ++ tailWord_339808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339808).length < 2 ^ (prefixWord ++ tailWord_339808).sum := by decide
  have hdescent : baseEnd_339808 < baseStart_339808 := by decide
  rcases family_descends (prefixWord ++ tailWord_339808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
