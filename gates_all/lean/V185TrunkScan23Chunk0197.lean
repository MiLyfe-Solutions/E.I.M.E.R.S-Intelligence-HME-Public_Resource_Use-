import V185TrunkScan23Chunk0196

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1166061 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_1166061 : Nat := 118140960795 + 1166061 * 2 ^ 59
def prefixEnd_1166061 : Nat := 4983230072969 + 3 ^ 40 * 1166061 * 2
def baseEnd_1166061 : Nat := 199583255154155838224963

theorem tailTrace_1166061 : CollatzResearch.WordTrace tailWord_1166061 prefixEnd_1166061 199583255154155838224963 := by
  unfold tailWord_1166061
  simp only [CollatzResearch.WordTrace]
  refine ⟨42529738628567619208978037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28353159085711746139318691 42529738628567619208978037)
  ·
    refine ⟨3987162996428214300841691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42529738628567619208978037 3987162996428214300841691)
    ·
      refine ⟨5980744494642321451262537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3987162996428214300841691 5980744494642321451262537)
      ·
        refine ⟨4485558370981741088446903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5980744494642321451262537 4485558370981741088446903)
        ·
          refine ⟨6728337556472611632670355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4485558370981741088446903 6728337556472611632670355)
          ·
            refine ⟨10092506334708917449005533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6728337556472611632670355 10092506334708917449005533)
            ·
              refine ⟨3784689875515844043377075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10092506334708917449005533 3784689875515844043377075)
              ·
                refine ⟨5677034813273766065065613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3784689875515844043377075 5677034813273766065065613)
                ·
                  refine ⟨2128888054977662274399605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5677034813273766065065613 2128888054977662274399605)
                  ·
                    refine ⟨199583255154155838224963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2128888054977662274399605 199583255154155838224963)
                    ·
                      rfl

theorem cell23_1166061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_1166061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166061 prefixEnd_1166061 := by exact prefixLift 1166061
  have htrace : WordTrace (prefixWord ++ tailWord_1166061) baseStart_1166061 baseEnd_1166061 := by
    simpa [prefixWord, tailWord_1166061, baseEnd_1166061] using wordTrace_append hprefix tailTrace_1166061
  have hstable : (prefixWord ++ tailWord_1166061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166061).length < 2 ^ (prefixWord ++ tailWord_1166061).sum := by decide
  have hdescent : baseEnd_1166061 < baseStart_1166061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166074 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 3, 6]
def baseStart_1166074 : Nat := 118140960795 + 1166074 * 2 ^ 59
def prefixEnd_1166074 : Nat := 4983230072969 + 3 ^ 40 * 1166074 * 2
def baseEnd_1166074 : Nat := 199585480236991987937443

theorem tailTrace_1166074 : CollatzResearch.WordTrace tailWord_1166074 prefixEnd_1166074 199585480236991987937443 := by
  unfold tailWord_1166074
  simp only [CollatzResearch.WordTrace]
  refine ⟨10632553194380130607300319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28353475185013681619467517 10632553194380130607300319)
  ·
    refine ⟨15948829791570195910950479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10632553194380130607300319 15948829791570195910950479)
    ·
      refine ⟨23923244687355293866425719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15948829791570195910950479 23923244687355293866425719)
      ·
        refine ⟨35884867031032940799638579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23923244687355293866425719 35884867031032940799638579)
        ·
          refine ⟨53827300546549411199457869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35884867031032940799638579 53827300546549411199457869)
          ·
            refine ⟨20185237704956029199796701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53827300546549411199457869 20185237704956029199796701)
            ·
              refine ⟨7569464139358510949923763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20185237704956029199796701 7569464139358510949923763)
              ·
                refine ⟨11354196209037766424885645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7569464139358510949923763 11354196209037766424885645)
                ·
                  refine ⟨4257823578389162409332117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11354196209037766424885645 4257823578389162409332117)
                  ·
                    refine ⟨199585480236991987937443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4257823578389162409332117 199585480236991987937443)
                    ·
                      rfl

theorem cell23_1166074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_1166074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166074 prefixEnd_1166074 := by exact prefixLift 1166074
  have htrace : WordTrace (prefixWord ++ tailWord_1166074) baseStart_1166074 baseEnd_1166074 := by
    simpa [prefixWord, tailWord_1166074, baseEnd_1166074] using wordTrace_append hprefix tailTrace_1166074
  have hstable : (prefixWord ++ tailWord_1166074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166074).length < 2 ^ (prefixWord ++ tailWord_1166074).sum := by decide
  have hdescent : baseEnd_1166074 < baseStart_1166074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166101 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 5, 2, 3]
def baseStart_1166101 : Nat := 118140960795 + 1166101 * 2 ^ 59
def prefixEnd_1166101 : Nat := 4983230072969 + 3 ^ 40 * 1166101 * 2
def baseEnd_1166101 : Nat := 598770304688647358174705

theorem tailTrace_1166101 : CollatzResearch.WordTrace tailWord_1166101 prefixEnd_1166101 598770304688647358174705 := by
  unfold tailWord_1166101
  simp only [CollatzResearch.WordTrace]
  refine ⟨42531197548422706040434157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28354131698948470693622771 42531197548422706040434157)
  ·
    refine ⟨15949199080658514765162809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42531197548422706040434157 15949199080658514765162809)
    ·
      refine ⟨11961899310493886073872107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15949199080658514765162809 11961899310493886073872107)
      ·
        refine ⟨17942848965740829110808161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11961899310493886073872107 17942848965740829110808161)
        ·
          refine ⟨13457136724305621833106121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17942848965740829110808161 13457136724305621833106121)
          ·
            refine ⟨10092852543229216374829591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13457136724305621833106121 10092852543229216374829591)
            ·
              refine ⟨15139278814843824562244387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10092852543229216374829591 15139278814843824562244387)
              ·
                refine ⟨22708918222265736843366581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15139278814843824562244387 22708918222265736843366581)
                ·
                  refine ⟨2128961083337412829065617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22708918222265736843366581 2128961083337412829065617)
                  ·
                    refine ⟨1596720812503059621799213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2128961083337412829065617 1596720812503059621799213)
                    ·
                      refine ⟨598770304688647358174705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1596720812503059621799213 598770304688647358174705)
                      ·
                        rfl

theorem cell23_1166101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_1166101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166101 prefixEnd_1166101 := by exact prefixLift 1166101
  have htrace : WordTrace (prefixWord ++ tailWord_1166101) baseStart_1166101 baseEnd_1166101 := by
    simpa [prefixWord, tailWord_1166101, baseEnd_1166101] using wordTrace_append hprefix tailTrace_1166101
  have hstable : (prefixWord ++ tailWord_1166101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166101).length < 2 ^ (prefixWord ++ tailWord_1166101).sum := by decide
  have hdescent : baseEnd_1166101 < baseStart_1166101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166108 : List Nat := [2, 2, 3, 1, 1, 3, 2, 3, 2, 4]
def baseStart_1166108 : Nat := 118140960795 + 1166108 * 2 ^ 59
def prefixEnd_1166108 : Nat := 4983230072969 + 3 ^ 40 * 1166108 * 2
def baseEnd_1166108 : Nat := 199591299684409610262391

theorem tailTrace_1166108 : CollatzResearch.WordTrace tailWord_1166108 prefixEnd_1166108 199591299684409610262391 := by
  unfold tailWord_1166108
  simp only [CollatzResearch.WordTrace]
  refine ⟨21265726429698673117969489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28354301906264897490625985 21265726429698673117969489)
  ·
    refine ⟨15949294822274004838477117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21265726429698673117969489 15949294822274004838477117)
    ·
      refine ⟨5980985558352751814428919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15949294822274004838477117 5980985558352751814428919)
      ·
        refine ⟨8971478337529127721643379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5980985558352751814428919 8971478337529127721643379)
        ·
          refine ⟨13457217506293691582465069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8971478337529127721643379 13457217506293691582465069)
          ·
            refine ⟨5046456564860134343424401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13457217506293691582465069 5046456564860134343424401)
            ·
              refine ⟨3784842423645100757568301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5046456564860134343424401 3784842423645100757568301)
              ·
                refine ⟨1419315908866912784088113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3784842423645100757568301 1419315908866912784088113)
                ·
                  refine ⟨1064486931650184588066085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1419315908866912784088113 1064486931650184588066085)
                  ·
                    refine ⟨199591299684409610262391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1064486931650184588066085 199591299684409610262391)
                    ·
                      rfl

theorem cell23_1166108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_1166108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166108 prefixEnd_1166108 := by exact prefixLift 1166108
  have htrace : WordTrace (prefixWord ++ tailWord_1166108) baseStart_1166108 baseEnd_1166108 := by
    simpa [prefixWord, tailWord_1166108, baseEnd_1166108] using wordTrace_append hprefix tailTrace_1166108
  have hstable : (prefixWord ++ tailWord_1166108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166108).length < 2 ^ (prefixWord ++ tailWord_1166108).sum := by decide
  have hdescent : baseEnd_1166108 < baseStart_1166108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166111 : List Nat := [1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 4]
def baseStart_1166111 : Nat := 118140960795 + 1166111 * 2 ^ 59
def prefixEnd_1166111 : Nat := 4983230072969 + 3 ^ 40 * 1166111 * 2
def baseEnd_1166111 : Nat := 598775439495192319049659

theorem tailTrace_1166111 : CollatzResearch.WordTrace tailWord_1166111 prefixEnd_1166111 598775439495192319049659 := by
  unfold tailWord_1166111
  simp only [CollatzResearch.WordTrace]
  refine ⟨42531562278386477748298187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28354374852257651832198791 42531562278386477748298187)
  ·
    refine ⟨63797343417579716622447281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42531562278386477748298187 63797343417579716622447281)
    ·
      refine ⟨47848007563184787466835461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63797343417579716622447281 47848007563184787466835461)
      ·
        refine ⟨8971501418097147650031649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47848007563184787466835461 8971501418097147650031649)
        ·
          refine ⟨6728626063572860737523737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8971501418097147650031649 6728626063572860737523737)
          ·
            refine ⟨5046469547679645553142803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6728626063572860737523737 5046469547679645553142803)
            ·
              refine ⟨7569704321519468329714205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5046469547679645553142803 7569704321519468329714205)
              ·
                refine ⟨2838639120569800623642827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7569704321519468329714205 2838639120569800623642827)
                ·
                  refine ⟨4257958680854700935464241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2838639120569800623642827 4257958680854700935464241)
                  ·
                    refine ⟨3193469010641025701598181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4257958680854700935464241 3193469010641025701598181)
                    ·
                      refine ⟨598775439495192319049659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3193469010641025701598181 598775439495192319049659)
                      ·
                        rfl

theorem cell23_1166111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_1166111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166111 prefixEnd_1166111 := by exact prefixLift 1166111
  have htrace : WordTrace (prefixWord ++ tailWord_1166111) baseStart_1166111 baseEnd_1166111 := by
    simpa [prefixWord, tailWord_1166111, baseEnd_1166111] using wordTrace_append hprefix tailTrace_1166111
  have hstable : (prefixWord ++ tailWord_1166111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166111).length < 2 ^ (prefixWord ++ tailWord_1166111).sum := by decide
  have hdescent : baseEnd_1166111 < baseStart_1166111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166142 : List Nat := [4, 2, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_1166142 : Nat := 118140960795 + 1166142 * 2 ^ 59
def prefixEnd_1166142 : Nat := 4983230072969 + 3 ^ 40 * 1166142 * 2
def baseEnd_1166142 : Nat := 199597119131827232587339

theorem tailTrace_1166142 : CollatzResearch.WordTrace tailWord_1166142 prefixEnd_1166142 199597119131827232587339 := by
  unfold tailWord_1166142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5316586617659271255334585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28355128627516113361784453 5316586617659271255334585)
  ·
    refine ⟨3987439963244453441500939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5316586617659271255334585 3987439963244453441500939)
    ·
      refine ⟨5981159944866680162251409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3987439963244453441500939 5981159944866680162251409)
      ·
        refine ⟨4485869958650010121688557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5981159944866680162251409 4485869958650010121688557)
        ·
          refine ⟨1682201234493753795633209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4485869958650010121688557 1682201234493753795633209)
          ·
            refine ⟨1261650925870315346724907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1682201234493753795633209 1261650925870315346724907)
            ·
              refine ⟨1892476388805473020087361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1261650925870315346724907 1892476388805473020087361)
              ·
                refine ⟨1419357291604104765065521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1892476388805473020087361 1419357291604104765065521)
                ·
                  refine ⟨1064517968703078573799141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1419357291604104765065521 1064517968703078573799141)
                  ·
                    refine ⟨199597119131827232587339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1064517968703078573799141 199597119131827232587339)
                    ·
                      rfl

theorem cell23_1166142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_1166142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166142 prefixEnd_1166142 := by exact prefixLift 1166142
  have htrace : WordTrace (prefixWord ++ tailWord_1166142) baseStart_1166142 baseEnd_1166142 := by
    simpa [prefixWord, tailWord_1166142, baseEnd_1166142] using wordTrace_append hprefix tailTrace_1166142
  have hstable : (prefixWord ++ tailWord_1166142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166142).length < 2 ^ (prefixWord ++ tailWord_1166142).sum := by decide
  have hdescent : baseEnd_1166142 < baseStart_1166142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166158 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2]
def baseStart_1166158 : Nat := 118140960795 + 1166158 * 2 ^ 59
def prefixEnd_1166158 : Nat := 4983230072969 + 3 ^ 40 * 1166158 * 2
def baseEnd_1166158 : Nat := 598799573085953635161943

theorem tailTrace_1166158 : CollatzResearch.WordTrace tailWord_1166158 prefixEnd_1166158 598799573085953635161943 := by
  unfold tailWord_1166158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5316659563652025596907391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28355517672810803183506085 5316659563652025596907391)
  ·
    refine ⟨7974989345478038395361087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5316659563652025596907391 7974989345478038395361087)
    ·
      refine ⟨11962484018217057593041631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7974989345478038395361087 11962484018217057593041631)
      ·
        refine ⟨17943726027325586389562447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11962484018217057593041631 17943726027325586389562447)
        ·
          refine ⟨26915589040988379584343671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17943726027325586389562447 26915589040988379584343671)
          ·
            refine ⟨40373383561482569376515507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26915589040988379584343671 40373383561482569376515507)
            ·
              refine ⟨60560075342223854064773261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40373383561482569376515507 60560075342223854064773261)
              ·
                refine ⟨22710028253333945274289973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60560075342223854064773261 22710028253333945274289973)
                ·
                  refine ⟨2129065148750057369464685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22710028253333945274289973 2129065148750057369464685)
                  ·
                    refine ⟨798399430781271513549257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2129065148750057369464685 798399430781271513549257)
                    ·
                      refine ⟨598799573085953635161943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 798399430781271513549257 598799573085953635161943)
                      ·
                        rfl

theorem cell23_1166158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_1166158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166158 prefixEnd_1166158 := by exact prefixLift 1166158
  have htrace : WordTrace (prefixWord ++ tailWord_1166158) baseStart_1166158 baseEnd_1166158 := by
    simpa [prefixWord, tailWord_1166158, baseEnd_1166158] using wordTrace_append hprefix tailTrace_1166158
  have hstable : (prefixWord ++ tailWord_1166158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166158).length < 2 ^ (prefixWord ++ tailWord_1166158).sum := by decide
  have hdescent : baseEnd_1166158 < baseStart_1166158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166175 : List Nat := [1, 1, 2, 3, 1, 3, 4, 2, 1, 3, 2]
def baseStart_1166175 : Nat := 118140960795 + 1166175 * 2 ^ 59
def prefixEnd_1166175 : Nat := 4983230072969 + 3 ^ 40 * 1166175 * 2
def baseEnd_1166175 : Nat := 598808302257080068649365

theorem tailTrace_1166175 : CollatzResearch.WordTrace tailWord_1166175 prefixEnd_1166175 598808302257080068649365 := by
  unfold tailWord_1166175
  simp only [CollatzResearch.WordTrace]
  refine ⟨42533896550154616678627979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28355931033436411119085319 42533896550154616678627979)
  ·
    refine ⟨63800844825231925017941969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42533896550154616678627979 63800844825231925017941969)
    ·
      refine ⟨47850633618923943763456477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63800844825231925017941969 47850633618923943763456477)
      ·
        refine ⟨17943987607096478911296179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47850633618923943763456477 17943987607096478911296179)
        ·
          refine ⟨26915981410644718366944269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17943987607096478911296179 26915981410644718366944269)
          ·
            refine ⟨10093493028991769387604101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26915981410644718366944269 10093493028991769387604101)
            ·
              refine ⟨1892529942935956760175769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10093493028991769387604101 1892529942935956760175769)
              ·
                refine ⟨1419397457201967570131827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1892529942935956760175769 1419397457201967570131827)
                ·
                  refine ⟨2129096185802951355197741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1419397457201967570131827 2129096185802951355197741)
                  ·
                    refine ⟨798411069676106758199153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2129096185802951355197741 798411069676106758199153)
                    ·
                      refine ⟨598808302257080068649365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 798411069676106758199153 598808302257080068649365)
                      ·
                        rfl

theorem cell23_1166175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_1166175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166175 prefixEnd_1166175 := by exact prefixLift 1166175
  have htrace : WordTrace (prefixWord ++ tailWord_1166175) baseStart_1166175 baseEnd_1166175 := by
    simpa [prefixWord, tailWord_1166175, baseEnd_1166175] using wordTrace_append hprefix tailTrace_1166175
  have hstable : (prefixWord ++ tailWord_1166175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166175).length < 2 ^ (prefixWord ++ tailWord_1166175).sum := by decide
  have hdescent : baseEnd_1166175 < baseStart_1166175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166188 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 3, 4, 2]
def baseStart_1166188 : Nat := 118140960795 + 1166188 * 2 ^ 59
def prefixEnd_1166188 : Nat := 4983230072969 + 3 ^ 40 * 1166188 * 2
def baseEnd_1166188 : Nat := 598814977505588517786805

theorem tailTrace_1166188 : CollatzResearch.WordTrace tailWord_1166188 prefixEnd_1166188 598814977505588517786805 := by
  unfold tailWord_1166188
  simp only [CollatzResearch.WordTrace]
  refine ⟨21267185349553759949425609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28356247132738346599234145 21267185349553759949425609)
  ·
    refine ⟨15950389012165319962069207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21267185349553759949425609 15950389012165319962069207)
    ·
      refine ⟨23925583518247979943103811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15950389012165319962069207 23925583518247979943103811)
      ·
        refine ⟨35888375277371969914655717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23925583518247979943103811 35888375277371969914655717)
        ·
          refine ⟨6729070364507244358997947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35888375277371969914655717 6729070364507244358997947)
          ·
            refine ⟨10093605546760866538496921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6729070364507244358997947 10093605546760866538496921)
            ·
              refine ⟨7570204160070649903872691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10093605546760866538496921 7570204160070649903872691)
              ·
                refine ⟨11355306240105974855809037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7570204160070649903872691 11355306240105974855809037)
                ·
                  refine ⟨4258239840039740570928389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11355306240105974855809037 4258239840039740570928389)
                  ·
                    refine ⟨798419970007451357049073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4258239840039740570928389 798419970007451357049073)
                    ·
                      refine ⟨598814977505588517786805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 798419970007451357049073 598814977505588517786805)
                      ·
                        rfl

theorem cell23_1166188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 4, 2].length) (baseStart_1166188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166188 prefixEnd_1166188 := by exact prefixLift 1166188
  have htrace : WordTrace (prefixWord ++ tailWord_1166188) baseStart_1166188 baseEnd_1166188 := by
    simpa [prefixWord, tailWord_1166188, baseEnd_1166188] using wordTrace_append hprefix tailTrace_1166188
  have hstable : (prefixWord ++ tailWord_1166188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166188).length < 2 ^ (prefixWord ++ tailWord_1166188).sum := by decide
  have hdescent : baseEnd_1166188 < baseStart_1166188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166205 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 4, 2, 2]
def baseStart_1166205 : Nat := 118140960795 + 1166205 * 2 ^ 59
def prefixEnd_1166205 : Nat := 4983230072969 + 3 ^ 40 * 1166205 * 2
def baseEnd_1166205 : Nat := 598823706676714951274227

theorem tailTrace_1166205 : CollatzResearch.WordTrace tailWord_1166205 prefixEnd_1166205 598823706676714951274227 := by
  unfold tailWord_1166205
  simp only [CollatzResearch.WordTrace]
  refine ⟨42534990740045931802220069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28356660493363954534813379 42534990740045931802220069)
  ·
    refine ⟨7975310763758612212916263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42534990740045931802220069 7975310763758612212916263)
    ·
      refine ⟨11962966145637918319374395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7975310763758612212916263 11962966145637918319374395)
      ·
        refine ⟨17944449218456877479061593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11962966145637918319374395 17944449218456877479061593)
        ·
          refine ⟨13458336913842658109296195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17944449218456877479061593 13458336913842658109296195)
          ·
            refine ⟨20187505370763987163944293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13458336913842658109296195 20187505370763987163944293)
            ·
              refine ⟨3785157257018247593239555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20187505370763987163944293 3785157257018247593239555)
              ·
                refine ⟨5677735885527371389859333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3785157257018247593239555 5677735885527371389859333)
                ·
                  refine ⟨1064575478536382135598625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5677735885527371389859333 1064575478536382135598625)
                  ·
                    refine ⟨798431608902286601698969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1064575478536382135598625 798431608902286601698969)
                    ·
                      refine ⟨598823706676714951274227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 798431608902286601698969 598823706676714951274227)
                      ·
                        rfl

theorem cell23_1166205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_1166205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166205 prefixEnd_1166205 := by exact prefixLift 1166205
  have htrace : WordTrace (prefixWord ++ tailWord_1166205) baseStart_1166205 baseEnd_1166205 := by
    simpa [prefixWord, tailWord_1166205, baseEnd_1166205] using wordTrace_append hprefix tailTrace_1166205
  have hstable : (prefixWord ++ tailWord_1166205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166205).length < 2 ^ (prefixWord ++ tailWord_1166205).sum := by decide
  have hdescent : baseEnd_1166205 < baseStart_1166205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166226 : List Nat := [3, 2, 3, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_1166226 : Nat := 118140960795 + 1166226 * 2 ^ 59
def prefixEnd_1166226 : Nat := 4983230072969 + 3 ^ 40 * 1166226 * 2
def baseEnd_1166226 : Nat := 598834489770459369111631

theorem tailTrace_1166226 : CollatzResearch.WordTrace tailWord_1166226 prefixEnd_1166226 598834489770459369111631 := by
  unfold tailWord_1166226
  simp only [CollatzResearch.WordTrace]
  refine ⟨10633939168242463097183633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28357171115313234925823021 10633939168242463097183633)
  ·
    refine ⟨7975454376181847322887725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10633939168242463097183633 7975454376181847322887725)
    ·
      refine ⟨2990795391068192746082897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7975454376181847322887725 2990795391068192746082897)
      ·
        refine ⟨2243096543301144559562173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2990795391068192746082897 2243096543301144559562173)
        ·
          refine ⟨841161203737929209835815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2243096543301144559562173 841161203737929209835815)
          ·
            refine ⟨1261741805606893814753723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841161203737929209835815 1261741805606893814753723)
            ·
              refine ⟨1892612708410340722130585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1261741805606893814753723 1892612708410340722130585)
              ·
                refine ⟨1419459531307755541597939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1892612708410340722130585 1419459531307755541597939)
                ·
                  refine ⟨2129189296961633312396909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1419459531307755541597939 2129189296961633312396909)
                  ·
                    refine ⟨798445986360612492148841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2129189296961633312396909 798445986360612492148841)
                    ·
                      refine ⟨598834489770459369111631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 798445986360612492148841 598834489770459369111631)
                      ·
                        rfl

theorem cell23_1166226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_1166226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166226 prefixEnd_1166226 := by exact prefixLift 1166226
  have htrace : WordTrace (prefixWord ++ tailWord_1166226) baseStart_1166226 baseEnd_1166226 := by
    simpa [prefixWord, tailWord_1166226, baseEnd_1166226] using wordTrace_append hprefix tailTrace_1166226
  have hstable : (prefixWord ++ tailWord_1166226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166226).length < 2 ^ (prefixWord ++ tailWord_1166226).sum := by decide
  have hdescent : baseEnd_1166226 < baseStart_1166226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166355 : List Nat := [1, 1, 1, 2, 1, 4, 1, 5, 2, 3, 2]
def baseStart_1166355 : Nat := 118140960795 + 1166355 * 2 ^ 59
def prefixEnd_1166355 : Nat := 4983230072969 + 3 ^ 40 * 1166355 * 2
def baseEnd_1166355 : Nat := 598900728774889364398537

theorem tailTrace_1166355 : CollatzResearch.WordTrace tailWord_1166355 prefixEnd_1166355 598900728774889364398537 := by
  unfold tailWord_1166355
  simp only [CollatzResearch.WordTrace]
  refine ⟨42540461689502507420180519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28360307793001671613453679 42540461689502507420180519)
  ·
    refine ⟨63810692534253761130270779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42540461689502507420180519 63810692534253761130270779)
    ·
      refine ⟨95716038801380641695406169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63810692534253761130270779 95716038801380641695406169)
      ·
        refine ⟨71787029101035481271554627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95716038801380641695406169 71787029101035481271554627)
        ·
          refine ⟨107680543651553221907331941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71787029101035481271554627 107680543651553221907331941)
          ·
            refine ⟨20190101934666229107624739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107680543651553221907331941 20190101934666229107624739)
            ·
              refine ⟨30285152901999343661437109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20190101934666229107624739 30285152901999343661437109)
              ·
                refine ⟨2839233084562438468259729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30285152901999343661437109 2839233084562438468259729)
                ·
                  refine ⟨2129424813421828851194797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2839233084562438468259729 2129424813421828851194797)
                  ·
                    refine ⟨798534305033185819198049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2129424813421828851194797 798534305033185819198049)
                    ·
                      refine ⟨598900728774889364398537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 798534305033185819198049 598900728774889364398537)
                      ·
                        rfl

theorem cell23_1166355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 3, 2].length) (baseStart_1166355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166355 prefixEnd_1166355 := by exact prefixLift 1166355
  have htrace : WordTrace (prefixWord ++ tailWord_1166355) baseStart_1166355 baseEnd_1166355 := by
    simpa [prefixWord, tailWord_1166355, baseEnd_1166355] using wordTrace_append hprefix tailTrace_1166355
  have hstable : (prefixWord ++ tailWord_1166355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166355).length < 2 ^ (prefixWord ++ tailWord_1166355).sum := by decide
  have hdescent : baseEnd_1166355 < baseStart_1166355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166372 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 4, 3, 2]
def baseStart_1166372 : Nat := 118140960795 + 1166372 * 2 ^ 59
def prefixEnd_1166372 : Nat := 4983230072969 + 3 ^ 40 * 1166372 * 2
def baseEnd_1166372 : Nat := 598909457946015797885959

theorem tailTrace_1166372 : CollatzResearch.WordTrace tailWord_1166372 prefixEnd_1166372 598909457946015797885959 := by
  unfold tailWord_1166372
  simp only [CollatzResearch.WordTrace]
  refine ⟨21270540865220459661774685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28360721153627279549032913 21270540865220459661774685)
  ·
    refine ⟨7976452824457672373165507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21270540865220459661774685 7976452824457672373165507)
    ·
      refine ⟨11964679236686508559748261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7976452824457672373165507 11964679236686508559748261)
      ·
        refine ⟨2243377356878720354952799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11964679236686508559748261 2243377356878720354952799)
        ·
          refine ⟨3365066035318080532429199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2243377356878720354952799 3365066035318080532429199)
          ·
            refine ⟨5047599052977120798643799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3365066035318080532429199 5047599052977120798643799)
            ·
              refine ⟨7571398579465681197965699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5047599052977120798643799 7571398579465681197965699)
              ·
                refine ⟨11357097869198521796948549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7571398579465681197965699 11357097869198521796948549)
                ·
                  refine ⟨2129455850474722836927853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11357097869198521796948549 2129455850474722836927853)
                  ·
                    refine ⟨798545943928021063847945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2129455850474722836927853 798545943928021063847945)
                    ·
                      refine ⟨598909457946015797885959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 798545943928021063847945 598909457946015797885959)
                      ·
                        rfl

theorem cell23_1166372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_1166372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166372 prefixEnd_1166372 := by exact prefixLift 1166372
  have htrace : WordTrace (prefixWord ++ tailWord_1166372) baseStart_1166372 baseEnd_1166372 := by
    simpa [prefixWord, tailWord_1166372, baseEnd_1166372] using wordTrace_append hprefix tailTrace_1166372
  have hstable : (prefixWord ++ tailWord_1166372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166372).length < 2 ^ (prefixWord ++ tailWord_1166372).sum := by decide
  have hdescent : baseEnd_1166372 < baseStart_1166372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166379 : List Nat := [1, 1, 1, 1, 2, 1, 9, 2, 1, 1, 3]
def baseStart_1166379 : Nat := 118140960795 + 1166379 * 2 ^ 59
def prefixEnd_1166379 : Nat := 4983230072969 + 3 ^ 40 * 1166379 * 2
def baseEnd_1166379 : Nat := 598913052310597270498427

theorem tailTrace_1166379 : CollatzResearch.WordTrace tailWord_1166379 prefixEnd_1166379 598913052310597270498427 := by
  unfold tailWord_1166379
  simp only [CollatzResearch.WordTrace]
  refine ⟨42541337041415559519054191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28360891360943706346036127 42541337041415559519054191)
  ·
    refine ⟨63812005562123339278581287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42541337041415559519054191 63812005562123339278581287)
    ·
      refine ⟨95718008343185008917871931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63812005562123339278581287 95718008343185008917871931)
      ·
        refine ⟨143577012514777513376807897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95718008343185008917871931 143577012514777513376807897)
        ·
          refine ⟨107682759386083135032605923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143577012514777513376807897 107682759386083135032605923)
          ·
            refine ⟨161524139079124702548908885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107682759386083135032605923 161524139079124702548908885)
            ·
              refine ⟨946430502416746303997513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 161524139079124702548908885 946430502416746303997513)
              ·
                refine ⟨709822876812559727998135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 946430502416746303997513 709822876812559727998135)
                ·
                  refine ⟨1064734315218839591997203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 709822876812559727998135 1064734315218839591997203)
                  ·
                    refine ⟨1597101472828259387995805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1064734315218839591997203 1597101472828259387995805)
                    ·
                      refine ⟨598913052310597270498427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1597101472828259387995805 598913052310597270498427)
                      ·
                        rfl

theorem cell23_1166379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 1, 1, 3].length) (baseStart_1166379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166379 prefixEnd_1166379 := by exact prefixLift 1166379
  have htrace : WordTrace (prefixWord ++ tailWord_1166379) baseStart_1166379 baseEnd_1166379 := by
    simpa [prefixWord, tailWord_1166379, baseEnd_1166379] using wordTrace_append hprefix tailTrace_1166379
  have hstable : (prefixWord ++ tailWord_1166379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166379).length < 2 ^ (prefixWord ++ tailWord_1166379).sum := by decide
  have hdescent : baseEnd_1166379 < baseStart_1166379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166406 : List Nat := [6, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_1166406 : Nat := 118140960795 + 1166406 * 2 ^ 59
def prefixEnd_1166406 : Nat := 4983230072969 + 3 ^ 40 * 1166406 * 2
def baseEnd_1166406 : Nat := 598926916288268664860803

theorem tailTrace_1166406 : CollatzResearch.WordTrace tailWord_1166406 prefixEnd_1166406 598926916288268664860803 := by
  unfold tailWord_1166406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1329447556634929472821471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28361547874878495420191381 1329447556634929472821471)
  ·
    refine ⟨1994171334952394209232207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1329447556634929472821471 1994171334952394209232207)
    ·
      refine ⟨2991257002428591313848311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1994171334952394209232207 2991257002428591313848311)
      ·
        refine ⟨4486885503642886970772467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2991257002428591313848311 4486885503642886970772467)
        ·
          refine ⟨6730328255464330456158701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4486885503642886970772467 6730328255464330456158701)
          ·
            refine ⟨2523873095799123921059513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6730328255464330456158701 2523873095799123921059513)
            ·
              refine ⟨1892904821849342940794635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2523873095799123921059513 1892904821849342940794635)
              ·
                refine ⟨2839357232774014411191953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1892904821849342940794635 2839357232774014411191953)
                ·
                  refine ⟨2129517924580510808393965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2839357232774014411191953 2129517924580510808393965)
                  ·
                    refine ⟨798569221717691553147737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2129517924580510808393965 798569221717691553147737)
                    ·
                      refine ⟨598926916288268664860803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 798569221717691553147737 598926916288268664860803)
                      ·
                        rfl

theorem cell23_1166406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_1166406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166406 prefixEnd_1166406 := by exact prefixLift 1166406
  have htrace : WordTrace (prefixWord ++ tailWord_1166406) baseStart_1166406 baseEnd_1166406 := by
    simpa [prefixWord, tailWord_1166406, baseEnd_1166406] using wordTrace_append hprefix tailTrace_1166406
  have hstable : (prefixWord ++ tailWord_1166406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166406).length < 2 ^ (prefixWord ++ tailWord_1166406).sum := by decide
  have hdescent : baseEnd_1166406 < baseStart_1166406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166430 : List Nat := [4, 4, 1, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_1166430 : Nat := 118140960795 + 1166430 * 2 ^ 59
def prefixEnd_1166430 : Nat := 4983230072969 + 3 ^ 40 * 1166430 * 2
def baseEnd_1166430 : Nat := 598939239823976570960693

theorem tailTrace_1166430 : CollatzResearch.WordTrace tailWord_1166430 prefixEnd_1166430 598939239823976570960693 := by
  unfold tailWord_1166430
  simp only [CollatzResearch.WordTrace]
  refine ⟨5317899645528849403645093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28362131442820530152773829 5317899645528849403645093)
  ·
    refine ⟨997106183536659263183455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5317899645528849403645093 997106183536659263183455)
    ·
      refine ⟨1495659275304988894775183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 997106183536659263183455 1495659275304988894775183)
      ·
        refine ⟨2243488912957483342162775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1495659275304988894775183 2243488912957483342162775)
        ·
          refine ⟨3365233369436225013244163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2243488912957483342162775 3365233369436225013244163)
          ·
            refine ⟨5047850054154337519866245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3365233369436225013244163 5047850054154337519866245)
            ·
              refine ⟨946471885153938284974921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5047850054154337519866245 946471885153938284974921)
              ·
                refine ⟨709853913865453713731191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 946471885153938284974921 709853913865453713731191)
                ·
                  refine ⟨1064780870798180570596787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 709853913865453713731191 1064780870798180570596787)
                  ·
                    refine ⟨1597171306197270855895181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1064780870798180570596787 1597171306197270855895181)
                    ·
                      refine ⟨598939239823976570960693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1597171306197270855895181 598939239823976570960693)
                      ·
                        rfl

theorem cell23_1166430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_1166430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166430 prefixEnd_1166430 := by exact prefixLift 1166430
  have htrace : WordTrace (prefixWord ++ tailWord_1166430) baseStart_1166430 baseEnd_1166430 := by
    simpa [prefixWord, tailWord_1166430, baseEnd_1166430] using wordTrace_append hprefix tailTrace_1166430
  have hstable : (prefixWord ++ tailWord_1166430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166430).length < 2 ^ (prefixWord ++ tailWord_1166430).sum := by decide
  have hdescent : baseEnd_1166430 < baseStart_1166430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166525 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 1, 5, 3]
def baseStart_1166525 : Nat := 118140960795 + 1166525 * 2 ^ 59
def prefixEnd_1166525 : Nat := 4983230072969 + 3 ^ 40 * 1166525 * 2
def baseEnd_1166525 : Nat := 598988020486153699272755

theorem tailTrace_1166525 : CollatzResearch.WordTrace tailWord_1166525 prefixEnd_1166525 598988020486153699272755 := by
  unfold tailWord_1166525
  simp only [CollatzResearch.WordTrace]
  refine ⟨42546662098886626453869029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28364441399257750969246019 42546662098886626453869029)
  ·
    refine ⟨7977499143541242460100443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42546662098886626453869029 7977499143541242460100443)
    ·
      refine ⟨11966248715311863690150665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7977499143541242460100443 11966248715311863690150665)
      ·
        refine ⟨8974686536483897767612999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11966248715311863690150665 8974686536483897767612999)
        ·
          refine ⟨13462029804725846651419499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8974686536483897767612999 13462029804725846651419499)
          ·
            refine ⟨20193044707088769977129249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13462029804725846651419499 20193044707088769977129249)
            ·
              refine ⟨15144783530316577482846937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20193044707088769977129249 15144783530316577482846937)
              ·
                refine ⟨11358587647737433112135203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15144783530316577482846937 11358587647737433112135203)
                ·
                  refine ⟨17037881471606149668202805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11358587647737433112135203 17037881471606149668202805)
                  ·
                    refine ⟨1597301387963076531394013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17037881471606149668202805 1597301387963076531394013)
                    ·
                      refine ⟨598988020486153699272755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1597301387963076531394013 598988020486153699272755)
                      ·
                        rfl

theorem cell23_1166525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_1166525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166525 prefixEnd_1166525 := by exact prefixLift 1166525
  have htrace : WordTrace (prefixWord ++ tailWord_1166525) baseStart_1166525 baseEnd_1166525 := by
    simpa [prefixWord, tailWord_1166525, baseEnd_1166525] using wordTrace_append hprefix tailTrace_1166525
  have hstable : (prefixWord ++ tailWord_1166525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166525).length < 2 ^ (prefixWord ++ tailWord_1166525).sum := by decide
  have hdescent : baseEnd_1166525 < baseStart_1166525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166609 : List Nat := [1, 2, 2, 1, 1, 4, 3, 4, 1, 4]
def baseStart_1166609 : Nat := 118140960795 + 1166609 * 2 ^ 59
def prefixEnd_1166609 : Nat := 4983230072969 + 3 ^ 40 * 1166609 * 2
def baseEnd_1166609 : Nat := 199677050953710456874123

theorem tailTrace_1166609 : CollatzResearch.WordTrace tailWord_1166609 prefixEnd_1166609 199677050953710456874123 := by
  unfold tailWord_1166609
  simp only [CollatzResearch.WordTrace]
  refine ⟨42549725830582308799926881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28366483887054872533284587 42549725830582308799926881)
  ·
    refine ⟨31912294372936731599945161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42549725830582308799926881 31912294372936731599945161)
    ·
      refine ⟨23934220779702548699958871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31912294372936731599945161 23934220779702548699958871)
      ·
        refine ⟨35901331169553823049938307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23934220779702548699958871 35901331169553823049938307)
        ·
          refine ⟨53851996754330734574907461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35901331169553823049938307 53851996754330734574907461)
          ·
            refine ⟨10097249391437012732795149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53851996754330734574907461 10097249391437012732795149)
            ·
              refine ⟨3786468521788879774798181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10097249391437012732795149 3786468521788879774798181)
              ·
                refine ⟨709962847835414957774659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3786468521788879774798181 709962847835414957774659)
                ·
                  refine ⟨1064944271753122436661989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 709962847835414957774659 1064944271753122436661989)
                  ·
                    refine ⟨199677050953710456874123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1064944271753122436661989 199677050953710456874123)
                    ·
                      rfl

theorem cell23_1166609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 1, 4].length) (baseStart_1166609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166609 prefixEnd_1166609 := by exact prefixLift 1166609
  have htrace : WordTrace (prefixWord ++ tailWord_1166609) baseStart_1166609 baseEnd_1166609 := by
    simpa [prefixWord, tailWord_1166609, baseEnd_1166609] using wordTrace_append hprefix tailTrace_1166609
  have hstable : (prefixWord ++ tailWord_1166609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166609).length < 2 ^ (prefixWord ++ tailWord_1166609).sum := by decide
  have hdescent : baseEnd_1166609 < baseStart_1166609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166665 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 3, 6]
def baseStart_1166665 : Nat := 118140960795 + 1166665 * 2 ^ 59
def prefixEnd_1166665 : Nat := 4983230072969 + 3 ^ 40 * 1166665 * 2
def baseEnd_1166665 : Nat := 199686635925927717174037

theorem tailTrace_1166665 : CollatzResearch.WordTrace tailWord_1166665 prefixEnd_1166665 199686635925927717174037 := by
  unfold tailWord_1166665
  simp only [CollatzResearch.WordTrace]
  refine ⟨42551768318379430363965449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28367845545586286909310299 42551768318379430363965449)
  ·
    refine ⟨31913826238784572772974087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42551768318379430363965449 31913826238784572772974087)
    ·
      refine ⟨47870739358176859159461131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31913826238784572772974087 47870739358176859159461131)
      ·
        refine ⟨71806109037265288739191697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47870739358176859159461131 71806109037265288739191697)
        ·
          refine ⟨53854581777948966554393773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71806109037265288739191697 53854581777948966554393773)
          ·
            refine ⟨20195468166730862457897665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53854581777948966554393773 20195468166730862457897665)
            ·
              refine ⟨15146601125048146843423249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20195468166730862457897665 15146601125048146843423249)
              ·
                refine ⟨11359950843786110132567437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15146601125048146843423249 11359950843786110132567437)
                ·
                  refine ⟨4259981566419791299712789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11359950843786110132567437 4259981566419791299712789)
                  ·
                    refine ⟨199686635925927717174037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4259981566419791299712789 199686635925927717174037)
                    ·
                      rfl

theorem cell23_1166665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 6].length) (baseStart_1166665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166665 prefixEnd_1166665 := by exact prefixLift 1166665
  have htrace : WordTrace (prefixWord ++ tailWord_1166665) baseStart_1166665 baseEnd_1166665 := by
    simpa [prefixWord, tailWord_1166665, baseEnd_1166665] using wordTrace_append hprefix tailTrace_1166665
  have hstable : (prefixWord ++ tailWord_1166665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166665).length < 2 ^ (prefixWord ++ tailWord_1166665).sum := by decide
  have hdescent : baseEnd_1166665 < baseStart_1166665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166682 : List Nat := [3, 1, 1, 2, 1, 2, 5, 1, 1, 6]
def baseStart_1166682 : Nat := 118140960795 + 1166682 * 2 ^ 59
def prefixEnd_1166682 : Nat := 4983230072969 + 3 ^ 40 * 1166682 * 2
def baseEnd_1166682 : Nat := 199689545649636528336511

theorem tailTrace_1166682 : CollatzResearch.WordTrace tailWord_1166682 prefixEnd_1166682 199689545649636528336511 := by
  unfold tailWord_1166682
  simp only [CollatzResearch.WordTrace]
  refine ⟨10638097089829460566833575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28368258906211894844889533 10638097089829460566833575)
  ·
    refine ⟨15957145634744190850250363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10638097089829460566833575 15957145634744190850250363)
    ·
      refine ⟨23935718452116286275375545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15957145634744190850250363 23935718452116286275375545)
      ·
        refine ⟨17951788839087214706531659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23935718452116286275375545 17951788839087214706531659)
        ·
          refine ⟨26927683258630822059797489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17951788839087214706531659 26927683258630822059797489)
          ·
            refine ⟨20195762443973116544848117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26927683258630822059797489 20195762443973116544848117)
            ·
              refine ⟨1893352729122479676079511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20195762443973116544848117 1893352729122479676079511)
              ·
                refine ⟨2840029093683719514119267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1893352729122479676079511 2840029093683719514119267)
                ·
                  refine ⟨4260043640525579271178901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2840029093683719514119267 4260043640525579271178901)
                  ·
                    refine ⟨199689545649636528336511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4260043640525579271178901 199689545649636528336511)
                    ·
                      rfl

theorem cell23_1166682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_1166682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166682 prefixEnd_1166682 := by exact prefixLift 1166682
  have htrace : WordTrace (prefixWord ++ tailWord_1166682) baseStart_1166682 baseEnd_1166682 := by
    simpa [prefixWord, tailWord_1166682, baseEnd_1166682] using wordTrace_append hprefix tailTrace_1166682
  have hstable : (prefixWord ++ tailWord_1166682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166682).length < 2 ^ (prefixWord ++ tailWord_1166682).sum := by decide
  have hdescent : baseEnd_1166682 < baseStart_1166682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166723 : List Nat := [1, 1, 1, 3, 5, 3, 1, 1, 3, 2, 2]
def baseStart_1166723 : Nat := 118140960795 + 1166723 * 2 ^ 59
def prefixEnd_1166723 : Nat := 4983230072969 + 3 ^ 40 * 1166723 * 2
def baseEnd_1166723 : Nat := 599089689655743924596845

theorem tailTrace_1166723 : CollatzResearch.WordTrace tailWord_1166723 prefixEnd_1166723 599089689655743924596845 := by
  unfold tailWord_1166723
  simp only [CollatzResearch.WordTrace]
  refine ⟨42553883752169306269576823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28369255834779537513051215 42553883752169306269576823)
  ·
    refine ⟨63830825628253959404365235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42553883752169306269576823 63830825628253959404365235)
    ·
      refine ⟨95746238442380939106547853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63830825628253959404365235 95746238442380939106547853)
      ·
        refine ⟨35904839415892852164955445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95746238442380939106547853 35904839415892852164955445)
        ·
          refine ⟨3366078695239954890464573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35904839415892852164955445 3366078695239954890464573)
          ·
            refine ⟨1262279510714983083924215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3366078695239954890464573 1262279510714983083924215)
            ·
              refine ⟨1893419266072474625886323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1262279510714983083924215 1893419266072474625886323)
              ·
                refine ⟨2840128899108711938829485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1893419266072474625886323 2840128899108711938829485)
                ·
                  refine ⟨1065048337165766977061057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2840128899108711938829485 1065048337165766977061057)
                  ·
                    refine ⟨798786252874325232795793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1065048337165766977061057 798786252874325232795793)
                    ·
                      refine ⟨599089689655743924596845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 798786252874325232795793 599089689655743924596845)
                      ·
                        rfl

theorem cell23_1166723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 2, 2].length) (baseStart_1166723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166723 prefixEnd_1166723 := by exact prefixLift 1166723
  have htrace : WordTrace (prefixWord ++ tailWord_1166723) baseStart_1166723 baseEnd_1166723 := by
    simpa [prefixWord, tailWord_1166723, baseEnd_1166723] using wordTrace_append hprefix tailTrace_1166723
  have hstable : (prefixWord ++ tailWord_1166723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166723).length < 2 ^ (prefixWord ++ tailWord_1166723).sum := by decide
  have hdescent : baseEnd_1166723 < baseStart_1166723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166760 : List Nat := [2, 1, 6, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_1166760 : Nat := 118140960795 + 1166760 * 2 ^ 59
def prefixEnd_1166760 : Nat := 4983230072969 + 3 ^ 40 * 1166760 * 2
def baseEnd_1166760 : Nat := 599108688439960279834175

theorem tailTrace_1166760 : CollatzResearch.WordTrace tailWord_1166760 prefixEnd_1166760 599108688439960279834175 := by
  unfold tailWord_1166760
  simp only [CollatzResearch.WordTrace]
  refine ⟨21277616626517630794336867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28370155502023507725782489 21277616626517630794336867)
  ·
    refine ⟨31916424939776446191505301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21277616626517630794336867 31916424939776446191505301)
    ·
      refine ⟨1496082419052020915226811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31916424939776446191505301 1496082419052020915226811)
      ·
        refine ⟨2244123628578031372840217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1496082419052020915226811 2244123628578031372840217)
        ·
          refine ⟨1683092721433523529630163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2244123628578031372840217 1683092721433523529630163)
          ·
            refine ⟨2524639082150285294445245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1683092721433523529630163 2524639082150285294445245)
            ·
              refine ⟨946739655806356985416967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2524639082150285294445245 946739655806356985416967)
              ·
                refine ⟨1420109483709535478125451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 946739655806356985416967 1420109483709535478125451)
                ·
                  refine ⟨2130164225564303217188177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1420109483709535478125451 2130164225564303217188177)
                  ·
                    refine ⟨1597623169173227412891133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2130164225564303217188177 1597623169173227412891133)
                    ·
                      refine ⟨599108688439960279834175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1597623169173227412891133 599108688439960279834175)
                      ·
                        rfl

theorem cell23_1166760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_1166760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166760 prefixEnd_1166760 := by exact prefixLift 1166760
  have htrace : WordTrace (prefixWord ++ tailWord_1166760) baseStart_1166760 baseEnd_1166760 := by
    simpa [prefixWord, tailWord_1166760, baseEnd_1166760] using wordTrace_append hprefix tailTrace_1166760
  have hstable : (prefixWord ++ tailWord_1166760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166760).length < 2 ^ (prefixWord ++ tailWord_1166760).sum := by decide
  have hdescent : baseEnd_1166760 < baseStart_1166760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166773 : List Nat := [1, 3, 3, 2, 2, 2, 2, 2, 2, 1, 3]
def baseStart_1166773 : Nat := 118140960795 + 1166773 * 2 ^ 59
def prefixEnd_1166773 : Nat := 4983230072969 + 3 ^ 40 * 1166773 * 2
def baseEnd_1166773 : Nat := 599115363688468728971615

theorem tailTrace_1166773 : CollatzResearch.WordTrace tailWord_1166773 prefixEnd_1166773 599115363688468728971615 := by
  unfold tailWord_1166773
  simp only [CollatzResearch.WordTrace]
  refine ⟨42555707401988164808896973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28370471601325443205931315 42555707401988164808896973)
  ·
    refine ⟨15958390275745561803336365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42555707401988164808896973 15958390275745561803336365)
    ·
      refine ⟨5984396353404585676251137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15958390275745561803336365 5984396353404585676251137)
      ·
        refine ⟨4488297265053439257188353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5984396353404585676251137 4488297265053439257188353)
        ·
          refine ⟨3366222948790079442891265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4488297265053439257188353 3366222948790079442891265)
          ·
            refine ⟨2524667211592559582168449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3366222948790079442891265 2524667211592559582168449)
            ·
              refine ⟨1893500408694419686626337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2524667211592559582168449 1893500408694419686626337)
              ·
                refine ⟨1420125306520814764969753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1893500408694419686626337 1420125306520814764969753)
                ·
                  refine ⟨1065093979890611073727315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1420125306520814764969753 1065093979890611073727315)
                  ·
                    refine ⟨1597640969835916610590973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1065093979890611073727315 1597640969835916610590973)
                    ·
                      refine ⟨599115363688468728971615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1597640969835916610590973 599115363688468728971615)
                      ·
                        rfl

theorem cell23_1166773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_1166773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166773 prefixEnd_1166773 := by exact prefixLift 1166773
  have htrace : WordTrace (prefixWord ++ tailWord_1166773) baseStart_1166773 baseEnd_1166773 := by
    simpa [prefixWord, tailWord_1166773, baseEnd_1166773] using wordTrace_append hprefix tailTrace_1166773
  have hstable : (prefixWord ++ tailWord_1166773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166773).length < 2 ^ (prefixWord ++ tailWord_1166773).sum := by decide
  have hdescent : baseEnd_1166773 < baseStart_1166773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166796 : List Nat := [2, 2, 1, 4, 2, 1, 1, 3, 1, 4, 2]
def baseStart_1166796 : Nat := 118140960795 + 1166796 * 2 ^ 59
def prefixEnd_1166796 : Nat := 4983230072969 + 3 ^ 40 * 1166796 * 2
def baseEnd_1166796 : Nat := 599127173743522138984009

theorem tailTrace_1166796 : CollatzResearch.WordTrace tailWord_1166796 prefixEnd_1166796 599127173743522138984009 := by
  unfold tailWord_1166796
  simp only [CollatzResearch.WordTrace]
  refine ⟨21278273140452419868492121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28371030853936559824656161 21278273140452419868492121)
  ·
    refine ⟨15958704855339314901369091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21278273140452419868492121 15958704855339314901369091)
    ·
      refine ⟨23938057283008972352053637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15958704855339314901369091 23938057283008972352053637)
      ·
        refine ⟨4488385740564182316010057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23938057283008972352053637 4488385740564182316010057)
        ·
          refine ⟨3366289305423136737007543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4488385740564182316010057 3366289305423136737007543)
          ·
            refine ⟨5049433958134705105511315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3366289305423136737007543 5049433958134705105511315)
            ·
              refine ⟨7574150937202057658266973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5049433958134705105511315 7574150937202057658266973)
              ·
                refine ⟨2840306601450771621850115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7574150937202057658266973 2840306601450771621850115)
                ·
                  refine ⟨4260459902176157432775173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2840306601450771621850115 4260459902176157432775173)
                  ·
                    refine ⟨798836231658029518645345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4260459902176157432775173 798836231658029518645345)
                    ·
                      refine ⟨599127173743522138984009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 798836231658029518645345 599127173743522138984009)
                      ·
                        rfl

theorem cell23_1166796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_1166796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166796 prefixEnd_1166796 := by exact prefixLift 1166796
  have htrace : WordTrace (prefixWord ++ tailWord_1166796) baseStart_1166796 baseEnd_1166796 := by
    simpa [prefixWord, tailWord_1166796, baseEnd_1166796] using wordTrace_append hprefix tailTrace_1166796
  have hstable : (prefixWord ++ tailWord_1166796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166796).length < 2 ^ (prefixWord ++ tailWord_1166796).sum := by decide
  have hdescent : baseEnd_1166796 < baseStart_1166796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166839 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 2, 5, 2]
def baseStart_1166839 : Nat := 118140960795 + 1166839 * 2 ^ 59
def prefixEnd_1166839 : Nat := 4983230072969 + 3 ^ 40 * 1166839 * 2
def baseEnd_1166839 : Nat := 599149253411665470746311

theorem tailTrace_1166839 : CollatzResearch.WordTrace tailWord_1166839 prefixEnd_1166839 599149253411665470746311 := by
  unfold tailWord_1166839
  simp only [CollatzResearch.WordTrace]
  refine ⟨42558114619749058080799571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28372076413166038720533047 42558114619749058080799571)
  ·
    refine ⟨63837171929623587121199357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42558114619749058080799571 63837171929623587121199357)
    ·
      refine ⟨23938939473608845170449759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63837171929623587121199357 23938939473608845170449759)
      ·
        refine ⟨35908409210413267755674639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23938939473608845170449759 35908409210413267755674639)
        ·
          refine ⟨53862613815619901633511959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35908409210413267755674639 53862613815619901633511959)
          ·
            refine ⟨80793920723429852450267939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53862613815619901633511959 80793920723429852450267939)
            ·
              refine ⟨121190881085144778675401909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80793920723429852450267939 121190881085144778675401909)
              ·
                refine ⟨11361645101732323000818929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121190881085144778675401909 11361645101732323000818929)
                ·
                  refine ⟨8521233826299242250614197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11361645101732323000818929 8521233826299242250614197)
                  ·
                    refine ⟨798865671215553960995081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8521233826299242250614197 798865671215553960995081)
                    ·
                      refine ⟨599149253411665470746311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 798865671215553960995081 599149253411665470746311)
                      ·
                        rfl

theorem cell23_1166839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 5, 2].length) (baseStart_1166839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166839 prefixEnd_1166839 := by exact prefixLift 1166839
  have htrace : WordTrace (prefixWord ++ tailWord_1166839) baseStart_1166839 baseEnd_1166839 := by
    simpa [prefixWord, tailWord_1166839, baseEnd_1166839] using wordTrace_append hprefix tailTrace_1166839
  have hstable : (prefixWord ++ tailWord_1166839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166839).length < 2 ^ (prefixWord ++ tailWord_1166839).sum := by decide
  have hdescent : baseEnd_1166839 < baseStart_1166839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166842 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7]
def baseStart_1166842 : Nat := 118140960795 + 1166842 * 2 ^ 59
def prefixEnd_1166842 : Nat := 4983230072969 + 3 ^ 40 * 1166842 * 2
def baseEnd_1166842 : Nat := 599150793853628959008797

theorem tailTrace_1166842 : CollatzResearch.WordTrace tailWord_1166842 prefixEnd_1166842 599150793853628959008797 := by
  unfold tailWord_1166842
  simp only [CollatzResearch.WordTrace]
  refine ⟨10639556009684547398289695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28372149359158793062105853 10639556009684547398289695)
  ·
    refine ⟨15959334014526821097434543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10639556009684547398289695 15959334014526821097434543)
    ·
      refine ⟨23939001021790231646151815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15959334014526821097434543 23939001021790231646151815)
      ·
        refine ⟨35908501532685347469227723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23939001021790231646151815 35908501532685347469227723)
        ·
          refine ⟨53862752299028021203841585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35908501532685347469227723 53862752299028021203841585)
          ·
            refine ⟨40397064224271015902881189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53862752299028021203841585 40397064224271015902881189)
            ·
              refine ⟨7574449542050815481790223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40397064224271015902881189 7574449542050815481790223)
              ·
                refine ⟨11361674313076223222685335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7574449542050815481790223 11361674313076223222685335)
                ·
                  refine ⟨17042511469614334834028003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11361674313076223222685335 17042511469614334834028003)
                  ·
                    refine ⟨25563767204421502251042005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17042511469614334834028003 25563767204421502251042005)
                    ·
                      refine ⟨599150793853628959008797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25563767204421502251042005 599150793853628959008797)
                      ·
                        rfl

theorem cell23_1166842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_1166842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166842 prefixEnd_1166842 := by exact prefixLift 1166842
  have htrace : WordTrace (prefixWord ++ tailWord_1166842) baseStart_1166842 baseEnd_1166842 := by
    simpa [prefixWord, tailWord_1166842, baseEnd_1166842] using wordTrace_append hprefix tailTrace_1166842
  have hstable : (prefixWord ++ tailWord_1166842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166842).length < 2 ^ (prefixWord ++ tailWord_1166842).sum := by decide
  have hdescent : baseEnd_1166842 < baseStart_1166842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166869 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_1166869 : Nat := 118140960795 + 1166869 * 2 ^ 59
def prefixEnd_1166869 : Nat := 4983230072969 + 3 ^ 40 * 1166869 * 2
def baseEnd_1166869 : Nat := 599164657831300353371173

theorem tailTrace_1166869 : CollatzResearch.WordTrace tailWord_1166869 prefixEnd_1166869 599164657831300353371173 := by
  unfold tailWord_1166869
  simp only [CollatzResearch.WordTrace]
  refine ⟨42559208809640373204391661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28372805873093582136261107 42559208809640373204391661)
  ·
    refine ⟨15959703303615139951646873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42559208809640373204391661 15959703303615139951646873)
    ·
      refine ⟨11969777477711354963735155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15959703303615139951646873 11969777477711354963735155)
      ·
        refine ⟨17954666216567032445602733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11969777477711354963735155 17954666216567032445602733)
        ·
          refine ⟨6732999831212637167101025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17954666216567032445602733 6732999831212637167101025)
          ·
            refine ⟨5049749873409477875325769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6732999831212637167101025 5049749873409477875325769)
            ·
              refine ⟨3787312405057108406494327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5049749873409477875325769 3787312405057108406494327)
              ·
                refine ⟨5680968607585662609741491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3787312405057108406494327 5680968607585662609741491)
                ·
                  refine ⟨8521452911378493914612237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5680968607585662609741491 8521452911378493914612237)
                  ·
                    refine ⟨3195544841766935217979589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8521452911378493914612237 3195544841766935217979589)
                    ·
                      refine ⟨599164657831300353371173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3195544841766935217979589 599164657831300353371173)
                      ·
                        rfl

theorem cell23_1166869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_1166869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166869 prefixEnd_1166869 := by exact prefixLift 1166869
  have htrace : WordTrace (prefixWord ++ tailWord_1166869) baseStart_1166869 baseEnd_1166869 := by
    simpa [prefixWord, tailWord_1166869, baseEnd_1166869] using wordTrace_append hprefix tailTrace_1166869
  have hstable : (prefixWord ++ tailWord_1166869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166869).length < 2 ^ (prefixWord ++ tailWord_1166869).sum := by decide
  have hdescent : baseEnd_1166869 < baseStart_1166869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166879 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 5, 4]
def baseStart_1166879 : Nat := 118140960795 + 1166879 * 2 ^ 59
def prefixEnd_1166879 : Nat := 4983230072969 + 3 ^ 40 * 1166879 * 2
def baseEnd_1166879 : Nat := 199723264212615104748709

theorem tailTrace_1166879 : CollatzResearch.WordTrace tailWord_1166879 prefixEnd_1166879 199723264212615104748709 := by
  unfold tailWord_1166879
  simp only [CollatzResearch.WordTrace]
  refine ⟨42559573539604144912255691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28373049026402763274837127 42559573539604144912255691)
  ·
    refine ⟨63839360309406217368383537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42559573539604144912255691 63839360309406217368383537)
    ·
      refine ⟨47879520232054663026287653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63839360309406217368383537 47879520232054663026287653)
      ·
        refine ⟨8977410043510249317428935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47879520232054663026287653 8977410043510249317428935)
        ·
          refine ⟨13466115065265373976143403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8977410043510249317428935 13466115065265373976143403)
          ·
            refine ⟨20199172597898060964215105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13466115065265373976143403 20199172597898060964215105)
            ·
              refine ⟨15149379448423545723161329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20199172597898060964215105 15149379448423545723161329)
              ·
                refine ⟨11362034586317659292370997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15149379448423545723161329 11362034586317659292370997)
                ·
                  refine ⟨1065190742467280558659781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11362034586317659292370997 1065190742467280558659781)
                  ·
                    refine ⟨199723264212615104748709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1065190742467280558659781 199723264212615104748709)
                    ·
                      rfl

theorem cell23_1166879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 4].length) (baseStart_1166879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166879 prefixEnd_1166879 := by exact prefixLift 1166879
  have htrace : WordTrace (prefixWord ++ tailWord_1166879) baseStart_1166879 baseEnd_1166879 := by
    simpa [prefixWord, tailWord_1166879, baseEnd_1166879] using wordTrace_append hprefix tailTrace_1166879
  have hstable : (prefixWord ++ tailWord_1166879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166879).length < 2 ^ (prefixWord ++ tailWord_1166879).sum := by decide
  have hdescent : baseEnd_1166879 < baseStart_1166879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166976 : List Nat := [2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 4]
def baseStart_1166976 : Nat := 118140960795 + 1166976 * 2 ^ 59
def prefixEnd_1166976 : Nat := 4983230072969 + 3 ^ 40 * 1166976 * 2
def baseEnd_1166976 : Nat := 599219600261331434733181

theorem tailTrace_1166976 : CollatzResearch.WordTrace tailWord_1166976 prefixEnd_1166976 599219600261331434733181 := by
  unfold tailWord_1166976
  simp only [CollatzResearch.WordTrace]
  refine ⟨21281555710126365239268391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28375407613501820319024521 21281555710126365239268391)
  ·
    refine ⟨31922333565189547858902587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21281555710126365239268391 31922333565189547858902587)
    ·
      refine ⟨47883500347784321788353881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31922333565189547858902587 47883500347784321788353881)
      ·
        refine ⟨35912625260838241341265411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47883500347784321788353881 35912625260838241341265411)
        ·
          refine ⟨53868937891257362011898117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35912625260838241341265411 53868937891257362011898117)
          ·
            refine ⟨10100425854610755377230897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53868937891257362011898117 10100425854610755377230897)
            ·
              refine ⟨7575319390958066532923173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10100425854610755377230897 7575319390958066532923173)
              ·
                refine ⟨1420372385804637474923095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7575319390958066532923173 1420372385804637474923095)
                ·
                  refine ⟨2130558578706956212384643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1420372385804637474923095 2130558578706956212384643)
                  ·
                    refine ⟨3195837868060434318576965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2130558578706956212384643 3195837868060434318576965)
                    ·
                      refine ⟨599219600261331434733181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3195837868060434318576965 599219600261331434733181)
                      ·
                        rfl

theorem cell23_1166976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 4].length) (baseStart_1166976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166976 prefixEnd_1166976 := by exact prefixLift 1166976
  have htrace : WordTrace (prefixWord ++ tailWord_1166976) baseStart_1166976 baseEnd_1166976 := by
    simpa [prefixWord, tailWord_1166976, baseEnd_1166976] using wordTrace_append hprefix tailTrace_1166976
  have hstable : (prefixWord ++ tailWord_1166976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166976).length < 2 ^ (prefixWord ++ tailWord_1166976).sum := by decide
  have hdescent : baseEnd_1166976 < baseStart_1166976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166986 : List Nat := [3, 1, 2, 3, 2, 1, 2, 2, 1, 6]
def baseStart_1166986 : Nat := 118140960795 + 1166986 * 2 ^ 59
def prefixEnd_1166986 : Nat := 4983230072969 + 3 ^ 40 * 1166986 * 2
def baseEnd_1166986 : Nat := 199741578355958798536045

theorem tailTrace_1166986 : CollatzResearch.WordTrace tailWord_1166986 prefixEnd_1166986 199741578355958798536045 := by
  unfold tailWord_1166986
  simp only [CollatzResearch.WordTrace]
  refine ⟨10640869037554125546600203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28375650766811001457600541 10640869037554125546600203)
  ·
    refine ⟨15961303556331188319900305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10640869037554125546600203 15961303556331188319900305)
    ·
      refine ⟨11970977667248391239925229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15961303556331188319900305 11970977667248391239925229)
      ·
        refine ⟨4489116625218146714971961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11970977667248391239925229 4489116625218146714971961)
        ·
          refine ⟨3366837468913610036228971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4489116625218146714971961 3366837468913610036228971)
          ·
            refine ⟨5050256203370415054343457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3366837468913610036228971 5050256203370415054343457)
            ·
              refine ⟨3787692152527811290757593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5050256203370415054343457 3787692152527811290757593)
              ·
                refine ⟨2840769114395858468068195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3787692152527811290757593 2840769114395858468068195)
                ·
                  refine ⟨4261153671593787702102293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2840769114395858468068195 4261153671593787702102293)
                  ·
                    refine ⟨199741578355958798536045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4261153671593787702102293 199741578355958798536045)
                    ·
                      rfl

theorem cell23_1166986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_1166986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166986 prefixEnd_1166986 := by exact prefixLift 1166986
  have htrace : WordTrace (prefixWord ++ tailWord_1166986) baseStart_1166986 baseEnd_1166986 := by
    simpa [prefixWord, tailWord_1166986, baseEnd_1166986] using wordTrace_append hprefix tailTrace_1166986
  have hstable : (prefixWord ++ tailWord_1166986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166986).length < 2 ^ (prefixWord ++ tailWord_1166986).sum := by decide
  have hdescent : baseEnd_1166986 < baseStart_1166986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166990 : List Nat := [4, 1, 1, 3, 1, 4, 2, 1, 1, 5]
def baseStart_1166990 : Nat := 118140960795 + 1166990 * 2 ^ 59
def prefixEnd_1166990 : Nat := 4983230072969 + 3 ^ 40 * 1166990 * 2
def baseEnd_1166990 : Nat := 199742262996831459986039

theorem tailTrace_1166990 : CollatzResearch.WordTrace tailWord_1166990 prefixEnd_1166990 199742262996831459986039 := by
  unfold tailWord_1166990
  simp only [CollatzResearch.WordTrace]
  refine ⟨5320452755275251358693303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28375748028134673913030949 5320452755275251358693303)
  ·
    refine ⟨7980679132912877038039955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5320452755275251358693303 7980679132912877038039955)
    ·
      refine ⟨11971018699369315557059933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7980679132912877038039955 11971018699369315557059933)
      ·
        refine ⟨4489132012263493333897475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11971018699369315557059933 4489132012263493333897475)
        ·
          refine ⟨6733698018395240000846213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4489132012263493333897475 6733698018395240000846213)
          ·
            refine ⟨1262568378449107500158665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6733698018395240000846213 1262568378449107500158665)
            ·
              refine ⟨946926283836830625118999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1262568378449107500158665 946926283836830625118999)
              ·
                refine ⟨1420389425755245937678499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 946926283836830625118999 1420389425755245937678499)
                ·
                  refine ⟨2130584138632868906517749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1420389425755245937678499 2130584138632868906517749)
                  ·
                    refine ⟨199742262996831459986039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2130584138632868906517749 199742262996831459986039)
                    ·
                      rfl

theorem cell23_1166990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_1166990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166990 prefixEnd_1166990 := by exact prefixLift 1166990
  have htrace : WordTrace (prefixWord ++ tailWord_1166990) baseStart_1166990 baseEnd_1166990 := by
    simpa [prefixWord, tailWord_1166990, baseEnd_1166990] using wordTrace_append hprefix tailTrace_1166990
  have hstable : (prefixWord ++ tailWord_1166990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166990).length < 2 ^ (prefixWord ++ tailWord_1166990).sum := by decide
  have hdescent : baseEnd_1166990 < baseStart_1166990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166999 : List Nat := [1, 1, 3, 3, 2, 3, 10]
def baseStart_1166999 : Nat := 118140960795 + 1166999 * 2 ^ 59
def prefixEnd_1166999 : Nat := 4983230072969 + 3 ^ 40 * 1166999 * 2
def baseEnd_1166999 : Nat := 7397918645881294379575

theorem tailTrace_1166999 : CollatzResearch.WordTrace tailWord_1166999 prefixEnd_1166999 7397918645881294379575 := by
  unfold tailWord_1166999
  simp only [CollatzResearch.WordTrace]
  refine ⟨42563950299169405406624051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28375966866112936937749367 42563950299169405406624051)
  ·
    refine ⟨63845925448754108109936077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42563950299169405406624051 63845925448754108109936077)
    ·
      refine ⟨23942222043282790541226029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63845925448754108109936077 23942222043282790541226029)
      ·
        refine ⟨8978333266231046452959761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23942222043282790541226029 8978333266231046452959761)
        ·
          refine ⟨6733749949673284839719821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8978333266231046452959761 6733749949673284839719821)
          ·
            refine ⟨2525156231127481814894933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6733749949673284839719821 2525156231127481814894933)
            ·
              refine ⟨7397918645881294379575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2525156231127481814894933 7397918645881294379575)
              ·
                rfl

theorem cell23_1166999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 10].length) (baseStart_1166999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1166999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1166999 prefixEnd_1166999 := by exact prefixLift 1166999
  have htrace : WordTrace (prefixWord ++ tailWord_1166999) baseStart_1166999 baseEnd_1166999 := by
    simpa [prefixWord, tailWord_1166999, baseEnd_1166999] using wordTrace_append hprefix tailTrace_1166999
  have hstable : (prefixWord ++ tailWord_1166999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166999).length < 2 ^ (prefixWord ++ tailWord_1166999).sum := by decide
  have hdescent : baseEnd_1166999 < baseStart_1166999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167039 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 5]
def baseStart_1167039 : Nat := 118140960795 + 1167039 * 2 ^ 59
def prefixEnd_1167039 : Nat := 4983230072969 + 3 ^ 40 * 1167039 * 2
def baseEnd_1167039 : Nat := 599251949542564688245391

theorem tailTrace_1167039 : CollatzResearch.WordTrace tailWord_1167039 prefixEnd_1167039 599251949542564688245391 := by
  unfold tailWord_1167039
  simp only [CollatzResearch.WordTrace]
  refine ⟨42565409219024492238080171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28376939479349661492053447 42565409219024492238080171)
  ·
    refine ⟨63848113828536738357120257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42565409219024492238080171 63848113828536738357120257)
    ·
      refine ⟨47886085371402553767840193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63848113828536738357120257 47886085371402553767840193)
      ·
        refine ⟨35914564028551915325880145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47886085371402553767840193 35914564028551915325880145)
        ·
          refine ⟨26935923021413936494410109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35914564028551915325880145 26935923021413936494410109)
          ·
            refine ⟨10100971133030226185403791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26935923021413936494410109 10100971133030226185403791)
            ·
              refine ⟨15151456699545339278105687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10100971133030226185403791 15151456699545339278105687)
              ·
                refine ⟨22727185049318008917158531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15151456699545339278105687 22727185049318008917158531)
                ·
                  refine ⟨34090777573977013375737797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22727185049318008917158531 34090777573977013375737797)
                  ·
                    refine ⟨6392020795120690007950837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34090777573977013375737797 6392020795120690007950837)
                    ·
                      refine ⟨599251949542564688245391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6392020795120690007950837 599251949542564688245391)
                      ·
                        rfl

theorem cell23_1167039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_1167039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167039 prefixEnd_1167039 := by exact prefixLift 1167039
  have htrace : WordTrace (prefixWord ++ tailWord_1167039) baseStart_1167039 baseEnd_1167039 := by
    simpa [prefixWord, tailWord_1167039, baseEnd_1167039] using wordTrace_append hprefix tailTrace_1167039
  have hstable : (prefixWord ++ tailWord_1167039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167039).length < 2 ^ (prefixWord ++ tailWord_1167039).sum := by decide
  have hdescent : baseEnd_1167039 < baseStart_1167039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167060 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 4, 1, 3]
def baseStart_1167060 : Nat := 118140960795 + 1167060 * 2 ^ 59
def prefixEnd_1167060 : Nat := 4983230072969 + 3 ^ 40 * 1167060 * 2
def baseEnd_1167060 : Nat := 599262732636309106082795

theorem tailTrace_1167060 : CollatzResearch.WordTrace tailWord_1167060 prefixEnd_1167060 599262732636309106082795 := by
  unfold tailWord_1167060
  simp only [CollatzResearch.WordTrace]
  refine ⟨21283087575974206412297317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28377450101298941883063089 21283087575974206412297317)
  ·
    refine ⟨3990578920495163702305747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21283087575974206412297317 3990578920495163702305747)
    ·
      refine ⟨5985868380742745553458621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3990578920495163702305747 5985868380742745553458621)
      ·
        refine ⟨2244700642778529582546983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5985868380742745553458621 2244700642778529582546983)
        ·
          refine ⟨3367050964167794373820475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2244700642778529582546983 3367050964167794373820475)
          ·
            refine ⟨5050576446251691560730713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3367050964167794373820475 5050576446251691560730713)
            ·
              refine ⟨3787932334688768670548035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5050576446251691560730713 3787932334688768670548035)
              ·
                refine ⟨5681898502033153005822053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3787932334688768670548035 5681898502033153005822053)
                ·
                  refine ⟨1065355969131216188591635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5681898502033153005822053 1065355969131216188591635)
                  ·
                    refine ⟨1598033953696824282887453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1065355969131216188591635 1598033953696824282887453)
                    ·
                      refine ⟨599262732636309106082795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1598033953696824282887453 599262732636309106082795)
                      ·
                        rfl

theorem cell23_1167060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_1167060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167060 prefixEnd_1167060 := by exact prefixLift 1167060
  have htrace : WordTrace (prefixWord ++ tailWord_1167060) baseStart_1167060 baseEnd_1167060 := by
    simpa [prefixWord, tailWord_1167060, baseEnd_1167060] using wordTrace_append hprefix tailTrace_1167060
  have hstable : (prefixWord ++ tailWord_1167060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167060).length < 2 ^ (prefixWord ++ tailWord_1167060).sum := by decide
  have hdescent : baseEnd_1167060 < baseStart_1167060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167086 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_1167086 : Nat := 118140960795 + 1167086 * 2 ^ 59
def prefixEnd_1167086 : Nat := 4983230072969 + 3 ^ 40 * 1167086 * 2
def baseEnd_1167086 : Nat := 599276083133326004357675

theorem tailTrace_1167086 : CollatzResearch.WordTrace tailWord_1167086 prefixEnd_1167086 599276083133326004357675 := by
  unfold tailWord_1167086
  simp only [CollatzResearch.WordTrace]
  refine ⟨5320890431231777408130139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28378082299902812843360741 5320890431231777408130139)
  ·
    refine ⟨7981335646847666112195209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5320890431231777408130139 7981335646847666112195209)
    ·
      refine ⟨5986001735135749584146407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7981335646847666112195209 5986001735135749584146407)
      ·
        refine ⟨8979002602703624376219611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5986001735135749584146407 8979002602703624376219611)
        ·
          refine ⟨13468503904055436564329417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8979002602703624376219611 13468503904055436564329417)
          ·
            refine ⟨10101377928041577423247063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13468503904055436564329417 10101377928041577423247063)
            ·
              refine ⟨15152066892062366134870595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10101377928041577423247063 15152066892062366134870595)
              ·
                refine ⟨22728100338093549202305893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15152066892062366134870595 22728100338093549202305893)
                ·
                  refine ⟨4261518813392540475432355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22728100338093549202305893 4261518813392540475432355)
                  ·
                    refine ⟨6392278220088810713148533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4261518813392540475432355 6392278220088810713148533)
                    ·
                      refine ⟨599276083133326004357675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6392278220088810713148533 599276083133326004357675)
                      ·
                        rfl

theorem cell23_1167086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_1167086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167086 prefixEnd_1167086 := by exact prefixLift 1167086
  have htrace : WordTrace (prefixWord ++ tailWord_1167086) baseStart_1167086 baseEnd_1167086 := by
    simpa [prefixWord, tailWord_1167086, baseEnd_1167086] using wordTrace_append hprefix tailTrace_1167086
  have hstable : (prefixWord ++ tailWord_1167086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167086).length < 2 ^ (prefixWord ++ tailWord_1167086).sum := by decide
  have hdescent : baseEnd_1167086 < baseStart_1167086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167099 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 7]
def baseStart_1167099 : Nat := 118140960795 + 1167099 * 2 ^ 59
def prefixEnd_1167099 : Nat := 4983230072969 + 3 ^ 40 * 1167099 * 2
def baseEnd_1167099 : Nat := 599282758381834453495115

theorem tailTrace_1167099 : CollatzResearch.WordTrace tailWord_1167099 prefixEnd_1167099 599282758381834453495115 := by
  unfold tailWord_1167099
  simp only [CollatzResearch.WordTrace]
  refine ⟨42567597598807122485264351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28378398399204748323509567 42567597598807122485264351)
  ·
    refine ⟨63851396398210683727896527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42567597598807122485264351 63851396398210683727896527)
    ·
      refine ⟨95777094597316025591844791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63851396398210683727896527 95777094597316025591844791)
      ·
        refine ⟨143665641895974038387767187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95777094597316025591844791 143665641895974038387767187)
        ·
          refine ⟨215498462843961057581650781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143665641895974038387767187 215498462843961057581650781)
          ·
            refine ⟨80811923566485396593119043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215498462843961057581650781 80811923566485396593119043)
            ·
              refine ⟨121217885349728094889678565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80811923566485396593119043 121217885349728094889678565)
              ·
                refine ⟨22728353503074017791814731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121217885349728094889678565 22728353503074017791814731)
                ·
                  refine ⟨34092530254611026687722097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22728353503074017791814731 34092530254611026687722097)
                  ·
                    refine ⟨25569397690958270015791573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34092530254611026687722097 25569397690958270015791573)
                    ·
                      refine ⟨599282758381834453495115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25569397690958270015791573 599282758381834453495115)
                      ·
                        rfl

theorem cell23_1167099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 7].length) (baseStart_1167099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167099 prefixEnd_1167099 := by exact prefixLift 1167099
  have htrace : WordTrace (prefixWord ++ tailWord_1167099) baseStart_1167099 baseEnd_1167099 := by
    simpa [prefixWord, tailWord_1167099, baseEnd_1167099] using wordTrace_append hprefix tailTrace_1167099
  have hstable : (prefixWord ++ tailWord_1167099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167099).length < 2 ^ (prefixWord ++ tailWord_1167099).sum := by decide
  have hdescent : baseEnd_1167099 < baseStart_1167099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167136 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 1, 7]
def baseStart_1167136 : Nat := 118140960795 + 1167136 * 2 ^ 59
def prefixEnd_1167136 : Nat := 4983230072969 + 3 ^ 40 * 1167136 * 2
def baseEnd_1167136 : Nat := 199767252388683602910815

theorem tailTrace_1167136 : CollatzResearch.WordTrace tailWord_1167136 prefixEnd_1167136 199767252388683602910815 := by
  unfold tailWord_1167136
  simp only [CollatzResearch.WordTrace]
  refine ⟨21284473549836538902180631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28379298066448718536240841 21284473549836538902180631)
  ·
    refine ⟨31926710324754808353270947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21284473549836538902180631 31926710324754808353270947)
    ·
      refine ⟨47890065487132212529906421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31926710324754808353270947 47890065487132212529906421)
      ·
        refine ⟨4489693639418644924678727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47890065487132212529906421 4489693639418644924678727)
        ·
          refine ⟨6734540459127967387018091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4489693639418644924678727 6734540459127967387018091)
          ·
            refine ⟨10101810688691951080527137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6734540459127967387018091 10101810688691951080527137)
            ·
              refine ⟨7576358016518963310395353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10101810688691951080527137 7576358016518963310395353)
              ·
                refine ⟨5682268512389222482796515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7576358016518963310395353 5682268512389222482796515)
                ·
                  refine ⟨8523402768583833724194773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5682268512389222482796515 8523402768583833724194773)
                  ·
                    refine ⟨199767252388683602910815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8523402768583833724194773 199767252388683602910815)
                    ·
                      rfl

theorem cell23_1167136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 1, 7].length) (baseStart_1167136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167136 prefixEnd_1167136 := by exact prefixLift 1167136
  have htrace : WordTrace (prefixWord ++ tailWord_1167136) baseStart_1167136 baseEnd_1167136 := by
    simpa [prefixWord, tailWord_1167136, baseEnd_1167136] using wordTrace_append hprefix tailTrace_1167136
  have hstable : (prefixWord ++ tailWord_1167136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167136).length < 2 ^ (prefixWord ++ tailWord_1167136).sum := by decide
  have hdescent : baseEnd_1167136 < baseStart_1167136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167153 : List Nat := [1, 2, 2, 3, 2, 2, 3, 1, 2, 5]
def baseStart_1167153 : Nat := 118140960795 + 1167153 * 2 ^ 59
def prefixEnd_1167153 : Nat := 4983230072969 + 3 ^ 40 * 1167153 * 2
def baseEnd_1167153 : Nat := 199770162112392414073289

theorem tailTrace_1167153 : CollatzResearch.WordTrace tailWord_1167153 prefixEnd_1167153 199770162112392414073289 := by
  unfold tailWord_1167153
  simp only [CollatzResearch.WordTrace]
  refine ⟨42569567140611489707730113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28379711427074326471820075 42569567140611489707730113)
  ·
    refine ⟨31927175355458617280797585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42569567140611489707730113 31927175355458617280797585)
    ·
      refine ⟨23945381516593962960598189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31927175355458617280797585 23945381516593962960598189)
      ·
        refine ⟨8979518068722736110224321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23945381516593962960598189 8979518068722736110224321)
        ·
          refine ⟨6734638551542052082668241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8979518068722736110224321 6734638551542052082668241)
          ·
            refine ⟨5050978913656539062001181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6734638551542052082668241 5050978913656539062001181)
            ·
              refine ⟨1894117092621202148250443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5050978913656539062001181 1894117092621202148250443)
              ·
                refine ⟨2841175638931803222375665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894117092621202148250443 2841175638931803222375665)
                ·
                  refine ⟨2130881729198852416781749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2841175638931803222375665 2130881729198852416781749)
                  ·
                    refine ⟨199770162112392414073289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2130881729198852416781749 199770162112392414073289)
                    ·
                      rfl

theorem cell23_1167153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_1167153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167153 prefixEnd_1167153 := by exact prefixLift 1167153
  have htrace : WordTrace (prefixWord ++ tailWord_1167153) baseStart_1167153 baseEnd_1167153 := by
    simpa [prefixWord, tailWord_1167153, baseEnd_1167153] using wordTrace_append hprefix tailTrace_1167153
  have hstable : (prefixWord ++ tailWord_1167153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167153).length < 2 ^ (prefixWord ++ tailWord_1167153).sum := by decide
  have hdescent : baseEnd_1167153 < baseStart_1167153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167173 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 4, 4, 2]
def baseStart_1167173 : Nat := 118140960795 + 1167173 * 2 ^ 59
def prefixEnd_1167173 : Nat := 4983230072969 + 3 ^ 40 * 1167173 * 2
def baseEnd_1167173 : Nat := 599320755950267163969775

theorem tailTrace_1167173 : CollatzResearch.WordTrace tailWord_1167173 prefixEnd_1167173 599320755950267163969775 := by
  unfold tailWord_1167173
  simp only [CollatzResearch.WordTrace]
  refine ⟨42570296600539033123458173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28380197733692688748972115 42570296600539033123458173)
  ·
    refine ⟨15963861225202137421296815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42570296600539033123458173 15963861225202137421296815)
    ·
      refine ⟨23945791837803206131945223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15963861225202137421296815 23945791837803206131945223)
      ·
        refine ⟨35918687756704809197917835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23945791837803206131945223 35918687756704809197917835)
        ·
          refine ⟨53878031635057213796876753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35918687756704809197917835 53878031635057213796876753)
          ·
            refine ⟨40408523726292910347657565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53878031635057213796876753 40408523726292910347657565)
            ·
              refine ⟨15153196397359841380371587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40408523726292910347657565 15153196397359841380371587)
              ·
                refine ⟨22729794596039762070557381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15153196397359841380371587 22729794596039762070557381)
                ·
                  refine ⟨4261836486757455388229509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22729794596039762070557381 4261836486757455388229509)
                  ·
                    refine ⟨799094341267022885293033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4261836486757455388229509 799094341267022885293033)
                    ·
                      refine ⟨599320755950267163969775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 799094341267022885293033 599320755950267163969775)
                      ·
                        rfl

theorem cell23_1167173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 4, 2].length) (baseStart_1167173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167173 prefixEnd_1167173 := by exact prefixLift 1167173
  have htrace : WordTrace (prefixWord ++ tailWord_1167173) baseStart_1167173 baseEnd_1167173 := by
    simpa [prefixWord, tailWord_1167173, baseEnd_1167173] using wordTrace_append hprefix tailTrace_1167173
  have hstable : (prefixWord ++ tailWord_1167173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167173).length < 2 ^ (prefixWord ++ tailWord_1167173).sum := by decide
  have hdescent : baseEnd_1167173 < baseStart_1167173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167230 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 8]
def baseStart_1167230 : Nat := 118140960795 + 1167230 * 2 ^ 59
def prefixEnd_1167230 : Nat := 4983230072969 + 3 ^ 40 * 1167230 * 2
def baseEnd_1167230 : Nat := 66594447149730382328557

theorem tailTrace_1167230 : CollatzResearch.WordTrace tailWord_1167230 prefixEnd_1167230 66594447149730382328557 := by
  unfold tailWord_1167230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5321546945166566482285393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28381583707555021238855429 5321546945166566482285393)
  ·
    refine ⟨3991160208874924861714045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5321546945166566482285393 3991160208874924861714045)
    ·
      refine ⟨1496685078328096823142767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3991160208874924861714045 1496685078328096823142767)
      ·
        refine ⟨2245027617492145234714151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1496685078328096823142767 2245027617492145234714151)
        ·
          refine ⟨3367541426238217852071227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2245027617492145234714151 3367541426238217852071227)
          ·
            refine ⟨5051312139357326778106841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3367541426238217852071227 5051312139357326778106841)
            ·
              refine ⟨3788484104517995083580131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5051312139357326778106841 3788484104517995083580131)
              ·
                refine ⟨5682726156776992625370197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3788484104517995083580131 5682726156776992625370197)
                ·
                  refine ⟨66594447149730382328557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5682726156776992625370197 66594447149730382328557)
                  ·
                    rfl

theorem cell23_1167230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_1167230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167230 prefixEnd_1167230 := by exact prefixLift 1167230
  have htrace : WordTrace (prefixWord ++ tailWord_1167230) baseStart_1167230 baseEnd_1167230 := by
    simpa [prefixWord, tailWord_1167230, baseEnd_1167230] using wordTrace_append hprefix tailTrace_1167230
  have hstable : (prefixWord ++ tailWord_1167230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167230).length < 2 ^ (prefixWord ++ tailWord_1167230).sum := by decide
  have hdescent : baseEnd_1167230 < baseStart_1167230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167260 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 3, 5]
def baseStart_1167260 : Nat := 118140960795 + 1167260 * 2 ^ 59
def prefixEnd_1167260 : Nat := 4983230072969 + 3 ^ 40 * 1167260 * 2
def baseEnd_1167260 : Nat := 199788476255736107860625

theorem tailTrace_1167260 : CollatzResearch.WordTrace tailWord_1167260 prefixEnd_1167260 199788476255736107860625 := by
  unfold tailWord_1167260
  simp only [CollatzResearch.WordTrace]
  refine ⟨21286734875611923490937617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28382313167482564654583489 21286734875611923490937617)
  ·
    refine ⟨15965051156708942618203213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21286734875611923490937617 15965051156708942618203213)
    ·
      refine ⟨5986894183765853481826205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15965051156708942618203213 5986894183765853481826205)
      ·
        refine ⟨2245085318912195055684827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5986894183765853481826205 2245085318912195055684827)
        ·
          refine ⟨3367627978368292583527241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2245085318912195055684827 3367627978368292583527241)
          ·
            refine ⟨2525720983776219437645431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3367627978368292583527241 2525720983776219437645431)
            ·
              refine ⟨3788581475664329156468147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2525720983776219437645431 3788581475664329156468147)
              ·
                refine ⟨5682872213496493734702221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3788581475664329156468147 5682872213496493734702221)
                ·
                  refine ⟨2131077080061185150513333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5682872213496493734702221 2131077080061185150513333)
                  ·
                    refine ⟨199788476255736107860625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2131077080061185150513333 199788476255736107860625)
                    ·
                      rfl

theorem cell23_1167260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_1167260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167260 prefixEnd_1167260 := by exact prefixLift 1167260
  have htrace : WordTrace (prefixWord ++ tailWord_1167260) baseStart_1167260 baseEnd_1167260 := by
    simpa [prefixWord, tailWord_1167260, baseEnd_1167260] using wordTrace_append hprefix tailTrace_1167260
  have hstable : (prefixWord ++ tailWord_1167260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167260).length < 2 ^ (prefixWord ++ tailWord_1167260).sum := by decide
  have hdescent : baseEnd_1167260 < baseStart_1167260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167273 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 4, 4]
def baseStart_1167273 : Nat := 118140960795 + 1167273 * 2 ^ 59
def prefixEnd_1167273 : Nat := 4983230072969 + 3 ^ 40 * 1167273 * 2
def baseEnd_1167273 : Nat := 199790701338572257573105

theorem tailTrace_1167273 : CollatzResearch.WordTrace tailWord_1167273 prefixEnd_1167273 199790701338572257573105 := by
  unfold tailWord_1167273
  simp only [CollatzResearch.WordTrace]
  refine ⟨42573943900176750202098473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28382629266784500134732315 42573943900176750202098473)
  ·
    refine ⟨31930457925132562651573855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42573943900176750202098473 31930457925132562651573855)
    ·
      refine ⟨47895686887698843977360783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31930457925132562651573855 47895686887698843977360783)
      ·
        refine ⟨71843530331548265966041175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47895686887698843977360783 71843530331548265966041175)
        ·
          refine ⟨107765295497322398949061763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71843530331548265966041175 107765295497322398949061763)
          ·
            refine ⟨161647943245983598423592645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107765295497322398949061763 161647943245983598423592645)
            ·
              refine ⟨30308989358621924704423621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161647943245983598423592645 30308989358621924704423621)
              ·
                refine ⟨5682935504741610882079429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30308989358621924704423621 5682935504741610882079429)
                ·
                  refine ⟨1065550407139052040389893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5682935504741610882079429 1065550407139052040389893)
                  ·
                    refine ⟨199790701338572257573105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1065550407139052040389893 199790701338572257573105)
                    ·
                      rfl

theorem cell23_1167273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 4].length) (baseStart_1167273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167273 prefixEnd_1167273 := by exact prefixLift 1167273
  have htrace : WordTrace (prefixWord ++ tailWord_1167273) baseStart_1167273 baseEnd_1167273 := by
    simpa [prefixWord, tailWord_1167273, baseEnd_1167273] using wordTrace_append hprefix tailTrace_1167273
  have hstable : (prefixWord ++ tailWord_1167273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167273).length < 2 ^ (prefixWord ++ tailWord_1167273).sum := by decide
  have hdescent : baseEnd_1167273 < baseStart_1167273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167310 : List Nat := [4, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4]
def baseStart_1167310 : Nat := 118140960795 + 1167310 * 2 ^ 59
def prefixEnd_1167310 : Nat := 4983230072969 + 3 ^ 40 * 1167310 * 2
def baseEnd_1167310 : Nat := 599391102799933127956645

theorem tailTrace_1167310 : CollatzResearch.WordTrace tailWord_1167310 prefixEnd_1167310 599391102799933127956645 := by
  unfold tailWord_1167310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5321911675130338190149423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28383528934028470347463589 5321911675130338190149423)
  ·
    refine ⟨7982867512695507285224135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5321911675130338190149423 7982867512695507285224135)
    ·
      refine ⟨11974301269043260927836203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7982867512695507285224135 11974301269043260927836203)
      ·
        refine ⟨17961451903564891391754305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11974301269043260927836203 17961451903564891391754305)
        ·
          refine ⟨13471088927673668543815729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17961451903564891391754305 13471088927673668543815729)
          ·
            refine ⟨10103316695755251407861797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13471088927673668543815729 10103316695755251407861797)
            ·
              refine ⟨1894371880454109638974087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10103316695755251407861797 1894371880454109638974087)
              ·
                refine ⟨2841557820681164458461131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894371880454109638974087 2841557820681164458461131)
                ·
                  refine ⟨4262336731021746687691697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2841557820681164458461131 4262336731021746687691697)
                  ·
                    refine ⟨3196752548266310015768773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4262336731021746687691697 3196752548266310015768773)
                    ·
                      refine ⟨599391102799933127956645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3196752548266310015768773 599391102799933127956645)
                      ·
                        rfl

theorem cell23_1167310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_1167310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167310 prefixEnd_1167310 := by exact prefixLift 1167310
  have htrace : WordTrace (prefixWord ++ tailWord_1167310) baseStart_1167310 baseEnd_1167310 := by
    simpa [prefixWord, tailWord_1167310, baseEnd_1167310] using wordTrace_append hprefix tailTrace_1167310
  have hstable : (prefixWord ++ tailWord_1167310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167310).length < 2 ^ (prefixWord ++ tailWord_1167310).sum := by decide
  have hdescent : baseEnd_1167310 < baseStart_1167310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167318 : List Nat := [5, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_1167318 : Nat := 118140960795 + 1167318 * 2 ^ 59
def prefixEnd_1167318 : Nat := 4983230072969 + 3 ^ 40 * 1167318 * 2
def baseEnd_1167318 : Nat := 599395210645169096656609

theorem tailTrace_1167318 : CollatzResearch.WordTrace tailWord_1167318 prefixEnd_1167318 599395210645169096656609 := by
  unfold tailWord_1167318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2660974074063357680467913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28383723456675815258324405 2660974074063357680467913)
  ·
    refine ⟨1995730555547518260350935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2660974074063357680467913 1995730555547518260350935)
    ·
      refine ⟨2993595833321277390526403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1995730555547518260350935 2993595833321277390526403)
      ·
        refine ⟨4490393749981916085789605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2993595833321277390526403 4490393749981916085789605)
        ·
          refine ⟨841948828121609266085551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4490393749981916085789605 841948828121609266085551)
          ·
            refine ⟨1262923242182413899128327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841948828121609266085551 1262923242182413899128327)
            ·
              refine ⟨1894384863273620848692491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1262923242182413899128327 1894384863273620848692491)
              ·
                refine ⟨2841577294910431273038737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894384863273620848692491 2841577294910431273038737)
                ·
                  refine ⟨2131182971182823454779053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2841577294910431273038737 2131182971182823454779053)
                  ·
                    refine ⟨799193614193558795542145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2131182971182823454779053 799193614193558795542145)
                    ·
                      refine ⟨599395210645169096656609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 799193614193558795542145 599395210645169096656609)
                      ·
                        rfl

theorem cell23_1167318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_1167318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167318 prefixEnd_1167318 := by exact prefixLift 1167318
  have htrace : WordTrace (prefixWord ++ tailWord_1167318) baseStart_1167318 baseEnd_1167318 := by
    simpa [prefixWord, tailWord_1167318, baseEnd_1167318] using wordTrace_append hprefix tailTrace_1167318
  have hstable : (prefixWord ++ tailWord_1167318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167318).length < 2 ^ (prefixWord ++ tailWord_1167318).sum := by decide
  have hdescent : baseEnd_1167318 < baseStart_1167318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167331 : List Nat := [1, 1, 1, 6, 1, 3, 2, 3, 1, 2, 2]
def baseStart_1167331 : Nat := 118140960795 + 1167331 * 2 ^ 59
def prefixEnd_1167331 : Nat := 4983230072969 + 3 ^ 40 * 1167331 * 2
def baseEnd_1167331 : Nat := 599401885893677545794049

theorem tailTrace_1167331 : CollatzResearch.WordTrace tailWord_1167331 prefixEnd_1167331 599401885893677545794049 := by
  unfold tailWord_1167331
  simp only [CollatzResearch.WordTrace]
  refine ⟨42576059333966626107709847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28384039555977750738473231 42576059333966626107709847)
  ·
    refine ⟨63864089000949939161564771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42576059333966626107709847 63864089000949939161564771)
    ·
      refine ⟨95796133501424908742347157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63864089000949939161564771 95796133501424908742347157)
      ·
        refine ⟨4490443757879292597297523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 95796133501424908742347157 4490443757879292597297523)
        ·
          refine ⟨6735665636818938895946285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4490443757879292597297523 6735665636818938895946285)
          ·
            refine ⟨2525874613807102085979857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6735665636818938895946285 2525874613807102085979857)
            ·
              refine ⟨1894405960355326564484893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2525874613807102085979857 1894405960355326564484893)
              ·
                refine ⟨710402235133247461681835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1894405960355326564484893 710402235133247461681835)
                ·
                  refine ⟨1065603352699871192522753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 710402235133247461681835 1065603352699871192522753)
                  ·
                    refine ⟨799202514524903394392065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1065603352699871192522753 799202514524903394392065)
                    ·
                      refine ⟨599401885893677545794049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 799202514524903394392065 599401885893677545794049)
                      ·
                        rfl

theorem cell23_1167331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_1167331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167331 prefixEnd_1167331 := by exact prefixLift 1167331
  have htrace : WordTrace (prefixWord ++ tailWord_1167331) baseStart_1167331 baseEnd_1167331 := by
    simpa [prefixWord, tailWord_1167331, baseEnd_1167331] using wordTrace_append hprefix tailTrace_1167331
  have hstable : (prefixWord ++ tailWord_1167331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167331).length < 2 ^ (prefixWord ++ tailWord_1167331).sum := by decide
  have hdescent : baseEnd_1167331 < baseStart_1167331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167341 : List Nat := [1, 5, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_1167341 : Nat := 118140960795 + 1167341 * 2 ^ 59
def prefixEnd_1167341 : Nat := 4983230072969 + 3 ^ 40 * 1167341 * 2
def baseEnd_1167341 : Nat := 199802340233407502223001

theorem tailTrace_1167341 : CollatzResearch.WordTrace tailWord_1167341 prefixEnd_1167341 199802340233407502223001 := by
  unfold tailWord_1167341
  simp only [CollatzResearch.WordTrace]
  refine ⟨42576424063930397815573877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28384282709286931877049251 42576424063930397815573877)
  ·
    refine ⟨3991539755993474795210051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42576424063930397815573877 3991539755993474795210051)
    ·
      refine ⟨5987309633990212192815077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3991539755993474795210051 5987309633990212192815077)
      ·
        refine ⟨1122620556373164786152827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5987309633990212192815077 1122620556373164786152827)
        ·
          refine ⟨1683930834559747179229241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1122620556373164786152827 1683930834559747179229241)
          ·
            refine ⟨1262948125919810384421931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1683930834559747179229241 1262948125919810384421931)
            ·
              refine ⟨1894422188879715576632897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1262948125919810384421931 1894422188879715576632897)
              ·
                refine ⟨1420816641659786682474673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1894422188879715576632897 1420816641659786682474673)
                ·
                  refine ⟨1065612481244840011856005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1420816641659786682474673 1065612481244840011856005)
                  ·
                    refine ⟨199802340233407502223001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1065612481244840011856005 199802340233407502223001)
                    ·
                      rfl

theorem cell23_1167341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_1167341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167341 prefixEnd_1167341 := by exact prefixLift 1167341
  have htrace : WordTrace (prefixWord ++ tailWord_1167341) baseStart_1167341 baseEnd_1167341 := by
    simpa [prefixWord, tailWord_1167341, baseEnd_1167341] using wordTrace_append hprefix tailTrace_1167341
  have hstable : (prefixWord ++ tailWord_1167341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167341).length < 2 ^ (prefixWord ++ tailWord_1167341).sum := by decide
  have hdescent : baseEnd_1167341 < baseStart_1167341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167374 : List Nat := [4, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2]
def baseStart_1167374 : Nat := 118140960795 + 1167374 * 2 ^ 59
def prefixEnd_1167374 : Nat := 4983230072969 + 3 ^ 40 * 1167374 * 2
def baseEnd_1167374 : Nat := 599423965561820877556351

theorem tailTrace_1167374 : CollatzResearch.WordTrace tailWord_1167374 prefixEnd_1167374 599423965561820877556351 := by
  unfold tailWord_1167374
  simp only [CollatzResearch.WordTrace]
  refine ⟨5322203459101355556440647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28385085115207229634350117 5322203459101355556440647)
  ·
    refine ⟨7983305188652033334660971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5322203459101355556440647 7983305188652033334660971)
    ·
      refine ⟨11974957782978050001991457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7983305188652033334660971 11974957782978050001991457)
      ·
        refine ⟨8981218337233537501493593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11974957782978050001991457 8981218337233537501493593)
        ·
          refine ⟨6735913752925153126120195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8981218337233537501493593 6735913752925153126120195)
          ·
            refine ⟨10103870629387729689180293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6735913752925153126120195 10103870629387729689180293)
            ·
              refine ⟨1894475743010199316721305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10103870629387729689180293 1894475743010199316721305)
              ·
                refine ⟨1420856807257649487540979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1894475743010199316721305 1420856807257649487540979)
                ·
                  refine ⟨2131285210886474231311469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1420856807257649487540979 2131285210886474231311469)
                  ·
                    refine ⟨799231954082427836741801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2131285210886474231311469 799231954082427836741801)
                    ·
                      refine ⟨599423965561820877556351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 799231954082427836741801 599423965561820877556351)
                      ·
                        rfl

theorem cell23_1167374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_1167374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167374 prefixEnd_1167374 := by exact prefixLift 1167374
  have htrace : WordTrace (prefixWord ++ tailWord_1167374) baseStart_1167374 baseEnd_1167374 := by
    simpa [prefixWord, tailWord_1167374, baseEnd_1167374] using wordTrace_append hprefix tailTrace_1167374
  have hstable : (prefixWord ++ tailWord_1167374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167374).length < 2 ^ (prefixWord ++ tailWord_1167374).sum := by decide
  have hdescent : baseEnd_1167374 < baseStart_1167374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167410 : List Nat := [3, 2, 1, 1, 2, 3, 3, 1, 7]
def baseStart_1167410 : Nat := 118140960795 + 1167410 * 2 ^ 59
def prefixEnd_1167410 : Nat := 4983230072969 + 3 ^ 40 * 1167410 * 2
def baseEnd_1167410 : Nat := 66604716762820304078465

theorem tailTrace_1167410 : CollatzResearch.WordTrace tailWord_1167410 prefixEnd_1167410 66604716762820304078465 := by
  unfold tailWord_1167410
  simp only [CollatzResearch.WordTrace]
  refine ⟨10644735175170105649958921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28385960467120281733223789 10644735175170105649958921)
  ·
    refine ⟨7983551381377579237469191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10644735175170105649958921 7983551381377579237469191)
    ·
      refine ⟨11975327072066368856203787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7983551381377579237469191 11975327072066368856203787)
      ·
        refine ⟨17962990608099553284305681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11975327072066368856203787 17962990608099553284305681)
        ·
          refine ⟨13472242956074664963229261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17962990608099553284305681 13472242956074664963229261)
          ·
            refine ⟨5052091108527999361210973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13472242956074664963229261 5052091108527999361210973)
            ·
              refine ⟨1894534165697999760454115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5052091108527999361210973 1894534165697999760454115)
              ·
                refine ⟨2841801248546999640681173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894534165697999760454115 2841801248546999640681173)
                ·
                  refine ⟨66604716762820304078465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2841801248546999640681173 66604716762820304078465)
                  ·
                    rfl

theorem cell23_1167410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_1167410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167410 prefixEnd_1167410 := by exact prefixLift 1167410
  have htrace : WordTrace (prefixWord ++ tailWord_1167410) baseStart_1167410 baseEnd_1167410 := by
    simpa [prefixWord, tailWord_1167410, baseEnd_1167410] using wordTrace_append hprefix tailTrace_1167410
  have hstable : (prefixWord ++ tailWord_1167410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167410).length < 2 ^ (prefixWord ++ tailWord_1167410).sum := by decide
  have hdescent : baseEnd_1167410 < baseStart_1167410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167420 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 1, 5, 3]
def baseStart_1167420 : Nat := 118140960795 + 1167420 * 2 ^ 59
def prefixEnd_1167420 : Nat := 4983230072969 + 3 ^ 40 * 1167420 * 2
def baseEnd_1167420 : Nat := 599447585671927697581139

theorem tailTrace_1167420 : CollatzResearch.WordTrace tailWord_1167420 prefixEnd_1167420 599447585671927697581139 := by
  unfold tailWord_1167420
  simp only [CollatzResearch.WordTrace]
  refine ⟨21289652715322097153849857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28386203620429462871799809 21289652715322097153849857)
  ·
    refine ⟨15967239536491572865387393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21289652715322097153849857 15967239536491572865387393)
    ·
      refine ⟨11975429652368679649040545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15967239536491572865387393 11975429652368679649040545)
      ·
        refine ⟨8981572239276509736780409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11975429652368679649040545 8981572239276509736780409)
        ·
          refine ⟨6736179179457382302585307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8981572239276509736780409 6736179179457382302585307)
          ·
            refine ⟨10104268769186073453877961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6736179179457382302585307 10104268769186073453877961)
            ·
              refine ⟨7578201576889555090408471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10104268769186073453877961 7578201576889555090408471)
              ·
                refine ⟨11367302365334332635612707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7578201576889555090408471 11367302365334332635612707)
                ·
                  refine ⟨17050953548001498953419061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11367302365334332635612707 17050953548001498953419061)
                  ·
                    refine ⟨1598526895125140526883037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17050953548001498953419061 1598526895125140526883037)
                    ·
                      refine ⟨599447585671927697581139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1598526895125140526883037 599447585671927697581139)
                      ·
                        rfl

theorem cell23_1167420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_1167420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167420 prefixEnd_1167420 := by exact prefixLift 1167420
  have htrace : WordTrace (prefixWord ++ tailWord_1167420) baseStart_1167420 baseEnd_1167420 := by
    simpa [prefixWord, tailWord_1167420, baseEnd_1167420] using wordTrace_append hprefix tailTrace_1167420
  have hstable : (prefixWord ++ tailWord_1167420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167420).length < 2 ^ (prefixWord ++ tailWord_1167420).sum := by decide
  have hdescent : baseEnd_1167420 < baseStart_1167420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167423 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 3, 7]
def baseStart_1167423 : Nat := 118140960795 + 1167423 * 2 ^ 59
def prefixEnd_1167423 : Nat := 4983230072969 + 3 ^ 40 * 1167423 * 2
def baseEnd_1167423 : Nat := 199816375371297061947875

theorem tailTrace_1167423 : CollatzResearch.WordTrace tailWord_1167423 prefixEnd_1167423 199816375371297061947875 := by
  unfold tailWord_1167423
  simp only [CollatzResearch.WordTrace]
  refine ⟨42579414849633325820058923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28386276566422217213372615 42579414849633325820058923)
  ·
    refine ⟨63869122274449988730088385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42579414849633325820058923 63869122274449988730088385)
    ·
      refine ⟨47901841705837491547566289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63869122274449988730088385 47901841705837491547566289)
      ·
        refine ⟨35926381279378118660674717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47901841705837491547566289 35926381279378118660674717)
        ·
          refine ⟨13472392979766794497753019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35926381279378118660674717 13472392979766794497753019)
          ·
            refine ⟨20208589469650191746629529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13472392979766794497753019 20208589469650191746629529)
            ·
              refine ⟨15156442102237643809972147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20208589469650191746629529 15156442102237643809972147)
              ·
                refine ⟨22734663153356465714958221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15156442102237643809972147 22734663153356465714958221)
                ·
                  refine ⟨8525498682508674643109333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22734663153356465714958221 8525498682508674643109333)
                  ·
                    refine ⟨199816375371297061947875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8525498682508674643109333 199816375371297061947875)
                    ·
                      rfl

theorem cell23_1167423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 7].length) (baseStart_1167423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167423 prefixEnd_1167423 := by exact prefixLift 1167423
  have htrace : WordTrace (prefixWord ++ tailWord_1167423) baseStart_1167423 baseEnd_1167423 := by
    simpa [prefixWord, tailWord_1167423, baseEnd_1167423] using wordTrace_append hprefix tailTrace_1167423
  have hstable : (prefixWord ++ tailWord_1167423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167423).length < 2 ^ (prefixWord ++ tailWord_1167423).sum := by decide
  have hdescent : baseEnd_1167423 < baseStart_1167423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167433 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 1, 1, 7]
def baseStart_1167433 : Nat := 118140960795 + 1167433 * 2 ^ 59
def prefixEnd_1167433 : Nat := 4983230072969 + 3 ^ 40 * 1167433 * 2
def baseEnd_1167433 : Nat := 599454260920436146718579

theorem tailTrace_1167433 : CollatzResearch.WordTrace tailWord_1167433 prefixEnd_1167433 599454260920436146718579 := by
  unfold tailWord_1167433
  simp only [CollatzResearch.WordTrace]
  refine ⟨42579779579597097527922953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28386519719731398351948635 42579779579597097527922953)
  ·
    refine ⟨31934834684697823145942215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42579779579597097527922953 31934834684697823145942215)
    ·
      refine ⟨47902252027046734718913323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31934834684697823145942215 47902252027046734718913323)
      ·
        refine ⟨71853378040570102078369985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47902252027046734718913323 71853378040570102078369985)
        ·
          refine ⟨53890033530427576558777489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71853378040570102078369985 53890033530427576558777489)
          ·
            refine ⟨40417525147820682419083117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53890033530427576558777489 40417525147820682419083117)
            ·
              refine ⟨15156571930432755907156169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40417525147820682419083117 15156571930432755907156169)
              ·
                refine ⟨11367428947824566930367127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15156571930432755907156169 11367428947824566930367127)
                ·
                  refine ⟨17051143421736850395550691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11367428947824566930367127 17051143421736850395550691)
                  ·
                    refine ⟨25576715132605275593326037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17051143421736850395550691 25576715132605275593326037)
                    ·
                      refine ⟨599454260920436146718579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25576715132605275593326037 599454260920436146718579)
                      ·
                        rfl

theorem cell23_1167433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_1167433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167433 prefixEnd_1167433 := by exact prefixLift 1167433
  have htrace : WordTrace (prefixWord ++ tailWord_1167433) baseStart_1167433 baseEnd_1167433 := by
    simpa [prefixWord, tailWord_1167433, baseEnd_1167433] using wordTrace_append hprefix tailTrace_1167433
  have hstable : (prefixWord ++ tailWord_1167433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167433).length < 2 ^ (prefixWord ++ tailWord_1167433).sum := by decide
  have hdescent : baseEnd_1167433 < baseStart_1167433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167480 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 1, 4, 3]
def baseStart_1167480 : Nat := 118140960795 + 1167480 * 2 ^ 59
def prefixEnd_1167480 : Nat := 4983230072969 + 3 ^ 40 * 1167480 * 2
def baseEnd_1167480 : Nat := 599478394511197462830863

theorem tailTrace_1167480 : CollatzResearch.WordTrace tailWord_1167480 prefixEnd_1167480 599478394511197462830863 := by
  unfold tailWord_1167480
  simp only [CollatzResearch.WordTrace]
  refine ⟨21290746905213412277441947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28387662540284549703255929 21290746905213412277441947)
  ·
    refine ⟨31936120357820118416162921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21290746905213412277441947 31936120357820118416162921)
    ·
      refine ⟨23952090268365088812122191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31936120357820118416162921 23952090268365088812122191)
      ·
        refine ⟨35928135402547633218183287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23952090268365088812122191 35928135402547633218183287)
        ·
          refine ⟨53892203103821449827274931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35928135402547633218183287 53892203103821449827274931)
          ·
            refine ⟨80838304655732174740912397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53892203103821449827274931 80838304655732174740912397)
            ·
              refine ⟨30314364245899565527842149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80838304655732174740912397 30314364245899565527842149)
              ·
                refine ⟨5683943296106168536470403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30314364245899565527842149 5683943296106168536470403)
                ·
                  refine ⟨8525914944159252804705605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5683943296106168536470403 8525914944159252804705605)
                  ·
                    refine ⟨1598609052029859900882301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8525914944159252804705605 1598609052029859900882301)
                    ·
                      refine ⟨599478394511197462830863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1598609052029859900882301 599478394511197462830863)
                      ·
                        rfl

theorem cell23_1167480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_1167480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167480 prefixEnd_1167480 := by exact prefixLift 1167480
  have htrace : WordTrace (prefixWord ++ tailWord_1167480) baseStart_1167480 baseEnd_1167480 := by
    simpa [prefixWord, tailWord_1167480, baseEnd_1167480] using wordTrace_append hprefix tailTrace_1167480
  have hstable : (prefixWord ++ tailWord_1167480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167480).length < 2 ^ (prefixWord ++ tailWord_1167480).sum := by decide
  have hdescent : baseEnd_1167480 < baseStart_1167480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167483 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 12]
def baseStart_1167483 : Nat := 118140960795 + 1167483 * 2 ^ 59
def prefixEnd_1167483 : Nat := 4983230072969 + 3 ^ 40 * 1167483 * 2
def baseEnd_1167483 : Nat := 66608881661462327899261

theorem tailTrace_1167483 : CollatzResearch.WordTrace tailWord_1167483 prefixEnd_1167483 66608881661462327899261 := by
  unfold tailWord_1167483
  simp only [CollatzResearch.WordTrace]
  refine ⟨42581603229415956067243103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28387735486277304044828735 42581603229415956067243103)
  ·
    refine ⟨63872404844123934100864655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42581603229415956067243103 63872404844123934100864655)
    ·
      refine ⟨95808607266185901151296983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63872404844123934100864655 95808607266185901151296983)
      ·
        refine ⟨143712910899278851726945475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95808607266185901151296983 143712910899278851726945475)
        ·
          refine ⟨215569366348918277590418213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143712910899278851726945475 215569366348918277590418213)
          ·
            refine ⟨40419256190422177048203415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 215569366348918277590418213 40419256190422177048203415)
            ·
              refine ⟨60628884285633265572305123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40419256190422177048203415 60628884285633265572305123)
              ·
                refine ⟨90943326428449898358457685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60628884285633265572305123 90943326428449898358457685)
                ·
                  refine ⟨66608881661462327899261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 90943326428449898358457685 66608881661462327899261)
                  ·
                    rfl

theorem cell23_1167483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 12].length) (baseStart_1167483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167483 prefixEnd_1167483 := by exact prefixLift 1167483
  have htrace : WordTrace (prefixWord ++ tailWord_1167483) baseStart_1167483 baseEnd_1167483 := by
    simpa [prefixWord, tailWord_1167483, baseEnd_1167483] using wordTrace_append hprefix tailTrace_1167483
  have hstable : (prefixWord ++ tailWord_1167483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167483).length < 2 ^ (prefixWord ++ tailWord_1167483).sum := by decide
  have hdescent : baseEnd_1167483 < baseStart_1167483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167504 : List Nat := [2, 1, 1, 1, 1, 1, 8, 3, 1, 4]
def baseStart_1167504 : Nat := 118140960795 + 1167504 * 2 ^ 59
def prefixEnd_1167504 : Nat := 4983230072969 + 3 ^ 40 * 1167504 * 2
def baseEnd_1167504 : Nat := 199830239348968456310251

theorem tailTrace_1167504 : CollatzResearch.WordTrace tailWord_1167504 prefixEnd_1167504 199830239348968456310251 := by
  unfold tailWord_1167504
  simp only [CollatzResearch.WordTrace]
  refine ⟨21291184581169938326878783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28388246108226584435838377 21291184581169938326878783)
  ·
    refine ⟨31936776871754907490318175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21291184581169938326878783 31936776871754907490318175)
    ·
      refine ⟨47905165307632361235477263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31936776871754907490318175 47905165307632361235477263)
      ·
        refine ⟨71857747961448541853215895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47905165307632361235477263 71857747961448541853215895)
        ·
          refine ⟨107786621942172812779823843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71857747961448541853215895 107786621942172812779823843)
          ·
            refine ⟨161679932913259219169735765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107786621942172812779823843 161679932913259219169735765)
            ·
              refine ⟨1894686713827256474645341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 161679932913259219169735765 1894686713827256474645341)
              ·
                refine ⟨710507517685221177992003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1894686713827256474645341 710507517685221177992003)
                ·
                  refine ⟨1065761276527831766988005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 710507517685221177992003 1065761276527831766988005)
                  ·
                    refine ⟨199830239348968456310251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1065761276527831766988005 199830239348968456310251)
                    ·
                      rfl

theorem cell23_1167504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 1, 4].length) (baseStart_1167504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167504 prefixEnd_1167504 := by exact prefixLift 1167504
  have htrace : WordTrace (prefixWord ++ tailWord_1167504) baseStart_1167504 baseEnd_1167504 := by
    simpa [prefixWord, tailWord_1167504, baseEnd_1167504] using wordTrace_append hprefix tailTrace_1167504
  have hstable : (prefixWord ++ tailWord_1167504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167504).length < 2 ^ (prefixWord ++ tailWord_1167504).sum := by decide
  have hdescent : baseEnd_1167504 < baseStart_1167504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167517 : List Nat := [1, 4, 2, 1, 1, 3, 3, 2, 6]
def baseStart_1167517 : Nat := 118140960795 + 1167517 * 2 ^ 59
def prefixEnd_1167517 : Nat := 4983230072969 + 3 ^ 40 * 1167517 * 2
def baseEnd_1167517 : Nat := 66610821477268202007577

theorem tailTrace_1167517 : CollatzResearch.WordTrace tailWord_1167517 prefixEnd_1167517 66610821477268202007577 := by
  unfold tailWord_1167517
  simp only [CollatzResearch.WordTrace]
  refine ⟨42582843311292779873980805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28388562207528519915987203 42582843311292779873980805)
  ·
    refine ⟨7984283120867396226371401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42582843311292779873980805 7984283120867396226371401)
    ·
      refine ⟨5988212340650547169778551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7984283120867396226371401 5988212340650547169778551)
      ·
        refine ⟨8982318510975820754667827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5988212340650547169778551 8982318510975820754667827)
        ·
          refine ⟨13473477766463731132001741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8982318510975820754667827 13473477766463731132001741)
          ·
            refine ⟨5052554162423899174500653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13473477766463731132001741 5052554162423899174500653)
            ·
              refine ⟨1894707810908962190437745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5052554162423899174500653 1894707810908962190437745)
              ·
                refine ⟨1421030858181721642828309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1894707810908962190437745 1421030858181721642828309)
                ·
                  refine ⟨66610821477268202007577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1421030858181721642828309 66610821477268202007577)
                  ·
                    rfl

theorem cell23_1167517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_1167517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167517 prefixEnd_1167517 := by exact prefixLift 1167517
  have htrace : WordTrace (prefixWord ++ tailWord_1167517) baseStart_1167517 baseEnd_1167517 := by
    simpa [prefixWord, tailWord_1167517, baseEnd_1167517] using wordTrace_append hprefix tailTrace_1167517
  have hstable : (prefixWord ++ tailWord_1167517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167517).length < 2 ^ (prefixWord ++ tailWord_1167517).sum := by decide
  have hdescent : baseEnd_1167517 < baseStart_1167517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167520 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 6]
def baseStart_1167520 : Nat := 118140960795 + 1167520 * 2 ^ 59
def prefixEnd_1167520 : Nat := 4983230072969 + 3 ^ 40 * 1167520 * 2
def baseEnd_1167520 : Nat := 599498933737377306330679

theorem tailTrace_1167520 : CollatzResearch.WordTrace tailWord_1167520 prefixEnd_1167520 599498933737377306330679 := by
  unfold tailWord_1167520
  simp only [CollatzResearch.WordTrace]
  refine ⟨21291476365140955693170007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28388635153521274257560009 21291476365140955693170007)
  ·
    refine ⟨31937214547711433539755011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21291476365140955693170007 31937214547711433539755011)
    ·
      refine ⟨47905821821567150309632517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31937214547711433539755011 47905821821567150309632517)
      ·
        refine ⟨8982341591543840683056097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47905821821567150309632517 8982341591543840683056097)
        ·
          refine ⟨6736756193657880512292073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8982341591543840683056097 6736756193657880512292073)
          ·
            refine ⟨5052567145243410384219055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6736756193657880512292073 5052567145243410384219055)
            ·
              refine ⟨7578850717865115576328583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5052567145243410384219055 7578850717865115576328583)
              ·
                refine ⟨11368276076797673364492875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7578850717865115576328583 11368276076797673364492875)
                ·
                  refine ⟨17052414115196510046739313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11368276076797673364492875 17052414115196510046739313)
                  ·
                    refine ⟨12789310586397382535054485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17052414115196510046739313 12789310586397382535054485)
                    ·
                      refine ⟨599498933737377306330679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12789310586397382535054485 599498933737377306330679)
                      ·
                        rfl

theorem cell23_1167520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_1167520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167520 prefixEnd_1167520 := by exact prefixLift 1167520
  have htrace : WordTrace (prefixWord ++ tailWord_1167520) baseStart_1167520 baseEnd_1167520 := by
    simpa [prefixWord, tailWord_1167520, baseEnd_1167520] using wordTrace_append hprefix tailTrace_1167520
  have hstable : (prefixWord ++ tailWord_1167520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167520).length < 2 ^ (prefixWord ++ tailWord_1167520).sum := by decide
  have hdescent : baseEnd_1167520 < baseStart_1167520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167547 : List Nat := [1, 1, 1, 1, 1, 2, 8, 2, 1, 5]
def baseStart_1167547 : Nat := 118140960795 + 1167547 * 2 ^ 59
def prefixEnd_1167547 : Nat := 4983230072969 + 3 ^ 40 * 1167547 * 2
def baseEnd_1167547 : Nat := 199837599238349566897685

theorem tailTrace_1167547 : CollatzResearch.WordTrace tailWord_1167547 prefixEnd_1167547 199837599238349566897685 := by
  unfold tailWord_1167547
  simp only [CollatzResearch.WordTrace]
  refine ⟨42583937501184094997572895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28389291667456063331715263 42583937501184094997572895)
  ·
    refine ⟨63875906251776142496359343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42583937501184094997572895 63875906251776142496359343)
    ·
      refine ⟨95813859377664213744539015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63875906251776142496359343 95813859377664213744539015)
      ·
        refine ⟨143720789066496320616808523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95813859377664213744539015 143720789066496320616808523)
        ·
          refine ⟨215581183599744480925212785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143720789066496320616808523 215581183599744480925212785)
          ·
            refine ⟨161685887699808360693909589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215581183599744480925212785 161685887699808360693909589)
            ·
              refine ⟨1894756496482129226881753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 161685887699808360693909589 1894756496482129226881753)
              ·
                refine ⟨1421067372361596920161315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1894756496482129226881753 1421067372361596920161315)
                ·
                  refine ⟨2131601058542395380241973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421067372361596920161315 2131601058542395380241973)
                  ·
                    refine ⟨199837599238349566897685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2131601058542395380241973 199837599238349566897685)
                    ·
                      rfl

theorem cell23_1167547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 5].length) (baseStart_1167547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167547 prefixEnd_1167547 := by exact prefixLift 1167547
  have htrace : WordTrace (prefixWord ++ tailWord_1167547) baseStart_1167547 baseEnd_1167547 := by
    simpa [prefixWord, tailWord_1167547, baseEnd_1167547] using wordTrace_append hprefix tailTrace_1167547
  have hstable : (prefixWord ++ tailWord_1167547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167547).length < 2 ^ (prefixWord ++ tailWord_1167547).sum := by decide
  have hdescent : baseEnd_1167547 < baseStart_1167547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167560 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 3, 6]
def baseStart_1167560 : Nat := 118140960795 + 1167560 * 2 ^ 59
def prefixEnd_1167560 : Nat := 4983230072969 + 3 ^ 40 * 1167560 * 2
def baseEnd_1167560 : Nat := 199839824321185716610165

theorem tailTrace_1167560 : CollatzResearch.WordTrace tailWord_1167560 prefixEnd_1167560 199839824321185716610165 := by
  unfold tailWord_1167560
  simp only [CollatzResearch.WordTrace]
  refine ⟨21292205825068499108898067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28389607766757998811864089 21292205825068499108898067)
  ·
    refine ⟨31938308737602748663347101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21292205825068499108898067 31938308737602748663347101)
    ·
      refine ⟨11976865776601030748755163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31938308737602748663347101 11976865776601030748755163)
      ·
        refine ⟨17965298664901546123132745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11976865776601030748755163 17965298664901546123132745)
        ·
          refine ⟨13473973998676159592349559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17965298664901546123132745 13473973998676159592349559)
          ·
            refine ⟨20210960998014239388524339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13473973998676159592349559 20210960998014239388524339)
            ·
              refine ⟨30316441497021359082786509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20210960998014239388524339 30316441497021359082786509)
              ·
                refine ⟨11368665561383009656044941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30316441497021359082786509 11368665561383009656044941)
                ·
                  refine ⟨4263249585518628621016853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11368665561383009656044941 4263249585518628621016853)
                  ·
                    refine ⟨199839824321185716610165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4263249585518628621016853 199839824321185716610165)
                    ·
                      rfl

theorem cell23_1167560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_1167560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167560 prefixEnd_1167560 := by exact prefixLift 1167560
  have htrace : WordTrace (prefixWord ++ tailWord_1167560) baseStart_1167560 baseEnd_1167560 := by
    simpa [prefixWord, tailWord_1167560, baseEnd_1167560] using wordTrace_append hprefix tailTrace_1167560
  have hstable : (prefixWord ++ tailWord_1167560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167560).length < 2 ^ (prefixWord ++ tailWord_1167560).sum := by decide
  have hdescent : baseEnd_1167560 < baseStart_1167560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167567 : List Nat := [1, 1, 2, 1, 1, 3, 3, 5, 1, 1, 4]
def baseStart_1167567 : Nat := 118140960795 + 1167567 * 2 ^ 59
def prefixEnd_1167567 : Nat := 4983230072969 + 3 ^ 40 * 1167567 * 2
def baseEnd_1167567 : Nat := 599523067328138622442963

theorem tailTrace_1167567 : CollatzResearch.WordTrace tailWord_1167567 prefixEnd_1167567 599523067328138622442963 := by
  unfold tailWord_1167567
  simp only [CollatzResearch.WordTrace]
  refine ⟨42584666961111638413300955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28389777974074425608867303 42584666961111638413300955)
  ·
    refine ⟨63877000441667457619951433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42584666961111638413300955 63877000441667457619951433)
    ·
      refine ⟨47907750331250593214963575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63877000441667457619951433 47907750331250593214963575)
      ·
        refine ⟨71861625496875889822445363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47907750331250593214963575 71861625496875889822445363)
        ·
          refine ⟨107792438245313834733668045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71861625496875889822445363 107792438245313834733668045)
          ·
            refine ⟨40422164341992688025125517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107792438245313834733668045 40422164341992688025125517)
            ·
              refine ⟨15158311628247258009422069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40422164341992688025125517 15158311628247258009422069)
              ·
                refine ⟨1421091715148180438383319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15158311628247258009422069 1421091715148180438383319)
                ·
                  refine ⟨2131637572722270657574979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421091715148180438383319 2131637572722270657574979)
                  ·
                    refine ⟨3197456359083405986362469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2131637572722270657574979 3197456359083405986362469)
                    ·
                      refine ⟨599523067328138622442963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3197456359083405986362469 599523067328138622442963)
                      ·
                        rfl

theorem cell23_1167567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 1, 4].length) (baseStart_1167567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167567 prefixEnd_1167567 := by exact prefixLift 1167567
  have htrace : WordTrace (prefixWord ++ tailWord_1167567) baseStart_1167567 baseEnd_1167567 := by
    simpa [prefixWord, tailWord_1167567, baseEnd_1167567] using wordTrace_append hprefix tailTrace_1167567
  have hstable : (prefixWord ++ tailWord_1167567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167567).length < 2 ^ (prefixWord ++ tailWord_1167567).sum := by decide
  have hdescent : baseEnd_1167567 < baseStart_1167567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167577 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 4, 4]
def baseStart_1167577 : Nat := 118140960795 + 1167577 * 2 ^ 59
def prefixEnd_1167577 : Nat := 4983230072969 + 3 ^ 40 * 1167577 * 2
def baseEnd_1167577 : Nat := 199842734044894527772639

theorem tailTrace_1167577 : CollatzResearch.WordTrace tailWord_1167577 prefixEnd_1167577 199842734044894527772639 := by
  unfold tailWord_1167577
  simp only [CollatzResearch.WordTrace]
  refine ⟨42585031691075410121164985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28390021127383606747443323 42585031691075410121164985)
  ·
    refine ⟨31938773768306557590873739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42585031691075410121164985 31938773768306557590873739)
    ·
      refine ⟨47908160652459836386310609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31938773768306557590873739 47908160652459836386310609)
      ·
        refine ⟨35931120489344877289732957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47908160652459836386310609 35931120489344877289732957)
        ·
          refine ⟨13474170183504328983649859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35931120489344877289732957 13474170183504328983649859)
          ·
            refine ⟨20211255275256493475474789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13474170183504328983649859 20211255275256493475474789)
            ·
              refine ⟨3789610364110592526651523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20211255275256493475474789 3789610364110592526651523)
              ·
                refine ⟨5684415546165888789977285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3789610364110592526651523 5684415546165888789977285)
                ·
                  refine ⟨1065827914906104148120741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5684415546165888789977285 1065827914906104148120741)
                  ·
                    refine ⟨199842734044894527772639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1065827914906104148120741 199842734044894527772639)
                    ·
                      rfl

theorem cell23_1167577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 4].length) (baseStart_1167577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167577 prefixEnd_1167577 := by exact prefixLift 1167577
  have htrace : WordTrace (prefixWord ++ tailWord_1167577) baseStart_1167577 baseEnd_1167577 := by
    simpa [prefixWord, tailWord_1167577, baseEnd_1167577] using wordTrace_append hprefix tailTrace_1167577
  have hstable : (prefixWord ++ tailWord_1167577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167577).length < 2 ^ (prefixWord ++ tailWord_1167577).sum := by decide
  have hdescent : baseEnd_1167577 < baseStart_1167577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167594 : List Nat := [3, 1, 3, 1, 1, 2, 3, 3, 2, 4]
def baseStart_1167594 : Nat := 118140960795 + 1167594 * 2 ^ 59
def prefixEnd_1167594 : Nat := 4983230072969 + 3 ^ 40 * 1167594 * 2
def baseEnd_1167594 : Nat := 199845643768603338935113

theorem tailTrace_1167594 : CollatzResearch.WordTrace tailWord_1167594 prefixEnd_1167594 199845643768603338935113 := by
  unfold tailWord_1167594
  simp only [CollatzResearch.WordTrace]
  refine ⟨10646412933003455506133459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28390434488009214683022557 10646412933003455506133459)
  ·
    refine ⟨15969619399505183259200189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10646412933003455506133459 15969619399505183259200189)
    ·
      refine ⟨5988607274814443722200071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15969619399505183259200189 5988607274814443722200071)
      ·
        refine ⟨8982910912221665583300107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5988607274814443722200071 8982910912221665583300107)
        ·
          refine ⟨13474366368332498374950161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8982910912221665583300107 13474366368332498374950161)
          ·
            refine ⟨10105774776249373781212621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13474366368332498374950161 10105774776249373781212621)
            ·
              refine ⟨3789665541093515167954733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10105774776249373781212621 3789665541093515167954733)
              ·
                refine ⟨1421124577910068187983025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3789665541093515167954733 1421124577910068187983025)
                ·
                  refine ⟨1065843433432551140987269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1421124577910068187983025 1065843433432551140987269)
                  ·
                    refine ⟨199845643768603338935113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1065843433432551140987269 199845643768603338935113)
                    ·
                      rfl

theorem cell23_1167594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_1167594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167594 prefixEnd_1167594 := by exact prefixLift 1167594
  have htrace : WordTrace (prefixWord ++ tailWord_1167594) baseStart_1167594 baseEnd_1167594 := by
    simpa [prefixWord, tailWord_1167594, baseEnd_1167594] using wordTrace_append hprefix tailTrace_1167594
  have hstable : (prefixWord ++ tailWord_1167594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167594).length < 2 ^ (prefixWord ++ tailWord_1167594).sum := by decide
  have hdescent : baseEnd_1167594 < baseStart_1167594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167614 : List Nat := [4, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_1167614 : Nat := 118140960795 + 1167614 * 2 ^ 59
def prefixEnd_1167614 : Nat := 4983230072969 + 3 ^ 40 * 1167614 * 2
def baseEnd_1167614 : Nat := 599547200918899938555247

theorem tailTrace_1167614 : CollatzResearch.WordTrace tailWord_1167614 prefixEnd_1167614 599547200918899938555247 := by
  unfold tailWord_1167614
  simp only [CollatzResearch.WordTrace]
  refine ⟨5323297648992670680032737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28390920794627576960174597 5323297648992670680032737)
  ·
    refine ⟨3992473236744503010024553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5323297648992670680032737 3992473236744503010024553)
    ·
      refine ⟨2994354927558377257518415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3992473236744503010024553 2994354927558377257518415)
      ·
        refine ⟨4491532391337565886277623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2994354927558377257518415 4491532391337565886277623)
        ·
          refine ⟨6737298587006348829416435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4491532391337565886277623 6737298587006348829416435)
          ·
            refine ⟨10105947880509523244124653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6737298587006348829416435 10105947880509523244124653)
            ·
              refine ⟨3789730455191071216546745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10105947880509523244124653 3789730455191071216546745)
              ·
                refine ⟨2842297841393303412410059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3789730455191071216546745 2842297841393303412410059)
                ·
                  refine ⟨4263446762089955118615089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2842297841393303412410059 4263446762089955118615089)
                  ·
                    refine ⟨3197585071567466338961317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4263446762089955118615089 3197585071567466338961317)
                    ·
                      refine ⟨599547200918899938555247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3197585071567466338961317 599547200918899938555247)
                      ·
                        rfl

theorem cell23_1167614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_1167614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167614 prefixEnd_1167614 := by exact prefixLift 1167614
  have htrace : WordTrace (prefixWord ++ tailWord_1167614) baseStart_1167614 baseEnd_1167614 := by
    simpa [prefixWord, tailWord_1167614, baseEnd_1167614] using wordTrace_append hprefix tailTrace_1167614
  have hstable : (prefixWord ++ tailWord_1167614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167614).length < 2 ^ (prefixWord ++ tailWord_1167614).sum := by decide
  have hdescent : baseEnd_1167614 < baseStart_1167614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167618 : List Nat := [3, 4, 1, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_1167618 : Nat := 118140960795 + 1167618 * 2 ^ 59
def prefixEnd_1167618 : Nat := 4983230072969 + 3 ^ 40 * 1167618 * 2
def baseEnd_1167618 : Nat := 599549254841517922905229

theorem tailTrace_1167618 : CollatzResearch.WordTrace tailWord_1167618 prefixEnd_1167618 599549254841517922905229 := by
  unfold tailWord_1167618
  simp only [CollatzResearch.WordTrace]
  refine ⟨10646631770981718530851877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28391018055951249415605005 10646631770981718530851877)
  ·
    refine ⟨1996243457059072224534727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10646631770981718530851877 1996243457059072224534727)
    ·
      refine ⟨2994365185588608336802091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1996243457059072224534727 2994365185588608336802091)
      ·
        refine ⟨4491547778382912505203137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2994365185588608336802091 4491547778382912505203137)
        ·
          refine ⟨3368660833787184378902353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4491547778382912505203137 3368660833787184378902353)
          ·
            refine ⟨2526495625340388284176765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3368660833787184378902353 2526495625340388284176765)
            ·
              refine ⟨947435859502645606566287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2526495625340388284176765 947435859502645606566287)
              ·
                refine ⟨1421153789253968409849431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 947435859502645606566287 1421153789253968409849431)
                ·
                  refine ⟨2131730683880952614774147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421153789253968409849431 2131730683880952614774147)
                  ·
                    refine ⟨3197596025821428922161221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2131730683880952614774147 3197596025821428922161221)
                    ·
                      refine ⟨599549254841517922905229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3197596025821428922161221 599549254841517922905229)
                      ·
                        rfl

theorem cell23_1167618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_1167618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167618 prefixEnd_1167618 := by exact prefixLift 1167618
  have htrace : WordTrace (prefixWord ++ tailWord_1167618) baseStart_1167618 baseEnd_1167618 := by
    simpa [prefixWord, tailWord_1167618, baseEnd_1167618] using wordTrace_append hprefix tailTrace_1167618
  have hstable : (prefixWord ++ tailWord_1167618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167618).length < 2 ^ (prefixWord ++ tailWord_1167618).sum := by decide
  have hdescent : baseEnd_1167618 < baseStart_1167618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167678 : List Nat := [4, 2, 1, 2, 1, 3, 1, 3, 1, 3, 2]
def baseStart_1167678 : Nat := 118140960795 + 1167678 * 2 ^ 59
def prefixEnd_1167678 : Nat := 4983230072969 + 3 ^ 40 * 1167678 * 2
def baseEnd_1167678 : Nat := 599580063680787688154953

theorem tailTrace_1167678 : CollatzResearch.WordTrace tailWord_1167678 prefixEnd_1167678 599580063680787688154953 := by
  unfold tailWord_1167678
  simp only [CollatzResearch.WordTrace]
  refine ⟨5323589432963688046323961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28392476975806336247061125 5323589432963688046323961)
  ·
    refine ⟨3992692074722766034742971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5323589432963688046323961 3992692074722766034742971)
    ·
      refine ⟨5989038112084149052114457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3992692074722766034742971 5989038112084149052114457)
      ·
        refine ⟨4491778584063111789085843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5989038112084149052114457 4491778584063111789085843)
        ·
          refine ⟨6737667876094667683628765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4491778584063111789085843 6737667876094667683628765)
          ·
            refine ⟨2526625453535500381360787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6737667876094667683628765 2526625453535500381360787)
            ·
              refine ⟨3789938180303250572041181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2526625453535500381360787 3789938180303250572041181)
              ·
                refine ⟨1421226817613718964515443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3789938180303250572041181 1421226817613718964515443)
                ·
                  refine ⟨2131840226420578446773165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421226817613718964515443 2131840226420578446773165)
                  ·
                    refine ⟨799440084907716917539937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2131840226420578446773165 799440084907716917539937)
                    ·
                      refine ⟨599580063680787688154953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 799440084907716917539937 599580063680787688154953)
                      ·
                        rfl

theorem cell23_1167678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_1167678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167678 prefixEnd_1167678 := by exact prefixLift 1167678
  have htrace : WordTrace (prefixWord ++ tailWord_1167678) baseStart_1167678 baseEnd_1167678 := by
    simpa [prefixWord, tailWord_1167678, baseEnd_1167678] using wordTrace_append hprefix tailTrace_1167678
  have hstable : (prefixWord ++ tailWord_1167678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167678).length < 2 ^ (prefixWord ++ tailWord_1167678).sum := by decide
  have hdescent : baseEnd_1167678 < baseStart_1167678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167687 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_1167687 : Nat := 118140960795 + 1167687 * 2 ^ 59
def prefixEnd_1167687 : Nat := 4983230072969 + 3 ^ 40 * 1167687 * 2
def baseEnd_1167687 : Nat := 599584685006678152942411

theorem tailTrace_1167687 : CollatzResearch.WordTrace tailWord_1167687 prefixEnd_1167687 599584685006678152942411 := by
  unfold tailWord_1167687
  simp only [CollatzResearch.WordTrace]
  refine ⟨42589043720676898907669315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28392695813784599271779543 42589043720676898907669315)
  ·
    refine ⟨63883565581015348361503973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42589043720676898907669315 63883565581015348361503973)
    ·
      refine ⟨11978168546440377817781995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63883565581015348361503973 11978168546440377817781995)
      ·
        refine ⟨17967252819660566726672993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11978168546440377817781995 17967252819660566726672993)
        ·
          refine ⟨13475439614745425045004745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17967252819660566726672993 13475439614745425045004745)
          ·
            refine ⟨10106579711059068783753559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13475439614745425045004745 10106579711059068783753559)
            ·
              refine ⟨15159869566588603175630339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10106579711059068783753559 15159869566588603175630339)
              ·
                refine ⟨22739804349882904763445509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15159869566588603175630339 22739804349882904763445509)
                ·
                  refine ⟨4263713315603044643146033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22739804349882904763445509 4263713315603044643146033)
                  ·
                    refine ⟨3197784986702283482359525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4263713315603044643146033 3197784986702283482359525)
                    ·
                      refine ⟨599584685006678152942411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3197784986702283482359525 599584685006678152942411)
                      ·
                        rfl

theorem cell23_1167687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_1167687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167687 prefixEnd_1167687 := by exact prefixLift 1167687
  have htrace : WordTrace (prefixWord ++ tailWord_1167687) baseStart_1167687 baseEnd_1167687 := by
    simpa [prefixWord, tailWord_1167687, baseEnd_1167687] using wordTrace_append hprefix tailTrace_1167687
  have hstable : (prefixWord ++ tailWord_1167687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167687).length < 2 ^ (prefixWord ++ tailWord_1167687).sum := by decide
  have hdescent : baseEnd_1167687 < baseStart_1167687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167691 : List Nat := [1, 1, 1, 1, 3, 1, 1, 8, 2, 2, 2]
def baseStart_1167691 : Nat := 118140960795 + 1167691 * 2 ^ 59
def prefixEnd_1167691 : Nat := 4983230072969 + 3 ^ 40 * 1167691 * 2
def baseEnd_1167691 : Nat := 599586738929296137292393

theorem tailTrace_1167691 : CollatzResearch.WordTrace tailWord_1167691 prefixEnd_1167691 599586738929296137292393 := by
  unfold tailWord_1167691
  simp only [CollatzResearch.WordTrace]
  refine ⟨42589189612662407590814927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28392793075108271727209951 42589189612662407590814927)
  ·
    refine ⟨63883784418993611386222391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42589189612662407590814927 63883784418993611386222391)
    ·
      refine ⟨95825676628490417079333587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63883784418993611386222391 95825676628490417079333587)
      ·
        refine ⟨143738514942735625619000381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95825676628490417079333587 143738514942735625619000381)
        ·
          refine ⟨53901943103525859607125143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143738514942735625619000381 53901943103525859607125143)
          ·
            refine ⟨80852914655288789410687715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53901943103525859607125143 80852914655288789410687715)
            ·
              refine ⟨121279371982933184116031573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80852914655288789410687715 121279371982933184116031573)
              ·
                refine ⟨1421242640424998251359745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 121279371982933184116031573 1421242640424998251359745)
                ·
                  refine ⟨1065931980318748688519809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1421242640424998251359745 1065931980318748688519809)
                  ·
                    refine ⟨799448985239061516389857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1065931980318748688519809 799448985239061516389857)
                    ·
                      refine ⟨599586738929296137292393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 799448985239061516389857 599586738929296137292393)
                      ·
                        rfl

theorem cell23_1167691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 2, 2].length) (baseStart_1167691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167691 prefixEnd_1167691 := by exact prefixLift 1167691
  have htrace : WordTrace (prefixWord ++ tailWord_1167691) baseStart_1167691 baseEnd_1167691 := by
    simpa [prefixWord, tailWord_1167691, baseEnd_1167691] using wordTrace_append hprefix tailTrace_1167691
  have hstable : (prefixWord ++ tailWord_1167691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167691).length < 2 ^ (prefixWord ++ tailWord_1167691).sum := by decide
  have hdescent : baseEnd_1167691 < baseStart_1167691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167697 : List Nat := [1, 2, 2, 1, 4, 2, 1, 3, 7]
def baseStart_1167697 : Nat := 118140960795 + 1167697 * 2 ^ 59
def prefixEnd_1167697 : Nat := 4983230072969 + 3 ^ 40 * 1167697 * 2
def baseEnd_1167697 : Nat := 66621091090358123757485

theorem tailTrace_1167697 : CollatzResearch.WordTrace tailWord_1167697 prefixEnd_1167697 66621091090358123757485 := by
  unfold tailWord_1167697
  simp only [CollatzResearch.WordTrace]
  refine ⟨42589408450640670615533345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28392938967093780410355563 42589408450640670615533345)
  ·
    refine ⟨31942056337980502961650009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42589408450640670615533345 31942056337980502961650009)
    ·
      refine ⟨23956542253485377221237507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31942056337980502961650009 23956542253485377221237507)
      ·
        refine ⟨35934813380228065831856261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23956542253485377221237507 35934813380228065831856261)
        ·
          refine ⟨6737777508792762343473049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35934813380228065831856261 6737777508792762343473049)
          ·
            refine ⟨5053333131594571757604787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6737777508792762343473049 5053333131594571757604787)
            ·
              refine ⟨7579999697391857636407181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5053333131594571757604787 7579999697391857636407181)
              ·
                refine ⟨2842499886521946613652693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7579999697391857636407181 2842499886521946613652693)
                ·
                  refine ⟨66621091090358123757485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2842499886521946613652693 66621091090358123757485)
                  ·
                    rfl

theorem cell23_1167697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 7].length) (baseStart_1167697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167697 prefixEnd_1167697 := by exact prefixLift 1167697
  have htrace : WordTrace (prefixWord ++ tailWord_1167697) baseStart_1167697 baseEnd_1167697 := by
    simpa [prefixWord, tailWord_1167697, baseEnd_1167697] using wordTrace_append hprefix tailTrace_1167697
  have hstable : (prefixWord ++ tailWord_1167697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167697).length < 2 ^ (prefixWord ++ tailWord_1167697).sum := by decide
  have hdescent : baseEnd_1167697 < baseStart_1167697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167714 : List Nat := [3, 3, 2, 1, 1, 2, 2, 2, 7]
def baseStart_1167714 : Nat := 118140960795 + 1167714 * 2 ^ 59
def prefixEnd_1167714 : Nat := 4983230072969 + 3 ^ 40 * 1167714 * 2
def baseEnd_1167714 : Nat := 66622060998261060811643

theorem tailTrace_1167714 : CollatzResearch.WordTrace tailWord_1167714 prefixEnd_1167714 66622060998261060811643 := by
  unfold tailWord_1167714
  simp only [CollatzResearch.WordTrace]
  refine ⟨10647507122894770629725549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28393352327719388345934797 10647507122894770629725549)
  ·
    refine ⟨3992815171085538986147081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10647507122894770629725549 3992815171085538986147081)
    ·
      refine ⟨2994611378314154239610311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3992815171085538986147081 2994611378314154239610311)
      ·
        refine ⟨4491917067471231359415467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2994611378314154239610311 4491917067471231359415467)
        ·
          refine ⟨6737875601206847039123201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4491917067471231359415467 6737875601206847039123201)
          ·
            refine ⟨5053406700905135279342401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6737875601206847039123201 5053406700905135279342401)
            ·
              refine ⟨3790055025678851459506801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5053406700905135279342401 3790055025678851459506801)
              ·
                refine ⟨2842541269259138594630101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3790055025678851459506801 2842541269259138594630101)
                ·
                  refine ⟨66622060998261060811643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2842541269259138594630101 66622060998261060811643)
                  ·
                    rfl

theorem cell23_1167714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_1167714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167714 prefixEnd_1167714 := by exact prefixLift 1167714
  have htrace : WordTrace (prefixWord ++ tailWord_1167714) baseStart_1167714 baseEnd_1167714 := by
    simpa [prefixWord, tailWord_1167714, baseEnd_1167714] using wordTrace_append hprefix tailTrace_1167714
  have hstable : (prefixWord ++ tailWord_1167714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167714).length < 2 ^ (prefixWord ++ tailWord_1167714).sum := by decide
  have hdescent : baseEnd_1167714 < baseStart_1167714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167737 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 1, 2, 5]
def baseStart_1167737 : Nat := 118140960795 + 1167737 * 2 ^ 59
def prefixEnd_1167737 : Nat := 4983230072969 + 3 ^ 40 * 1167737 * 2
def baseEnd_1167737 : Nat := 599610359039402957317181

theorem tailTrace_1167737 : CollatzResearch.WordTrace tailWord_1167737 prefixEnd_1167737 599610359039402957317181 := by
  unfold tailWord_1167737
  simp only [CollatzResearch.WordTrace]
  refine ⟨42590867370495757446989465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28393911580330504964659643 42590867370495757446989465)
  ·
    refine ⟨31943150527871818085242099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42590867370495757446989465 31943150527871818085242099)
    ·
      refine ⟨47914725791807727127863149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31943150527871818085242099 47914725791807727127863149)
      ·
        refine ⟨17968022171927897672948681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47914725791807727127863149 17968022171927897672948681)
        ·
          refine ⟨13476016628945923254711511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17968022171927897672948681 13476016628945923254711511)
          ·
            refine ⟨20214024943418884882067267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13476016628945923254711511 20214024943418884882067267)
            ·
              refine ⟨30321037415128327323100901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20214024943418884882067267 30321037415128327323100901)
              ·
                refine ⟨5685194515336561373081419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30321037415128327323100901 5685194515336561373081419)
                ·
                  refine ⟨8527791773004842059622129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5685194515336561373081419 8527791773004842059622129)
                  ·
                    refine ⟨6395843829753631544716597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8527791773004842059622129 6395843829753631544716597)
                    ·
                      refine ⟨599610359039402957317181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6395843829753631544716597 599610359039402957317181)
                      ·
                        rfl

theorem cell23_1167737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_1167737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167737 prefixEnd_1167737 := by exact prefixLift 1167737
  have htrace : WordTrace (prefixWord ++ tailWord_1167737) baseStart_1167737 baseEnd_1167737 := by
    simpa [prefixWord, tailWord_1167737, baseEnd_1167737] using wordTrace_append hprefix tailTrace_1167737
  have hstable : (prefixWord ++ tailWord_1167737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167737).length < 2 ^ (prefixWord ++ tailWord_1167737).sum := by decide
  have hdescent : baseEnd_1167737 < baseStart_1167737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167801 : List Nat := [1, 2, 1, 4, 3, 1, 2, 2, 2, 2, 3]
def baseStart_1167801 : Nat := 118140960795 + 1167801 * 2 ^ 59
def prefixEnd_1167801 : Nat := 4983230072969 + 3 ^ 40 * 1167801 * 2
def baseEnd_1167801 : Nat := 599643221801290706916887

theorem tailTrace_1167801 : CollatzResearch.WordTrace tailWord_1167801 prefixEnd_1167801 599643221801290706916887 := by
  unfold tailWord_1167801
  simp only [CollatzResearch.WordTrace]
  refine ⟨42593201642263896377319257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28395467761509264251546171 42593201642263896377319257)
  ·
    refine ⟨31944901231697922282989443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42593201642263896377319257 31944901231697922282989443)
    ·
      refine ⟨47917351847546883424484165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31944901231697922282989443 47917351847546883424484165)
      ·
        refine ⟨8984503471415040642090781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47917351847546883424484165 8984503471415040642090781)
        ·
          refine ⟨3369188801780640240784043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8984503471415040642090781 3369188801780640240784043)
          ·
            refine ⟨5053783202670960361176065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3369188801780640240784043 5053783202670960361176065)
            ·
              refine ⟨3790337402003220270882049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5053783202670960361176065 3790337402003220270882049)
              ·
                refine ⟨2842753051502415203161537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3790337402003220270882049 2842753051502415203161537)
                ·
                  refine ⟨2132064788626811402371153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2842753051502415203161537 2132064788626811402371153)
                  ·
                    refine ⟨1599048591470108551778365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2132064788626811402371153 1599048591470108551778365)
                    ·
                      refine ⟨599643221801290706916887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1599048591470108551778365 599643221801290706916887)
                      ·
                        rfl

theorem cell23_1167801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_1167801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167801 prefixEnd_1167801 := by exact prefixLift 1167801
  have htrace : WordTrace (prefixWord ++ tailWord_1167801) baseStart_1167801 baseEnd_1167801 := by
    simpa [prefixWord, tailWord_1167801, baseEnd_1167801] using wordTrace_append hprefix tailTrace_1167801
  have hstable : (prefixWord ++ tailWord_1167801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167801).length < 2 ^ (prefixWord ++ tailWord_1167801).sum := by decide
  have hdescent : baseEnd_1167801 < baseStart_1167801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167827 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 5]
def baseStart_1167827 : Nat := 118140960795 + 1167827 * 2 ^ 59
def prefixEnd_1167827 : Nat := 4983230072969 + 3 ^ 40 * 1167827 * 2
def baseEnd_1167827 : Nat := 599656572298307605191767

theorem tailTrace_1167827 : CollatzResearch.WordTrace tailWord_1167827 prefixEnd_1167827 599656572298307605191767 := by
  unfold tailWord_1167827
  simp only [CollatzResearch.WordTrace]
  refine ⟨42594149940169702817765735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28396099960113135211843823 42594149940169702817765735)
  ·
    refine ⟨63891224910254554226648603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42594149940169702817765735 63891224910254554226648603)
    ·
      refine ⟨95836837365381831339972905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63891224910254554226648603 95836837365381831339972905)
      ·
        refine ⟨71877628024036373504979679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95836837365381831339972905 71877628024036373504979679)
        ·
          refine ⟨107816442036054560257469519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71877628024036373504979679 107816442036054560257469519)
          ·
            refine ⟨161724663054081840386204279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107816442036054560257469519 161724663054081840386204279)
            ·
              refine ⟨242586994581122760579306419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161724663054081840386204279 242586994581122760579306419)
              ·
                refine ⟨363880491871684140868959629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242586994581122760579306419 363880491871684140868959629)
                ·
                  refine ⟨136455184451881552825859861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 363880491871684140868959629 136455184451881552825859861)
                  ·
                    refine ⟨6396336771181947788712181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 136455184451881552825859861 6396336771181947788712181)
                    ·
                      refine ⟨599656572298307605191767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6396336771181947788712181 599656572298307605191767)
                      ·
                        rfl

theorem cell23_1167827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_1167827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167827 prefixEnd_1167827 := by exact prefixLift 1167827
  have htrace : WordTrace (prefixWord ++ tailWord_1167827) baseStart_1167827 baseEnd_1167827 := by
    simpa [prefixWord, tailWord_1167827, baseEnd_1167827] using wordTrace_append hprefix tailTrace_1167827
  have hstable : (prefixWord ++ tailWord_1167827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167827).length < 2 ^ (prefixWord ++ tailWord_1167827).sum := by decide
  have hdescent : baseEnd_1167827 < baseStart_1167827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167834 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 3, 5]
def baseStart_1167834 : Nat := 118140960795 + 1167834 * 2 ^ 59
def prefixEnd_1167834 : Nat := 4983230072969 + 3 ^ 40 * 1167834 * 2
def baseEnd_1167834 : Nat := 199886722220963025934745

theorem tailTrace_1167834 : CollatzResearch.WordTrace tailWord_1167834 prefixEnd_1167834 199886722220963025934745 := by
  unfold tailWord_1167834
  simp only [CollatzResearch.WordTrace]
  refine ⟨10648601312786085753317639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28396270167429562008847037 10648601312786085753317639)
  ·
    refine ⟨15972901969179128629976459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10648601312786085753317639 15972901969179128629976459)
    ·
      refine ⟨23959352953768692944964689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15972901969179128629976459 23959352953768692944964689)
      ·
        refine ⟨17969514715326519708723517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23959352953768692944964689 17969514715326519708723517)
        ·
          refine ⟨6738568018247444890771319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17969514715326519708723517 6738568018247444890771319)
          ·
            refine ⟨10107852027371167336156979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6738568018247444890771319 10107852027371167336156979)
            ·
              refine ⟨15161778041056751004235469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10107852027371167336156979 15161778041056751004235469)
              ·
                refine ⟨5685666765396281626588301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15161778041056751004235469 5685666765396281626588301)
                ·
                  refine ⟨2132125037023605609970613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5685666765396281626588301 2132125037023605609970613)
                  ·
                    refine ⟨199886722220963025934745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2132125037023605609970613 199886722220963025934745)
                    ·
                      rfl

theorem cell23_1167834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_1167834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167834 prefixEnd_1167834 := by exact prefixLift 1167834
  have htrace : WordTrace (prefixWord ++ tailWord_1167834) baseStart_1167834 baseEnd_1167834 := by
    simpa [prefixWord, tailWord_1167834, baseEnd_1167834] using wordTrace_append hprefix tailTrace_1167834
  have hstable : (prefixWord ++ tailWord_1167834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167834).length < 2 ^ (prefixWord ++ tailWord_1167834).sum := by decide
  have hdescent : baseEnd_1167834 < baseStart_1167834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167841 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 1, 5, 2]
def baseStart_1167841 : Nat := 118140960795 + 1167841 * 2 ^ 59
def prefixEnd_1167841 : Nat := 4983230072969 + 3 ^ 40 * 1167841 * 2
def baseEnd_1167841 : Nat := 599663761027470550416703

theorem tailTrace_1167841 : CollatzResearch.WordTrace tailWord_1167841 prefixEnd_1167841 599663761027470550416703 := by
  unfold tailWord_1167841
  simp only [CollatzResearch.WordTrace]
  refine ⟨42594660562118983208775377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28396440374745988805850251 42594660562118983208775377)
  ·
    refine ⟨31945995421589237406581533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42594660562118983208775377 31945995421589237406581533)
    ·
      refine ⟨11979748283095964027468075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31945995421589237406581533 11979748283095964027468075)
      ·
        refine ⟨17969622424643946041202113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11979748283095964027468075 17969622424643946041202113)
        ·
          refine ⟨13477216818482959530901585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17969622424643946041202113 13477216818482959530901585)
          ·
            refine ⟨10107912613862219648176189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13477216818482959530901585 10107912613862219648176189)
            ·
              refine ⟨3790467230198332368066071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10107912613862219648176189 3790467230198332368066071)
              ·
                refine ⟨5685700845297498552099107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3790467230198332368066071 5685700845297498552099107)
                ·
                  refine ⟨8528551267946247828148661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5685700845297498552099107 8528551267946247828148661)
                  ·
                    refine ⟨799551681369960733888937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8528551267946247828148661 799551681369960733888937)
                    ·
                      refine ⟨599663761027470550416703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 799551681369960733888937 599663761027470550416703)
                      ·
                        rfl

theorem cell23_1167841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_1167841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167841 prefixEnd_1167841 := by exact prefixLift 1167841
  have htrace : WordTrace (prefixWord ++ tailWord_1167841) baseStart_1167841 baseEnd_1167841 := by
    simpa [prefixWord, tailWord_1167841, baseEnd_1167841] using wordTrace_append hprefix tailTrace_1167841
  have hstable : (prefixWord ++ tailWord_1167841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167841).length < 2 ^ (prefixWord ++ tailWord_1167841).sum := by decide
  have hdescent : baseEnd_1167841 < baseStart_1167841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167885 : List Nat := [1, 7, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_1167885 : Nat := 118140960795 + 1167885 * 2 ^ 59
def prefixEnd_1167885 : Nat := 4983230072969 + 3 ^ 40 * 1167885 * 2
def baseEnd_1167885 : Nat := 199895451392089459422167

theorem tailTrace_1167885 : CollatzResearch.WordTrace tailWord_1167885 prefixEnd_1167885 199895451392089459422167 := by
  unfold tailWord_1167885
  simp only [CollatzResearch.WordTrace]
  refine ⟨42596265373959578723377109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28397510249306385815584739 42596265373959578723377109)
  ·
    refine ⟨998349969702177626329151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 42596265373959578723377109 998349969702177626329151)
    ·
      refine ⟨1497524954553266439493727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 998349969702177626329151 1497524954553266439493727)
      ·
        refine ⟨2246287431829899659240591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1497524954553266439493727 2246287431829899659240591)
        ·
          refine ⟨3369431147744849488860887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2246287431829899659240591 3369431147744849488860887)
          ·
            refine ⟨5054146721617274233291331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3369431147744849488860887 5054146721617274233291331)
            ·
              refine ⟨7581220082425911349936997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5054146721617274233291331 7581220082425911349936997)
              ·
                refine ⟨1421478765454858378113187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7581220082425911349936997 1421478765454858378113187)
                ·
                  refine ⟨2132218148182287567169781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421478765454858378113187 2132218148182287567169781)
                  ·
                    refine ⟨199895451392089459422167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2132218148182287567169781 199895451392089459422167)
                    ·
                      rfl

theorem cell23_1167885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_1167885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167885 prefixEnd_1167885 := by exact prefixLift 1167885
  have htrace : WordTrace (prefixWord ++ tailWord_1167885) baseStart_1167885 baseEnd_1167885 := by
    simpa [prefixWord, tailWord_1167885, baseEnd_1167885] using wordTrace_append hprefix tailTrace_1167885
  have hstable : (prefixWord ++ tailWord_1167885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167885).length < 2 ^ (prefixWord ++ tailWord_1167885).sum := by decide
  have hdescent : baseEnd_1167885 < baseStart_1167885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167942 : List Nat := [6, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_1167942 : Nat := 118140960795 + 1167942 * 2 ^ 59
def prefixEnd_1167942 : Nat := 4983230072969 + 3 ^ 40 * 1167942 * 2
def baseEnd_1167942 : Nat := 599715622573574655253739

theorem tailTrace_1167942 : CollatzResearch.WordTrace tailWord_1167942 prefixEnd_1167942 599715622573574655253739 := by
  unfold tailWord_1167942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1331198260461033670568815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28398896223168718305468053 1331198260461033670568815)
  ·
    refine ⟨1996797390691550505853223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1331198260461033670568815 1996797390691550505853223)
    ·
      refine ⟨2995196086037325758779835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1996797390691550505853223 2995196086037325758779835)
      ·
        refine ⟨4492794129055988638169753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2995196086037325758779835 4492794129055988638169753)
        ·
          refine ⟨3369595596791991478627315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4492794129055988638169753 3369595596791991478627315)
          ·
            refine ⟨5054393395187987217940973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3369595596791991478627315 5054393395187987217940973)
            ·
              refine ⟨1895397523195495206727865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5054393395187987217940973 1895397523195495206727865)
              ·
                refine ⟨1421548142396621405045899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1895397523195495206727865 1421548142396621405045899)
                ·
                  refine ⟨2132322213594932107568849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421548142396621405045899 2132322213594932107568849)
                  ·
                    refine ⟨1599241660196199080676637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2132322213594932107568849 1599241660196199080676637)
                    ·
                      refine ⟨599715622573574655253739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1599241660196199080676637 599715622573574655253739)
                      ·
                        rfl

theorem cell23_1167942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_1167942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167942 prefixEnd_1167942 := by exact prefixLift 1167942
  have htrace : WordTrace (prefixWord ++ tailWord_1167942) baseStart_1167942 baseEnd_1167942 := by
    simpa [prefixWord, tailWord_1167942, baseEnd_1167942] using wordTrace_append hprefix tailTrace_1167942
  have hstable : (prefixWord ++ tailWord_1167942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167942).length < 2 ^ (prefixWord ++ tailWord_1167942).sum := by decide
  have hdescent : baseEnd_1167942 < baseStart_1167942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167948 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 3, 3, 2]
def baseStart_1167948 : Nat := 118140960795 + 1167948 * 2 ^ 59
def prefixEnd_1167948 : Nat := 4983230072969 + 3 ^ 40 * 1167948 * 2
def baseEnd_1167948 : Nat := 599718703457501631778711

theorem tailTrace_1167948 : CollatzResearch.WordTrace tailWord_1167948 prefixEnd_1167948 599718703457501631778711 := by
  unfold tailWord_1167948
  simp only [CollatzResearch.WordTrace]
  refine ⟨21299281586365670241460249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28399042115154226988613665 21299281586365670241460249)
  ·
    refine ⟨15974461189774252681095187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21299281586365670241460249 15974461189774252681095187)
    ·
      refine ⟨23961691784661379021642781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15974461189774252681095187 23961691784661379021642781)
      ·
        refine ⟨8985634419248017133116043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23961691784661379021642781 8985634419248017133116043)
        ·
          refine ⟨13478451628872025699674065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8985634419248017133116043 13478451628872025699674065)
          ·
            refine ⟨10108838721654019274755549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13478451628872025699674065 10108838721654019274755549)
            ·
              refine ⟨3790814520620257228033331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10108838721654019274755549 3790814520620257228033331)
              ·
                refine ⟨5686221780930385842049997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3790814520620257228033331 5686221780930385842049997)
                ·
                  refine ⟨2132333167848894690768749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5686221780930385842049997 2132333167848894690768749)
                  ·
                    refine ⟨799624937943335509038281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2132333167848894690768749 799624937943335509038281)
                    ·
                      refine ⟨599718703457501631778711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 799624937943335509038281 599718703457501631778711)
                      ·
                        rfl

theorem cell23_1167948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_1167948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167948 prefixEnd_1167948 := by exact prefixLift 1167948
  have htrace : WordTrace (prefixWord ++ tailWord_1167948) baseStart_1167948 baseEnd_1167948 := by
    simpa [prefixWord, tailWord_1167948, baseEnd_1167948] using wordTrace_append hprefix tailTrace_1167948
  have hstable : (prefixWord ++ tailWord_1167948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167948).length < 2 ^ (prefixWord ++ tailWord_1167948).sum := by decide
  have hdescent : baseEnd_1167948 < baseStart_1167948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167978 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 3, 4, 2]
def baseStart_1167978 : Nat := 118140960795 + 1167978 * 2 ^ 59
def prefixEnd_1167978 : Nat := 4983230072969 + 3 ^ 40 * 1167978 * 2
def baseEnd_1167978 : Nat := 599734107877136514403573

theorem tailTrace_1167978 : CollatzResearch.WordTrace tailWord_1167978 prefixEnd_1167978 599734107877136514403573 := by
  unfold tailWord_1167978
  simp only [CollatzResearch.WordTrace]
  refine ⟨10649914340655663901628147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28399771575081770404341725 10649914340655663901628147)
  ·
    refine ⟨15974871510983495852442221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10649914340655663901628147 15974871510983495852442221)
    ·
      refine ⟨5990576816618810944665833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15974871510983495852442221 5990576816618810944665833)
      ·
        refine ⟨4492932612464108208499375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5990576816618810944665833 4492932612464108208499375)
        ·
          refine ⟨6739398918696162312749063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4492932612464108208499375 6739398918696162312749063)
          ·
            refine ⟨10109098378044243469123595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6739398918696162312749063 10109098378044243469123595)
            ·
              refine ⟨15163647567066365203685393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10109098378044243469123595 15163647567066365203685393)
              ·
                refine ⟨11372735675299773902764045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15163647567066365203685393 11372735675299773902764045)
                ·
                  refine ⟨4264775878237415213536517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11372735675299773902764045 4264775878237415213536517)
                  ·
                    refine ⟨799645477169515352538097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4264775878237415213536517 799645477169515352538097)
                    ·
                      refine ⟨599734107877136514403573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 799645477169515352538097 599734107877136514403573)
                      ·
                        rfl

theorem cell23_1167978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_1167978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167978 prefixEnd_1167978 := by exact prefixLift 1167978
  have htrace : WordTrace (prefixWord ++ tailWord_1167978) baseStart_1167978 baseEnd_1167978 := by
    simpa [prefixWord, tailWord_1167978, baseEnd_1167978] using wordTrace_append hprefix tailTrace_1167978
  have hstable : (prefixWord ++ tailWord_1167978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167978).length < 2 ^ (prefixWord ++ tailWord_1167978).sum := by decide
  have hdescent : baseEnd_1167978 < baseStart_1167978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167994 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7]
def baseStart_1167994 : Nat := 118140960795 + 1167994 * 2 ^ 59
def prefixEnd_1167994 : Nat := 4983230072969 + 3 ^ 40 * 1167994 * 2
def baseEnd_1167994 : Nat := 599742323567608451803499

theorem tailTrace_1167994 : CollatzResearch.WordTrace tailWord_1167994 prefixEnd_1167994 599742323567608451803499 := by
  unfold tailWord_1167994
  simp only [CollatzResearch.WordTrace]
  refine ⟨10650060232641172584773759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28400160620376460226063357 10650060232641172584773759)
  ·
    refine ⟨15975090348961758877160639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10650060232641172584773759 15975090348961758877160639)
    ·
      refine ⟨23962635523442638315740959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15975090348961758877160639 23962635523442638315740959)
      ·
        refine ⟨35943953285163957473611439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23962635523442638315740959 35943953285163957473611439)
        ·
          refine ⟨53915929927745936210417159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35943953285163957473611439 53915929927745936210417159)
          ·
            refine ⟨80873894891618904315625739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53915929927745936210417159 80873894891618904315625739)
            ·
              refine ⟨121310842337428356473438609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80873894891618904315625739 121310842337428356473438609)
              ·
                refine ⟨90983131753071267355078957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121310842337428356473438609 90983131753071267355078957)
                ·
                  refine ⟨34118674407401725258154609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90983131753071267355078957 34118674407401725258154609)
                  ·
                    refine ⟨25589005805551293943615957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34118674407401725258154609 25589005805551293943615957)
                    ·
                      refine ⟨599742323567608451803499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25589005805551293943615957 599742323567608451803499)
                      ·
                        rfl

theorem cell23_1167994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_1167994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1167994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1167994 prefixEnd_1167994 := by exact prefixLift 1167994
  have htrace : WordTrace (prefixWord ++ tailWord_1167994) baseStart_1167994 baseEnd_1167994 := by
    simpa [prefixWord, tailWord_1167994, baseEnd_1167994] using wordTrace_append hprefix tailTrace_1167994
  have hstable : (prefixWord ++ tailWord_1167994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167994).length < 2 ^ (prefixWord ++ tailWord_1167994).sum := by decide
  have hdescent : baseEnd_1167994 < baseStart_1167994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168001 : List Nat := [1, 2, 4, 2, 1, 1, 3, 2, 7]
def baseStart_1168001 : Nat := 118140960795 + 1168001 * 2 ^ 59
def prefixEnd_1168001 : Nat := 4983230072969 + 3 ^ 40 * 1168001 * 2
def baseEnd_1168001 : Nat := 66638435325798880490663

theorem tailTrace_1168001 : CollatzResearch.WordTrace tailWord_1168001 prefixEnd_1168001 66638435325798880490663 := by
  unfold tailWord_1168001
  simp only [CollatzResearch.WordTrace]
  refine ⟨42600496241539330534599857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28400330827692887023066571 42600496241539330534599857)
  ·
    refine ⟨31950372181154497900949893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42600496241539330534599857 31950372181154497900949893)
    ·
      refine ⟨5990694783966468356428105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31950372181154497900949893 5990694783966468356428105)
      ·
        refine ⟨4493021087974851267321079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5990694783966468356428105 4493021087974851267321079)
        ·
          refine ⟨6739531631962276900981619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4493021087974851267321079 6739531631962276900981619)
          ·
            refine ⟨10109297447943415351472429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6739531631962276900981619 10109297447943415351472429)
            ·
              refine ⟨3790986542978780756802161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10109297447943415351472429 3790986542978780756802161)
              ·
                refine ⟨2843239907234085567601621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3790986542978780756802161 2843239907234085567601621)
                ·
                  refine ⟨66638435325798880490663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2843239907234085567601621 66638435325798880490663)
                  ·
                    rfl

theorem cell23_1168001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 7].length) (baseStart_1168001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168001 prefixEnd_1168001 := by exact prefixLift 1168001
  have htrace : WordTrace (prefixWord ++ tailWord_1168001) baseStart_1168001 baseEnd_1168001 := by
    simpa [prefixWord, tailWord_1168001, baseEnd_1168001] using wordTrace_append hprefix tailTrace_1168001
  have hstable : (prefixWord ++ tailWord_1168001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168001).length < 2 ^ (prefixWord ++ tailWord_1168001).sum := by decide
  have hdescent : baseEnd_1168001 < baseStart_1168001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168028 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_1168028 : Nat := 118140960795 + 1168028 * 2 ^ 59
def prefixEnd_1168028 : Nat := 4983230072969 + 3 ^ 40 * 1168028 * 2
def baseEnd_1168028 : Nat := 599759781909861318778343

theorem tailTrace_1168028 : CollatzResearch.WordTrace tailWord_1168028 prefixEnd_1168028 599759781909861318778343 := by
  unfold tailWord_1168028
  simp only [CollatzResearch.WordTrace]
  refine ⟨21300740506220757072916369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28400987341627676097221825 21300740506220757072916369)
  ·
    refine ⟨15975555379665567804687277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21300740506220757072916369 15975555379665567804687277)
    ·
      refine ⟨5990833267374587926757729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15975555379665567804687277 5990833267374587926757729)
      ·
        refine ⟨4493124950530940945068297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5990833267374587926757729 4493124950530940945068297)
        ·
          refine ⟨3369843712898205708801223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4493124950530940945068297 3369843712898205708801223)
          ·
            refine ⟨5054765569347308563201835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3369843712898205708801223 5054765569347308563201835)
            ·
              refine ⟨7582148354020962844802753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5054765569347308563201835 7582148354020962844802753)
              ·
                refine ⟨5686611265515722133602065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7582148354020962844802753 5686611265515722133602065)
                ·
                  refine ⟨4264958449136791600201549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5686611265515722133602065 4264958449136791600201549)
                  ·
                    refine ⟨1599359418426296850075581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4264958449136791600201549 1599359418426296850075581)
                    ·
                      refine ⟨599759781909861318778343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1599359418426296850075581 599759781909861318778343)
                      ·
                        rfl

theorem cell23_1168028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_1168028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168028 prefixEnd_1168028 := by exact prefixLift 1168028
  have htrace : WordTrace (prefixWord ++ tailWord_1168028) baseStart_1168028 baseEnd_1168028 := by
    simpa [prefixWord, tailWord_1168028, baseEnd_1168028] using wordTrace_append hprefix tailTrace_1168028
  have hstable : (prefixWord ++ tailWord_1168028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168028).length < 2 ^ (prefixWord ++ tailWord_1168028).sum := by decide
  have hdescent : baseEnd_1168028 < baseStart_1168028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168046 : List Nat := [4, 1, 4, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_1168046 : Nat := 118140960795 + 1168046 * 2 ^ 59
def prefixEnd_1168046 : Nat := 4983230072969 + 3 ^ 40 * 1168046 * 2
def baseEnd_1168046 : Nat := 599769024561642248353261

theorem tailTrace_1168046 : CollatzResearch.WordTrace tailWord_1168046 prefixEnd_1168046 599769024561642248353261 := by
  unfold tailWord_1168046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5325267190797037902498499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28401425017584202146658661 5325267190797037902498499)
  ·
    refine ⟨7987900786195556853747749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5325267190797037902498499 7987900786195556853747749)
    ·
      refine ⟨1497731397411666910077703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7987900786195556853747749 1497731397411666910077703)
      ·
        refine ⟨2246597096117500365116555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1497731397411666910077703 2246597096117500365116555)
        ·
          refine ⟨3369895644176250547674833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2246597096117500365116555 3369895644176250547674833)
          ·
            refine ⟨2527421733132187910756125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3369895644176250547674833 2527421733132187910756125)
            ·
              refine ⟨947783149924570466533547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2527421733132187910756125 947783149924570466533547)
              ·
                refine ⟨1421674724886855699800321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 947783149924570466533547 1421674724886855699800321)
                ·
                  refine ⟨1066256043665141774850241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1421674724886855699800321 1066256043665141774850241)
                  ·
                    refine ⟨799692032748856331137681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1066256043665141774850241 799692032748856331137681)
                    ·
                      refine ⟨599769024561642248353261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 799692032748856331137681 599769024561642248353261)
                      ·
                        rfl

theorem cell23_1168046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_1168046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168046 prefixEnd_1168046 := by exact prefixLift 1168046
  have htrace : WordTrace (prefixWord ++ tailWord_1168046) baseStart_1168046 baseEnd_1168046 := by
    simpa [prefixWord, tailWord_1168046, baseEnd_1168046] using wordTrace_append hprefix tailTrace_1168046
  have hstable : (prefixWord ++ tailWord_1168046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168046).length < 2 ^ (prefixWord ++ tailWord_1168046).sum := by decide
  have hdescent : baseEnd_1168046 < baseStart_1168046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168051 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 4]
def baseStart_1168051 : Nat := 118140960795 + 1168051 * 2 ^ 59
def prefixEnd_1168051 : Nat := 4983230072969 + 3 ^ 40 * 1168051 * 2
def baseEnd_1168051 : Nat := 599771591964914728790737

theorem tailTrace_1168051 : CollatzResearch.WordTrace tailWord_1168051 prefixEnd_1168051 599771591964914728790737 := by
  unfold tailWord_1168051
  simp only [CollatzResearch.WordTrace]
  refine ⟨42602319891358189073920007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28401546594238792715946671 42602319891358189073920007)
  ·
    refine ⟨63903479837037283610880011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42602319891358189073920007 63903479837037283610880011)
    ·
      refine ⟨95855219755555925416320017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63903479837037283610880011 95855219755555925416320017)
      ·
        refine ⟨71891414816666944062240013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95855219755555925416320017 71891414816666944062240013)
        ·
          refine ⟨26959280556250104023340005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71891414816666944062240013 26959280556250104023340005)
          ·
            refine ⟨5054865104296894504376251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26959280556250104023340005 5054865104296894504376251)
            ·
              refine ⟨7582297656445341756564377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5054865104296894504376251 7582297656445341756564377)
              ·
                refine ⟨5686723242334006317423283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7582297656445341756564377 5686723242334006317423283)
                ·
                  refine ⟨8530084863501009476134925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5686723242334006317423283 8530084863501009476134925)
                  ·
                    refine ⟨3198781823812878553550597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8530084863501009476134925 3198781823812878553550597)
                    ·
                      refine ⟨599771591964914728790737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3198781823812878553550597 599771591964914728790737)
                      ·
                        rfl

theorem cell23_1168051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 4].length) (baseStart_1168051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168051 prefixEnd_1168051 := by exact prefixLift 1168051
  have htrace : WordTrace (prefixWord ++ tailWord_1168051) baseStart_1168051 baseEnd_1168051 := by
    simpa [prefixWord, tailWord_1168051, baseEnd_1168051] using wordTrace_append hprefix tailTrace_1168051
  have hstable : (prefixWord ++ tailWord_1168051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168051).length < 2 ^ (prefixWord ++ tailWord_1168051).sum := by decide
  have hdescent : baseEnd_1168051 < baseStart_1168051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168068 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_1168068 : Nat := 118140960795 + 1168068 * 2 ^ 59
def prefixEnd_1168068 : Nat := 4983230072969 + 3 ^ 40 * 1168068 * 2
def baseEnd_1168068 : Nat := 599780321136041162278159

theorem tailTrace_1168068 : CollatzResearch.WordTrace tailWord_1168068 prefixEnd_1168068 599780321136041162278159 := by
  unfold tailWord_1168068
  simp only [CollatzResearch.WordTrace]
  refine ⟨21301469966148300488644429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28401959954864400651525905 21301469966148300488644429)
  ·
    refine ⟨7988051237305612683241661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21301469966148300488644429 7988051237305612683241661)
    ·
      refine ⟨2995519213989604756215623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7988051237305612683241661 2995519213989604756215623)
      ·
        refine ⟨4493278820984407134323435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2995519213989604756215623 4493278820984407134323435)
        ·
          refine ⟨6739918231476610701485153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4493278820984407134323435 6739918231476610701485153)
          ·
            refine ⟨5054938673607458026113865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6739918231476610701485153 5054938673607458026113865)
            ·
              refine ⟨3791204005205593519585399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5054938673607458026113865 3791204005205593519585399)
              ·
                refine ⟨5686806007808390279378099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3791204005205593519585399 5686806007808390279378099)
                ·
                  refine ⟨8530209011712585419067149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5686806007808390279378099 8530209011712585419067149)
                  ·
                    refine ⟨3198828379392219532150181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8530209011712585419067149 3198828379392219532150181)
                    ·
                      refine ⟨599780321136041162278159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3198828379392219532150181 599780321136041162278159)
                      ·
                        rfl

theorem cell23_1168068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_1168068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168068 prefixEnd_1168068 := by exact prefixLift 1168068
  have htrace : WordTrace (prefixWord ++ tailWord_1168068) baseStart_1168068 baseEnd_1168068 := by
    simpa [prefixWord, tailWord_1168068, baseEnd_1168068] using wordTrace_append hprefix tailTrace_1168068
  have hstable : (prefixWord ++ tailWord_1168068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168068).length < 2 ^ (prefixWord ++ tailWord_1168068).sum := by decide
  have hdescent : baseEnd_1168068 < baseStart_1168068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168088 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 4, 2, 3]
def baseStart_1168088 : Nat := 118140960795 + 1168088 * 2 ^ 59
def prefixEnd_1168088 : Nat := 4983230072969 + 3 ^ 40 * 1168088 * 2
def baseEnd_1168088 : Nat := 599790590749131084028067

theorem tailTrace_1168088 : CollatzResearch.WordTrace tailWord_1168088 prefixEnd_1168088 599790590749131084028067 := by
  unfold tailWord_1168088
  simp only [CollatzResearch.WordTrace]
  refine ⟨21301834696112072196508459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28402446261482762928677945 21301834696112072196508459)
  ·
    refine ⟨31952752044168108294762689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21301834696112072196508459 31952752044168108294762689)
    ·
      refine ⟨23964564033126081221072017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31952752044168108294762689 23964564033126081221072017)
      ·
        refine ⟨17973423024844560915804013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23964564033126081221072017 17973423024844560915804013)
        ·
          refine ⟨6740033634316710343426505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17973423024844560915804013 6740033634316710343426505)
          ·
            refine ⟨5055025225737532757569879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6740033634316710343426505 5055025225737532757569879)
            ·
              refine ⟨7582537838606299136354819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5055025225737532757569879 7582537838606299136354819)
              ·
                refine ⟨11373806757909448704532229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7582537838606299136354819 11373806757909448704532229)
                ·
                  refine ⟨2132588767108021632099793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11373806757909448704532229 2132588767108021632099793)
                  ·
                    refine ⟨1599441575331016224074845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2132588767108021632099793 1599441575331016224074845)
                    ·
                      refine ⟨599790590749131084028067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1599441575331016224074845 599790590749131084028067)
                      ·
                        rfl

theorem cell23_1168088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_1168088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168088 prefixEnd_1168088 := by exact prefixLift 1168088
  have htrace : WordTrace (prefixWord ++ tailWord_1168088) baseStart_1168088 baseEnd_1168088 := by
    simpa [prefixWord, tailWord_1168088, baseEnd_1168088] using wordTrace_append hprefix tailTrace_1168088
  have hstable : (prefixWord ++ tailWord_1168088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168088).length < 2 ^ (prefixWord ++ tailWord_1168088).sum := by decide
  have hdescent : baseEnd_1168088 < baseStart_1168088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168095 : List Nat := [1, 1, 2, 3, 2, 5, 1, 1, 3, 4]
def baseStart_1168095 : Nat := 118140960795 + 1168095 * 2 ^ 59
def prefixEnd_1168095 : Nat := 4983230072969 + 3 ^ 40 * 1168095 * 2
def baseEnd_1168095 : Nat := 199931395037904185546845

theorem tailTrace_1168095 : CollatzResearch.WordTrace tailWord_1168095 prefixEnd_1168095 199931395037904185546845 := by
  unfold tailWord_1168095
  simp only [CollatzResearch.WordTrace]
  refine ⟨42603924703198784588521739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28402616468799189725681159 42603924703198784588521739)
  ·
    refine ⟨63905887054798176882782609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42603924703198784588521739 63905887054798176882782609)
    ·
      refine ⟨47929415291098632662086957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63905887054798176882782609 47929415291098632662086957)
      ·
        refine ⟨17973530734161987248282609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47929415291098632662086957 17973530734161987248282609)
        ·
          refine ⟨13480148050621490436211957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17973530734161987248282609 13480148050621490436211957)
          ·
            refine ⟨1263763879745764728394871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13480148050621490436211957 1263763879745764728394871)
            ·
              refine ⟨1895645819618647092592307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1263763879745764728394871 1895645819618647092592307)
              ·
                refine ⟨2843468729427970638888461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1895645819618647092592307 2843468729427970638888461)
                ·
                  refine ⟨1066300773535488989583173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2843468729427970638888461 1066300773535488989583173)
                  ·
                    refine ⟨199931395037904185546845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1066300773535488989583173 199931395037904185546845)
                    ·
                      rfl

theorem cell23_1168095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 4].length) (baseStart_1168095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168095 prefixEnd_1168095 := by exact prefixLift 1168095
  have htrace : WordTrace (prefixWord ++ tailWord_1168095) baseStart_1168095 baseEnd_1168095 := by
    simpa [prefixWord, tailWord_1168095, baseEnd_1168095] using wordTrace_append hprefix tailTrace_1168095
  have hstable : (prefixWord ++ tailWord_1168095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168095).length < 2 ^ (prefixWord ++ tailWord_1168095).sum := by decide
  have hdescent : baseEnd_1168095 < baseStart_1168095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168145 : List Nat := [1, 2, 2, 1, 1, 3, 4, 2, 2, 3, 2]
def baseStart_1168145 : Nat := 118140960795 + 1168145 * 2 ^ 59
def prefixEnd_1168145 : Nat := 4983230072969 + 3 ^ 40 * 1168145 * 2
def baseEnd_1168145 : Nat := 599819859146437361015305

theorem tailTrace_1168145 : CollatzResearch.WordTrace tailWord_1168145 prefixEnd_1168145 599819859146437361015305 := by
  unfold tailWord_1168145
  simp only [CollatzResearch.WordTrace]
  refine ⟨42605748353017643127841889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28403832235345095418561259 42605748353017643127841889)
  ·
    refine ⟨31954311264763232345881417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42605748353017643127841889 31954311264763232345881417)
    ·
      refine ⟨23965733448572424259411063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31954311264763232345881417 23965733448572424259411063)
      ·
        refine ⟨35948600172858636389116595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23965733448572424259411063 35948600172858636389116595)
        ·
          refine ⟨53922900259287954583674893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35948600172858636389116595 53922900259287954583674893)
          ·
            refine ⟨20221087597232982968878085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53922900259287954583674893 20221087597232982968878085)
            ·
              refine ⟨3791453924481184306664641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20221087597232982968878085 3791453924481184306664641)
              ·
                refine ⟨2843590443360888229998481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3791453924481184306664641 2843590443360888229998481)
                ·
                  refine ⟨2132692832520666172498861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2843590443360888229998481 2132692832520666172498861)
                  ·
                    refine ⟨799759812195249814687073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2132692832520666172498861 799759812195249814687073)
                    ·
                      refine ⟨599819859146437361015305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 799759812195249814687073 599819859146437361015305)
                      ·
                        rfl

theorem cell23_1168145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 3, 2].length) (baseStart_1168145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168145 prefixEnd_1168145 := by exact prefixLift 1168145
  have htrace : WordTrace (prefixWord ++ tailWord_1168145) baseStart_1168145 baseEnd_1168145 := by
    simpa [prefixWord, tailWord_1168145, baseEnd_1168145] using wordTrace_append hprefix tailTrace_1168145
  have hstable : (prefixWord ++ tailWord_1168145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168145).length < 2 ^ (prefixWord ++ tailWord_1168145).sum := by decide
  have hdescent : baseEnd_1168145 < baseStart_1168145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168189 : List Nat := [1, 4, 1, 4, 2, 2, 2, 1, 1, 5]
def baseStart_1168189 : Nat := 118140960795 + 1168189 * 2 ^ 59
def prefixEnd_1168189 : Nat := 4983230072969 + 3 ^ 40 * 1168189 * 2
def baseEnd_1168189 : Nat := 199947484098411729621701

theorem tailTrace_1168189 : CollatzResearch.WordTrace tailWord_1168189 prefixEnd_1168189 199947484098411729621701 := by
  unfold tailWord_1168189
  simp only [CollatzResearch.WordTrace]
  refine ⟨42607353164858238642443621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28404902109905492428295747 42607353164858238642443621)
  ·
    refine ⟨7988878718410919745458179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42607353164858238642443621 7988878718410919745458179)
    ·
      refine ⟨11983318077616379618187269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7988878718410919745458179 11983318077616379618187269)
      ·
        refine ⟨2246872139553071178410113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11983318077616379618187269 2246872139553071178410113)
        ·
          refine ⟨1685154104664803383807585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2246872139553071178410113 1685154104664803383807585)
          ·
            refine ⟨1263865578498602537855689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1685154104664803383807585 1263865578498602537855689)
            ·
              refine ⟨947899183873951903391767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1263865578498602537855689 947899183873951903391767)
              ·
                refine ⟨1421848775810927855087651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 947899183873951903391767 1421848775810927855087651)
                ·
                  refine ⟨2132773163716391782631477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421848775810927855087651 2132773163716391782631477)
                  ·
                    refine ⟨199947484098411729621701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2132773163716391782631477 199947484098411729621701)
                    ·
                      rfl

theorem cell23_1168189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_1168189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168189 prefixEnd_1168189 := by exact prefixLift 1168189
  have htrace : WordTrace (prefixWord ++ tailWord_1168189) baseStart_1168189 baseEnd_1168189 := by
    simpa [prefixWord, tailWord_1168189, baseEnd_1168189] using wordTrace_append hprefix tailTrace_1168189
  have hstable : (prefixWord ++ tailWord_1168189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168189).length < 2 ^ (prefixWord ++ tailWord_1168189).sum := by decide
  have hdescent : baseEnd_1168189 < baseStart_1168189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168195 : List Nat := [1, 1, 1, 3, 1, 4, 3, 3, 1, 2, 3]
def baseStart_1168195 : Nat := 118140960795 + 1168195 * 2 ^ 59
def prefixEnd_1168195 : Nat := 4983230072969 + 3 ^ 40 * 1168195 * 2
def baseEnd_1168195 : Nat := 599845533179162165390075

theorem tailTrace_1168195 : CollatzResearch.WordTrace tailWord_1168195 prefixEnd_1168195 599845533179162165390075 := by
  unfold tailWord_1168195
  simp only [CollatzResearch.WordTrace]
  refine ⟨42607572002836501667162039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28405048001891001111441359 42607572002836501667162039)
  ·
    refine ⟨63911358004254752500743059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42607572002836501667162039 63911358004254752500743059)
    ·
      refine ⟨95867037006382128751114589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63911358004254752500743059 95867037006382128751114589)
      ·
        refine ⟨35950138877393298281667971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95867037006382128751114589 35950138877393298281667971)
        ·
          refine ⟨53925208316089947422501957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35950138877393298281667971 53925208316089947422501957)
          ·
            refine ⟨10110976559266865141719117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53925208316089947422501957 10110976559266865141719117)
            ·
              refine ⟨3791616209725074428144669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10110976559266865141719117 3791616209725074428144669)
              ·
                refine ⟨1421856078646902910554251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3791616209725074428144669 1421856078646902910554251)
                ·
                  refine ⟨2132784117970354365831377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421856078646902910554251 2132784117970354365831377)
                  ·
                    refine ⟨1599588088477765774373533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2132784117970354365831377 1599588088477765774373533)
                    ·
                      refine ⟨599845533179162165390075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1599588088477765774373533 599845533179162165390075)
                      ·
                        rfl

theorem cell23_1168195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 2, 3].length) (baseStart_1168195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168195 prefixEnd_1168195 := by exact prefixLift 1168195
  have htrace : WordTrace (prefixWord ++ tailWord_1168195) baseStart_1168195 baseEnd_1168195 := by
    simpa [prefixWord, tailWord_1168195, baseEnd_1168195] using wordTrace_append hprefix tailTrace_1168195
  have hstable : (prefixWord ++ tailWord_1168195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168195).length < 2 ^ (prefixWord ++ tailWord_1168195).sum := by decide
  have hdescent : baseEnd_1168195 < baseStart_1168195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168208 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 3]
def baseStart_1168208 : Nat := 118140960795 + 1168208 * 2 ^ 59
def prefixEnd_1168208 : Nat := 4983230072969 + 3 ^ 40 * 1168208 * 2
def baseEnd_1168208 : Nat := 599852208427670614527515

theorem tailTrace_1168208 : CollatzResearch.WordTrace tailWord_1168208 prefixEnd_1168208 599852208427670614527515 := by
  unfold tailWord_1168208
  simp only [CollatzResearch.WordTrace]
  refine ⟨21304023075894702443692639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28405364101192936591590185 21304023075894702443692639)
  ·
    refine ⟨31956034613842053665538959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21304023075894702443692639 31956034613842053665538959)
    ·
      refine ⟨47934051920763080498308439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31956034613842053665538959 47934051920763080498308439)
      ·
        refine ⟨71901077881144620747462659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47934051920763080498308439 71901077881144620747462659)
        ·
          refine ⟨107851616821716931121193989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71901077881144620747462659 107851616821716931121193989)
          ·
            refine ⟨20222178154071924585223873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107851616821716931121193989 20222178154071924585223873)
            ·
              refine ⟨15166633615553943438917905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20222178154071924585223873 15166633615553943438917905)
              ·
                refine ⟨11374975211665457579188429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15166633615553943438917905 11374975211665457579188429)
                ·
                  refine ⟨4265615704374546592195661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11374975211665457579188429 4265615704374546592195661)
                  ·
                    refine ⟨1599605889140454972073373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4265615704374546592195661 1599605889140454972073373)
                    ·
                      refine ⟨599852208427670614527515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1599605889140454972073373 599852208427670614527515)
                      ·
                        rfl

theorem cell23_1168208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 3].length) (baseStart_1168208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168208 prefixEnd_1168208 := by exact prefixLift 1168208
  have htrace : WordTrace (prefixWord ++ tailWord_1168208) baseStart_1168208 baseEnd_1168208 := by
    simpa [prefixWord, tailWord_1168208, baseEnd_1168208] using wordTrace_append hprefix tailTrace_1168208
  have hstable : (prefixWord ++ tailWord_1168208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168208).length < 2 ^ (prefixWord ++ tailWord_1168208).sum := by decide
  have hdescent : baseEnd_1168208 < baseStart_1168208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168209 : List Nat := [1, 2, 2, 1, 6, 1, 2, 1, 3, 2, 2]
def baseStart_1168209 : Nat := 118140960795 + 1168209 * 2 ^ 59
def prefixEnd_1168209 : Nat := 4983230072969 + 3 ^ 40 * 1168209 * 2
def baseEnd_1168209 : Nat := 599852721908325110615011

theorem tailTrace_1168209 : CollatzResearch.WordTrace tailWord_1168209 prefixEnd_1168209 599852721908325110615011 := by
  unfold tailWord_1168209
  simp only [CollatzResearch.WordTrace]
  refine ⟨42608082624785782058171681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28405388416523854705447787 42608082624785782058171681)
  ·
    refine ⟨31956061968589336543628761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42608082624785782058171681 31956061968589336543628761)
    ·
      refine ⟨23967046476442002407721571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31956061968589336543628761 23967046476442002407721571)
      ·
        refine ⟨35950569714663003611582357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23967046476442002407721571 35950569714663003611582357)
        ·
          refine ⟨1685182955374828294292923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35950569714663003611582357 1685182955374828294292923)
          ·
            refine ⟨2527774433062242441439385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1685182955374828294292923 2527774433062242441439385)
            ·
              refine ⟨1895830824796681831079539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2527774433062242441439385 1895830824796681831079539)
              ·
                refine ⟨2843746237195022746619309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1895830824796681831079539 2843746237195022746619309)
                ·
                  refine ⟨1066404838948133529982241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2843746237195022746619309 1066404838948133529982241)
                  ·
                    refine ⟨799803629211100147486681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1066404838948133529982241 799803629211100147486681)
                    ·
                      refine ⟨599852721908325110615011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 799803629211100147486681 599852721908325110615011)
                      ·
                        rfl

theorem cell23_1168209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 2, 2].length) (baseStart_1168209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168209 prefixEnd_1168209 := by exact prefixLift 1168209
  have htrace : WordTrace (prefixWord ++ tailWord_1168209) baseStart_1168209 baseEnd_1168209 := by
    simpa [prefixWord, tailWord_1168209, baseEnd_1168209] using wordTrace_append hprefix tailTrace_1168209
  have hstable : (prefixWord ++ tailWord_1168209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168209).length < 2 ^ (prefixWord ++ tailWord_1168209).sum := by decide
  have hdescent : baseEnd_1168209 < baseStart_1168209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168211 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 1, 9]
def baseStart_1168211 : Nat := 118140960795 + 1168211 * 2 ^ 59
def prefixEnd_1168211 : Nat := 4983230072969 + 3 ^ 40 * 1168211 * 2
def baseEnd_1168211 : Nat := 199951249623211367596667

theorem tailTrace_1168211 : CollatzResearch.WordTrace tailWord_1168211 prefixEnd_1168211 199951249623211367596667 := by
  unfold tailWord_1168211
  simp only [CollatzResearch.WordTrace]
  refine ⟨42608155570778536399744487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28405437047185690933162991 42608155570778536399744487)
  ·
    refine ⟨63912233356167804599616731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42608155570778536399744487 63912233356167804599616731)
    ·
      refine ⟨95868350034251706899425097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63912233356167804599616731 95868350034251706899425097)
      ·
        refine ⟨71901262525688780174568823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95868350034251706899425097 71901262525688780174568823)
        ·
          refine ⟨107851893788533170261853235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71901262525688780174568823 107851893788533170261853235)
          ·
            refine ⟨161777840682799755392779853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107851893788533170261853235 161777840682799755392779853)
            ·
              refine ⟨60666690256049908272292445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161777840682799755392779853 60666690256049908272292445)
              ·
                refine ⟨22750008846018715602109667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60666690256049908272292445 22750008846018715602109667)
                ·
                  refine ⟨34125013269028073403164501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22750008846018715602109667 34125013269028073403164501)
                  ·
                    refine ⟨199951249623211367596667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 34125013269028073403164501 199951249623211367596667)
                    ·
                      rfl

theorem cell23_1168211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 9].length) (baseStart_1168211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168211 prefixEnd_1168211 := by exact prefixLift 1168211
  have htrace : WordTrace (prefixWord ++ tailWord_1168211) baseStart_1168211 baseEnd_1168211 := by
    simpa [prefixWord, tailWord_1168211, baseEnd_1168211] using wordTrace_append hprefix tailTrace_1168211
  have hstable : (prefixWord ++ tailWord_1168211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168211).length < 2 ^ (prefixWord ++ tailWord_1168211).sum := by decide
  have hdescent : baseEnd_1168211 < baseStart_1168211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168235 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 3, 3, 2]
def baseStart_1168235 : Nat := 118140960795 + 1168235 * 2 ^ 59
def prefixEnd_1168235 : Nat := 4983230072969 + 3 ^ 40 * 1168235 * 2
def baseEnd_1168235 : Nat := 599866072405342008889891

theorem tailTrace_1168235 : CollatzResearch.WordTrace tailWord_1168235 prefixEnd_1168235 599866072405342008889891 := by
  unfold tailWord_1168235
  simp only [CollatzResearch.WordTrace]
  refine ⟨42609030922691588498618159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28406020615127725665745439 42609030922691588498618159)
  ·
    refine ⟨63913546384037382747927239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42609030922691588498618159 63913546384037382747927239)
    ·
      refine ⟨95870319576056074121890859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63913546384037382747927239 95870319576056074121890859)
      ·
        refine ⟨143805479364084111182836289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95870319576056074121890859 143805479364084111182836289)
        ·
          refine ⟨107854109523063083387127217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143805479364084111182836289 107854109523063083387127217)
          ·
            refine ⟨80890582142297312540345413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107854109523063083387127217 80890582142297312540345413)
            ·
              refine ⟨15166984151680746101314765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80890582142297312540345413 15166984151680746101314765)
              ·
                refine ⟨5687619056880279787993037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15166984151680746101314765 5687619056880279787993037)
                ·
                  refine ⟨2132857146330104920497389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5687619056880279787993037 2132857146330104920497389)
                  ·
                    refine ⟨799821429873789345186521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2132857146330104920497389 799821429873789345186521)
                    ·
                      refine ⟨599866072405342008889891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 799821429873789345186521 599866072405342008889891)
                      ·
                        rfl

theorem cell23_1168235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 3, 2].length) (baseStart_1168235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168235 prefixEnd_1168235 := by exact prefixLift 1168235
  have htrace : WordTrace (prefixWord ++ tailWord_1168235) baseStart_1168235 baseEnd_1168235 := by
    simpa [prefixWord, tailWord_1168235, baseEnd_1168235] using wordTrace_append hprefix tailTrace_1168235
  have hstable : (prefixWord ++ tailWord_1168235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168235).length < 2 ^ (prefixWord ++ tailWord_1168235).sum := by decide
  have hdescent : baseEnd_1168235 < baseStart_1168235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168288 : List Nat := [2, 1, 1, 4, 1, 1, 2, 4, 7]
def baseStart_1168288 : Nat := 118140960795 + 1168288 * 2 ^ 59
def prefixEnd_1168288 : Nat := 4983230072969 + 3 ^ 40 * 1168288 * 2
def baseEnd_1168288 : Nat := 66654809653336700169683

theorem tailTrace_1168288 : CollatzResearch.WordTrace tailWord_1168288 prefixEnd_1168288 66654809653336700169683 := by
  unfold tailWord_1168288
  simp only [CollatzResearch.WordTrace]
  refine ⟨21305481995749789275148759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28407309327666385700198345 21305481995749789275148759)
  ·
    refine ⟨31958222993624683912723139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21305481995749789275148759 31958222993624683912723139)
    ·
      refine ⟨47937334490437025869084709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31958222993624683912723139 47937334490437025869084709)
      ·
        refine ⟨8988250216956942350453383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47937334490437025869084709 8988250216956942350453383)
        ·
          refine ⟨13482375325435413525680075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8988250216956942350453383 13482375325435413525680075)
          ·
            refine ⟨20223562988153120288520113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13482375325435413525680075 20223562988153120288520113)
            ·
              refine ⟨15167672241114840216390085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20223562988153120288520113 15167672241114840216390085)
              ·
                refine ⟨2843938545209032540573141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15167672241114840216390085 2843938545209032540573141)
                ·
                  refine ⟨66654809653336700169683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2843938545209032540573141 66654809653336700169683)
                  ·
                    rfl

theorem cell23_1168288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 7].length) (baseStart_1168288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168288 prefixEnd_1168288 := by exact prefixLift 1168288
  have htrace : WordTrace (prefixWord ++ tailWord_1168288) baseStart_1168288 baseEnd_1168288 := by
    simpa [prefixWord, tailWord_1168288, baseEnd_1168288] using wordTrace_append hprefix tailTrace_1168288
  have hstable : (prefixWord ++ tailWord_1168288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168288).length < 2 ^ (prefixWord ++ tailWord_1168288).sum := by decide
  have hdescent : baseEnd_1168288 < baseStart_1168288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168310 : List Nat := [5, 1, 4, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_1168310 : Nat := 118140960795 + 1168310 * 2 ^ 59
def prefixEnd_1168310 : Nat := 4983230072969 + 3 ^ 40 * 1168310 * 2
def baseEnd_1168310 : Nat := 599904583454429215452047

theorem tailTrace_1168310 : CollatzResearch.WordTrace tailWord_1168310 prefixEnd_1168310 599904583454429215452047 := by
  unfold tailWord_1168310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2663235399838742269224899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28407844264946584205065589 2663235399838742269224899)
  ·
    refine ⟨3994853099758113403837349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2663235399838742269224899 3994853099758113403837349)
    ·
      refine ⟨749034956204646263219503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3994853099758113403837349 749034956204646263219503)
      ·
        refine ⟨1123552434306969394829255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 749034956204646263219503 1123552434306969394829255)
        ·
          refine ⟨1685328651460454092243883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1123552434306969394829255 1685328651460454092243883)
          ·
            refine ⟨2527992977190681138365825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1685328651460454092243883 2527992977190681138365825)
            ·
              refine ⟨1895994732893010853774369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2527992977190681138365825 1895994732893010853774369)
              ·
                refine ⟨1421996049669758140330777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1895994732893010853774369 1421996049669758140330777)
                ·
                  refine ⟨1066497037252318605248083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1421996049669758140330777 1066497037252318605248083)
                  ·
                    refine ⟨1599745555878477907872125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1066497037252318605248083 1599745555878477907872125)
                    ·
                      refine ⟨599904583454429215452047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1599745555878477907872125 599904583454429215452047)
                      ·
                        rfl

theorem cell23_1168310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_1168310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168310 prefixEnd_1168310 := by exact prefixLift 1168310
  have htrace : WordTrace (prefixWord ++ tailWord_1168310) baseStart_1168310 baseEnd_1168310 := by
    simpa [prefixWord, tailWord_1168310, baseEnd_1168310] using wordTrace_append hprefix tailTrace_1168310
  have hstable : (prefixWord ++ tailWord_1168310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168310).length < 2 ^ (prefixWord ++ tailWord_1168310).sum := by decide
  have hdescent : baseEnd_1168310 < baseStart_1168310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168355 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 4]
def baseStart_1168355 : Nat := 118140960795 + 1168355 * 2 ^ 59
def prefixEnd_1168355 : Nat := 4983230072969 + 3 ^ 40 * 1168355 * 2
def baseEnd_1168355 : Nat := 599927690083881539389339

theorem tailTrace_1168355 : CollatzResearch.WordTrace tailWord_1168355 prefixEnd_1168355 599927690083881539389339 := by
  unfold tailWord_1168355
  simp only [CollatzResearch.WordTrace]
  refine ⟨42613407682256848992986519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28408938454837899328657679 42613407682256848992986519)
  ·
    refine ⟨63920111523385273489479779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42613407682256848992986519 63920111523385273489479779)
    ·
      refine ⟨95880167285077910234219669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63920111523385273489479779 95880167285077910234219669)
      ·
        refine ⟨4494382841488027042229047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 95880167285077910234219669 4494382841488027042229047)
        ·
          refine ⟨6741574262232040563343571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4494382841488027042229047 6741574262232040563343571)
          ·
            refine ⟨10112361393348060845015357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6741574262232040563343571 10112361393348060845015357)
            ·
              refine ⟨3792135522505522816880759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10112361393348060845015357 3792135522505522816880759)
              ·
                refine ⟨5688203283758284225321139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3792135522505522816880759 5688203283758284225321139)
                ·
                  refine ⟨8532304925637426337981709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5688203283758284225321139 8532304925637426337981709)
                  ·
                    refine ⟨3199614347114034876743141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8532304925637426337981709 3199614347114034876743141)
                    ·
                      refine ⟨599927690083881539389339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3199614347114034876743141 599927690083881539389339)
                      ·
                        rfl

theorem cell23_1168355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_1168355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168355 prefixEnd_1168355 := by exact prefixLift 1168355
  have htrace : WordTrace (prefixWord ++ tailWord_1168355) baseStart_1168355 baseEnd_1168355 := by
    simpa [prefixWord, tailWord_1168355, baseEnd_1168355] using wordTrace_append hprefix tailTrace_1168355
  have hstable : (prefixWord ++ tailWord_1168355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168355).length < 2 ^ (prefixWord ++ tailWord_1168355).sum := by decide
  have hdescent : baseEnd_1168355 < baseStart_1168355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168446 : List Nat := [4, 2, 1, 3, 1, 3, 2, 1, 6]
def baseStart_1168446 : Nat := 118140960795 + 1168446 * 2 ^ 59
def prefixEnd_1168446 : Nat := 4983230072969 + 3 ^ 40 * 1168446 * 2
def baseEnd_1168446 : Nat := 66663824091493409261269

theorem tailTrace_1168446 : CollatzResearch.WordTrace tailWord_1168446 prefixEnd_1168446 66663824091493409261269 := by
  unfold tailWord_1168446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5327090840615896441818649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28411151149951447689699461 5327090840615896441818649)
  ·
    refine ⟨3995318130461922331363987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5327090840615896441818649 3995318130461922331363987)
    ·
      refine ⟨5992977195692883497045981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3995318130461922331363987 5992977195692883497045981)
      ·
        refine ⟨2247366448384831311392243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5992977195692883497045981 2247366448384831311392243)
        ·
          refine ⟨3371049672577246967088365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2247366448384831311392243 3371049672577246967088365)
          ·
            refine ⟨1264143627216467612658137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3371049672577246967088365 1264143627216467612658137)
            ·
              refine ⟨948107720412350709493603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1264143627216467612658137 948107720412350709493603)
              ·
                refine ⟨1422161580618526064240405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 948107720412350709493603 1422161580618526064240405)
                ·
                  refine ⟨66663824091493409261269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1422161580618526064240405 66663824091493409261269)
                  ·
                    rfl

theorem cell23_1168446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_1168446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168446 prefixEnd_1168446 := by exact prefixLift 1168446
  have htrace : WordTrace (prefixWord ++ tailWord_1168446) baseStart_1168446 baseEnd_1168446 := by
    simpa [prefixWord, tailWord_1168446, baseEnd_1168446] using wordTrace_append hprefix tailTrace_1168446
  have hstable : (prefixWord ++ tailWord_1168446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168446).length < 2 ^ (prefixWord ++ tailWord_1168446).sum := by decide
  have hdescent : baseEnd_1168446 < baseStart_1168446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168462 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4]
def baseStart_1168462 : Nat := 118140960795 + 1168462 * 2 ^ 59
def prefixEnd_1168462 : Nat := 4983230072969 + 3 ^ 40 * 1168462 * 2
def baseEnd_1168462 : Nat := 599982632513912620751347

theorem tailTrace_1168462 : CollatzResearch.WordTrace tailWord_1168462 prefixEnd_1168462 599982632513912620751347 := by
  unfold tailWord_1168462
  simp only [CollatzResearch.WordTrace]
  refine ⟨5327163786608650783391455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28411540195246137511421093 5327163786608650783391455)
  ·
    refine ⟨7990745679912976175087183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5327163786608650783391455 7990745679912976175087183)
    ·
      refine ⟨11986118519869464262630775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7990745679912976175087183 11986118519869464262630775)
      ·
        refine ⟨17979177779804196393946163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11986118519869464262630775 17979177779804196393946163)
        ·
          refine ⟨26968766669706294590919245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17979177779804196393946163 26968766669706294590919245)
          ·
            refine ⟨10113287501139860471594717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26968766669706294590919245 10113287501139860471594717)
            ·
              refine ⟨3792482812927447676848019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10113287501139860471594717 3792482812927447676848019)
              ·
                refine ⟨5688724219391171515272029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3792482812927447676848019 5688724219391171515272029)
                ·
                  refine ⟨2133271582271689318227011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5688724219391171515272029 2133271582271689318227011)
                  ·
                    refine ⟨3199907373407533977340517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2133271582271689318227011 3199907373407533977340517)
                    ·
                      refine ⟨599982632513912620751347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3199907373407533977340517 599982632513912620751347)
                      ·
                        rfl

theorem cell23_1168462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_1168462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168462 prefixEnd_1168462 := by exact prefixLift 1168462
  have htrace : WordTrace (prefixWord ++ tailWord_1168462) baseStart_1168462 baseEnd_1168462 := by
    simpa [prefixWord, tailWord_1168462, baseEnd_1168462] using wordTrace_append hprefix tailTrace_1168462
  have hstable : (prefixWord ++ tailWord_1168462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168462).length < 2 ^ (prefixWord ++ tailWord_1168462).sum := by decide
  have hdescent : baseEnd_1168462 < baseStart_1168462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168465 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 3, 1, 5]
def baseStart_1168465 : Nat := 118140960795 + 1168465 * 2 ^ 59
def prefixEnd_1168465 : Nat := 4983230072969 + 3 ^ 40 * 1168465 * 2
def baseEnd_1168465 : Nat := 599984172955876109013833

theorem tailTrace_1168465 : CollatzResearch.WordTrace tailWord_1168465 prefixEnd_1168465 599984172955876109013833 := by
  unfold tailWord_1168465
  simp only [CollatzResearch.WordTrace]
  refine ⟨42617419711858337779490849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28411613141238891852993899 42617419711858337779490849)
  ·
    refine ⟨31963064783893753334618137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42617419711858337779490849 31963064783893753334618137)
    ·
      refine ⟨23972298587920315000963603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31963064783893753334618137 23972298587920315000963603)
      ·
        refine ⟨35958447881880472501445405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23972298587920315000963603 35958447881880472501445405)
        ·
          refine ⟨13484417955705177188042027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35958447881880472501445405 13484417955705177188042027)
          ·
            refine ⟨20226626933557765782063041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13484417955705177188042027 20226626933557765782063041)
            ·
              refine ⟨15169970200168324336547281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20226626933557765782063041 15169970200168324336547281)
              ·
                refine ⟨11377477650126243252410461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15169970200168324336547281 11377477650126243252410461)
                ·
                  refine ⟨4266554118797341219653923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11377477650126243252410461 4266554118797341219653923)
                  ·
                    refine ⟨6399831178196011829480885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4266554118797341219653923 6399831178196011829480885)
                    ·
                      refine ⟨599984172955876109013833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6399831178196011829480885 599984172955876109013833)
                      ·
                        rfl

theorem cell23_1168465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_1168465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168465 prefixEnd_1168465 := by exact prefixLift 1168465
  have htrace : WordTrace (prefixWord ++ tailWord_1168465) baseStart_1168465 baseEnd_1168465 := by
    simpa [prefixWord, tailWord_1168465, baseEnd_1168465] using wordTrace_append hprefix tailTrace_1168465
  have hstable : (prefixWord ++ tailWord_1168465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168465).length < 2 ^ (prefixWord ++ tailWord_1168465).sum := by decide
  have hdescent : baseEnd_1168465 < baseStart_1168465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168466 : List Nat := [3, 2, 2, 1, 3, 2, 2, 1, 2, 3, 2]
def baseStart_1168466 : Nat := 118140960795 + 1168466 * 2 ^ 59
def prefixEnd_1168466 : Nat := 4983230072969 + 3 ^ 40 * 1168466 * 2
def baseEnd_1168466 : Nat := 599984686436530605101329

theorem tailTrace_1168466 : CollatzResearch.WordTrace tailWord_1168466 prefixEnd_1168466 599984686436530605101329 := by
  unfold tailWord_1168466
  simp only [CollatzResearch.WordTrace]
  refine ⟨10654364046213678737569313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28411637456569809966851501 10654364046213678737569313)
  ·
    refine ⟨7990773034660259053176985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10654364046213678737569313 7990773034660259053176985)
    ·
      refine ⟨5993079775995194289882739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7990773034660259053176985 5993079775995194289882739)
      ·
        refine ⟨8989619663992791434824109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5993079775995194289882739 8989619663992791434824109)
        ·
          refine ⟨3371107373997296788059041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8989619663992791434824109 3371107373997296788059041)
          ·
            refine ⟨2528330530497972591044281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3371107373997296788059041 2528330530497972591044281)
            ·
              refine ⟨1896247897873479443283211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2528330530497972591044281 1896247897873479443283211)
              ·
                refine ⟨2844371846810219164924817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1896247897873479443283211 2844371846810219164924817)
                ·
                  refine ⟨2133278885107664373693613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2844371846810219164924817 2133278885107664373693613)
                  ·
                    refine ⟨799979581915374140135105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2133278885107664373693613 799979581915374140135105)
                    ·
                      refine ⟨599984686436530605101329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 799979581915374140135105 599984686436530605101329)
                      ·
                        rfl

theorem cell23_1168466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_1168466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168466 prefixEnd_1168466 := by exact prefixLift 1168466
  have htrace : WordTrace (prefixWord ++ tailWord_1168466) baseStart_1168466 baseEnd_1168466 := by
    simpa [prefixWord, tailWord_1168466, baseEnd_1168466] using wordTrace_append hprefix tailTrace_1168466
  have hstable : (prefixWord ++ tailWord_1168466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168466).length < 2 ^ (prefixWord ++ tailWord_1168466).sum := by decide
  have hdescent : baseEnd_1168466 < baseStart_1168466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168479 : List Nat := [1, 1, 2, 3, 1, 1, 7, 1, 1, 1, 4]
def baseStart_1168479 : Nat := 118140960795 + 1168479 * 2 ^ 59
def prefixEnd_1168479 : Nat := 4983230072969 + 3 ^ 40 * 1168479 * 2
def baseEnd_1168479 : Nat := 599991361685039054238769

theorem tailTrace_1168479 : CollatzResearch.WordTrace tailWord_1168479 prefixEnd_1168479 599991361685039054238769 := by
  unfold tailWord_1168479
  simp only [CollatzResearch.WordTrace]
  refine ⟨42617930333807618170500491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28411953555871745447000327 42617930333807618170500491)
  ·
    refine ⟨63926895500711427255750737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42617930333807618170500491 63926895500711427255750737)
    ·
      refine ⟨47945171625533570441813053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63926895500711427255750737 47945171625533570441813053)
      ·
        refine ⟨17979439359575088915679895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47945171625533570441813053 17979439359575088915679895)
        ·
          refine ⟨26969159039362633373519843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17979439359575088915679895 26969159039362633373519843)
          ·
            refine ⟨40453738559043950060279765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26969159039362633373519843 40453738559043950060279765)
            ·
              refine ⟨948134497477592579537807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 40453738559043950060279765 948134497477592579537807)
              ·
                refine ⟨1422201746216388869306711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 948134497477592579537807 1422201746216388869306711)
                ·
                  refine ⟨2133302619324583303960067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1422201746216388869306711 2133302619324583303960067)
                  ·
                    refine ⟨3199953928986874955940101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2133302619324583303960067 3199953928986874955940101)
                    ·
                      refine ⟨599991361685039054238769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3199953928986874955940101 599991361685039054238769)
                      ·
                        rfl

theorem cell23_1168479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_1168479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168479 prefixEnd_1168479 := by exact prefixLift 1168479
  have htrace : WordTrace (prefixWord ++ tailWord_1168479) baseStart_1168479 baseEnd_1168479 := by
    simpa [prefixWord, tailWord_1168479, baseEnd_1168479] using wordTrace_append hprefix tailTrace_1168479
  have hstable : (prefixWord ++ tailWord_1168479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168479).length < 2 ^ (prefixWord ++ tailWord_1168479).sum := by decide
  have hdescent : baseEnd_1168479 < baseStart_1168479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168489 : List Nat := [1, 2, 1, 1, 1, 7, 2, 2, 2, 4]
def baseStart_1168489 : Nat := 118140960795 + 1168489 * 2 ^ 59
def prefixEnd_1168489 : Nat := 4983230072969 + 3 ^ 40 * 1168489 * 2
def baseEnd_1168489 : Nat := 199998832163861338371241

theorem tailTrace_1168489 : CollatzResearch.WordTrace tailWord_1168489 prefixEnd_1168489 199998832163861338371241 := by
  unfold tailWord_1168489
  simp only [CollatzResearch.WordTrace]
  refine ⟨42618295063771389878364521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28412196709180926585576347 42618295063771389878364521)
  ·
    refine ⟨31963721297828542408773391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42618295063771389878364521 31963721297828542408773391)
    ·
      refine ⟨47945581946742813613160087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31963721297828542408773391 47945581946742813613160087)
      ·
        refine ⟨71918372920114220419740131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47945581946742813613160087 71918372920114220419740131)
        ·
          refine ⟨107877559380171330629610197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71918372920114220419740131 107877559380171330629610197)
          ·
            refine ⟨2528380297972765561631489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 107877559380171330629610197 2528380297972765561631489)
            ·
              refine ⟨1896285223479574171223617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2528380297972765561631489 1896285223479574171223617)
              ·
                refine ⟨1422213917609680628417713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1896285223479574171223617 1422213917609680628417713)
                ·
                  refine ⟨1066660438207260471313285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1422213917609680628417713 1066660438207260471313285)
                  ·
                    refine ⟨199998832163861338371241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1066660438207260471313285 199998832163861338371241)
                    ·
                      rfl

theorem cell23_1168489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 4].length) (baseStart_1168489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168489 prefixEnd_1168489 := by exact prefixLift 1168489
  have htrace : WordTrace (prefixWord ++ tailWord_1168489) baseStart_1168489 baseEnd_1168489 := by
    simpa [prefixWord, tailWord_1168489, baseEnd_1168489] using wordTrace_append hprefix tailTrace_1168489
  have hstable : (prefixWord ++ tailWord_1168489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168489).length < 2 ^ (prefixWord ++ tailWord_1168489).sum := by decide
  have hdescent : baseEnd_1168489 < baseStart_1168489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168490 : List Nat := [3, 1, 3, 2, 2, 3, 2, 2, 1, 1, 3]
def baseStart_1168490 : Nat := 118140960795 + 1168490 * 2 ^ 59
def prefixEnd_1168490 : Nat := 4983230072969 + 3 ^ 40 * 1168490 * 2
def baseEnd_1168490 : Nat := 599997009972238511201219

theorem tailTrace_1168490 : CollatzResearch.WordTrace tailWord_1168490 prefixEnd_1168490 599997009972238511201219 := by
  unfold tailWord_1168490
  simp only [CollatzResearch.WordTrace]
  refine ⟨10654582884191941762287731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28412221024511844699433949 10654582884191941762287731)
  ·
    refine ⟨15981874326287912643431597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10654582884191941762287731 15981874326287912643431597)
    ·
      refine ⟨5993202872357967241286849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15981874326287912643431597 5993202872357967241286849)
      ·
        refine ⟨4494902154268475430965137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5993202872357967241286849 4494902154268475430965137)
        ·
          refine ⟨3371176615701356573223853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4494902154268475430965137 3371176615701356573223853)
          ·
            refine ⟨1264191230888008714958945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3371176615701356573223853 1264191230888008714958945)
            ·
              refine ⟨948143423166006536219209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1264191230888008714958945 948143423166006536219209)
              ·
                refine ⟨711107567374504902164407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 948143423166006536219209 711107567374504902164407)
                ·
                  refine ⟨1066661351061757353246611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711107567374504902164407 1066661351061757353246611)
                  ·
                    refine ⟨1599992026592636029869917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1066661351061757353246611 1599992026592636029869917)
                    ·
                      refine ⟨599997009972238511201219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1599992026592636029869917 599997009972238511201219)
                      ·
                        rfl

theorem cell23_1168490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_1168490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168490 prefixEnd_1168490 := by exact prefixLift 1168490
  have htrace : WordTrace (prefixWord ++ tailWord_1168490) baseStart_1168490 baseEnd_1168490 := by
    simpa [prefixWord, tailWord_1168490, baseEnd_1168490] using wordTrace_append hprefix tailTrace_1168490
  have hstable : (prefixWord ++ tailWord_1168490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168490).length < 2 ^ (prefixWord ++ tailWord_1168490).sum := by decide
  have hdescent : baseEnd_1168490 < baseStart_1168490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168512 : List Nat := [2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 3]
def baseStart_1168512 : Nat := 118140960795 + 1168512 * 2 ^ 59
def prefixEnd_1168512 : Nat := 4983230072969 + 3 ^ 40 * 1168512 * 2
def baseEnd_1168512 : Nat := 600008306546637425126117

theorem tailTrace_1168512 : CollatzResearch.WordTrace tailWord_1168512 prefixEnd_1168512 600008306546637425126117 := by
  unfold tailWord_1168512
  simp only [CollatzResearch.WordTrace]
  refine ⟨21309566971344032403225895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28412755961792043204301193 21309566971344032403225895)
  ·
    refine ⟨31964350457016048604838843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21309566971344032403225895 31964350457016048604838843)
    ·
      refine ⟨47946525685524072907258265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31964350457016048604838843 47946525685524072907258265)
      ·
        refine ⟨35959894264143054680443699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47946525685524072907258265 35959894264143054680443699)
        ·
          refine ⟨53939841396214582020665549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35959894264143054680443699 53939841396214582020665549)
          ·
            refine ⟨20227440523580468257749581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53939841396214582020665549 20227440523580468257749581)
            ·
              refine ⟨7585290196342675596656093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20227440523580468257749581 7585290196342675596656093)
              ·
                refine ⟨2844483823628503348746035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7585290196342675596656093 2844483823628503348746035)
                ·
                  refine ⟨4266725735442755023119053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2844483823628503348746035 4266725735442755023119053)
                  ·
                    refine ⟨1600022150791033133669645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4266725735442755023119053 1600022150791033133669645)
                    ·
                      refine ⟨600008306546637425126117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1600022150791033133669645 600008306546637425126117)
                      ·
                        rfl

theorem cell23_1168512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_1168512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168512 prefixEnd_1168512 := by exact prefixLift 1168512
  have htrace : WordTrace (prefixWord ++ tailWord_1168512) baseStart_1168512 baseEnd_1168512 := by
    simpa [prefixWord, tailWord_1168512, baseEnd_1168512] using wordTrace_append hprefix tailTrace_1168512
  have hstable : (prefixWord ++ tailWord_1168512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168512).length < 2 ^ (prefixWord ++ tailWord_1168512).sum := by decide
  have hdescent : baseEnd_1168512 < baseStart_1168512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168515 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 2, 7]
def baseStart_1168515 : Nat := 118140960795 + 1168515 * 2 ^ 59
def prefixEnd_1168515 : Nat := 4983230072969 + 3 ^ 40 * 1168515 * 2
def baseEnd_1168515 : Nat := 200003282329533637796201

theorem tailTrace_1168515 : CollatzResearch.WordTrace tailWord_1168515 prefixEnd_1168515 200003282329533637796201 := by
  unfold tailWord_1168515
  simp only [CollatzResearch.WordTrace]
  refine ⟨42619243361677196318810999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28412828907784797545873999 42619243361677196318810999)
  ·
    refine ⟨63928865042515794478216499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42619243361677196318810999 63928865042515794478216499)
    ·
      refine ⟨95893297563773691717324749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63928865042515794478216499 95893297563773691717324749)
      ·
        refine ⟨35959986586415134393996781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95893297563773691717324749 35959986586415134393996781)
        ·
          refine ⟨13484994969905675397748793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35959986586415134393996781 13484994969905675397748793)
          ·
            refine ⟨10113746227429256548311595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13484994969905675397748793 10113746227429256548311595)
            ·
              refine ⟨15170619341143884822467393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10113746227429256548311595 15170619341143884822467393)
              ·
                refine ⟨11377964505857913616850545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15170619341143884822467393 11377964505857913616850545)
                ·
                  refine ⟨8533473379393435212637909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11377964505857913616850545 8533473379393435212637909)
                  ·
                    refine ⟨200003282329533637796201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8533473379393435212637909 200003282329533637796201)
                    ·
                      rfl

theorem cell23_1168515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 7].length) (baseStart_1168515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168515 prefixEnd_1168515 := by exact prefixLift 1168515
  have htrace : WordTrace (prefixWord ++ tailWord_1168515) baseStart_1168515 baseEnd_1168515 := by
    simpa [prefixWord, tailWord_1168515, baseEnd_1168515] using wordTrace_append hprefix tailTrace_1168515
  have hstable : (prefixWord ++ tailWord_1168515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168515).length < 2 ^ (prefixWord ++ tailWord_1168515).sum := by decide
  have hdescent : baseEnd_1168515 < baseStart_1168515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168530 : List Nat := [3, 2, 3, 1, 1, 3, 2, 3, 1, 2, 2]
def baseStart_1168530 : Nat := 118140960795 + 1168530 * 2 ^ 59
def prefixEnd_1168530 : Nat := 4983230072969 + 3 ^ 40 * 1168530 * 2
def baseEnd_1168530 : Nat := 600017549198418354701035

theorem tailTrace_1168530 : CollatzResearch.WordTrace tailWord_1168530 prefixEnd_1168530 600017549198418354701035 := by
  unfold tailWord_1168530
  simp only [CollatzResearch.WordTrace]
  refine ⟨10654947614155713470151761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28413193637748569253738029 10654947614155713470151761)
  ·
    refine ⟨7991210710616785102613821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10654947614155713470151761 7991210710616785102613821)
    ·
      refine ⟨2996704016481294413480183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7991210710616785102613821 2996704016481294413480183)
      ·
        refine ⟨4495056024721941620220275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2996704016481294413480183 4495056024721941620220275)
        ·
          refine ⟨6742584037082912430330413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4495056024721941620220275 6742584037082912430330413)
          ·
            refine ⟨2528469013906092161373905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6742584037082912430330413 2528469013906092161373905)
            ·
              refine ⟨1896351760429569121030429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2528469013906092161373905 1896351760429569121030429)
              ·
                refine ⟨711131910161088420386411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1896351760429569121030429 711131910161088420386411)
                ·
                  refine ⟨1066697865241632630579617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711131910161088420386411 1066697865241632630579617)
                  ·
                    refine ⟨800023398931224472934713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1066697865241632630579617 800023398931224472934713)
                    ·
                      refine ⟨600017549198418354701035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 800023398931224472934713 600017549198418354701035)
                      ·
                        rfl

theorem cell23_1168530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_1168530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168530 prefixEnd_1168530 := by exact prefixLift 1168530
  have htrace : WordTrace (prefixWord ++ tailWord_1168530) baseStart_1168530 baseEnd_1168530 := by
    simpa [prefixWord, tailWord_1168530, baseEnd_1168530] using wordTrace_append hprefix tailTrace_1168530
  have hstable : (prefixWord ++ tailWord_1168530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168530).length < 2 ^ (prefixWord ++ tailWord_1168530).sum := by decide
  have hdescent : baseEnd_1168530 < baseStart_1168530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168562 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 2, 6]
def baseStart_1168562 : Nat := 118140960795 + 1168562 * 2 ^ 59
def prefixEnd_1168562 : Nat := 4983230072969 + 3 ^ 40 * 1168562 * 2
def baseEnd_1168562 : Nat := 200011326859787409833629

theorem tailTrace_1168562 : CollatzResearch.WordTrace tailWord_1168562 prefixEnd_1168562 200011326859787409833629 := by
  unfold tailWord_1168562
  simp only [CollatzResearch.WordTrace]
  refine ⟨10655239398126730836442985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28413971728337948897181293 10655239398126730836442985)
  ·
    refine ⟨7991429548595048127332239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10655239398126730836442985 7991429548595048127332239)
    ·
      refine ⟨11987144322892572190998359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7991429548595048127332239 11987144322892572190998359)
      ·
        refine ⟨17980716484338858286497539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11987144322892572190998359 17980716484338858286497539)
        ·
          refine ⟨26971074726508287429746309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17980716484338858286497539 26971074726508287429746309)
          ·
            refine ⟨5057076511220303893077433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26971074726508287429746309 5057076511220303893077433)
            ·
              refine ⟨3792807383415227919808075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5057076511220303893077433 3792807383415227919808075)
              ·
                refine ⟨5689211075122841879712113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3792807383415227919808075 5689211075122841879712113)
                ·
                  refine ⟨4266908306342131409784085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5689211075122841879712113 4266908306342131409784085)
                  ·
                    refine ⟨200011326859787409833629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4266908306342131409784085 200011326859787409833629)
                    ·
                      rfl

theorem cell23_1168562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_1168562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168562 prefixEnd_1168562 := by exact prefixLift 1168562
  have htrace : WordTrace (prefixWord ++ tailWord_1168562) baseStart_1168562 baseEnd_1168562 := by
    simpa [prefixWord, tailWord_1168562, baseEnd_1168562] using wordTrace_append hprefix tailTrace_1168562
  have hstable : (prefixWord ++ tailWord_1168562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168562).length < 2 ^ (prefixWord ++ tailWord_1168562).sum := by decide
  have hdescent : baseEnd_1168562 < baseStart_1168562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168586 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 4, 2, 2]
def baseStart_1168586 : Nat := 118140960795 + 1168586 * 2 ^ 59
def prefixEnd_1168586 : Nat := 4983230072969 + 3 ^ 40 * 1168586 * 2
def baseEnd_1168586 : Nat := 600046304115070135600777

theorem tailTrace_1168586 : CollatzResearch.WordTrace tailWord_1168586 prefixEnd_1168586 600046304115070135600777 := by
  unfold tailWord_1168586
  simp only [CollatzResearch.WordTrace]
  refine ⟨10655458236104993861161403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28414555296279983629763741 10655458236104993861161403)
  ·
    refine ⟨15983187354157490791742105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10655458236104993861161403 15983187354157490791742105)
    ·
      refine ⟨11987390515618118093806579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15983187354157490791742105 11987390515618118093806579)
      ·
        refine ⟨17981085773427177140709869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11987390515618118093806579 17981085773427177140709869)
        ·
          refine ⟨6742907165035191427766201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17981085773427177140709869 6742907165035191427766201)
          ·
            refine ⟨5057180373776393570824651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6742907165035191427766201 5057180373776393570824651)
            ·
              refine ⟨7585770560664590356236977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5057180373776393570824651 7585770560664590356236977)
              ·
                refine ⟨5689327920498442767177733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7585770560664590356236977 5689327920498442767177733)
                ·
                  refine ⟨1066748985093458018845825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5689327920498442767177733 1066748985093458018845825)
                  ·
                    refine ⟨800061738820093514134369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1066748985093458018845825 800061738820093514134369)
                    ·
                      refine ⟨600046304115070135600777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 800061738820093514134369 600046304115070135600777)
                      ·
                        rfl

theorem cell23_1168586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_1168586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168586 prefixEnd_1168586 := by exact prefixLift 1168586
  have htrace : WordTrace (prefixWord ++ tailWord_1168586) baseStart_1168586 baseEnd_1168586 := by
    simpa [prefixWord, tailWord_1168586, baseEnd_1168586] using wordTrace_append hprefix tailTrace_1168586
  have hstable : (prefixWord ++ tailWord_1168586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168586).length < 2 ^ (prefixWord ++ tailWord_1168586).sum := by decide
  have hdescent : baseEnd_1168586 < baseStart_1168586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168609 : List Nat := [1, 2, 3, 1, 3, 4, 1, 1, 7]
def baseStart_1168609 : Nat := 118140960795 + 1168609 * 2 ^ 59
def prefixEnd_1168609 : Nat := 4983230072969 + 3 ^ 40 * 1168609 * 2
def baseEnd_1168609 : Nat := 66673123796680393957019

theorem tailTrace_1168609 : CollatzResearch.WordTrace tailWord_1168609 prefixEnd_1168609 66673123796680393957019 := by
  unfold tailWord_1168609
  simp only [CollatzResearch.WordTrace]
  refine ⟨42622671823336650372732881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28415114548891100248488587 42622671823336650372732881)
  ·
    refine ⟨31967003867502487779549661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42622671823336650372732881 31967003867502487779549661)
    ·
      refine ⟨11987626450313432917331123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31967003867502487779549661 11987626450313432917331123)
      ·
        refine ⟨17981439675470149375996685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11987626450313432917331123 17981439675470149375996685)
        ·
          refine ⟨6743039878301306015998757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17981439675470149375996685 6743039878301306015998757)
          ·
            refine ⟨1264319977181494877999767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6743039878301306015998757 1264319977181494877999767)
            ·
              refine ⟨1896479965772242316999651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264319977181494877999767 1896479965772242316999651)
              ·
                refine ⟨2844719948658363475499477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1896479965772242316999651 2844719948658363475499477)
                ·
                  refine ⟨66673123796680393957019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2844719948658363475499477 66673123796680393957019)
                  ·
                    rfl

theorem cell23_1168609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 7].length) (baseStart_1168609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168609 prefixEnd_1168609 := by exact prefixLift 1168609
  have htrace : WordTrace (prefixWord ++ tailWord_1168609) baseStart_1168609 baseEnd_1168609 := by
    simpa [prefixWord, tailWord_1168609, baseEnd_1168609] using wordTrace_append hprefix tailTrace_1168609
  have hstable : (prefixWord ++ tailWord_1168609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168609).length < 2 ^ (prefixWord ++ tailWord_1168609).sum := by decide
  have hdescent : baseEnd_1168609 < baseStart_1168609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168620 : List Nat := [2, 2, 1, 1, 2, 6, 2, 1, 2, 2, 2]
def baseStart_1168620 : Nat := 118140960795 + 1168620 * 2 ^ 59
def prefixEnd_1168620 : Nat := 4983230072969 + 3 ^ 40 * 1168620 * 2
def baseEnd_1168620 : Nat := 600063762457323002575621

theorem tailTrace_1168620 : CollatzResearch.WordTrace tailWord_1168620 prefixEnd_1168620 600063762457323002575621 := by
  unfold tailWord_1168620
  simp only [CollatzResearch.WordTrace]
  refine ⟨21311536513148399625691657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28415382017531199500922209 21311536513148399625691657)
  ·
    refine ⟨15983652384861299719268743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21311536513148399625691657 15983652384861299719268743)
    ·
      refine ⟨23975478577291949578903115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15983652384861299719268743 23975478577291949578903115)
      ·
        refine ⟨35963217865937924368354673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23975478577291949578903115 35963217865937924368354673)
        ·
          refine ⟨26972413399453443276266005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35963217865937924368354673 26972413399453443276266005)
          ·
            refine ⟨1264331878099380153574969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26972413399453443276266005 1264331878099380153574969)
            ·
              refine ⟨948248908574535115181227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1264331878099380153574969 948248908574535115181227)
              ·
                refine ⟨1422373362861802672771841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 948248908574535115181227 1422373362861802672771841)
                ·
                  refine ⟨1066780022146352004578881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1422373362861802672771841 1066780022146352004578881)
                  ·
                    refine ⟨800085016609764003434161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1066780022146352004578881 800085016609764003434161)
                    ·
                      refine ⟨600063762457323002575621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 800085016609764003434161 600063762457323002575621)
                      ·
                        rfl

theorem cell23_1168620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 2, 2].length) (baseStart_1168620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168620 prefixEnd_1168620 := by exact prefixLift 1168620
  have htrace : WordTrace (prefixWord ++ tailWord_1168620) baseStart_1168620 baseEnd_1168620 := by
    simpa [prefixWord, tailWord_1168620, baseEnd_1168620] using wordTrace_append hprefix tailTrace_1168620
  have hstable : (prefixWord ++ tailWord_1168620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168620).length < 2 ^ (prefixWord ++ tailWord_1168620).sum := by decide
  have hdescent : baseEnd_1168620 < baseStart_1168620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168622 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 3, 7]
def baseStart_1168622 : Nat := 118140960795 + 1168622 * 2 ^ 59
def prefixEnd_1168622 : Nat := 4983230072969 + 3 ^ 40 * 1168622 * 2
def baseEnd_1168622 : Nat := 200021596472877331583537

theorem tailTrace_1168622 : CollatzResearch.WordTrace tailWord_1168622 prefixEnd_1168622 200021596472877331583537 := by
  unfold tailWord_1168622
  simp only [CollatzResearch.WordTrace]
  refine ⟨5327893246536194199119515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28415430648193035728637413 5327893246536194199119515)
  ·
    refine ⟨7991839869804291298679273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5327893246536194199119515 7991839869804291298679273)
    ·
      refine ⟨5993879902353218474009455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7991839869804291298679273 5993879902353218474009455)
      ·
        refine ⟨8990819853529827711014183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5993879902353218474009455 8990819853529827711014183)
        ·
          refine ⟨13486229780294741566521275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8990819853529827711014183 13486229780294741566521275)
          ·
            refine ⟨20229344670442112349781913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13486229780294741566521275 20229344670442112349781913)
            ·
              refine ⟨15172008502831584262336435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20229344670442112349781913 15172008502831584262336435)
              ·
                refine ⟨22758012754247376393504653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15172008502831584262336435 22758012754247376393504653)
                ·
                  refine ⟨8534254782842766147564245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22758012754247376393504653 8534254782842766147564245)
                  ·
                    refine ⟨200021596472877331583537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8534254782842766147564245 200021596472877331583537)
                    ·
                      rfl

theorem cell23_1168622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_1168622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168622 prefixEnd_1168622 := by exact prefixLift 1168622
  have htrace : WordTrace (prefixWord ++ tailWord_1168622) baseStart_1168622 baseEnd_1168622 := by
    simpa [prefixWord, tailWord_1168622, baseEnd_1168622] using wordTrace_append hprefix tailTrace_1168622
  have hstable : (prefixWord ++ tailWord_1168622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168622).length < 2 ^ (prefixWord ++ tailWord_1168622).sum := by decide
  have hdescent : baseEnd_1168622 < baseStart_1168622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168639 : List Nat := [1, 1, 2, 2, 1, 6, 2, 1, 2, 5]
def baseStart_1168639 : Nat := 118140960795 + 1168639 * 2 ^ 59
def prefixEnd_1168639 : Nat := 4983230072969 + 3 ^ 40 * 1168639 * 2
def baseEnd_1168639 : Nat := 200024506196586142746011

theorem tailTrace_1168639 : CollatzResearch.WordTrace tailWord_1168639 prefixEnd_1168639 200024506196586142746011 := by
  unfold tailWord_1168639
  simp only [CollatzResearch.WordTrace]
  refine ⟨42623766013227965496324971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28415844008818643664216647 42623766013227965496324971)
  ·
    refine ⟨63935649019841948244487457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42623766013227965496324971 63935649019841948244487457)
    ·
      refine ⟨47951736764881461183365593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63935649019841948244487457 47951736764881461183365593)
      ·
        refine ⟨35963802573661095887524195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47951736764881461183365593 35963802573661095887524195)
        ·
          refine ⟨53945703860491643831286293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35963802573661095887524195 53945703860491643831286293)
          ·
            refine ⟨2528704868460545804591545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53945703860491643831286293 2528704868460545804591545)
            ·
              refine ⟨1896528651345409353443659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2528704868460545804591545 1896528651345409353443659)
              ·
                refine ⟨2844792977018114030165489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1896528651345409353443659 2844792977018114030165489)
                ·
                  refine ⟨2133594732763585522624117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2844792977018114030165489 2133594732763585522624117)
                  ·
                    refine ⟨200024506196586142746011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2133594732763585522624117 200024506196586142746011)
                    ·
                      rfl

theorem cell23_1168639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 5].length) (baseStart_1168639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168639 prefixEnd_1168639 := by exact prefixLift 1168639
  have htrace : WordTrace (prefixWord ++ tailWord_1168639) baseStart_1168639 baseEnd_1168639 := by
    simpa [prefixWord, tailWord_1168639, baseEnd_1168639] using wordTrace_append hprefix tailTrace_1168639
  have hstable : (prefixWord ++ tailWord_1168639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168639).length < 2 ^ (prefixWord ++ tailWord_1168639).sum := by decide
  have hdescent : baseEnd_1168639 < baseStart_1168639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168676 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 2, 4, 2]
def baseStart_1168676 : Nat := 118140960795 + 1168676 * 2 ^ 59
def prefixEnd_1168676 : Nat := 4983230072969 + 3 ^ 40 * 1168676 * 2
def baseEnd_1168676 : Nat := 600092517373974783475363

theorem tailTrace_1168676 : CollatzResearch.WordTrace tailWord_1168676 prefixEnd_1168676 600092517373974783475363 := by
  unfold tailWord_1168676
  simp only [CollatzResearch.WordTrace]
  refine ⟨21312557757046960407710941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28416743676062613876947921 21312557757046960407710941)
  ·
    refine ⟨7992209158892610152891603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21312557757046960407710941 7992209158892610152891603)
    ·
      refine ⟨11988313738338915229337405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7992209158892610152891603 11988313738338915229337405)
      ·
        refine ⟨4495617651877093211001527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11988313738338915229337405 4495617651877093211001527)
        ·
          refine ⟨6743426477815639816502291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4495617651877093211001527 6743426477815639816502291)
          ·
            refine ⟨10115139716723459724753437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6743426477815639816502291 10115139716723459724753437)
            ·
              refine ⟨3793177393771297396782539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10115139716723459724753437 3793177393771297396782539)
              ·
                refine ⟨5689766090656946095173809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3793177393771297396782539 5689766090656946095173809)
                ·
                  refine ⟨4267324567992709571380357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5689766090656946095173809 4267324567992709571380357)
                  ·
                    refine ⟨800123356498633044633817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4267324567992709571380357 800123356498633044633817)
                    ·
                      refine ⟨600092517373974783475363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 800123356498633044633817 600092517373974783475363)
                      ·
                        rfl

theorem cell23_1168676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_1168676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168676 prefixEnd_1168676 := by exact prefixLift 1168676
  have htrace : WordTrace (prefixWord ++ tailWord_1168676) baseStart_1168676 baseEnd_1168676 := by
    simpa [prefixWord, tailWord_1168676, baseEnd_1168676] using wordTrace_append hprefix tailTrace_1168676
  have hstable : (prefixWord ++ tailWord_1168676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168676).length < 2 ^ (prefixWord ++ tailWord_1168676).sum := by decide
  have hdescent : baseEnd_1168676 < baseStart_1168676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168703 : List Nat := [1, 1, 2, 2, 4, 3, 2, 3, 1, 4]
def baseStart_1168703 : Nat := 118140960795 + 1168703 * 2 ^ 59
def prefixEnd_1168703 : Nat := 4983230072969 + 3 ^ 40 * 1168703 * 2
def baseEnd_1168703 : Nat := 200035460450548725945913

theorem tailTrace_1168703 : CollatzResearch.WordTrace tailWord_1168703 prefixEnd_1168703 200035460450548725945913 := by
  unfold tailWord_1168703
  simp only [CollatzResearch.WordTrace]
  refine ⟨42626100284996104426654763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28417400189997402951103175 42626100284996104426654763)
  ·
    refine ⟨63939150427494156639982145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42626100284996104426654763 63939150427494156639982145)
    ·
      refine ⟨47954362820620617479986609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63939150427494156639982145 47954362820620617479986609)
      ·
        refine ⟨35965772115465463109989957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47954362820620617479986609 35965772115465463109989957)
        ·
          refine ⟨6743582271649774333123117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35965772115465463109989957 6743582271649774333123117)
          ·
            refine ⟨2528843351868665374921169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6743582271649774333123117 2528843351868665374921169)
            ·
              refine ⟨1896632513901499031190877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2528843351868665374921169 1896632513901499031190877)
              ·
                refine ⟨711237192713062136696579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1896632513901499031190877 711237192713062136696579)
                ·
                  refine ⟨1066855789069593205044869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711237192713062136696579 1066855789069593205044869)
                  ·
                    refine ⟨200035460450548725945913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1066855789069593205044869 200035460450548725945913)
                    ·
                      rfl

theorem cell23_1168703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 1, 4].length) (baseStart_1168703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168703 prefixEnd_1168703 := by exact prefixLift 1168703
  have htrace : WordTrace (prefixWord ++ tailWord_1168703) baseStart_1168703 baseEnd_1168703 := by
    simpa [prefixWord, tailWord_1168703, baseEnd_1168703] using wordTrace_append hprefix tailTrace_1168703
  have hstable : (prefixWord ++ tailWord_1168703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168703).length < 2 ^ (prefixWord ++ tailWord_1168703).sum := by decide
  have hdescent : baseEnd_1168703 < baseStart_1168703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168716 : List Nat := [2, 2, 1, 3, 2, 4, 1, 2, 6]
def baseStart_1168716 : Nat := 118140960795 + 1168716 * 2 ^ 59
def prefixEnd_1168716 : Nat := 4983230072969 + 3 ^ 40 * 1168716 * 2
def baseEnd_1168716 : Nat := 66679228511128291886131

theorem tailTrace_1168716 : CollatzResearch.WordTrace tailWord_1168716 prefixEnd_1168716 66679228511128291886131 := by
  unfold tailWord_1168716
  simp only [CollatzResearch.WordTrace]
  refine ⟨21313287216974503823439001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28417716289299338431252001 21313287216974503823439001)
  ·
    refine ⟨15984965412730877867579251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21313287216974503823439001 15984965412730877867579251)
    ·
      refine ⟨23977448119096316801368877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15984965412730877867579251 23977448119096316801368877)
      ·
        refine ⟨8991543044661118800513329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23977448119096316801368877 8991543044661118800513329)
        ·
          refine ⟨6743657283495839100384997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8991543044661118800513329 6743657283495839100384997)
          ·
            refine ⟨1264435740655469831322187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6743657283495839100384997 1264435740655469831322187)
            ·
              refine ⟨1896653610983204746983281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264435740655469831322187 1896653610983204746983281)
              ·
                refine ⟨1422490208237403560237461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1896653610983204746983281 1422490208237403560237461)
                ·
                  refine ⟨66679228511128291886131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1422490208237403560237461 66679228511128291886131)
                  ·
                    rfl

theorem cell23_1168716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 6].length) (baseStart_1168716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168716 prefixEnd_1168716 := by exact prefixLift 1168716
  have htrace : WordTrace (prefixWord ++ tailWord_1168716) baseStart_1168716 baseEnd_1168716 := by
    simpa [prefixWord, tailWord_1168716, baseEnd_1168716] using wordTrace_append hprefix tailTrace_1168716
  have hstable : (prefixWord ++ tailWord_1168716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168716).length < 2 ^ (prefixWord ++ tailWord_1168716).sum := by decide
  have hdescent : baseEnd_1168716 < baseStart_1168716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168736 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 1, 5, 2]
def baseStart_1168736 : Nat := 118140960795 + 1168736 * 2 ^ 59
def prefixEnd_1168736 : Nat := 4983230072969 + 3 ^ 40 * 1168736 * 2
def baseEnd_1168736 : Nat := 600123326213244548725087

theorem tailTrace_1168736 : CollatzResearch.WordTrace tailWord_1168736 prefixEnd_1168736 600123326213244548725087 := by
  unfold tailWord_1168736
  simp only [CollatzResearch.WordTrace]
  refine ⟨21313651946938275531303031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28418202595917700708404041 21313651946938275531303031)
  ·
    refine ⟨31970477920407413296954547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21313651946938275531303031 31970477920407413296954547)
    ·
      refine ⟨47955716880611119945431821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31970477920407413296954547 47955716880611119945431821)
      ·
        refine ⟨17983393830229169979536933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47955716880611119945431821 17983393830229169979536933)
        ·
          refine ⟨3371886343167969371163175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17983393830229169979536933 3371886343167969371163175)
          ·
            refine ⟨5057829514751954056744763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3371886343167969371163175 5057829514751954056744763)
            ·
              refine ⟨7586744272127931085117145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5057829514751954056744763 7586744272127931085117145)
              ·
                refine ⟨5690058204095948313837859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7586744272127931085117145 5690058204095948313837859)
                ·
                  refine ⟨8535087306143922470756789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5690058204095948313837859 8535087306143922470756789)
                  ·
                    refine ⟨800164434950992731633449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8535087306143922470756789 800164434950992731633449)
                    ·
                      refine ⟨600123326213244548725087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 800164434950992731633449 600123326213244548725087)
                      ·
                        rfl

theorem cell23_1168736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_1168736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168736 prefixEnd_1168736 := by exact prefixLift 1168736
  have htrace : WordTrace (prefixWord ++ tailWord_1168736) baseStart_1168736 baseEnd_1168736 := by
    simpa [prefixWord, tailWord_1168736, baseEnd_1168736] using wordTrace_append hprefix tailTrace_1168736
  have hstable : (prefixWord ++ tailWord_1168736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168736).length < 2 ^ (prefixWord ++ tailWord_1168736).sum := by decide
  have hdescent : baseEnd_1168736 < baseStart_1168736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168759 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 6, 4]
def baseStart_1168759 : Nat := 118140960795 + 1168759 * 2 ^ 59
def prefixEnd_1168759 : Nat := 4983230072969 + 3 ^ 40 * 1168759 * 2
def baseEnd_1168759 : Nat := 200045045422765986245827

theorem tailTrace_1168759 : CollatzResearch.WordTrace tailWord_1168759 prefixEnd_1168759 200045045422765986245827 := by
  unfold tailWord_1168759
  simp only [CollatzResearch.WordTrace]
  refine ⟨42628142772793225990693331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28418761848528817327128887 42628142772793225990693331)
  ·
    refine ⟨63942214159189838986039997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42628142772793225990693331 63942214159189838986039997)
    ·
      refine ⟨23978330309696189619764999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63942214159189838986039997 23978330309696189619764999)
      ·
        refine ⟨35967495464544284429647499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23978330309696189619764999 35967495464544284429647499)
        ·
          refine ⟨53951243196816426644471249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35967495464544284429647499 53951243196816426644471249)
          ·
            refine ⟨40463432397612319983353437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53951243196816426644471249 40463432397612319983353437)
            ·
              refine ⟨15173787149104619993757539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40463432397612319983353437 15173787149104619993757539)
              ·
                refine ⟨22760680723656929990636309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15173787149104619993757539 22760680723656929990636309)
                ·
                  refine ⟨1066906908921418593311077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22760680723656929990636309 1066906908921418593311077)
                  ·
                    refine ⟨200045045422765986245827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1066906908921418593311077 200045045422765986245827)
                    ·
                      rfl

theorem cell23_1168759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 4].length) (baseStart_1168759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168759 prefixEnd_1168759 := by exact prefixLift 1168759
  have htrace : WordTrace (prefixWord ++ tailWord_1168759) baseStart_1168759 baseEnd_1168759 := by
    simpa [prefixWord, tailWord_1168759, baseEnd_1168759] using wordTrace_append hprefix tailTrace_1168759
  have hstable : (prefixWord ++ tailWord_1168759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168759).length < 2 ^ (prefixWord ++ tailWord_1168759).sum := by decide
  have hdescent : baseEnd_1168759 < baseStart_1168759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168770 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_1168770 : Nat := 118140960795 + 1168770 * 2 ^ 59
def prefixEnd_1168770 : Nat := 4983230072969 + 3 ^ 40 * 1168770 * 2
def baseEnd_1168770 : Nat := 600140784555497415699931

theorem tailTrace_1168770 : CollatzResearch.WordTrace tailWord_1168770 prefixEnd_1168770 600140784555497415699931 := by
  unfold tailWord_1168770
  simp only [CollatzResearch.WordTrace]
  refine ⟨10657135993938343717335941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28419029317168916579562509 10657135993938343717335941)
  ·
    refine ⟨1998212998863439447000489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10657135993938343717335941 1998212998863439447000489)
    ·
      refine ⟨1498659749147579585250367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1998212998863439447000489 1498659749147579585250367)
      ·
        refine ⟨2247989623721369377875551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1498659749147579585250367 2247989623721369377875551)
        ·
          refine ⟨3371984435582054066813327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2247989623721369377875551 3371984435582054066813327)
          ·
            refine ⟨5057976653373081100219991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3371984435582054066813327 5057976653373081100219991)
            ·
              refine ⟨7586964980059621650329987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5057976653373081100219991 7586964980059621650329987)
              ·
                refine ⟨11380447470089432475494981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7586964980059621650329987 11380447470089432475494981)
                ·
                  refine ⟨2133833900641768589155309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11380447470089432475494981 2133833900641768589155309)
                  ·
                    refine ⟨800187712740663220933241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2133833900641768589155309 800187712740663220933241)
                    ·
                      refine ⟨600140784555497415699931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 800187712740663220933241 600140784555497415699931)
                      ·
                        rfl

theorem cell23_1168770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_1168770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168770 prefixEnd_1168770 := by exact prefixLift 1168770
  have htrace : WordTrace (prefixWord ++ tailWord_1168770) baseStart_1168770 baseEnd_1168770 := by
    simpa [prefixWord, tailWord_1168770, baseEnd_1168770] using wordTrace_append hprefix tailTrace_1168770
  have hstable : (prefixWord ++ tailWord_1168770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168770).length < 2 ^ (prefixWord ++ tailWord_1168770).sum := by decide
  have hdescent : baseEnd_1168770 < baseStart_1168770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168776 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 4, 4]
def baseStart_1168776 : Nat := 118140960795 + 1168776 * 2 ^ 59
def prefixEnd_1168776 : Nat := 4983230072969 + 3 ^ 40 * 1168776 * 2
def baseEnd_1168776 : Nat := 200047955146474797408301

theorem tailTrace_1168776 : CollatzResearch.WordTrace tailWord_1168776 prefixEnd_1168776 200047955146474797408301 := by
  unfold tailWord_1168776
  simp only [CollatzResearch.WordTrace]
  refine ⟨21314381406865818947031091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28419175209154425262708121 21314381406865818947031091)
  ·
    refine ⟨31971572110298728420546637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21314381406865818947031091 31971572110298728420546637)
    ·
      refine ⟨11989339541362023157704989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31971572110298728420546637 11989339541362023157704989)
      ·
        refine ⟨4496002328010758684139371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11989339541362023157704989 4496002328010758684139371)
        ·
          refine ⟨6744003492016138026209057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4496002328010758684139371 6744003492016138026209057)
          ·
            refine ⟨5058002619012103519656793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6744003492016138026209057 5058002619012103519656793)
            ·
              refine ⟨3793501964259077639742595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5058002619012103519656793 3793501964259077639742595)
              ·
                refine ⟨5690252946388616459613893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3793501964259077639742595 5690252946388616459613893)
                ·
                  refine ⟨1066922427447865586177605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5690252946388616459613893 1066922427447865586177605)
                  ·
                    refine ⟨200047955146474797408301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1066922427447865586177605 200047955146474797408301)
                    ·
                      rfl

theorem cell23_1168776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_1168776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168776 prefixEnd_1168776 := by exact prefixLift 1168776
  have htrace : WordTrace (prefixWord ++ tailWord_1168776) baseStart_1168776 baseEnd_1168776 := by
    simpa [prefixWord, tailWord_1168776, baseEnd_1168776] using wordTrace_append hprefix tailTrace_1168776
  have hstable : (prefixWord ++ tailWord_1168776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168776).length < 2 ^ (prefixWord ++ tailWord_1168776).sum := by decide
  have hdescent : baseEnd_1168776 < baseStart_1168776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168777 : List Nat := [1, 2, 1, 1, 7, 1, 3, 2, 1, 1, 3]
def baseStart_1168777 : Nat := 118140960795 + 1168777 * 2 ^ 59
def prefixEnd_1168777 : Nat := 4983230072969 + 3 ^ 40 * 1168777 * 2
def baseEnd_1168777 : Nat := 600144378920078888312399

theorem tailTrace_1168777 : CollatzResearch.WordTrace tailWord_1168777 prefixEnd_1168777 600144378920078888312399 := by
  unfold tailWord_1168777
  simp only [CollatzResearch.WordTrace]
  refine ⟨42628799286728015064848585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28419199524485343376565723 42628799286728015064848585)
  ·
    refine ⟨31971599465046011298636439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42628799286728015064848585 31971599465046011298636439)
    ·
      refine ⟨47957399197569016947954659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31971599465046011298636439 47957399197569016947954659)
      ·
        refine ⟨71936098796353525421931989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47957399197569016947954659 71936098796353525421931989)
        ·
          refine ⟨1686002315539535752076531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 71936098796353525421931989 1686002315539535752076531)
          ·
            refine ⟨2529003473309303628114797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1686002315539535752076531 2529003473309303628114797)
            ·
              refine ⟨948376302490988860543049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2529003473309303628114797 948376302490988860543049)
              ·
                refine ⟨711282226868241645407287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 948376302490988860543049 711282226868241645407287)
                ·
                  refine ⟨1066923340302362468110931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711282226868241645407287 1066923340302362468110931)
                  ·
                    refine ⟨1600385010453543702166397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1066923340302362468110931 1600385010453543702166397)
                    ·
                      refine ⟨600144378920078888312399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1600385010453543702166397 600144378920078888312399)
                      ·
                        rfl

theorem cell23_1168777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 1, 1, 3].length) (baseStart_1168777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168777 prefixEnd_1168777 := by exact prefixLift 1168777
  have htrace : WordTrace (prefixWord ++ tailWord_1168777) baseStart_1168777 baseEnd_1168777 := by
    simpa [prefixWord, tailWord_1168777, baseEnd_1168777] using wordTrace_append hprefix tailTrace_1168777
  have hstable : (prefixWord ++ tailWord_1168777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168777).length < 2 ^ (prefixWord ++ tailWord_1168777).sum := by decide
  have hdescent : baseEnd_1168777 < baseStart_1168777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168793 : List Nat := [1, 2, 1, 2, 1, 5, 4, 1, 2, 4]
def baseStart_1168793 : Nat := 118140960795 + 1168793 * 2 ^ 59
def prefixEnd_1168793 : Nat := 4983230072969 + 3 ^ 40 * 1168793 * 2
def baseEnd_1168793 : Nat := 200050864870183608570775

theorem tailTrace_1168793 : CollatzResearch.WordTrace tailWord_1168793 prefixEnd_1168793 200050864870183608570775 := by
  unfold tailWord_1168793
  simp only [CollatzResearch.WordTrace]
  refine ⟨42629382854670049797431033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28419588569780033198287355 42629382854670049797431033)
  ·
    refine ⟨31972037141002537348073275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42629382854670049797431033 31972037141002537348073275)
    ·
      refine ⟨47958055711503806022109913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31972037141002537348073275 47958055711503806022109913)
      ·
        refine ⟨35968541783627854516582435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47958055711503806022109913 35968541783627854516582435)
        ·
          refine ⟨53952812675441781774873653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35968541783627854516582435 53952812675441781774873653)
          ·
            refine ⟨5058076188322667041394405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53952812675441781774873653 5058076188322667041394405)
            ·
              refine ⟨948389285310500070261451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5058076188322667041394405 948389285310500070261451)
              ·
                refine ⟨1422583927965750105392177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 948389285310500070261451 1422583927965750105392177)
                ·
                  refine ⟨1066937945974312579044133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1422583927965750105392177 1066937945974312579044133)
                  ·
                    refine ⟨200050864870183608570775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1066937945974312579044133 200050864870183608570775)
                    ·
                      rfl

theorem cell23_1168793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 2, 4].length) (baseStart_1168793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168793 prefixEnd_1168793 := by exact prefixLift 1168793
  have htrace : WordTrace (prefixWord ++ tailWord_1168793) baseStart_1168793 baseEnd_1168793 := by
    simpa [prefixWord, tailWord_1168793, baseEnd_1168793] using wordTrace_append hprefix tailTrace_1168793
  have hstable : (prefixWord ++ tailWord_1168793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168793).length < 2 ^ (prefixWord ++ tailWord_1168793).sum := by decide
  have hdescent : baseEnd_1168793 < baseStart_1168793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168813 : List Nat := [1, 5, 2, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1168813 : Nat := 118140960795 + 1168813 * 2 ^ 59
def prefixEnd_1168813 : Nat := 4983230072969 + 3 ^ 40 * 1168813 * 2
def baseEnd_1168813 : Nat := 600162864223640747462233

theorem tailTrace_1168813 : CollatzResearch.WordTrace tailWord_1168813 prefixEnd_1168813 600162864223640747462233 := by
  unfold tailWord_1168813
  simp only [CollatzResearch.WordTrace]
  refine ⟨42630112314597593213159093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28420074876398395475439395 42630112314597593213159093)
  ·
    refine ⟨3996573029493524363733665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42630112314597593213159093 3996573029493524363733665)
    ·
      refine ⟨2997429772120143272800249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3996573029493524363733665 2997429772120143272800249)
      ·
        refine ⟨2248072329090107454600187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2997429772120143272800249 2248072329090107454600187)
        ·
          refine ⟨3372108493635161181900281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2248072329090107454600187 3372108493635161181900281)
          ·
            refine ⟨2529081370226370886425211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3372108493635161181900281 2529081370226370886425211)
            ·
              refine ⟨3793622055339556329637817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2529081370226370886425211 3793622055339556329637817)
              ·
                refine ⟨2845216541504667247228363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3793622055339556329637817 2845216541504667247228363)
                ·
                  refine ⟨4267824812257000870842545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2845216541504667247228363 4267824812257000870842545)
                  ·
                    refine ⟨3200868609192750653131909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4267824812257000870842545 3200868609192750653131909)
                    ·
                      refine ⟨600162864223640747462233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3200868609192750653131909 600162864223640747462233)
                      ·
                        rfl

theorem cell23_1168813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1168813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168813 prefixEnd_1168813 := by exact prefixLift 1168813
  have htrace : WordTrace (prefixWord ++ tailWord_1168813) baseStart_1168813 baseEnd_1168813 := by
    simpa [prefixWord, tailWord_1168813, baseEnd_1168813] using wordTrace_append hprefix tailTrace_1168813
  have hstable : (prefixWord ++ tailWord_1168813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168813).length < 2 ^ (prefixWord ++ tailWord_1168813).sum := by decide
  have hdescent : baseEnd_1168813 < baseStart_1168813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168816 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 4, 1, 3]
def baseStart_1168816 : Nat := 118140960795 + 1168816 * 2 ^ 59
def prefixEnd_1168816 : Nat := 4983230072969 + 3 ^ 40 * 1168816 * 2
def baseEnd_1168816 : Nat := 600164404665604235724719

theorem tailTrace_1168816 : CollatzResearch.WordTrace tailWord_1168816 prefixEnd_1168816 600164404665604235724719 := by
  unfold tailWord_1168816
  simp only [CollatzResearch.WordTrace]
  refine ⟨21315110866793362362759151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28420147822391149817012201 21315110866793362362759151)
  ·
    refine ⟨31972666300190043544138727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21315110866793362362759151 31972666300190043544138727)
    ·
      refine ⟨47958999450285065316208091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31972666300190043544138727 47958999450285065316208091)
      ·
        refine ⟨71938499175427597974312137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47958999450285065316208091 71938499175427597974312137)
        ·
          refine ⟨53953874381570698480734103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71938499175427597974312137 53953874381570698480734103)
          ·
            refine ⟨80930811572356047721101155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53953874381570698480734103 80930811572356047721101155)
            ·
              refine ⟨121396217358534071581651733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80930811572356047721101155 121396217358534071581651733)
              ·
                refine ⟨5690447688681284605389925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 121396217358534071581651733 5690447688681284605389925)
                ·
                  refine ⟨1066958941627740863510611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5690447688681284605389925 1066958941627740863510611)
                  ·
                    refine ⟨1600438412441611295265917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1066958941627740863510611 1600438412441611295265917)
                    ·
                      refine ⟨600164404665604235724719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1600438412441611295265917 600164404665604235724719)
                      ·
                        rfl

theorem cell23_1168816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 4, 1, 3].length) (baseStart_1168816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168816 prefixEnd_1168816 := by exact prefixLift 1168816
  have htrace : WordTrace (prefixWord ++ tailWord_1168816) baseStart_1168816 baseEnd_1168816 := by
    simpa [prefixWord, tailWord_1168816, baseEnd_1168816] using wordTrace_append hprefix tailTrace_1168816
  have hstable : (prefixWord ++ tailWord_1168816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168816).length < 2 ^ (prefixWord ++ tailWord_1168816).sum := by decide
  have hdescent : baseEnd_1168816 < baseStart_1168816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168836 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 2, 7]
def baseStart_1168836 : Nat := 118140960795 + 1168836 * 2 ^ 59
def prefixEnd_1168836 : Nat := 4983230072969 + 3 ^ 40 * 1168836 * 2
def baseEnd_1168836 : Nat := 200058224759564719158209

theorem tailTrace_1168836 : CollatzResearch.WordTrace tailWord_1168836 prefixEnd_1168836 200058224759564719158209 := by
  unfold tailWord_1168836
  simp only [CollatzResearch.WordTrace]
  refine ⟨21315475596757134070623181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28420634129009512094164241 21315475596757134070623181)
  ·
    refine ⟨7993303348783925276483693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21315475596757134070623181 7993303348783925276483693)
    ·
      refine ⟨2997488755793971978681385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7993303348783925276483693 2997488755793971978681385)
      ·
        refine ⟨2248116566845478984011039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2997488755793971978681385 2248116566845478984011039)
        ·
          refine ⟨3372174850268218476016559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2248116566845478984011039 3372174850268218476016559)
          ·
            refine ⟨5058262275402327714024839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3372174850268218476016559 5058262275402327714024839)
            ·
              refine ⟨7587393413103491571037259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5058262275402327714024839 7587393413103491571037259)
              ·
                refine ⟨11381090119655237356555889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7587393413103491571037259 11381090119655237356555889)
                ·
                  refine ⟨8535817589741428017416917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11381090119655237356555889 8535817589741428017416917)
                  ·
                    refine ⟨200058224759564719158209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8535817589741428017416917 200058224759564719158209)
                    ·
                      rfl

theorem cell23_1168836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_1168836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168836 prefixEnd_1168836 := by exact prefixLift 1168836
  have htrace : WordTrace (prefixWord ++ tailWord_1168836) baseStart_1168836 baseEnd_1168836 := by
    simpa [prefixWord, tailWord_1168836, baseEnd_1168836] using wordTrace_append hprefix tailTrace_1168836
  have hstable : (prefixWord ++ tailWord_1168836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168836).length < 2 ^ (prefixWord ++ tailWord_1168836).sum := by decide
  have hdescent : baseEnd_1168836 < baseStart_1168836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168839 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_1168839 : Nat := 118140960795 + 1168839 * 2 ^ 59
def prefixEnd_1168839 : Nat := 4983230072969 + 3 ^ 40 * 1168839 * 2
def baseEnd_1168839 : Nat := 600176214720657645737113

theorem tailTrace_1168839 : CollatzResearch.WordTrace tailWord_1168839 prefixEnd_1168839 600176214720657645737113 := by
  unfold tailWord_1168839
  simp only [CollatzResearch.WordTrace]
  refine ⟨42631060612503399653605571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28420707075002266435737047 42631060612503399653605571)
  ·
    refine ⟨63946590918755099480408357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42631060612503399653605571 63946590918755099480408357)
    ·
      refine ⟨11989985797266581152576567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63946590918755099480408357 11989985797266581152576567)
      ·
        refine ⟨17984978695899871728864851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11989985797266581152576567 17984978695899871728864851)
        ·
          refine ⟨26977468043849807593297277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17984978695899871728864851 26977468043849807593297277)
          ·
            refine ⟨10116550516443677847486479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26977468043849807593297277 10116550516443677847486479)
            ·
              refine ⟨15174825774665516771229719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10116550516443677847486479 15174825774665516771229719)
              ·
                refine ⟨22762238661998275156844579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15174825774665516771229719 22762238661998275156844579)
                ·
                  refine ⟨34143357992997412735266869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22762238661998275156844579 34143357992997412735266869)
                  ·
                    refine ⟨3200939811843507443931269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34143357992997412735266869 3200939811843507443931269)
                    ·
                      refine ⟨600176214720657645737113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3200939811843507443931269 600176214720657645737113)
                      ·
                        rfl

theorem cell23_1168839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_1168839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168839 prefixEnd_1168839 := by exact prefixLift 1168839
  have htrace : WordTrace (prefixWord ++ tailWord_1168839) baseStart_1168839 baseEnd_1168839 := by
    simpa [prefixWord, tailWord_1168839, baseEnd_1168839] using wordTrace_append hprefix tailTrace_1168839
  have hstable : (prefixWord ++ tailWord_1168839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168839).length < 2 ^ (prefixWord ++ tailWord_1168839).sum := by decide
  have hdescent : baseEnd_1168839 < baseStart_1168839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168877 : List Nat := [1, 5, 1, 3, 2, 1, 1, 3, 1, 3, 2]
def baseStart_1168877 : Nat := 118140960795 + 1168877 * 2 ^ 59
def prefixEnd_1168877 : Nat := 4983230072969 + 3 ^ 40 * 1168877 * 2
def baseEnd_1168877 : Nat := 600195726985528497061939

theorem tailTrace_1168877 : CollatzResearch.WordTrace tailWord_1168877 prefixEnd_1168877 600195726985528497061939 := by
  unfold tailWord_1168877
  simp only [CollatzResearch.WordTrace]
  refine ⟨42632446586365732143488885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28421631057577154762325923 42632446586365732143488885)
  ·
    refine ⟨3996791867471787388452083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42632446586365732143488885 3996791867471787388452083)
    ·
      refine ⟨5995187801207681082678125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3996791867471787388452083 5995187801207681082678125)
      ·
        refine ⟨2248195425452880406004297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5995187801207681082678125 2248195425452880406004297)
        ·
          refine ⟨1686146569089660304503223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2248195425452880406004297 1686146569089660304503223)
          ·
            refine ⟨2529219853634490456754835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1686146569089660304503223 2529219853634490456754835)
            ·
              refine ⟨3793829780451735685132253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2529219853634490456754835 3793829780451735685132253)
              ·
                refine ⟨1422686167669400881924595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3793829780451735685132253 1422686167669400881924595)
                ·
                  refine ⟨2134029251504101322886893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1422686167669400881924595 2134029251504101322886893)
                  ·
                    refine ⟨800260969314037996082585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2134029251504101322886893 800260969314037996082585)
                    ·
                      refine ⟨600195726985528497061939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 800260969314037996082585 600195726985528497061939)
                      ·
                        rfl

theorem cell23_1168877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_1168877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168877 prefixEnd_1168877 := by exact prefixLift 1168877
  have htrace : WordTrace (prefixWord ++ tailWord_1168877) baseStart_1168877 baseEnd_1168877 := by
    simpa [prefixWord, tailWord_1168877, baseEnd_1168877] using wordTrace_append hprefix tailTrace_1168877
  have hstable : (prefixWord ++ tailWord_1168877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168877).length < 2 ^ (prefixWord ++ tailWord_1168877).sum := by decide
  have hdescent : baseEnd_1168877 < baseStart_1168877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168907 : List Nat := [1, 1, 1, 1, 9, 1, 1, 1, 1, 4, 2]
def baseStart_1168907 : Nat := 118140960795 + 1168907 * 2 ^ 59
def prefixEnd_1168907 : Nat := 4983230072969 + 3 ^ 40 * 1168907 * 2
def baseEnd_1168907 : Nat := 600211131405163379686801

theorem tailTrace_1168907 : CollatzResearch.WordTrace tailWord_1168907 prefixEnd_1168907 600211131405163379686801 := by
  unfold tailWord_1168907
  simp only [CollatzResearch.WordTrace]
  refine ⟨42633540776257047267080975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28422360517504698178053983 42633540776257047267080975)
  ·
    refine ⟨63950311164385570900621463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42633540776257047267080975 63950311164385570900621463)
    ·
      refine ⟨95925466746578356350932195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63950311164385570900621463 95925466746578356350932195)
      ·
        refine ⟨143888200119867534526398293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95925466746578356350932195 143888200119867534526398293)
        ·
          refine ⟨843094922577348835115615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 143888200119867534526398293 843094922577348835115615)
          ·
            refine ⟨1264642383866023252673423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 843094922577348835115615 1264642383866023252673423)
            ·
              refine ⟨1896963575799034879010135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264642383866023252673423 1896963575799034879010135)
              ·
                refine ⟨2845445363698552318515203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1896963575799034879010135 2845445363698552318515203)
                ·
                  refine ⟨4268168045547828477772805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2845445363698552318515203 4268168045547828477772805)
                  ·
                    refine ⟨800281508540217839582401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4268168045547828477772805 800281508540217839582401)
                    ·
                      refine ⟨600211131405163379686801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 800281508540217839582401 600211131405163379686801)
                      ·
                        rfl

theorem cell23_1168907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 4, 2].length) (baseStart_1168907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168907 prefixEnd_1168907 := by exact prefixLift 1168907
  have htrace : WordTrace (prefixWord ++ tailWord_1168907) baseStart_1168907 baseEnd_1168907 := by
    simpa [prefixWord, tailWord_1168907, baseEnd_1168907] using wordTrace_append hprefix tailTrace_1168907
  have hstable : (prefixWord ++ tailWord_1168907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168907).length < 2 ^ (prefixWord ++ tailWord_1168907).sum := by decide
  have hdescent : baseEnd_1168907 < baseStart_1168907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168983 : List Nat := [1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 3]
def baseStart_1168983 : Nat := 118140960795 + 1168983 * 2 ^ 59
def prefixEnd_1168983 : Nat := 4983230072969 + 3 ^ 40 * 1168983 * 2
def baseEnd_1168983 : Nat := 600250155934905082336451

theorem tailTrace_1168983 : CollatzResearch.WordTrace tailWord_1168983 prefixEnd_1168983 600250155934905082336451 := by
  unfold tailWord_1168983
  simp only [CollatzResearch.WordTrace]
  refine ⟨42636312723981712246847603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28424208482654474831231735 42636312723981712246847603)
  ·
    refine ⟨63954469085972568370271405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42636312723981712246847603 63954469085972568370271405)
    ·
      refine ⟨23982925907239713138851777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63954469085972568370271405 23982925907239713138851777)
      ·
        refine ⟨17987194430429784854138833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23982925907239713138851777 17987194430429784854138833)
        ·
          refine ⟨13490395822822338640604125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17987194430429784854138833 13490395822822338640604125)
          ·
            refine ⟨5058898433558376990226547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13490395822822338640604125 5058898433558376990226547)
            ·
              refine ⟨7588347650337565485339821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5058898433558376990226547 7588347650337565485339821)
              ·
                refine ⟨2845630368876587057002433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7588347650337565485339821 2845630368876587057002433)
                ·
                  refine ⟨2134222776657440292751825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2845630368876587057002433 2134222776657440292751825)
                  ·
                    refine ⟨1600667082493080219563869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2134222776657440292751825 1600667082493080219563869)
                    ·
                      refine ⟨600250155934905082336451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1600667082493080219563869 600250155934905082336451)
                      ·
                        rfl

theorem cell23_1168983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_1168983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1168983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1168983 prefixEnd_1168983 := by exact prefixLift 1168983
  have htrace : WordTrace (prefixWord ++ tailWord_1168983) baseStart_1168983 baseEnd_1168983 := by
    simpa [prefixWord, tailWord_1168983, baseEnd_1168983] using wordTrace_append hprefix tailTrace_1168983
  have hstable : (prefixWord ++ tailWord_1168983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168983).length < 2 ^ (prefixWord ++ tailWord_1168983).sum := by decide
  have hdescent : baseEnd_1168983 < baseStart_1168983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169000 : List Nat := [2, 1, 4, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1169000 : Nat := 118140960795 + 1169000 * 2 ^ 59
def prefixEnd_1169000 : Nat := 4983230072969 + 3 ^ 40 * 1169000 * 2
def baseEnd_1169000 : Nat := 600258885106031515823873

theorem tailTrace_1169000 : CollatzResearch.WordTrace tailWord_1169000 prefixEnd_1169000 600258885106031515823873 := by
  unfold tailWord_1169000
  simp only [CollatzResearch.WordTrace]
  refine ⟨21318466382460062075108227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28424621843280082766810969 21318466382460062075108227)
  ·
    refine ⟨31977699573690093112662341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21318466382460062075108227 31977699573690093112662341)
    ·
      refine ⟨5995818670066892458624189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31977699573690093112662341 5995818670066892458624189)
      ·
        refine ⟨2248432001275084671984071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5995818670066892458624189 2248432001275084671984071)
        ·
          refine ⟨3372648001912627007976107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2248432001275084671984071 3372648001912627007976107)
          ·
            refine ⟨5058972002868940511964161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3372648001912627007976107 5058972002868940511964161)
            ·
              refine ⟨3794229002151705383973121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5058972002868940511964161 3794229002151705383973121)
              ·
                refine ⟨2845671751613779037979841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3794229002151705383973121 2845671751613779037979841)
                ·
                  refine ⟨2134253813710334278484881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2845671751613779037979841 2134253813710334278484881)
                  ·
                    refine ⟨1600690360282750708863661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2134253813710334278484881 1600690360282750708863661)
                    ·
                      refine ⟨600258885106031515823873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1600690360282750708863661 600258885106031515823873)
                      ·
                        rfl

theorem cell23_1169000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1169000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169000 prefixEnd_1169000 := by exact prefixLift 1169000
  have htrace : WordTrace (prefixWord ++ tailWord_1169000) baseStart_1169000 baseEnd_1169000 := by
    simpa [prefixWord, tailWord_1169000, baseEnd_1169000] using wordTrace_append hprefix tailTrace_1169000
  have hstable : (prefixWord ++ tailWord_1169000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169000).length < 2 ^ (prefixWord ++ tailWord_1169000).sum := by decide
  have hdescent : baseEnd_1169000 < baseStart_1169000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169047 : List Nat := [1, 1, 3, 3, 2, 2, 1, 5, 1, 1, 3]
def baseStart_1169047 : Nat := 118140960795 + 1169047 * 2 ^ 59
def prefixEnd_1169047 : Nat := 4983230072969 + 3 ^ 40 * 1169047 * 2
def baseEnd_1169047 : Nat := 600283018696792831936157

theorem tailTrace_1169047 : CollatzResearch.WordTrace tailWord_1169047 prefixEnd_1169047 600283018696792831936157 := by
  unfold tailWord_1169047
  simp only [CollatzResearch.WordTrace]
  refine ⟨42638646995749851177177395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28425764663833234118118263 42638646995749851177177395)
  ·
    refine ⟨63957970493624776765766093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42638646995749851177177395 63957970493624776765766093)
    ·
      refine ⟨23984238935109291287162285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63957970493624776765766093 23984238935109291287162285)
      ·
        refine ⟨8994089600665984232685857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23984238935109291287162285 8994089600665984232685857)
        ·
          refine ⟨6745567200499488174514393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8994089600665984232685857 6745567200499488174514393)
          ·
            refine ⟨5059175400374616130885795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6745567200499488174514393 5059175400374616130885795)
            ·
              refine ⟨7588763100561924196328693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5059175400374616130885795 7588763100561924196328693)
              ·
                refine ⟨711446540677680393405815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7588763100561924196328693 711446540677680393405815)
                ·
                  refine ⟨1067169811016520590108723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711446540677680393405815 1067169811016520590108723)
                  ·
                    refine ⟨1600754716524780885163085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1067169811016520590108723 1600754716524780885163085)
                    ·
                      refine ⟨600283018696792831936157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1600754716524780885163085 600283018696792831936157)
                      ·
                        rfl

theorem cell23_1169047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_1169047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169047 prefixEnd_1169047 := by exact prefixLift 1169047
  have htrace : WordTrace (prefixWord ++ tailWord_1169047) baseStart_1169047 baseEnd_1169047 := by
    simpa [prefixWord, tailWord_1169047, baseEnd_1169047] using wordTrace_append hprefix tailTrace_1169047
  have hstable : (prefixWord ++ tailWord_1169047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169047).length < 2 ^ (prefixWord ++ tailWord_1169047).sum := by decide
  have hdescent : baseEnd_1169047 < baseStart_1169047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169103 : List Nat := [1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 3]
def baseStart_1169103 : Nat := 118140960795 + 1169103 * 2 ^ 59
def prefixEnd_1169103 : Nat := 4983230072969 + 3 ^ 40 * 1169103 * 2
def baseEnd_1169103 : Nat := 600311773613444612835899

theorem tailTrace_1169103 : CollatzResearch.WordTrace tailWord_1169103 prefixEnd_1169103 600311773613444612835899 := by
  unfold tailWord_1169103
  simp only [CollatzResearch.WordTrace]
  refine ⟨42640689483546972741215963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28427126322364648494143975 42640689483546972741215963)
  ·
    refine ⟨63961034225320459111823945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42640689483546972741215963 63961034225320459111823945)
    ·
      refine ⟨47970775668990344333867959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63961034225320459111823945 47970775668990344333867959)
      ·
        refine ⟨71956163503485516500801939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47970775668990344333867959 71956163503485516500801939)
        ·
          refine ⟨107934245255228274751202909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71956163503485516500801939 107934245255228274751202909)
          ·
            refine ⟨40475341970710603031701091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107934245255228274751202909 40475341970710603031701091)
            ·
              refine ⟨60713012956065904547551637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40475341970710603031701091 60713012956065904547551637)
              ·
                refine ⟨2845922482315589275666483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60713012956065904547551637 2845922482315589275666483)
                ·
                  refine ⟨4268883723473383913499725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2845922482315589275666483 4268883723473383913499725)
                  ·
                    refine ⟨1600831396302518967562397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4268883723473383913499725 1600831396302518967562397)
                    ·
                      refine ⟨600311773613444612835899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1600831396302518967562397 600311773613444612835899)
                      ·
                        rfl

theorem cell23_1169103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 3].length) (baseStart_1169103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169103 prefixEnd_1169103 := by exact prefixLift 1169103
  have htrace : WordTrace (prefixWord ++ tailWord_1169103) baseStart_1169103 baseEnd_1169103 := by
    simpa [prefixWord, tailWord_1169103, baseEnd_1169103] using wordTrace_append hprefix tailTrace_1169103
  have hstable : (prefixWord ++ tailWord_1169103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169103).length < 2 ^ (prefixWord ++ tailWord_1169103).sum := by decide
  have hdescent : baseEnd_1169103 < baseStart_1169103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169120 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 4, 1, 3]
def baseStart_1169120 : Nat := 118140960795 + 1169120 * 2 ^ 59
def prefixEnd_1169120 : Nat := 4983230072969 + 3 ^ 40 * 1169120 * 2
def baseEnd_1169120 : Nat := 600320502784571046323321

theorem tailTrace_1169120 : CollatzResearch.WordTrace tailWord_1169120 prefixEnd_1169120 600320502784571046323321 := by
  unfold tailWord_1169120
  simp only [CollatzResearch.WordTrace]
  refine ⟨21320654762242692322292407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28427539682990256429723209 21320654762242692322292407)
  ·
    refine ⟨31980982143364038483438611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21320654762242692322292407 31980982143364038483438611)
    ·
      refine ⟨47971473215046057725157917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31980982143364038483438611 47971473215046057725157917)
      ·
        refine ⟨17989302455642271646934219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47971473215046057725157917 17989302455642271646934219)
        ·
          refine ⟨26983953683463407470401329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17989302455642271646934219 26983953683463407470401329)
          ·
            refine ⟨20237965262597555602800997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26983953683463407470401329 20237965262597555602800997)
            ·
              refine ⟨3794618486737041675525187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20237965262597555602800997 3794618486737041675525187)
              ·
                refine ⟨5691927730105562513287781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3794618486737041675525187 5691927730105562513287781)
                ·
                  refine ⟨1067236449394792971241459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5691927730105562513287781 1067236449394792971241459)
                  ·
                    refine ⟨1600854674092189456862189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1067236449394792971241459 1600854674092189456862189)
                    ·
                      refine ⟨600320502784571046323321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1600854674092189456862189 600320502784571046323321)
                      ·
                        rfl

theorem cell23_1169120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_1169120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169120 prefixEnd_1169120 := by exact prefixLift 1169120
  have htrace : WordTrace (prefixWord ++ tailWord_1169120) baseStart_1169120 baseEnd_1169120 := by
    simpa [prefixWord, tailWord_1169120, baseEnd_1169120] using wordTrace_append hprefix tailTrace_1169120
  have hstable : (prefixWord ++ tailWord_1169120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169120).length < 2 ^ (prefixWord ++ tailWord_1169120).sum := by decide
  have hdescent : baseEnd_1169120 < baseStart_1169120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169121 : List Nat := [1, 2, 3, 1, 6, 1, 1, 1, 3, 2, 2]
def baseStart_1169121 : Nat := 118140960795 + 1169121 * 2 ^ 59
def prefixEnd_1169121 : Nat := 4983230072969 + 3 ^ 40 * 1169121 * 2
def baseEnd_1169121 : Nat := 600321016265225542410817

theorem tailTrace_1169121 : CollatzResearch.WordTrace tailWord_1169121 prefixEnd_1169121 600321016265225542410817 := by
  unfold tailWord_1169121
  simp only [CollatzResearch.WordTrace]
  refine ⟨42641345997481761815371217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28427563998321174543580811 42641345997481761815371217)
  ·
    refine ⟨31981009498111321361528413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42641345997481761815371217 31981009498111321361528413)
    ·
      refine ⟨11992878561791745510573155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31981009498111321361528413 11992878561791745510573155)
      ·
        refine ⟨17989317842687618265859733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11992878561791745510573155 17989317842687618265859733)
        ·
          refine ⟨843249273875982106212175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17989317842687618265859733 843249273875982106212175)
          ·
            refine ⟨1264873910813973159318263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 843249273875982106212175 1264873910813973159318263)
            ·
              refine ⟨1897310866220959738977395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264873910813973159318263 1897310866220959738977395)
              ·
                refine ⟨2845966299331439608466093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1897310866220959738977395 2845966299331439608466093)
                ·
                  refine ⟨1067237362249289853174785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2845966299331439608466093 1067237362249289853174785)
                  ·
                    refine ⟨800428021686967389881089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1067237362249289853174785 800428021686967389881089)
                    ·
                      refine ⟨600321016265225542410817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 800428021686967389881089 600321016265225542410817)
                      ·
                        rfl

theorem cell23_1169121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_1169121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169121 prefixEnd_1169121 := by exact prefixLift 1169121
  have htrace : WordTrace (prefixWord ++ tailWord_1169121) baseStart_1169121 baseEnd_1169121 := by
    simpa [prefixWord, tailWord_1169121, baseEnd_1169121] using wordTrace_append hprefix tailTrace_1169121
  have hstable : (prefixWord ++ tailWord_1169121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169121).length < 2 ^ (prefixWord ++ tailWord_1169121).sum := by decide
  have hdescent : baseEnd_1169121 < baseStart_1169121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169137 : List Nat := [1, 2, 2, 2, 2, 4, 1, 3, 2, 1, 3]
def baseStart_1169137 : Nat := 118140960795 + 1169137 * 2 ^ 59
def prefixEnd_1169137 : Nat := 4983230072969 + 3 ^ 40 * 1169137 * 2
def baseEnd_1169137 : Nat := 600329231955697479810743

theorem tailTrace_1169137 : CollatzResearch.WordTrace tailWord_1169137 prefixEnd_1169137 600329231955697479810743 := by
  unfold tailWord_1169137
  simp only [CollatzResearch.WordTrace]
  refine ⟨42641929565423796547953665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28427953043615864365302443 42641929565423796547953665)
  ·
    refine ⟨31981447174067847410965249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42641929565423796547953665 31981447174067847410965249)
    ·
      refine ⟨23986085380550885558223937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31981447174067847410965249 23986085380550885558223937)
      ·
        refine ⟨17989564035413164168667953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23986085380550885558223937 17989564035413164168667953)
        ·
          refine ⟨13492173026559873126500965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17989564035413164168667953 13492173026559873126500965)
          ·
            refine ⟨2529782442479976211218931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13492173026559873126500965 2529782442479976211218931)
            ·
              refine ⟨3794673663719964316828397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2529782442479976211218931 3794673663719964316828397)
              ·
                refine ⟨1423002623894986618810649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3794673663719964316828397 1423002623894986618810649)
                ·
                  refine ⟨1067251967921239964107987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1423002623894986618810649 1067251967921239964107987)
                  ·
                    refine ⟨1600877951881859946161981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1067251967921239964107987 1600877951881859946161981)
                    ·
                      refine ⟨600329231955697479810743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1600877951881859946161981 600329231955697479810743)
                      ·
                        rfl

theorem cell23_1169137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_1169137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169137 prefixEnd_1169137 := by exact prefixLift 1169137
  have htrace : WordTrace (prefixWord ++ tailWord_1169137) baseStart_1169137 baseEnd_1169137 := by
    simpa [prefixWord, tailWord_1169137, baseEnd_1169137] using wordTrace_append hprefix tailTrace_1169137
  have hstable : (prefixWord ++ tailWord_1169137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169137).length < 2 ^ (prefixWord ++ tailWord_1169137).sum := by decide
  have hdescent : baseEnd_1169137 < baseStart_1169137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169163 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 5]
def baseStart_1169163 : Nat := 118140960795 + 1169163 * 2 ^ 59
def prefixEnd_1169163 : Nat := 4983230072969 + 3 ^ 40 * 1169163 * 2
def baseEnd_1169163 : Nat := 600342582452714378085623

theorem tailTrace_1169163 : CollatzResearch.WordTrace tailWord_1169163 prefixEnd_1169163 600342582452714378085623 := by
  unfold tailWord_1169163
  simp only [CollatzResearch.WordTrace]
  refine ⟨42642877863329602988400143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28428585242219735325600095 42642877863329602988400143)
  ·
    refine ⟨63964316794994404482600215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42642877863329602988400143 63964316794994404482600215)
    ·
      refine ⟨95946475192491606723900323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63964316794994404482600215 95946475192491606723900323)
      ·
        refine ⟨143919712788737410085850485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95946475192491606723900323 143919712788737410085850485)
        ·
          refine ⟨13492473073944132195548483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 143919712788737410085850485 13492473073944132195548483)
          ·
            refine ⟨20238709610916198293322725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13492473073944132195548483 20238709610916198293322725)
            ·
              refine ⟨3794758052046787179998011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20238709610916198293322725 3794758052046787179998011)
              ·
                refine ⟨5692137078070180769997017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3794758052046787179998011 5692137078070180769997017)
                ·
                  refine ⟨4269102808552635577497763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5692137078070180769997017 4269102808552635577497763)
                  ·
                    refine ⟨6403654212828953366246645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4269102808552635577497763 6403654212828953366246645)
                    ·
                      refine ⟨600342582452714378085623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6403654212828953366246645 600342582452714378085623)
                      ·
                        rfl

theorem cell23_1169163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 5].length) (baseStart_1169163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169163 prefixEnd_1169163 := by exact prefixLift 1169163
  have htrace : WordTrace (prefixWord ++ tailWord_1169163) baseStart_1169163 baseEnd_1169163 := by
    simpa [prefixWord, tailWord_1169163, baseEnd_1169163] using wordTrace_append hprefix tailTrace_1169163
  have hstable : (prefixWord ++ tailWord_1169163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169163).length < 2 ^ (prefixWord ++ tailWord_1169163).sum := by decide
  have hdescent : baseEnd_1169163 < baseStart_1169163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169183 : List Nat := [1, 1, 2, 4, 2, 1, 2, 3, 7]
def baseStart_1169183 : Nat := 118140960795 + 1169183 * 2 ^ 59
def prefixEnd_1169183 : Nat := 4983230072969 + 3 ^ 40 * 1169183 * 2
def baseEnd_1169183 : Nat := 66705872451756033315059

theorem tailTrace_1169183 : CollatzResearch.WordTrace tailWord_1169183 prefixEnd_1169183 66705872451756033315059 := by
  unfold tailWord_1169183
  simp only [CollatzResearch.WordTrace]
  refine ⟨42643607323257146404128203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28429071548838097602752135 42643607323257146404128203)
  ·
    refine ⟨63965410984885719606192305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42643607323257146404128203 63965410984885719606192305)
    ·
      refine ⟨47974058238664289704644229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63965410984885719606192305 47974058238664289704644229)
      ·
        refine ⟨8995135919749554319620793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47974058238664289704644229 8995135919749554319620793)
        ·
          refine ⟨6746351939812165739715595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8995135919749554319620793 6746351939812165739715595)
          ·
            refine ⟨10119527909718248609573393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6746351939812165739715595 10119527909718248609573393)
            ·
              refine ⟨7589645932288686457180045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10119527909718248609573393 7589645932288686457180045)
              ·
                refine ⟨2846117224608257421442517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7589645932288686457180045 2846117224608257421442517)
                ·
                  refine ⟨66705872451756033315059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2846117224608257421442517 66705872451756033315059)
                  ·
                    rfl

theorem cell23_1169183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 7].length) (baseStart_1169183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169183 prefixEnd_1169183 := by exact prefixLift 1169183
  have htrace : WordTrace (prefixWord ++ tailWord_1169183) baseStart_1169183 baseEnd_1169183 := by
    simpa [prefixWord, tailWord_1169183, baseEnd_1169183] using wordTrace_append hprefix tailTrace_1169183
  have hstable : (prefixWord ++ tailWord_1169183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169183).length < 2 ^ (prefixWord ++ tailWord_1169183).sum := by decide
  have hdescent : baseEnd_1169183 < baseStart_1169183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169223 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_1169223 : Nat := 118140960795 + 1169223 * 2 ^ 59
def prefixEnd_1169223 : Nat := 4983230072969 + 3 ^ 40 * 1169223 * 2
def baseEnd_1169223 : Nat := 600373391291984143335347

theorem tailTrace_1169223 : CollatzResearch.WordTrace tailWord_1169223 prefixEnd_1169223 600373391291984143335347 := by
  unfold tailWord_1169223
  simp only [CollatzResearch.WordTrace]
  refine ⟨42645066243112233235584323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28430044162074822157056215 42645066243112233235584323)
  ·
    refine ⟨63967599364668349853376485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42645066243112233235584323 63967599364668349853376485)
    ·
      refine ⟨11993924880875315597508091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63967599364668349853376485 11993924880875315597508091)
      ·
        refine ⟨17990887321312973396262137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11993924880875315597508091 17990887321312973396262137)
        ·
          refine ⟨13493165490984730047196603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17990887321312973396262137 13493165490984730047196603)
          ·
            refine ⟨20239748236477095070794905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13493165490984730047196603 20239748236477095070794905)
            ·
              refine ⟨15179811177357821303096179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20239748236477095070794905 15179811177357821303096179)
              ·
                refine ⟨22769716766036731954644269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15179811177357821303096179 22769716766036731954644269)
                ·
                  refine ⟨8538643787263774482991601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22769716766036731954644269 8538643787263774482991601)
                  ·
                    refine ⟨6403982840447830862243701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8538643787263774482991601 6403982840447830862243701)
                    ·
                      refine ⟨600373391291984143335347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6403982840447830862243701 600373391291984143335347)
                      ·
                        rfl

theorem cell23_1169223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_1169223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169223 prefixEnd_1169223 := by exact prefixLift 1169223
  have htrace : WordTrace (prefixWord ++ tailWord_1169223) baseStart_1169223 baseEnd_1169223 := by
    simpa [prefixWord, tailWord_1169223, baseEnd_1169223] using wordTrace_append hprefix tailTrace_1169223
  have hstable : (prefixWord ++ tailWord_1169223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169223).length < 2 ^ (prefixWord ++ tailWord_1169223).sum := by decide
  have hdescent : baseEnd_1169223 < baseStart_1169223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169228 : List Nat := [2, 2, 1, 3, 5, 1, 1, 2, 2, 2, 2]
def baseStart_1169228 : Nat := 118140960795 + 1169228 * 2 ^ 59
def prefixEnd_1169228 : Nat := 4983230072969 + 3 ^ 40 * 1169228 * 2
def baseEnd_1169228 : Nat := 600375958695256623772825

theorem tailTrace_1169228 : CollatzResearch.WordTrace tailWord_1169228 prefixEnd_1169228 600375958695256623772825 := by
  unfold tailWord_1169228
  simp only [CollatzResearch.WordTrace]
  refine ⟨21322624304047059544758169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28430165738729412726344225 21322624304047059544758169)
  ·
    refine ⟨15991968228035294658568627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21322624304047059544758169 15991968228035294658568627)
    ·
      refine ⟨23987952342052941987852941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15991968228035294658568627 23987952342052941987852941)
      ·
        refine ⟨8995482128269853245444853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23987952342052941987852941 8995482128269853245444853)
        ·
          refine ⟨843326449525298741760455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8995482128269853245444853 843326449525298741760455)
          ·
            refine ⟨1264989674287948112640683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 843326449525298741760455 1264989674287948112640683)
            ·
              refine ⟨1897484511431922168961025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264989674287948112640683 1897484511431922168961025)
              ·
                refine ⟨1423113383573941626720769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1897484511431922168961025 1423113383573941626720769)
                ·
                  refine ⟨1067335037680456220040577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1423113383573941626720769 1067335037680456220040577)
                  ·
                    refine ⟨800501278260342165030433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1067335037680456220040577 800501278260342165030433)
                    ·
                      refine ⟨600375958695256623772825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 800501278260342165030433 600375958695256623772825)
                      ·
                        rfl

theorem cell23_1169228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_1169228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169228 prefixEnd_1169228 := by exact prefixLift 1169228
  have htrace : WordTrace (prefixWord ++ tailWord_1169228) baseStart_1169228 baseEnd_1169228 := by
    simpa [prefixWord, tailWord_1169228, baseEnd_1169228] using wordTrace_append hprefix tailTrace_1169228
  have hstable : (prefixWord ++ tailWord_1169228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169228).length < 2 ^ (prefixWord ++ tailWord_1169228).sum := by decide
  have hdescent : baseEnd_1169228 < baseStart_1169228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169273 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 10]
def baseStart_1169273 : Nat := 118140960795 + 1169273 * 2 ^ 59
def prefixEnd_1169273 : Nat := 4983230072969 + 3 ^ 40 * 1169273 * 2
def baseEnd_1169273 : Nat := 66711007258300994190013

theorem tailTrace_1169273 : CollatzResearch.WordTrace tailWord_1169273 prefixEnd_1169273 66711007258300994190013 := by
  unfold tailWord_1169273
  simp only [CollatzResearch.WordTrace]
  refine ⟨42646889892931091774904473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28431259928620727849936315 42646889892931091774904473)
  ·
    refine ⟨31985167419698318831178355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42646889892931091774904473 31985167419698318831178355)
    ·
      refine ⟨47977751129547478246767533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31985167419698318831178355 47977751129547478246767533)
      ·
        refine ⟨17991656673580304342537825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47977751129547478246767533 17991656673580304342537825)
        ·
          refine ⟨13493742505185228256903369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17991656673580304342537825 13493742505185228256903369)
          ·
            refine ⟨10120306878888921192677527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13493742505185228256903369 10120306878888921192677527)
            ·
              refine ⟨15180460318333381789016291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10120306878888921192677527 15180460318333381789016291)
              ·
                refine ⟨22770690477500072683524437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15180460318333381789016291 22770690477500072683524437)
                ·
                  refine ⟨66711007258300994190013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 22770690477500072683524437 66711007258300994190013)
                  ·
                    rfl

theorem cell23_1169273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 10].length) (baseStart_1169273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169273 prefixEnd_1169273 := by exact prefixLift 1169273
  have htrace : WordTrace (prefixWord ++ tailWord_1169273) baseStart_1169273 baseEnd_1169273 := by
    simpa [prefixWord, tailWord_1169273, baseEnd_1169273] using wordTrace_append hprefix tailTrace_1169273
  have hstable : (prefixWord ++ tailWord_1169273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169273).length < 2 ^ (prefixWord ++ tailWord_1169273).sum := by decide
  have hdescent : baseEnd_1169273 < baseStart_1169273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169317 : List Nat := [1, 3, 1, 2, 1, 1, 1, 6, 3, 1, 3]
def baseStart_1169317 : Nat := 118140960795 + 1169317 * 2 ^ 59
def prefixEnd_1169317 : Nat := 4983230072969 + 3 ^ 40 * 1169317 * 2
def baseEnd_1169317 : Nat := 600421658473506775559915

theorem tailTrace_1169317 : CollatzResearch.WordTrace tailWord_1169317 prefixEnd_1169317 600421658473506775559915 := by
  unfold tailWord_1169317
  simp only [CollatzResearch.WordTrace]
  refine ⟨42648494704771687289506205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28432329803181124859670803 42648494704771687289506205)
  ·
    refine ⟨15993185514289382733564827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42648494704771687289506205 15993185514289382733564827)
    ·
      refine ⟨23989778271434074100347241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15993185514289382733564827 23989778271434074100347241)
      ·
        refine ⟨17992333703575555575260431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23989778271434074100347241 17992333703575555575260431)
        ·
          refine ⟨26988500555363333362890647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17992333703575555575260431 26988500555363333362890647)
          ·
            refine ⟨40482750833045000044335971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26988500555363333362890647 40482750833045000044335971)
            ·
              refine ⟨60724126249567500066503957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40482750833045000044335971 60724126249567500066503957)
              ·
                refine ⟨2846443417948476565617373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60724126249567500066503957 2846443417948476565617373)
                ·
                  refine ⟨1067416281730678712106515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2846443417948476565617373 1067416281730678712106515)
                  ·
                    refine ⟨1601124422596018068159773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1067416281730678712106515 1601124422596018068159773)
                    ·
                      refine ⟨600421658473506775559915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1601124422596018068159773 600421658473506775559915)
                      ·
                        rfl

theorem cell23_1169317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_1169317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169317 prefixEnd_1169317 := by exact prefixLift 1169317
  have htrace : WordTrace (prefixWord ++ tailWord_1169317) baseStart_1169317 baseEnd_1169317 := by
    simpa [prefixWord, tailWord_1169317, baseEnd_1169317] using wordTrace_append hprefix tailTrace_1169317
  have hstable : (prefixWord ++ tailWord_1169317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169317).length < 2 ^ (prefixWord ++ tailWord_1169317).sum := by decide
  have hdescent : baseEnd_1169317 < baseStart_1169317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169360 : List Nat := [2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 5]
def baseStart_1169360 : Nat := 118140960795 + 1169360 * 2 ^ 59
def prefixEnd_1169360 : Nat := 4983230072969 + 3 ^ 40 * 1169360 * 2
def baseEnd_1169360 : Nat := 600443738141650107322217

theorem tailTrace_1169360 : CollatzResearch.WordTrace tailWord_1169360 prefixEnd_1169360 600443738141650107322217 := by
  unfold tailWord_1169360
  simp only [CollatzResearch.WordTrace]
  refine ⟨21325031521807952816660767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28433375362410603755547689 21325031521807952816660767)
  ·
    refine ⟨31987547282711929224991151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21325031521807952816660767 31987547282711929224991151)
    ·
      refine ⟨47981320924067893837486727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31987547282711929224991151 47981320924067893837486727)
      ·
        refine ⟨71971981386101840756230091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47981320924067893837486727 71971981386101840756230091)
        ·
          refine ⟨107957972079152761134345137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71971981386101840756230091 107957972079152761134345137)
          ·
            refine ⟨80968479059364570850758853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107957972079152761134345137 80968479059364570850758853)
            ·
              refine ⟨15181589823630857034517285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80968479059364570850758853 15181589823630857034517285)
              ·
                refine ⟨2846548091930785693971991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15181589823630857034517285 2846548091930785693971991)
                ·
                  refine ⟨4269822137896178540957987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2846548091930785693971991 4269822137896178540957987)
                  ·
                    refine ⟨6404733206844267811436981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4269822137896178540957987 6404733206844267811436981)
                    ·
                      refine ⟨600443738141650107322217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6404733206844267811436981 600443738141650107322217)
                      ·
                        rfl

theorem cell23_1169360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 5].length) (baseStart_1169360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169360 prefixEnd_1169360 := by exact prefixLift 1169360
  have htrace : WordTrace (prefixWord ++ tailWord_1169360) baseStart_1169360 baseEnd_1169360 := by
    simpa [prefixWord, tailWord_1169360, baseEnd_1169360] using wordTrace_append hprefix tailTrace_1169360
  have hstable : (prefixWord ++ tailWord_1169360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169360).length < 2 ^ (prefixWord ++ tailWord_1169360).sum := by decide
  have hdescent : baseEnd_1169360 < baseStart_1169360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169367 : List Nat := [1, 1, 3, 2, 1, 1, 3, 5, 2, 4]
def baseStart_1169367 : Nat := 118140960795 + 1169367 * 2 ^ 59
def prefixEnd_1169367 : Nat := 4983230072969 + 3 ^ 40 * 1169367 * 2
def baseEnd_1169367 : Nat := 200149110835410526644895

theorem tailTrace_1169367 : CollatzResearch.WordTrace tailWord_1169367 prefixEnd_1169367 200149110835410526644895 := by
  unfold tailWord_1169367
  simp only [CollatzResearch.WordTrace]
  refine ⟨42650318354590545828826355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28433545569727030552550903 42650318354590545828826355)
  ·
    refine ⟨63975477531885818743239533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42650318354590545828826355 63975477531885818743239533)
    ·
      refine ⟨23990804074457182028714825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63975477531885818743239533 23990804074457182028714825)
      ·
        refine ⟨17993103055842886521536119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23990804074457182028714825 17993103055842886521536119)
        ·
          refine ⟨26989654583764329782304179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17993103055842886521536119 26989654583764329782304179)
          ·
            refine ⟨40484481875646494673456269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26989654583764329782304179 40484481875646494673456269)
            ·
              refine ⟨15181680703367435502546101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40484481875646494673456269 15181680703367435502546101)
              ·
                refine ⟨1423282565940697078363697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15181680703367435502546101 1423282565940697078363697)
                ·
                  refine ⟨1067461924455522808772773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1423282565940697078363697 1067461924455522808772773)
                  ·
                    refine ⟨200149110835410526644895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1067461924455522808772773 200149110835410526644895)
                    ·
                      rfl

theorem cell23_1169367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 4].length) (baseStart_1169367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169367 prefixEnd_1169367 := by exact prefixLift 1169367
  have htrace : WordTrace (prefixWord ++ tailWord_1169367) baseStart_1169367 baseEnd_1169367 := by
    simpa [prefixWord, tailWord_1169367, baseEnd_1169367] using wordTrace_append hprefix tailTrace_1169367
  have hstable : (prefixWord ++ tailWord_1169367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169367).length < 2 ^ (prefixWord ++ tailWord_1169367).sum := by decide
  have hdescent : baseEnd_1169367 < baseStart_1169367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169377 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 3, 2, 3]
def baseStart_1169377 : Nat := 118140960795 + 1169377 * 2 ^ 59
def prefixEnd_1169377 : Nat := 4983230072969 + 3 ^ 40 * 1169377 * 2
def baseEnd_1169377 : Nat := 600452467312776540809639

theorem tailTrace_1169377 : CollatzResearch.WordTrace tailWord_1169377 prefixEnd_1169377 600452467312776540809639 := by
  unfold tailWord_1169377
  simp only [CollatzResearch.WordTrace]
  refine ⟨42650683084554317536690385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28433788723036211691126923 42650683084554317536690385)
  ·
    refine ⟨31988012313415738152517789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42650683084554317536690385 31988012313415738152517789)
    ·
      refine ⟨11995504617530901807194171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31988012313415738152517789 11995504617530901807194171)
      ·
        refine ⟨17993256926296352710791257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11995504617530901807194171 17993256926296352710791257)
        ·
          refine ⟨13494942694722264533093443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17993256926296352710791257 13494942694722264533093443)
          ·
            refine ⟨20242414042083396799640165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13494942694722264533093443 20242414042083396799640165)
            ·
              refine ⟨3795452632890636899932531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20242414042083396799640165 3795452632890636899932531)
              ·
                refine ⟨5693178949335955349898797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3795452632890636899932531 5693178949335955349898797)
                ·
                  refine ⟨2134942106000983256212049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5693178949335955349898797 2134942106000983256212049)
                  ·
                    refine ⟨1601206579500737442159037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2134942106000983256212049 1601206579500737442159037)
                    ·
                      refine ⟨600452467312776540809639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1601206579500737442159037 600452467312776540809639)
                      ·
                        rfl

theorem cell23_1169377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_1169377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169377 prefixEnd_1169377 := by exact prefixLift 1169377
  have htrace : WordTrace (prefixWord ++ tailWord_1169377) baseStart_1169377 baseEnd_1169377 := by
    simpa [prefixWord, tailWord_1169377, baseEnd_1169377] using wordTrace_append hprefix tailTrace_1169377
  have hstable : (prefixWord ++ tailWord_1169377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169377).length < 2 ^ (prefixWord ++ tailWord_1169377).sum := by decide
  have hdescent : baseEnd_1169377 < baseStart_1169377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169431 : List Nat := [1, 1, 3, 5, 3, 1, 2, 7]
def baseStart_1169431 : Nat := 118140960795 + 1169431 * 2 ^ 59
def prefixEnd_1169431 : Nat := 4983230072969 + 3 ^ 40 * 1169431 * 2
def baseEnd_1169431 : Nat := 22240007232152567760533

theorem tailTrace_1169431 : CollatzResearch.WordTrace tailWord_1169431 prefixEnd_1169431 22240007232152567760533 := by
  unfold tailWord_1169431
  simp only [CollatzResearch.WordTrace]
  refine ⟨42652652626358684759156147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28435101750905789839437431 42652652626358684759156147)
  ·
    refine ⟨63978978939538027138734221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42652652626358684759156147 63978978939538027138734221)
    ·
      refine ⟨23992117102326760177025333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63978978939538027138734221 23992117102326760177025333)
      ·
        refine ⟨2249260978343133766596125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23992117102326760177025333 2249260978343133766596125)
        ·
          refine ⟨843472866878675162473547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2249260978343133766596125 843472866878675162473547)
          ·
            refine ⟨1265209300318012743710321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 843472866878675162473547 1265209300318012743710321)
            ·
              refine ⟨948906975238509557782741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1265209300318012743710321 948906975238509557782741)
              ·
                refine ⟨22240007232152567760533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 948906975238509557782741 22240007232152567760533)
                ·
                  rfl

theorem cell23_1169431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 7].length) (baseStart_1169431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169431 prefixEnd_1169431 := by exact prefixLift 1169431
  have htrace : WordTrace (prefixWord ++ tailWord_1169431) baseStart_1169431 baseEnd_1169431 := by
    simpa [prefixWord, tailWord_1169431, baseEnd_1169431] using wordTrace_append hprefix tailTrace_1169431
  have hstable : (prefixWord ++ tailWord_1169431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169431).length < 2 ^ (prefixWord ++ tailWord_1169431).sum := by decide
  have hdescent : baseEnd_1169431 < baseStart_1169431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169437 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_1169437 : Nat := 118140960795 + 1169437 * 2 ^ 59
def prefixEnd_1169437 : Nat := 4983230072969 + 3 ^ 40 * 1169437 * 2
def baseEnd_1169437 : Nat := 600483276152046306059363

theorem tailTrace_1169437 : CollatzResearch.WordTrace tailWord_1169437 prefixEnd_1169437 600483276152046306059363 := by
  unfold tailWord_1169437
  simp only [CollatzResearch.WordTrace]
  refine ⟨42652871464336947783874565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28435247642891298522583043 42652871464336947783874565)
  ·
    refine ⟨7997413399563177709476481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42652871464336947783874565 7997413399563177709476481)
    ·
      refine ⟨5998060049672383282107361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7997413399563177709476481 5998060049672383282107361)
      ·
        refine ⟨4498545037254287461580521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5998060049672383282107361 4498545037254287461580521)
        ·
          refine ⟨3373908777940715596185391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4498545037254287461580521 3373908777940715596185391)
          ·
            refine ⟨5060863166911073394278087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3373908777940715596185391 5060863166911073394278087)
            ·
              refine ⟨7591294750366610091417131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5060863166911073394278087 7591294750366610091417131)
              ·
                refine ⟨11386942125549915137125697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7591294750366610091417131 11386942125549915137125697)
                ·
                  refine ⟨8540206594162436352844273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11386942125549915137125697 8540206594162436352844273)
                  ·
                    refine ⟨6405154945621827264633205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8540206594162436352844273 6405154945621827264633205)
                    ·
                      refine ⟨600483276152046306059363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6405154945621827264633205 600483276152046306059363)
                      ·
                        rfl

theorem cell23_1169437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_1169437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169437 prefixEnd_1169437 := by exact prefixLift 1169437
  have htrace : WordTrace (prefixWord ++ tailWord_1169437) baseStart_1169437 baseEnd_1169437 := by
    simpa [prefixWord, tailWord_1169437, baseEnd_1169437] using wordTrace_append hprefix tailTrace_1169437
  have hstable : (prefixWord ++ tailWord_1169437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169437).length < 2 ^ (prefixWord ++ tailWord_1169437).sum := by decide
  have hdescent : baseEnd_1169437 < baseStart_1169437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169481 : List Nat := [1, 2, 1, 1, 2, 2, 5, 3, 2, 2, 2]
def baseStart_1169481 : Nat := 118140960795 + 1169481 * 2 ^ 59
def prefixEnd_1169481 : Nat := 4983230072969 + 3 ^ 40 * 1169481 * 2
def baseEnd_1169481 : Nat := 600505869300844133909161

theorem tailTrace_1169481 : CollatzResearch.WordTrace tailWord_1169481 prefixEnd_1169481 600505869300844133909161 := by
  unfold tailWord_1169481
  simp only [CollatzResearch.WordTrace]
  refine ⟨42654476276177543298476297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28436317517451695532317531 42654476276177543298476297)
  ·
    refine ⟨31990857207133157473857223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42654476276177543298476297 31990857207133157473857223)
    ·
      refine ⟨47986285810699736210785835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31990857207133157473857223 47986285810699736210785835)
      ·
        refine ⟨71979428716049604316178753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47986285810699736210785835 71979428716049604316178753)
        ·
          refine ⟨53984571537037203237134065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71979428716049604316178753 53984571537037203237134065)
          ·
            refine ⟨40488428652777902427850549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53984571537037203237134065 40488428652777902427850549)
            ·
              refine ⟨3795790186197928352610989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40488428652777902427850549 3795790186197928352610989)
              ·
                refine ⟨1423421319824223132229121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3795790186197928352610989 1423421319824223132229121)
                ·
                  refine ⟨1067565989868167349171841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1423421319824223132229121 1067565989868167349171841)
                  ·
                    refine ⟨800674492401125511878881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1067565989868167349171841 800674492401125511878881)
                    ·
                      refine ⟨600505869300844133909161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 800674492401125511878881 600505869300844133909161)
                      ·
                        rfl

theorem cell23_1169481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 2, 2].length) (baseStart_1169481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169481 prefixEnd_1169481 := by exact prefixLift 1169481
  have htrace : WordTrace (prefixWord ++ tailWord_1169481) baseStart_1169481 baseEnd_1169481 := by
    simpa [prefixWord, tailWord_1169481, baseEnd_1169481] using wordTrace_append hprefix tailTrace_1169481
  have hstable : (prefixWord ++ tailWord_1169481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169481).length < 2 ^ (prefixWord ++ tailWord_1169481).sum := by decide
  have hdescent : baseEnd_1169481 < baseStart_1169481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169527 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 5]
def baseStart_1169527 : Nat := 118140960795 + 1169527 * 2 ^ 59
def prefixEnd_1169527 : Nat := 4983230072969 + 3 ^ 40 * 1169527 * 2
def baseEnd_1169527 : Nat := 600529489410950953933949

theorem tailTrace_1169527 : CollatzResearch.WordTrace tailWord_1169527 prefixEnd_1169527 600529489410950953933949 := by
  unfold tailWord_1169527
  simp only [CollatzResearch.WordTrace]
  refine ⟨42656154034010893154650835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28437436022673928769767223 42656154034010893154650835)
  ·
    refine ⟨63984231051016339731976253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42656154034010893154650835 63984231051016339731976253)
    ·
      refine ⟨23994086644131127399491095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63984231051016339731976253 23994086644131127399491095)
      ·
        refine ⟨35991129966196691099236643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23994086644131127399491095 35991129966196691099236643)
        ·
          refine ⟨53986694949295036648854965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35991129966196691099236643 53986694949295036648854965)
          ·
            refine ⟨5061252651496409685830153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53986694949295036648854965 5061252651496409685830153)
            ·
              refine ⟨3795939488622307264372615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5061252651496409685830153 3795939488622307264372615)
              ·
                refine ⟨5693909232933460896558923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3795939488622307264372615 5693909232933460896558923)
                ·
                  refine ⟨8540863849400191344838385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5693909232933460896558923 8540863849400191344838385)
                  ·
                    refine ⟨6405647887050143508628789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8540863849400191344838385 6405647887050143508628789)
                    ·
                      refine ⟨600529489410950953933949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6405647887050143508628789 600529489410950953933949)
                      ·
                        rfl

theorem cell23_1169527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_1169527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169527 prefixEnd_1169527 := by exact prefixLift 1169527
  have htrace : WordTrace (prefixWord ++ tailWord_1169527) baseStart_1169527 baseEnd_1169527 := by
    simpa [prefixWord, tailWord_1169527, baseEnd_1169527] using wordTrace_append hprefix tailTrace_1169527
  have hstable : (prefixWord ++ tailWord_1169527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169527).length < 2 ^ (prefixWord ++ tailWord_1169527).sum := by decide
  have hdescent : baseEnd_1169527 < baseStart_1169527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169554 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_1169554 : Nat := 118140960795 + 1169554 * 2 ^ 59
def prefixEnd_1169554 : Nat := 4983230072969 + 3 ^ 40 * 1169554 * 2
def baseEnd_1169554 : Nat := 600543353388622348296325

theorem tailTrace_1169554 : CollatzResearch.WordTrace tailWord_1169554 prefixEnd_1169554 600543353388622348296325 := by
  unfold tailWord_1169554
  simp only [CollatzResearch.WordTrace]
  refine ⟨10664284701228269191470929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28438092536608717843922477 10664284701228269191470929)
  ·
    refine ⟨7998213525921201893603197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10664284701228269191470929 7998213525921201893603197)
    ·
      refine ⟨2999330072220450710101199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7998213525921201893603197 2999330072220450710101199)
      ·
        refine ⟨4498995108330676065151799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2999330072220450710101199 4498995108330676065151799)
        ·
          refine ⟨6748492662496014097727699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4498995108330676065151799 6748492662496014097727699)
          ·
            refine ⟨10122738993744021146591549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6748492662496014097727699 10122738993744021146591549)
            ·
              refine ⟨3796027122654007929971831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10122738993744021146591549 3796027122654007929971831)
              ·
                refine ⟨5694040683981011894957747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3796027122654007929971831 5694040683981011894957747)
                ·
                  refine ⟨8541061025971517842436621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5694040683981011894957747 8541061025971517842436621)
                  ·
                    refine ⟨3202897884739319190913733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8541061025971517842436621 3202897884739319190913733)
                    ·
                      refine ⟨600543353388622348296325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3202897884739319190913733 600543353388622348296325)
                      ·
                        rfl

theorem cell23_1169554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_1169554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169554 prefixEnd_1169554 := by exact prefixLift 1169554
  have htrace : WordTrace (prefixWord ++ tailWord_1169554) baseStart_1169554 baseEnd_1169554 := by
    simpa [prefixWord, tailWord_1169554, baseEnd_1169554] using wordTrace_append hprefix tailTrace_1169554
  have hstable : (prefixWord ++ tailWord_1169554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169554).length < 2 ^ (prefixWord ++ tailWord_1169554).sum := by decide
  have hdescent : baseEnd_1169554 < baseStart_1169554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169564 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 5, 4]
def baseStart_1169564 : Nat := 118140960795 + 1169564 * 2 ^ 59
def prefixEnd_1169564 : Nat := 4983230072969 + 3 ^ 40 * 1169564 * 2
def baseEnd_1169564 : Nat := 200182829398389103057093

theorem tailTrace_1169564 : CollatzResearch.WordTrace tailWord_1169564 prefixEnd_1169564 200182829398389103057093 := by
  unfold tailWord_1169564
  simp only [CollatzResearch.WordTrace]
  refine ⟨21328751767438424236873873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28438335689917898982498497 21328751767438424236873873)
  ·
    refine ⟨15996563825578818177655405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21328751767438424236873873 15996563825578818177655405)
    ·
      refine ⟨5998711434592056816620777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15996563825578818177655405 5998711434592056816620777)
      ·
        refine ⟨4499033575944042612465583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5998711434592056816620777 4499033575944042612465583)
        ·
          refine ⟨6748550363916063918698375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4499033575944042612465583 6748550363916063918698375)
          ·
            refine ⟨10122825545874095878047563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6748550363916063918698375 10122825545874095878047563)
            ·
              refine ⟨15184238318811143817071345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10122825545874095878047563 15184238318811143817071345)
              ·
                refine ⟨11388178739108357862803509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15184238318811143817071345 11388178739108357862803509)
                ·
                  refine ⟨1067641756791408549637829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11388178739108357862803509 1067641756791408549637829)
                  ·
                    refine ⟨200182829398389103057093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1067641756791408549637829 200182829398389103057093)
                    ·
                      rfl

theorem cell23_1169564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_1169564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169564 prefixEnd_1169564 := by exact prefixLift 1169564
  have htrace : WordTrace (prefixWord ++ tailWord_1169564) baseStart_1169564 baseEnd_1169564 := by
    simpa [prefixWord, tailWord_1169564, baseEnd_1169564] using wordTrace_append hprefix tailTrace_1169564
  have hstable : (prefixWord ++ tailWord_1169564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169564).length < 2 ^ (prefixWord ++ tailWord_1169564).sum := by decide
  have hdescent : baseEnd_1169564 < baseStart_1169564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169581 : List Nat := [1, 5, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_1169581 : Nat := 118140960795 + 1169581 * 2 ^ 59
def prefixEnd_1169581 : Nat := 4983230072969 + 3 ^ 40 * 1169581 * 2
def baseEnd_1169581 : Nat := 200185739122097914219567

theorem tailTrace_1169581 : CollatzResearch.WordTrace tailWord_1169581 prefixEnd_1169581 200185739122097914219567 := by
  unfold tailWord_1169581
  simp only [CollatzResearch.WordTrace]
  refine ⟨42658123575815260377116597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28438749050543506918077731 42658123575815260377116597)
  ·
    refine ⟨3999199085232680660354681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42658123575815260377116597 3999199085232680660354681)
    ·
      refine ⟨2999399313924510495266011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3999199085232680660354681 2999399313924510495266011)
      ·
        refine ⟨4499098970886765742899017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2999399313924510495266011 4499098970886765742899017)
        ·
          refine ⟨3374324228165074307174263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4499098970886765742899017 3374324228165074307174263)
          ·
            refine ⟨5061486342247611460761395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3374324228165074307174263 5061486342247611460761395)
            ·
              refine ⟨7592229513371417191142093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5061486342247611460761395 7592229513371417191142093)
              ·
                refine ⟨2847086067514281446678285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7592229513371417191142093 2847086067514281446678285)
                ·
                  refine ⟨1067657275317855542504357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2847086067514281446678285 1067657275317855542504357)
                  ·
                    refine ⟨200185739122097914219567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1067657275317855542504357 200185739122097914219567)
                    ·
                      rfl

theorem cell23_1169581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_1169581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169581 prefixEnd_1169581 := by exact prefixLift 1169581
  have htrace : WordTrace (prefixWord ++ tailWord_1169581) baseStart_1169581 baseEnd_1169581 := by
    simpa [prefixWord, tailWord_1169581, baseEnd_1169581] using wordTrace_append hprefix tailTrace_1169581
  have hstable : (prefixWord ++ tailWord_1169581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169581).length < 2 ^ (prefixWord ++ tailWord_1169581).sum := by decide
  have hdescent : baseEnd_1169581 < baseStart_1169581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169597 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_1169597 : Nat := 118140960795 + 1169597 * 2 ^ 59
def prefixEnd_1169597 : Nat := 4983230072969 + 3 ^ 40 * 1169597 * 2
def baseEnd_1169597 : Nat := 600565433056765680058627

theorem tailTrace_1169597 : CollatzResearch.WordTrace tailWord_1169597 prefixEnd_1169597 600565433056765680058627 := by
  unfold tailWord_1169597
  simp only [CollatzResearch.WordTrace]
  refine ⟨42658707143757295109699045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28439138095838196739799363 42658707143757295109699045)
  ·
    refine ⟨7998507589454492833068571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42658707143757295109699045 7998507589454492833068571)
    ·
      refine ⟨11997761384181739249602857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7998507589454492833068571 11997761384181739249602857)
      ·
        refine ⟨8998321038136304437202143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11997761384181739249602857 8998321038136304437202143)
        ·
          refine ⟨13497481557204456655803215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8998321038136304437202143 13497481557204456655803215)
          ·
            refine ⟨20246222335806684983704823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13497481557204456655803215 20246222335806684983704823)
            ·
              refine ⟨30369333503710027475557235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20246222335806684983704823 30369333503710027475557235)
              ·
                refine ⟨45554000255565041213335853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30369333503710027475557235 45554000255565041213335853)
                ·
                  refine ⟨17082750095836890455000945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45554000255565041213335853 17082750095836890455000945)
                  ·
                    refine ⟨12812062571877667841250709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17082750095836890455000945 12812062571877667841250709)
                    ·
                      refine ⟨600565433056765680058627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12812062571877667841250709 600565433056765680058627)
                      ·
                        rfl

theorem cell23_1169597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_1169597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169597 prefixEnd_1169597 := by exact prefixLift 1169597
  have htrace : WordTrace (prefixWord ++ tailWord_1169597) baseStart_1169597 baseEnd_1169597 := by
    simpa [prefixWord, tailWord_1169597, baseEnd_1169597] using wordTrace_append hprefix tailTrace_1169597
  have hstable : (prefixWord ++ tailWord_1169597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169597).length < 2 ^ (prefixWord ++ tailWord_1169597).sum := by decide
  have hdescent : baseEnd_1169597 < baseStart_1169597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169644 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 4]
def baseStart_1169644 : Nat := 118140960795 + 1169644 * 2 ^ 59
def prefixEnd_1169644 : Nat := 4983230072969 + 3 ^ 40 * 1169644 * 2
def baseEnd_1169644 : Nat := 600589566647526996170911

theorem tailTrace_1169644 : CollatzResearch.WordTrace tailWord_1169644 prefixEnd_1169644 600589566647526996170911 := by
  unfold tailWord_1169644
  simp only [CollatzResearch.WordTrace]
  refine ⟨21330210687293511068329993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28440280916391348091106657 21330210687293511068329993)
  ·
    refine ⟨15997658015470133301247495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21330210687293511068329993 15997658015470133301247495)
    ·
      refine ⟨23996487023205199951871243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15997658015470133301247495 23996487023205199951871243)
      ·
        refine ⟨35994730534807799927806865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23996487023205199951871243 35994730534807799927806865)
        ·
          refine ⟨26996047901105849945855149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35994730534807799927806865 26996047901105849945855149)
          ·
            refine ⟨10123517962914693729695681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26996047901105849945855149 10123517962914693729695681)
            ·
              refine ⟨7592638472186020297271761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10123517962914693729695681 7592638472186020297271761)
              ·
                refine ⟨5694478854139515222953821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7592638472186020297271761 5694478854139515222953821)
                ·
                  refine ⟨2135429570302318208607683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5694478854139515222953821 2135429570302318208607683)
                  ·
                    refine ⟨3203144355453477312911525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2135429570302318208607683 3203144355453477312911525)
                    ·
                      refine ⟨600589566647526996170911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3203144355453477312911525 600589566647526996170911)
                      ·
                        rfl

theorem cell23_1169644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_1169644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169644 prefixEnd_1169644 := by exact prefixLift 1169644
  have htrace : WordTrace (prefixWord ++ tailWord_1169644) baseStart_1169644 baseEnd_1169644 := by
    simpa [prefixWord, tailWord_1169644, baseEnd_1169644] using wordTrace_append hprefix tailTrace_1169644
  have hstable : (prefixWord ++ tailWord_1169644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169644).length < 2 ^ (prefixWord ++ tailWord_1169644).sum := by decide
  have hdescent : baseEnd_1169644 < baseStart_1169644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169645 : List Nat := [1, 5, 1, 2, 4, 1, 2, 1, 6]
def baseStart_1169645 : Nat := 118140960795 + 1169645 * 2 ^ 59
def prefixEnd_1169645 : Nat := 4983230072969 + 3 ^ 40 * 1169645 * 2
def baseEnd_1169645 : Nat := 66732231125353499139823

theorem tailTrace_1169645 : CollatzResearch.WordTrace tailWord_1169645 prefixEnd_1169645 66732231125353499139823 := by
  unfold tailWord_1169645
  simp only [CollatzResearch.WordTrace]
  refine ⟨42660457847583399307446389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28440305231722266204964259 42660457847583399307446389)
  ·
    refine ⟨3999417923210943685073099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42660457847583399307446389 3999417923210943685073099)
    ·
      refine ⟨5999126884816415527609649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3999417923210943685073099 5999126884816415527609649)
      ·
        refine ⟨4499345163612311645707237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5999126884816415527609649 4499345163612311645707237)
        ·
          refine ⟨843627218177308433570107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4499345163612311645707237 843627218177308433570107)
          ·
            refine ⟨1265440827265962650355161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 843627218177308433570107 1265440827265962650355161)
            ·
              refine ⟨949080620449471987766371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1265440827265962650355161 949080620449471987766371)
              ·
                refine ⟨1423620930674207981649557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 949080620449471987766371 1423620930674207981649557)
                ·
                  refine ⟨66732231125353499139823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1423620930674207981649557 66732231125353499139823)
                  ·
                    rfl

theorem cell23_1169645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_1169645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169645 prefixEnd_1169645 := by exact prefixLift 1169645
  have htrace : WordTrace (prefixWord ++ tailWord_1169645) baseStart_1169645 baseEnd_1169645 := by
    simpa [prefixWord, tailWord_1169645, baseEnd_1169645] using wordTrace_append hprefix tailTrace_1169645
  have hstable : (prefixWord ++ tailWord_1169645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169645).length < 2 ^ (prefixWord ++ tailWord_1169645).sum := by decide
  have hdescent : baseEnd_1169645 < baseStart_1169645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169667 : List Nat := [1, 1, 1, 3, 2, 3, 1, 11]
def baseStart_1169667 : Nat := 118140960795 + 1169667 * 2 ^ 59
def prefixEnd_1169667 : Nat := 4983230072969 + 3 ^ 40 * 1169667 * 2
def baseEnd_1169667 : Nat := 22244495433428903932715

theorem tailTrace_1169667 : CollatzResearch.WordTrace tailWord_1169667 prefixEnd_1169667 22244495433428903932715 := by
  unfold tailWord_1169667
  simp only [CollatzResearch.WordTrace]
  refine ⟨42661260253503697064747255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28440840169002464709831503 42661260253503697064747255)
  ·
    refine ⟨63991890380255545597120883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42661260253503697064747255 63991890380255545597120883)
    ·
      refine ⟨95987835570383318395681325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63991890380255545597120883 95987835570383318395681325)
      ·
        refine ⟨35995438338893744398380497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95987835570383318395681325 35995438338893744398380497)
        ·
          refine ⟨26996578754170308298785373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35995438338893744398380497 26996578754170308298785373)
          ·
            refine ⟨10123717032813865612044515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26996578754170308298785373 10123717032813865612044515)
            ·
              refine ⟨15185575549220798418066773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10123717032813865612044515 15185575549220798418066773)
              ·
                refine ⟨22244495433428903932715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 15185575549220798418066773 22244495433428903932715)
                ·
                  rfl

theorem cell23_1169667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 11].length) (baseStart_1169667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169667 prefixEnd_1169667 := by exact prefixLift 1169667
  have htrace : WordTrace (prefixWord ++ tailWord_1169667) baseStart_1169667 baseEnd_1169667 := by
    simpa [prefixWord, tailWord_1169667, baseEnd_1169667] using wordTrace_append hprefix tailTrace_1169667
  have hstable : (prefixWord ++ tailWord_1169667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169667).length < 2 ^ (prefixWord ++ tailWord_1169667).sum := by decide
  have hdescent : baseEnd_1169667 < baseStart_1169667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169674 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_1169674 : Nat := 118140960795 + 1169674 * 2 ^ 59
def prefixEnd_1169674 : Nat := 4983230072969 + 3 ^ 40 * 1169674 * 2
def baseEnd_1169674 : Nat := 600604971067161878795773

theorem tailTrace_1169674 : CollatzResearch.WordTrace tailWord_1169674 prefixEnd_1169674 600604971067161878795773 := by
  unfold tailWord_1169674
  simp only [CollatzResearch.WordTrace]
  refine ⟨10665378891119584315063019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28441010376318891506834717 10665378891119584315063019)
  ·
    refine ⟨15998068336679376472594529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10665378891119584315063019 15998068336679376472594529)
    ·
      refine ⟨11998551252509532354445897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15998068336679376472594529 11998551252509532354445897)
      ·
        refine ⟨8998913439382149265834423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11998551252509532354445897 8998913439382149265834423)
        ·
          refine ⟨13498370159073223898751635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8998913439382149265834423 13498370159073223898751635)
          ·
            refine ⟨20247555238609835848127453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13498370159073223898751635 20247555238609835848127453)
            ·
              refine ⟨7592833214478688443047795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20247555238609835848127453 7592833214478688443047795)
              ·
                refine ⟨11389249821718032664571693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7592833214478688443047795 11389249821718032664571693)
                ·
                  refine ⟨4270968683144262249214385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11389249821718032664571693 4270968683144262249214385)
                  ·
                    refine ⟨3203226512358196686910789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4270968683144262249214385 3203226512358196686910789)
                    ·
                      refine ⟨600604971067161878795773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3203226512358196686910789 600604971067161878795773)
                      ·
                        rfl

theorem cell23_1169674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_1169674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169674 prefixEnd_1169674 := by exact prefixLift 1169674
  have htrace : WordTrace (prefixWord ++ tailWord_1169674) baseStart_1169674 baseEnd_1169674 := by
    simpa [prefixWord, tailWord_1169674, baseEnd_1169674] using wordTrace_append hprefix tailTrace_1169674
  have hstable : (prefixWord ++ tailWord_1169674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169674).length < 2 ^ (prefixWord ++ tailWord_1169674).sum := by decide
  have hdescent : baseEnd_1169674 < baseStart_1169674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169678 : List Nat := [4, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4]
def baseStart_1169678 : Nat := 118140960795 + 1169678 * 2 ^ 59
def prefixEnd_1169678 : Nat := 4983230072969 + 3 ^ 40 * 1169678 * 2
def baseEnd_1169678 : Nat := 600607024989779863145755

theorem tailTrace_1169678 : CollatzResearch.WordTrace tailWord_1169678 prefixEnd_1169678 600607024989779863145755 := by
  unfold tailWord_1169678
  simp only [CollatzResearch.WordTrace]
  refine ⟨5332707682057980742924711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28441107637642563962265125 5332707682057980742924711)
  ·
    refine ⟨7999061523086971114387067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5332707682057980742924711 7999061523086971114387067)
    ·
      refine ⟨11998592284630456671580601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7999061523086971114387067 11998592284630456671580601)
      ·
        refine ⟨8998944213472842503685451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11998592284630456671580601 8998944213472842503685451)
        ·
          refine ⟨13498416320209263755528177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8998944213472842503685451 13498416320209263755528177)
          ·
            refine ⟨10123812240156947816646133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13498416320209263755528177 10123812240156947816646133)
            ·
              refine ⟨949107397514713857810575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10123812240156947816646133 949107397514713857810575)
              ·
                refine ⟨1423661096272070786715863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 949107397514713857810575 1423661096272070786715863)
                ·
                  refine ⟨2135491644408106180073795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1423661096272070786715863 2135491644408106180073795)
                  ·
                    refine ⟨3203237466612159270110693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2135491644408106180073795 3203237466612159270110693)
                    ·
                      refine ⟨600607024989779863145755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3203237466612159270110693 600607024989779863145755)
                      ·
                        rfl

theorem cell23_1169678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_1169678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169678 prefixEnd_1169678 := by exact prefixLift 1169678
  have htrace : WordTrace (prefixWord ++ tailWord_1169678) baseStart_1169678 baseEnd_1169678 := by
    simpa [prefixWord, tailWord_1169678, baseEnd_1169678] using wordTrace_append hprefix tailTrace_1169678
  have hstable : (prefixWord ++ tailWord_1169678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169678).length < 2 ^ (prefixWord ++ tailWord_1169678).sum := by decide
  have hdescent : baseEnd_1169678 < baseStart_1169678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169681 : List Nat := [1, 2, 2, 1, 1, 7, 1, 1, 1, 1, 5]
def baseStart_1169681 : Nat := 118140960795 + 1169681 * 2 ^ 59
def prefixEnd_1169681 : Nat := 4983230072969 + 3 ^ 40 * 1169681 * 2
def baseEnd_1169681 : Nat := 600608565431743351408241

theorem tailTrace_1169681 : CollatzResearch.WordTrace tailWord_1169681 prefixEnd_1169681 600608565431743351408241 := by
  unfold tailWord_1169681
  simp only [CollatzResearch.WordTrace]
  refine ⟨42661770875452977455756897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28441180583635318303837931 42661770875452977455756897)
  ·
    refine ⟨31996328156589733091817673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42661770875452977455756897 31996328156589733091817673)
    ·
      refine ⟨23997246117442299818863255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31996328156589733091817673 23997246117442299818863255)
      ·
        refine ⟨35995869176163449728294883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23997246117442299818863255 35995869176163449728294883)
        ·
          refine ⟨53993803764245174592442325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35995869176163449728294883 53993803764245174592442325)
          ·
            refine ⟨1265479775724496279510367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 53993803764245174592442325 1265479775724496279510367)
            ·
              refine ⟨1898219663586744419265551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265479775724496279510367 1898219663586744419265551)
              ·
                refine ⟨2847329495380116628898327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1898219663586744419265551 2847329495380116628898327)
                ·
                  refine ⟨4270994243070174943347491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2847329495380116628898327 4270994243070174943347491)
                  ·
                    refine ⟨6406491364605262415021237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4270994243070174943347491 6406491364605262415021237)
                    ·
                      refine ⟨600608565431743351408241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6406491364605262415021237 600608565431743351408241)
                      ·
                        rfl

theorem cell23_1169681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 1, 5].length) (baseStart_1169681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169681 prefixEnd_1169681 := by exact prefixLift 1169681
  have htrace : WordTrace (prefixWord ++ tailWord_1169681) baseStart_1169681 baseEnd_1169681 := by
    simpa [prefixWord, tailWord_1169681, baseEnd_1169681] using wordTrace_append hprefix tailTrace_1169681
  have hstable : (prefixWord ++ tailWord_1169681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169681).length < 2 ^ (prefixWord ++ tailWord_1169681).sum := by decide
  have hdescent : baseEnd_1169681 < baseStart_1169681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169701 : List Nat := [1, 3, 1, 2, 5, 2, 1, 8]
def baseStart_1169701 : Nat := 118140960795 + 1169701 * 2 ^ 59
def prefixEnd_1169701 : Nat := 4983230072969 + 3 ^ 40 * 1169701 * 2
def baseEnd_1169701 : Nat := 22245142038697528635487

theorem tailTrace_1169701 : CollatzResearch.WordTrace tailWord_1169701 prefixEnd_1169701 22245142038697528635487 := by
  unfold tailWord_1169701
  simp only [CollatzResearch.WordTrace]
  refine ⟨42662500335380520871484957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28441666890253680580989971 42662500335380520871484957)
  ·
    refine ⟨15998437625767695326806859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42662500335380520871484957 15998437625767695326806859)
    ·
      refine ⟨23997656438651542990210289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15998437625767695326806859 23997656438651542990210289)
      ·
        refine ⟨17998242328988657242657717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23997656438651542990210289 17998242328988657242657717)
        ·
          refine ⟨1687335218342686616499161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17998242328988657242657717 1687335218342686616499161)
          ·
            refine ⟨1265501413757014962374371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1687335218342686616499161 1265501413757014962374371)
            ·
              refine ⟨1898252120635522443561557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265501413757014962374371 1898252120635522443561557)
              ·
                refine ⟨22245142038697528635487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1898252120635522443561557 22245142038697528635487)
                ·
                  rfl

theorem cell23_1169701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 8].length) (baseStart_1169701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169701 prefixEnd_1169701 := by exact prefixLift 1169701
  have htrace : WordTrace (prefixWord ++ tailWord_1169701) baseStart_1169701 baseEnd_1169701 := by
    simpa [prefixWord, tailWord_1169701, baseEnd_1169701] using wordTrace_append hprefix tailTrace_1169701
  have hstable : (prefixWord ++ tailWord_1169701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169701).length < 2 ^ (prefixWord ++ tailWord_1169701).sum := by decide
  have hdescent : baseEnd_1169701 < baseStart_1169701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169724 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_1169724 : Nat := 118140960795 + 1169724 * 2 ^ 59
def prefixEnd_1169724 : Nat := 4983230072969 + 3 ^ 40 * 1169724 * 2
def baseEnd_1169724 : Nat := 600630645099886683170543

theorem tailTrace_1169724 : CollatzResearch.WordTrace tailWord_1169724 prefixEnd_1169724 600630645099886683170543 := by
  unfold tailWord_1169724
  simp only [CollatzResearch.WordTrace]
  refine ⟨21331669607148597899786113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28442226142864797199714817 21331669607148597899786113)
  ·
    refine ⟨15998752205361448424839585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21331669607148597899786113 15998752205361448424839585)
    ·
      refine ⟨11999064154021086318629689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15998752205361448424839585 11999064154021086318629689)
      ·
        refine ⟨8999298115515814738972267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11999064154021086318629689 8999298115515814738972267)
        ·
          refine ⟨13498947173273722108458401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8999298115515814738972267 13498947173273722108458401)
          ·
            refine ⟨10124210379955291581343801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13498947173273722108458401 10124210379955291581343801)
            ·
              refine ⟨7593157784966468686007851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10124210379955291581343801 7593157784966468686007851)
              ·
                refine ⟨11389736677449703029011777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7593157784966468686007851 11389736677449703029011777)
                ·
                  refine ⟨8542302508087277271758833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11389736677449703029011777 8542302508087277271758833)
                  ·
                    refine ⟨6406726881065457953819125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8542302508087277271758833 6406726881065457953819125)
                    ·
                      refine ⟨600630645099886683170543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6406726881065457953819125 600630645099886683170543)
                      ·
                        rfl

theorem cell23_1169724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_1169724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169724 prefixEnd_1169724 := by exact prefixLift 1169724
  have htrace : WordTrace (prefixWord ++ tailWord_1169724) baseStart_1169724 baseEnd_1169724 := by
    simpa [prefixWord, tailWord_1169724, baseEnd_1169724] using wordTrace_append hprefix tailTrace_1169724
  have hstable : (prefixWord ++ tailWord_1169724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169724).length < 2 ^ (prefixWord ++ tailWord_1169724).sum := by decide
  have hdescent : baseEnd_1169724 < baseStart_1169724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169729 : List Nat := [1, 2, 5, 2, 2, 1, 2, 3, 1, 2, 2]
def baseStart_1169729 : Nat := 118140960795 + 1169729 * 2 ^ 59
def prefixEnd_1169729 : Nat := 4983230072969 + 3 ^ 40 * 1169729 * 2
def baseEnd_1169729 : Nat := 600633212503159163608021

theorem tailTrace_1169729 : CollatzResearch.WordTrace tailWord_1169729 prefixEnd_1169729 600633212503159163608021 := by
  unfold tailWord_1169729
  simp only [CollatzResearch.WordTrace]
  refine ⟨42663521579279081653504241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28442347719519387769002827 42663521579279081653504241)
  ·
    refine ⟨31997641184459311240128181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42663521579279081653504241 31997641184459311240128181)
    ·
      refine ⟨2999778861043060428762017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31997641184459311240128181 2999778861043060428762017)
      ·
        refine ⟨2249834145782295321571513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2999778861043060428762017 2249834145782295321571513)
        ·
          refine ⟨1687375609336721491178635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2249834145782295321571513 1687375609336721491178635)
          ·
            refine ⟨2531063414005082236767953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1687375609336721491178635 2531063414005082236767953)
            ·
              refine ⟨1898297560503811677575965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2531063414005082236767953 1898297560503811677575965)
              ·
                refine ⟨711861585188929379090987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1898297560503811677575965 711861585188929379090987)
                ·
                  refine ⟨1067792377783394068636481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711861585188929379090987 1067792377783394068636481)
                  ·
                    refine ⟨800844283337545551477361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1067792377783394068636481 800844283337545551477361)
                    ·
                      refine ⟨600633212503159163608021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 800844283337545551477361 600633212503159163608021)
                      ·
                        rfl

theorem cell23_1169729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_1169729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169729 prefixEnd_1169729 := by exact prefixLift 1169729
  have htrace : WordTrace (prefixWord ++ tailWord_1169729) baseStart_1169729 baseEnd_1169729 := by
    simpa [prefixWord, tailWord_1169729, baseEnd_1169729] using wordTrace_append hprefix tailTrace_1169729
  have hstable : (prefixWord ++ tailWord_1169729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169729).length < 2 ^ (prefixWord ++ tailWord_1169729).sum := by decide
  have hdescent : baseEnd_1169729 < baseStart_1169729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169744 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 2, 6]
def baseStart_1169744 : Nat := 118140960795 + 1169744 * 2 ^ 59
def prefixEnd_1169744 : Nat := 4983230072969 + 3 ^ 40 * 1169744 * 2
def baseEnd_1169744 : Nat := 200213638237658868306817

theorem tailTrace_1169744 : CollatzResearch.WordTrace tailWord_1169744 prefixEnd_1169744 200213638237658868306817 := by
  unfold tailWord_1169744
  simp only [CollatzResearch.WordTrace]
  refine ⟨21332034337112369607650143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28442712449483159476866857 21332034337112369607650143)
  ·
    refine ⟨31998051505668554411475215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21332034337112369607650143 31998051505668554411475215)
    ·
      refine ⟨47997077258502831617212823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31998051505668554411475215 47997077258502831617212823)
      ·
        refine ⟨71995615887754247425819235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47997077258502831617212823 71995615887754247425819235)
        ·
          refine ⟨107993423831631371138728853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71995615887754247425819235 107993423831631371138728853)
          ·
            refine ⟨5062191742107720522127915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 107993423831631371138728853 5062191742107720522127915)
            ·
              refine ⟨7593287613161580783191873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5062191742107720522127915 7593287613161580783191873)
              ·
                refine ⟨5694965709871185587393905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7593287613161580783191873 5694965709871185587393905)
                ·
                  refine ⟨4271224282403389190545429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5694965709871185587393905 4271224282403389190545429)
                  ·
                    refine ⟨200213638237658868306817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4271224282403389190545429 200213638237658868306817)
                    ·
                      rfl

theorem cell23_1169744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 2, 6].length) (baseStart_1169744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169744 prefixEnd_1169744 := by exact prefixLift 1169744
  have htrace : WordTrace (prefixWord ++ tailWord_1169744) baseStart_1169744 baseEnd_1169744 := by
    simpa [prefixWord, tailWord_1169744, baseEnd_1169744] using wordTrace_append hprefix tailTrace_1169744
  have hstable : (prefixWord ++ tailWord_1169744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169744).length < 2 ^ (prefixWord ++ tailWord_1169744).sum := by decide
  have hdescent : baseEnd_1169744 < baseStart_1169744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169745 : List Nat := [1, 2, 2, 1, 4, 4, 1, 2, 2, 1, 3]
def baseStart_1169745 : Nat := 118140960795 + 1169745 * 2 ^ 59
def prefixEnd_1169745 : Nat := 4983230072969 + 3 ^ 40 * 1169745 * 2
def baseEnd_1169745 : Nat := 600641428193631101007947

theorem tailTrace_1169745 : CollatzResearch.WordTrace tailWord_1169745 prefixEnd_1169745 600641428193631101007947 := by
  unfold tailWord_1169745
  simp only [CollatzResearch.WordTrace]
  refine ⟨42664105147221116386086689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28442736764814077590724459 42664105147221116386086689)
  ·
    refine ⟨31998078860415837289565017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42664105147221116386086689 31998078860415837289565017)
    ·
      refine ⟨23998559145311877967173763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31998078860415837289565017 23998559145311877967173763)
      ·
        refine ⟨35997838717967816950760645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23998559145311877967173763 35997838717967816950760645)
        ·
          refine ⟨6749594759618965678267621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35997838717967816950760645 6749594759618965678267621)
          ·
            refine ⟨1265549017428556064675179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6749594759618965678267621 1265549017428556064675179)
            ·
              refine ⟨1898323526142834097012769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265549017428556064675179 1898323526142834097012769)
              ·
                refine ⟨1423742644607125572759577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1898323526142834097012769 1423742644607125572759577)
                ·
                  refine ⟨1067806983455344179569683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1423742644607125572759577 1067806983455344179569683)
                  ·
                    refine ⟨1601710475183016269354525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1067806983455344179569683 1601710475183016269354525)
                    ·
                      refine ⟨600641428193631101007947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1601710475183016269354525 600641428193631101007947)
                      ·
                        rfl

theorem cell23_1169745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 1, 3].length) (baseStart_1169745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169745 prefixEnd_1169745 := by exact prefixLift 1169745
  have htrace : WordTrace (prefixWord ++ tailWord_1169745) baseStart_1169745 baseEnd_1169745 := by
    simpa [prefixWord, tailWord_1169745, baseEnd_1169745] using wordTrace_append hprefix tailTrace_1169745
  have hstable : (prefixWord ++ tailWord_1169745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169745).length < 2 ^ (prefixWord ++ tailWord_1169745).sum := by decide
  have hdescent : baseEnd_1169745 < baseStart_1169745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169754 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5]
def baseStart_1169754 : Nat := 118140960795 + 1169754 * 2 ^ 59
def prefixEnd_1169754 : Nat := 4983230072969 + 3 ^ 40 * 1169754 * 2
def baseEnd_1169754 : Nat := 600646049519521565795405

theorem tailTrace_1169754 : CollatzResearch.WordTrace tailWord_1169754 prefixEnd_1169754 600646049519521565795405 := by
  unfold tailWord_1169754
  simp only [CollatzResearch.WordTrace]
  refine ⟨10666108351047127730791079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28442955602792340615442877 10666108351047127730791079)
  ·
    refine ⟨15999162526570691596186619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10666108351047127730791079 15999162526570691596186619)
    ·
      refine ⟨23998743789856037394279929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15999162526570691596186619 23998743789856037394279929)
      ·
        refine ⟨17999057842392028045709947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23998743789856037394279929 17999057842392028045709947)
        ·
          refine ⟨26998586763588042068564921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17999057842392028045709947 26998586763588042068564921)
          ·
            refine ⟨20248940072691031551423691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26998586763588042068564921 20248940072691031551423691)
            ·
              refine ⟨30373410109036547327135537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20248940072691031551423691 30373410109036547327135537)
              ·
                refine ⟨22780057581777410495351653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30373410109036547327135537 22780057581777410495351653)
                ·
                  refine ⟨4271260796583264467878435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22780057581777410495351653 4271260796583264467878435)
                  ·
                    refine ⟨6406891194874896701817653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4271260796583264467878435 6406891194874896701817653)
                    ·
                      refine ⟨600646049519521565795405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6406891194874896701817653 600646049519521565795405)
                      ·
                        rfl

theorem cell23_1169754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_1169754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169754 prefixEnd_1169754 := by exact prefixLift 1169754
  have htrace : WordTrace (prefixWord ++ tailWord_1169754) baseStart_1169754 baseEnd_1169754 := by
    simpa [prefixWord, tailWord_1169754, baseEnd_1169754] using wordTrace_append hprefix tailTrace_1169754
  have hstable : (prefixWord ++ tailWord_1169754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169754).length < 2 ^ (prefixWord ++ tailWord_1169754).sum := by decide
  have hdescent : baseEnd_1169754 < baseStart_1169754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169762 : List Nat := [3, 3, 2, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_1169762 : Nat := 118140960795 + 1169762 * 2 ^ 59
def prefixEnd_1169762 : Nat := 4983230072969 + 3 ^ 40 * 1169762 * 2
def baseEnd_1169762 : Nat := 600650157364757534495369

theorem tailTrace_1169762 : CollatzResearch.WordTrace tailWord_1169762 prefixEnd_1169762 600650157364757534495369 := by
  unfold tailWord_1169762
  simp only [CollatzResearch.WordTrace]
  refine ⟨10666181297039882072363885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28443150125439685526303693 10666181297039882072363885)
  ·
    refine ⟨3999817986389955777136457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10666181297039882072363885 3999817986389955777136457)
    ·
      refine ⟨2999863489792466832852343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3999817986389955777136457 2999863489792466832852343)
      ·
        refine ⟨4499795234688700249278515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2999863489792466832852343 4499795234688700249278515)
        ·
          refine ⟨6749692852033050373917773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4499795234688700249278515 6749692852033050373917773)
          ·
            refine ⟨2531134819512393890219165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6749692852033050373917773 2531134819512393890219165)
            ·
              refine ⟨949175557317147708832187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2531134819512393890219165 949175557317147708832187)
              ·
                refine ⟨1423763335975721563248281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 949175557317147708832187 1423763335975721563248281)
                ·
                  refine ⟨1067822501981791172436211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1423763335975721563248281 1067822501981791172436211)
                  ·
                    refine ⟨1601733752972686758654317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1067822501981791172436211 1601733752972686758654317)
                    ·
                      refine ⟨600650157364757534495369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1601733752972686758654317 600650157364757534495369)
                      ·
                        rfl

theorem cell23_1169762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_1169762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169762 prefixEnd_1169762 := by exact prefixLift 1169762
  have htrace : WordTrace (prefixWord ++ tailWord_1169762) baseStart_1169762 baseEnd_1169762 := by
    simpa [prefixWord, tailWord_1169762, baseEnd_1169762] using wordTrace_append hprefix tailTrace_1169762
  have hstable : (prefixWord ++ tailWord_1169762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169762).length < 2 ^ (prefixWord ++ tailWord_1169762).sum := by decide
  have hdescent : baseEnd_1169762 < baseStart_1169762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169881 : List Nat := [1, 2, 1, 2, 4, 1, 1, 5, 6]
def baseStart_1169881 : Nat := 118140960795 + 1169881 * 2 ^ 59
def prefixEnd_1169881 : Nat := 4983230072969 + 3 ^ 40 * 1169881 * 2
def baseEnd_1169881 : Nat := 66745695729182507656369

theorem tailTrace_1169881 : CollatzResearch.WordTrace tailWord_1169881 prefixEnd_1169881 66745695729182507656369 := by
  unfold tailWord_1169881
  simp only [CollatzResearch.WordTrace]
  refine ⟨42669065474728411613037497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28446043649818941075358331 42669065474728411613037497)
  ·
    refine ⟨32001799106046308709778123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42669065474728411613037497 32001799106046308709778123)
    ·
      refine ⟨48002698659069463064667185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32001799106046308709778123 48002698659069463064667185)
      ·
        refine ⟨36002023994302097298500389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48002698659069463064667185 36002023994302097298500389)
        ·
          refine ⟨6750379498931643243468823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36002023994302097298500389 6750379498931643243468823)
          ·
            refine ⟨10125569248397464865203235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6750379498931643243468823 10125569248397464865203235)
            ·
              refine ⟨15188353872596197297804853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10125569248397464865203235 15188353872596197297804853)
              ·
                refine ⟨1423908175555893496669205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15188353872596197297804853 1423908175555893496669205)
                ·
                  refine ⟨66745695729182507656369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1423908175555893496669205 66745695729182507656369)
                  ·
                    rfl

theorem cell23_1169881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 6].length) (baseStart_1169881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169881 prefixEnd_1169881 := by exact prefixLift 1169881
  have htrace : WordTrace (prefixWord ++ tailWord_1169881) baseStart_1169881 baseEnd_1169881 := by
    simpa [prefixWord, tailWord_1169881, baseEnd_1169881] using wordTrace_append hprefix tailTrace_1169881
  have hstable : (prefixWord ++ tailWord_1169881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169881).length < 2 ^ (prefixWord ++ tailWord_1169881).sum := by decide
  have hdescent : baseEnd_1169881 < baseStart_1169881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169902 : List Nat := [4, 1, 2, 1, 2, 3, 2, 3, 1, 4]
def baseStart_1169902 : Nat := 118140960795 + 1169902 * 2 ^ 59
def prefixEnd_1169902 : Nat := 4983230072969 + 3 ^ 40 * 1169902 * 2
def baseEnd_1169902 : Nat := 200240681552128995581575

theorem tailTrace_1169902 : CollatzResearch.WordTrace tailWord_1169902 prefixEnd_1169902 200240681552128995581575 := by
  unfold tailWord_1169902
  simp only [CollatzResearch.WordTrace]
  refine ⟨5333728925956541524943995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28446554271768221466367973 5333728925956541524943995)
  ·
    refine ⟨8000593388934812287415993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5333728925956541524943995 8000593388934812287415993)
    ·
      refine ⟨6000445041701109215561995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8000593388934812287415993 6000445041701109215561995)
      ·
        refine ⟨9000667562551663823342993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6000445041701109215561995 9000667562551663823342993)
        ·
          refine ⟨6750500671913747867507245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9000667562551663823342993 6750500671913747867507245)
          ·
            refine ⟨2531437751967655450315217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6750500671913747867507245 2531437751967655450315217)
            ·
              refine ⟨1898578313975741587736413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2531437751967655450315217 1898578313975741587736413)
              ·
                refine ⟨711966867740903095401155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1898578313975741587736413 711966867740903095401155)
                ·
                  refine ⟨1067950301611354643101733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711966867740903095401155 1067950301611354643101733)
                  ·
                    refine ⟨200240681552128995581575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1067950301611354643101733 200240681552128995581575)
                    ·
                      rfl

theorem cell23_1169902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_1169902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169902 prefixEnd_1169902 := by exact prefixLift 1169902
  have htrace : WordTrace (prefixWord ++ tailWord_1169902) baseStart_1169902 baseEnd_1169902 := by
    simpa [prefixWord, tailWord_1169902, baseEnd_1169902] using wordTrace_append hprefix tailTrace_1169902
  have hstable : (prefixWord ++ tailWord_1169902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169902).length < 2 ^ (prefixWord ++ tailWord_1169902).sum := by decide
  have hdescent : baseEnd_1169902 < baseStart_1169902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169951 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 5]
def baseStart_1169951 : Nat := 118140960795 + 1169951 * 2 ^ 59
def prefixEnd_1169951 : Nat := 4983230072969 + 3 ^ 40 * 1169951 * 2
def baseEnd_1169951 : Nat := 600747205208457295031999

theorem tailTrace_1169951 : CollatzResearch.WordTrace tailWord_1169951 prefixEnd_1169951 600747205208457295031999 := by
  unfold tailWord_1169951
  simp only [CollatzResearch.WordTrace]
  refine ⟨42671618584474813568085707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28447745722983209045390471 42671618584474813568085707)
  ·
    refine ⟨64007427876712220352128561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42671618584474813568085707 64007427876712220352128561)
    ·
      refine ⟨48005570907534165264096421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64007427876712220352128561 48005570907534165264096421)
      ·
        refine ⟨9001044545162655987018079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48005570907534165264096421 9001044545162655987018079)
        ·
          refine ⟨13501566817743983980527119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9001044545162655987018079 13501566817743983980527119)
          ·
            refine ⟨20252350226615975970790679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13501566817743983980527119 20252350226615975970790679)
            ·
              refine ⟨30378525339923963956186019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20252350226615975970790679 30378525339923963956186019)
              ·
                refine ⟨45567788009885945934279029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30378525339923963956186019 45567788009885945934279029)
                ·
                  refine ⟨4271980125926807431338659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45567788009885945934279029 4271980125926807431338659)
                  ·
                    refine ⟨6407970188890211147007989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4271980125926807431338659 6407970188890211147007989)
                    ·
                      refine ⟨600747205208457295031999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6407970188890211147007989 600747205208457295031999)
                      ·
                        rfl

theorem cell23_1169951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_1169951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1169951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1169951 prefixEnd_1169951 := by exact prefixLift 1169951
  have htrace : WordTrace (prefixWord ++ tailWord_1169951) baseStart_1169951 baseEnd_1169951 := by
    simpa [prefixWord, tailWord_1169951, baseEnd_1169951] using wordTrace_append hprefix tailTrace_1169951
  have hstable : (prefixWord ++ tailWord_1169951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169951).length < 2 ^ (prefixWord ++ tailWord_1169951).sum := by decide
  have hdescent : baseEnd_1169951 < baseStart_1169951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170048 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 2, 6]
def baseStart_1170048 : Nat := 118140960795 + 1170048 * 2 ^ 59
def prefixEnd_1170048 : Nat := 4983230072969 + 3 ^ 40 * 1170048 * 2
def baseEnd_1170048 : Nat := 200265670943981138506351

theorem tailTrace_1170048 : CollatzResearch.WordTrace tailWord_1170048 prefixEnd_1170048 200265670943981138506351 := by
  unfold tailWord_1170048
  simp only [CollatzResearch.WordTrace]
  refine ⟨21337578232561699567183399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28450104310082266089577865 21337578232561699567183399)
  ·
    refine ⟨32006367348842549350775099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21337578232561699567183399 32006367348842549350775099)
    ·
      refine ⟨48009551023263824026162649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32006367348842549350775099 48009551023263824026162649)
      ·
        refine ⟨36007163267447868019621987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48009551023263824026162649 36007163267447868019621987)
        ·
          refine ⟨54010744901171802029432981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36007163267447868019621987 54010744901171802029432981)
          ·
            refine ⟨2531753667242428220129671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 54010744901171802029432981 2531753667242428220129671)
            ·
              refine ⟨3797630500863642330194507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2531753667242428220129671 3797630500863642330194507)
              ·
                refine ⟨5696445751295463495291761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3797630500863642330194507 5696445751295463495291761)
                ·
                  refine ⟨4272334313471597621468821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5696445751295463495291761 4272334313471597621468821)
                  ·
                    refine ⟨200265670943981138506351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4272334313471597621468821 200265670943981138506351)
                    ·
                      rfl

theorem cell23_1170048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 2, 6].length) (baseStart_1170048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170048 prefixEnd_1170048 := by exact prefixLift 1170048
  have htrace : WordTrace (prefixWord ++ tailWord_1170048) baseStart_1170048 baseEnd_1170048 := by
    simpa [prefixWord, tailWord_1170048, baseEnd_1170048] using wordTrace_append hprefix tailTrace_1170048
  have hstable : (prefixWord ++ tailWord_1170048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170048).length < 2 ^ (prefixWord ++ tailWord_1170048).sum := by decide
  have hdescent : baseEnd_1170048 < baseStart_1170048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170072 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 4, 2, 2]
def baseStart_1170072 : Nat := 118140960795 + 1170072 * 2 ^ 59
def prefixEnd_1170072 : Nat := 4983230072969 + 3 ^ 40 * 1170072 * 2
def baseEnd_1170072 : Nat := 600809336367651321618943

theorem tailTrace_1170072 : CollatzResearch.WordTrace tailWord_1170072 prefixEnd_1170072 600809336367651321618943 := by
  unfold tailWord_1170072
  simp only [CollatzResearch.WordTrace]
  refine ⟨21338015908518225616620235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28450687878024300822160313 21338015908518225616620235)
  ·
    refine ⟨32007023862777338424930353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21338015908518225616620235 32007023862777338424930353)
    ·
      refine ⟨24005267897083003818697765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32007023862777338424930353 24005267897083003818697765)
      ·
        refine ⟨4500987730703063216005831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24005267897083003818697765 4500987730703063216005831)
        ·
          refine ⟨6751481596054594824008747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4500987730703063216005831 6751481596054594824008747)
          ·
            refine ⟨10127222394081892236013121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6751481596054594824008747 10127222394081892236013121)
            ·
              refine ⟨7595416795561419177009841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10127222394081892236013121 7595416795561419177009841)
              ·
                refine ⟨5696562596671064382757381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7595416795561419177009841 5696562596671064382757381)
                ·
                  refine ⟨1068105486875824571767009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5696562596671064382757381 1068105486875824571767009)
                  ·
                    refine ⟨801079115156868428825257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1068105486875824571767009 801079115156868428825257)
                    ·
                      refine ⟨600809336367651321618943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 801079115156868428825257 600809336367651321618943)
                      ·
                        rfl

theorem cell23_1170072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_1170072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170072 prefixEnd_1170072 := by exact prefixLift 1170072
  have htrace : WordTrace (prefixWord ++ tailWord_1170072) baseStart_1170072 baseEnd_1170072 := by
    simpa [prefixWord, tailWord_1170072, baseEnd_1170072] using wordTrace_append hprefix tailTrace_1170072
  have hstable : (prefixWord ++ tailWord_1170072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170072).length < 2 ^ (prefixWord ++ tailWord_1170072).sum := by decide
  have hdescent : baseEnd_1170072 < baseStart_1170072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170076 : List Nat := [2, 2, 3, 2, 2, 3, 2, 1, 1, 3, 2]
def baseStart_1170076 : Nat := 118140960795 + 1170076 * 2 ^ 59
def prefixEnd_1170076 : Nat := 4983230072969 + 3 ^ 40 * 1170076 * 2
def baseEnd_1170076 : Nat := 600811390290269305968925

theorem tailTrace_1170076 : CollatzResearch.WordTrace tailWord_1170076 prefixEnd_1170076 600811390290269305968925 := by
  unfold tailWord_1170076
  simp only [CollatzResearch.WordTrace]
  refine ⟨21338088854510979958193041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28450785139347973277590721 21338088854510979958193041)
  ·
    refine ⟨16003566640883234968644781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21338088854510979958193041 16003566640883234968644781)
    ·
      refine ⟨6001337490331213113241793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16003566640883234968644781 6001337490331213113241793)
      ·
        refine ⟨4501003117748409834931345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6001337490331213113241793 4501003117748409834931345)
        ·
          refine ⟨3375752338311307376198509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4501003117748409834931345 3375752338311307376198509)
          ·
            refine ⟨1265907126866740266074441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3375752338311307376198509 1265907126866740266074441)
            ·
              refine ⟨949430345150055199555831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1265907126866740266074441 949430345150055199555831)
              ·
                refine ⟨1424145517725082799333747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 949430345150055199555831 1424145517725082799333747)
                ·
                  refine ⟨2136218276587624199000621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1424145517725082799333747 2136218276587624199000621)
                  ·
                    refine ⟨801081853720359074625233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2136218276587624199000621 801081853720359074625233)
                    ·
                      refine ⟨600811390290269305968925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 801081853720359074625233 600811390290269305968925)
                      ·
                        rfl

theorem cell23_1170076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_1170076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170076 prefixEnd_1170076 := by exact prefixLift 1170076
  have htrace : WordTrace (prefixWord ++ tailWord_1170076) baseStart_1170076 baseEnd_1170076 := by
    simpa [prefixWord, tailWord_1170076, baseEnd_1170076] using wordTrace_append hprefix tailTrace_1170076
  have hstable : (prefixWord ++ tailWord_1170076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170076).length < 2 ^ (prefixWord ++ tailWord_1170076).sum := by decide
  have hdescent : baseEnd_1170076 < baseStart_1170076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170095 : List Nat := [1, 1, 2, 1, 2, 5, 2, 4, 5]
def baseStart_1170095 : Nat := 118140960795 + 1170095 * 2 ^ 59
def prefixEnd_1170095 : Nat := 4983230072969 + 3 ^ 40 * 1170095 * 2
def baseEnd_1170095 : Nat := 66757905158078303514593

theorem tailTrace_1170095 : CollatzResearch.WordTrace tailWord_1170095 prefixEnd_1170095 66757905158078303514593 := by
  unfold tailWord_1170095
  simp only [CollatzResearch.WordTrace]
  refine ⟨42676870695953126161327739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28451247130635417440885159 42676870695953126161327739)
  ·
    refine ⟨64015306043929689241991609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42676870695953126161327739 64015306043929689241991609)
    ·
      refine ⟨48011479532947266931493707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64015306043929689241991609 48011479532947266931493707)
      ·
        refine ⟨72017219299420900397240561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48011479532947266931493707 72017219299420900397240561)
        ·
          refine ⟨54012914474565675297930421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72017219299420900397240561 54012914474565675297930421)
          ·
            refine ⟨5063710731990532059180977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54012914474565675297930421 5063710731990532059180977)
            ·
              refine ⟨3797783048992899044385733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5063710731990532059180977 3797783048992899044385733)
              ·
                refine ⟨712084321686168570822325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3797783048992899044385733 712084321686168570822325)
                ·
                  refine ⟨66757905158078303514593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 712084321686168570822325 66757905158078303514593)
                  ·
                    rfl

theorem cell23_1170095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 5].length) (baseStart_1170095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170095 prefixEnd_1170095 := by exact prefixLift 1170095
  have htrace : WordTrace (prefixWord ++ tailWord_1170095) baseStart_1170095 baseEnd_1170095 := by
    simpa [prefixWord, tailWord_1170095, baseEnd_1170095] using wordTrace_append hprefix tailTrace_1170095
  have hstable : (prefixWord ++ tailWord_1170095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170095).length < 2 ^ (prefixWord ++ tailWord_1170095).sum := by decide
  have hdescent : baseEnd_1170095 < baseStart_1170095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170108 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 3, 7]
def baseStart_1170108 : Nat := 118140960795 + 1170108 * 2 ^ 59
def prefixEnd_1170108 : Nat := 4983230072969 + 3 ^ 40 * 1170108 * 2
def baseEnd_1170108 : Nat := 200275940557071060256259

theorem tailTrace_1170108 : CollatzResearch.WordTrace tailWord_1170108 prefixEnd_1170108 200275940557071060256259 := by
  unfold tailWord_1170108
  simp only [CollatzResearch.WordTrace]
  refine ⟨21338672422453014690775489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28451563229937352921033985 21338672422453014690775489)
  ·
    refine ⟨16004004316839761018081617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21338672422453014690775489 16004004316839761018081617)
    ·
      refine ⟨12003003237629820763561213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16004004316839761018081617 12003003237629820763561213)
      ·
        refine ⟨4501126214111182786335455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12003003237629820763561213 4501126214111182786335455)
        ·
          refine ⟨6751689321166774179503183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4501126214111182786335455 6751689321166774179503183)
          ·
            refine ⟨10127533981750161269254775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6751689321166774179503183 10127533981750161269254775)
            ·
              refine ⟨15191300972625241903882163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10127533981750161269254775 15191300972625241903882163)
              ·
                refine ⟨22786951458937862855823245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15191300972625241903882163 22786951458937862855823245)
                ·
                  refine ⟨8545106797101698570933717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22786951458937862855823245 8545106797101698570933717)
                  ·
                    refine ⟨200275940557071060256259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8545106797101698570933717 200275940557071060256259)
                    ·
                      rfl

theorem cell23_1170108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_1170108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170108 prefixEnd_1170108 := by exact prefixLift 1170108
  have htrace : WordTrace (prefixWord ++ tailWord_1170108) baseStart_1170108 baseEnd_1170108 := by
    simpa [prefixWord, tailWord_1170108, baseEnd_1170108] using wordTrace_append hprefix tailTrace_1170108
  have hstable : (prefixWord ++ tailWord_1170108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170108).length < 2 ^ (prefixWord ++ tailWord_1170108).sum := by decide
  have hdescent : baseEnd_1170108 < baseStart_1170108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170145 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 4, 1, 4]
def baseStart_1170145 : Nat := 118140960795 + 1170145 * 2 ^ 59
def prefixEnd_1170145 : Nat := 4983230072969 + 3 ^ 40 * 1170145 * 2
def baseEnd_1170145 : Nat := 600846820455429536006107

theorem tailTrace_1170145 : CollatzResearch.WordTrace tailWord_1170145 prefixEnd_1170145 600846820455429536006107 := by
  unfold tailWord_1170145
  simp only [CollatzResearch.WordTrace]
  refine ⟨42678694345771984700647889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28452462897181323133765259 42678694345771984700647889)
  ·
    refine ⟨32009020759328988525485917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42678694345771984700647889 32009020759328988525485917)
    ·
      refine ⟨12003382784748370697057219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32009020759328988525485917 12003382784748370697057219)
      ·
        refine ⟨18005074177122556045585829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12003382784748370697057219 18005074177122556045585829)
        ·
          refine ⟨3375951408210479258547343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18005074177122556045585829 3375951408210479258547343)
          ·
            refine ⟨5063927112315718887821015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3375951408210479258547343 5063927112315718887821015)
            ·
              refine ⟨7595890668473578331731523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5063927112315718887821015 7595890668473578331731523)
              ·
                refine ⟨11393836002710367497597285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7595890668473578331731523 11393836002710367497597285)
                ·
                  refine ⟨2136344250508193905799491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11393836002710367497597285 2136344250508193905799491)
                  ·
                    refine ⟨3204516375762290858699237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2136344250508193905799491 3204516375762290858699237)
                    ·
                      refine ⟨600846820455429536006107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3204516375762290858699237 600846820455429536006107)
                      ·
                        rfl

theorem cell23_1170145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_1170145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170145 prefixEnd_1170145 := by exact prefixLift 1170145
  have htrace : WordTrace (prefixWord ++ tailWord_1170145) baseStart_1170145 baseEnd_1170145 := by
    simpa [prefixWord, tailWord_1170145, baseEnd_1170145] using wordTrace_append hprefix tailTrace_1170145
  have hstable : (prefixWord ++ tailWord_1170145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170145).length < 2 ^ (prefixWord ++ tailWord_1170145).sum := by decide
  have hdescent : baseEnd_1170145 < baseStart_1170145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170188 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 1, 1, 8]
def baseStart_1170188 : Nat := 118140960795 + 1170188 * 2 ^ 59
def prefixEnd_1170188 : Nat := 4983230072969 + 3 ^ 40 * 1170188 * 2
def baseEnd_1170188 : Nat := 600868900123572867768409

theorem tailTrace_1170188 : CollatzResearch.WordTrace tailWord_1170188 prefixEnd_1170188 600868900123572867768409 := by
  unfold tailWord_1170188
  simp only [CollatzResearch.WordTrace]
  refine ⟨21340131342308101522231609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28453508456410802029642145 21340131342308101522231609)
  ·
    refine ⟨16005098506731076141673707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21340131342308101522231609 16005098506731076141673707)
    ·
      refine ⟨24007647760096614212510561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16005098506731076141673707 24007647760096614212510561)
      ·
        refine ⟨18005735820072460659382921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24007647760096614212510561 18005735820072460659382921)
        ·
          refine ⟨13504301865054345494537191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18005735820072460659382921 13504301865054345494537191)
          ·
            refine ⟨20256452797581518241805787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13504301865054345494537191 20256452797581518241805787)
            ·
              refine ⟨30384679196372277362708681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20256452797581518241805787 30384679196372277362708681)
              ·
                refine ⟨22788509397279208022031511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30384679196372277362708681 22788509397279208022031511)
                ·
                  refine ⟨34182764095918812033047267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22788509397279208022031511 34182764095918812033047267)
                  ·
                    refine ⟨51274146143878218049570901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34182764095918812033047267 51274146143878218049570901)
                    ·
                      refine ⟨600868900123572867768409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 51274146143878218049570901 600868900123572867768409)
                      ·
                        rfl

theorem cell23_1170188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_1170188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170188 prefixEnd_1170188 := by exact prefixLift 1170188
  have htrace : WordTrace (prefixWord ++ tailWord_1170188) baseStart_1170188 baseEnd_1170188 := by
    simpa [prefixWord, tailWord_1170188, baseEnd_1170188] using wordTrace_append hprefix tailTrace_1170188
  have hstable : (prefixWord ++ tailWord_1170188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170188).length < 2 ^ (prefixWord ++ tailWord_1170188).sum := by decide
  have hdescent : baseEnd_1170188 < baseStart_1170188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170229 : List Nat := [1, 3, 3, 1, 3, 2, 1, 2, 3, 1, 3]
def baseStart_1170229 : Nat := 118140960795 + 1170229 * 2 ^ 59
def prefixEnd_1170229 : Nat := 4983230072969 + 3 ^ 40 * 1170229 * 2
def baseEnd_1170229 : Nat := 600889952830407207355721

theorem tailTrace_1170229 : CollatzResearch.WordTrace tailWord_1170229 prefixEnd_1170229 600889952830407207355721 := by
  unfold tailWord_1170229
  simp only [CollatzResearch.WordTrace]
  refine ⟨42681758077467667046705741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28454505384978444697803827 42681758077467667046705741)
  ·
    refine ⟨16005659279050375142514653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42681758077467667046705741 16005659279050375142514653)
    ·
      refine ⟨6002122229643890678442995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16005659279050375142514653 6002122229643890678442995)
      ·
        refine ⟨9003183344465836017664493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6002122229643890678442995 9003183344465836017664493)
        ·
          refine ⟨3376193754174688506624185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9003183344465836017664493 3376193754174688506624185)
          ·
            refine ⟨2532145315631016379968139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3376193754174688506624185 2532145315631016379968139)
            ·
              refine ⟨3798217973446524569952209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2532145315631016379968139 3798217973446524569952209)
              ·
                refine ⟨2848663480084893427464157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3798217973446524569952209 2848663480084893427464157)
                ·
                  refine ⟨1068248805031835035299059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2848663480084893427464157 1068248805031835035299059)
                  ·
                    refine ⟨1602373207547752552948589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1068248805031835035299059 1602373207547752552948589)
                    ·
                      refine ⟨600889952830407207355721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1602373207547752552948589 600889952830407207355721)
                      ·
                        rfl

theorem cell23_1170229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_1170229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170229 prefixEnd_1170229 := by exact prefixLift 1170229
  have htrace : WordTrace (prefixWord ++ tailWord_1170229) baseStart_1170229 baseEnd_1170229 := by
    simpa [prefixWord, tailWord_1170229, baseEnd_1170229] using wordTrace_append hprefix tailTrace_1170229
  have hstable : (prefixWord ++ tailWord_1170229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170229).length < 2 ^ (prefixWord ++ tailWord_1170229).sum := by decide
  have hdescent : baseEnd_1170229 < baseStart_1170229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170239 : List Nat := [1, 1, 2, 2, 5, 1, 3, 1, 2, 3, 2]
def baseStart_1170239 : Nat := 118140960795 + 1170239 * 2 ^ 59
def prefixEnd_1170239 : Nat := 4983230072969 + 3 ^ 40 * 1170239 * 2
def baseEnd_1170239 : Nat := 600895087636952168230675

theorem tailTrace_1170239 : CollatzResearch.WordTrace tailWord_1170239 prefixEnd_1170239 600895087636952168230675 := by
  unfold tailWord_1170239
  simp only [CollatzResearch.WordTrace]
  refine ⟨42682122807431438754569771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28454748538287625836379847 42682122807431438754569771)
  ·
    refine ⟨64023184211147158131854657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42682122807431438754569771 64023184211147158131854657)
    ·
      refine ⟨48017388158360368598890993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64023184211147158131854657 48017388158360368598890993)
      ·
        refine ⟨36013041118770276449168245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48017388158360368598890993 36013041118770276449168245)
        ·
          refine ⟨3376222604884713417109523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36013041118770276449168245 3376222604884713417109523)
          ·
            refine ⟨5064333907327070125664285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3376222604884713417109523 5064333907327070125664285)
            ·
              refine ⟨1899125215247651297124107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5064333907327070125664285 1899125215247651297124107)
              ·
                refine ⟨2848687822871476945686161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1899125215247651297124107 2848687822871476945686161)
                ·
                  refine ⟨2136515867153607709264621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2848687822871476945686161 2136515867153607709264621)
                  ·
                    refine ⟨801193450182602890974233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2136515867153607709264621 801193450182602890974233)
                    ·
                      refine ⟨600895087636952168230675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 801193450182602890974233 600895087636952168230675)
                      ·
                        rfl

theorem cell23_1170239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 3, 2].length) (baseStart_1170239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170239 prefixEnd_1170239 := by exact prefixLift 1170239
  have htrace : WordTrace (prefixWord ++ tailWord_1170239) baseStart_1170239 baseEnd_1170239 := by
    simpa [prefixWord, tailWord_1170239, baseEnd_1170239] using wordTrace_append hprefix tailTrace_1170239
  have hstable : (prefixWord ++ tailWord_1170239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170239).length < 2 ^ (prefixWord ++ tailWord_1170239).sum := by decide
  have hdescent : baseEnd_1170239 < baseStart_1170239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170249 : List Nat := [1, 2, 1, 1, 2, 7, 2, 1, 1, 5]
def baseStart_1170249 : Nat := 118140960795 + 1170249 * 2 ^ 59
def prefixEnd_1170249 : Nat := 4983230072969 + 3 ^ 40 * 1170249 * 2
def baseEnd_1170249 : Nat := 200300074147832376368543

theorem tailTrace_1170249 : CollatzResearch.WordTrace tailWord_1170249 prefixEnd_1170249 200300074147832376368543 := by
  unfold tailWord_1170249
  simp only [CollatzResearch.WordTrace]
  refine ⟨42682487537395210462433801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28454991691596806974955867 42682487537395210462433801)
  ·
    refine ⟨32011865653046407846825351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42682487537395210462433801 32011865653046407846825351)
    ·
      refine ⟨48017798479569611770238027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32011865653046407846825351 48017798479569611770238027)
      ·
        refine ⟨72026697719354417655357041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48017798479569611770238027 72026697719354417655357041)
        ·
          refine ⟨54020023289515813241517781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72026697719354417655357041 54020023289515813241517781)
          ·
            refine ⟨1266094295848026872848073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 54020023289515813241517781 1266094295848026872848073)
            ·
              refine ⟨949570721886020154636055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1266094295848026872848073 949570721886020154636055)
              ·
                refine ⟨1424356082829030231954083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 949570721886020154636055 1424356082829030231954083)
                ·
                  refine ⟨2136534124243545347931125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1424356082829030231954083 2136534124243545347931125)
                  ·
                    refine ⟨200300074147832376368543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2136534124243545347931125 200300074147832376368543)
                    ·
                      rfl

theorem cell23_1170249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 1, 5].length) (baseStart_1170249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170249 prefixEnd_1170249 := by exact prefixLift 1170249
  have htrace : WordTrace (prefixWord ++ tailWord_1170249) baseStart_1170249 baseEnd_1170249 := by
    simpa [prefixWord, tailWord_1170249, baseEnd_1170249] using wordTrace_append hprefix tailTrace_1170249
  have hstable : (prefixWord ++ tailWord_1170249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170249).length < 2 ^ (prefixWord ++ tailWord_1170249).sum := by decide
  have hdescent : baseEnd_1170249 < baseStart_1170249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170286 : List Nat := [4, 1, 2, 3, 2, 1, 2, 2, 1, 1, 4]
def baseStart_1170286 : Nat := 118140960795 + 1170286 * 2 ^ 59
def prefixEnd_1170286 : Nat := 4983230072969 + 3 ^ 40 * 1170286 * 2
def baseEnd_1170286 : Nat := 600919221227713484342959

theorem tailTrace_1170286 : CollatzResearch.WordTrace tailWord_1170286 prefixEnd_1170286 600919221227713484342959 := by
  unfold tailWord_1170286
  simp only [CollatzResearch.WordTrace]
  refine ⟨5335479629782645722691339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28455891358840777187687141 5335479629782645722691339)
  ·
    refine ⟨8003219444673968584037009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5335479629782645722691339 8003219444673968584037009)
    ·
      refine ⟨6002414583505476438027757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8003219444673968584037009 6002414583505476438027757)
      ·
        refine ⟨2250905468814553664260409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6002414583505476438027757 2250905468814553664260409)
        ·
          refine ⟨1688179101610915248195307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2250905468814553664260409 1688179101610915248195307)
          ·
            refine ⟨2532268652416372872292961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1688179101610915248195307 2532268652416372872292961)
            ·
              refine ⟨1899201489312279654219721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2532268652416372872292961 1899201489312279654219721)
              ·
                refine ⟨1424401116984209740664791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1899201489312279654219721 1424401116984209740664791)
                ·
                  refine ⟨2136601675476314610997187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1424401116984209740664791 2136601675476314610997187)
                  ·
                    refine ⟨3204902513214471916495781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2136601675476314610997187 3204902513214471916495781)
                    ·
                      refine ⟨600919221227713484342959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3204902513214471916495781 600919221227713484342959)
                      ·
                        rfl

theorem cell23_1170286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_1170286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170286 prefixEnd_1170286 := by exact prefixLift 1170286
  have htrace : WordTrace (prefixWord ++ tailWord_1170286) baseStart_1170286 baseEnd_1170286 := by
    simpa [prefixWord, tailWord_1170286, baseEnd_1170286] using wordTrace_append hprefix tailTrace_1170286
  have hstable : (prefixWord ++ tailWord_1170286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170286).length < 2 ^ (prefixWord ++ tailWord_1170286).sum := by decide
  have hdescent : baseEnd_1170286 < baseStart_1170286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170289 : List Nat := [1, 2, 2, 2, 1, 5, 2, 2, 1, 2, 3]
def baseStart_1170289 : Nat := 118140960795 + 1170289 * 2 ^ 59
def prefixEnd_1170289 : Nat := 4983230072969 + 3 ^ 40 * 1170289 * 2
def baseEnd_1170289 : Nat := 600920761669676972605445

theorem tailTrace_1170289 : CollatzResearch.WordTrace tailWord_1170289 prefixEnd_1170289 600920761669676972605445 := by
  unfold tailWord_1170289
  simp only [CollatzResearch.WordTrace]
  refine ⟨42683946457250297293889921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28455964304833531529259947 42683946457250297293889921)
  ·
    refine ⟨32012959842937722970417441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42683946457250297293889921 32012959842937722970417441)
    ·
      refine ⟨24009719882203292227813081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32012959842937722970417441 24009719882203292227813081)
      ·
        refine ⟨18007289911652469170859811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24009719882203292227813081 18007289911652469170859811)
        ·
          refine ⟨27010934867478703756289717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18007289911652469170859811 27010934867478703756289717)
          ·
            refine ⟨2532275143826128477152161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27010934867478703756289717 2532275143826128477152161)
            ·
              refine ⟨1899206357869596357864121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2532275143826128477152161 1899206357869596357864121)
              ·
                refine ⟨1424404768402197268398091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1899206357869596357864121 1424404768402197268398091)
                ·
                  refine ⟨2136607152603295902597137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1424404768402197268398091 2136607152603295902597137)
                  ·
                    refine ⟨1602455364452471926947853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2136607152603295902597137 1602455364452471926947853)
                    ·
                      refine ⟨600920761669676972605445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1602455364452471926947853 600920761669676972605445)
                      ·
                        rfl

theorem cell23_1170289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_1170289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170289 prefixEnd_1170289 := by exact prefixLift 1170289
  have htrace : WordTrace (prefixWord ++ tailWord_1170289) baseStart_1170289 baseEnd_1170289 := by
    simpa [prefixWord, tailWord_1170289, baseEnd_1170289] using wordTrace_append hprefix tailTrace_1170289
  have hstable : (prefixWord ++ tailWord_1170289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170289).length < 2 ^ (prefixWord ++ tailWord_1170289).sum := by decide
  have hdescent : baseEnd_1170289 < baseStart_1170289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170326 : List Nat := [5, 3, 1, 1, 1, 2, 2, 8]
def baseStart_1170326 : Nat := 118140960795 + 1170326 * 2 ^ 59
def prefixEnd_1170326 : Nat := 4983230072969 + 3 ^ 40 * 1170326 * 2
def baseEnd_1170326 : Nat := 22257028164959012142325

theorem tailTrace_1170326 : CollatzResearch.WordTrace tailWord_1170326 prefixEnd_1170326 22257028164959012142325 := by
  unfold tailWord_1170326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2667830997382265788311677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28456863972077501741991221 2667830997382265788311677)
  ·
    refine ⟨1000436624018349670616879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2667830997382265788311677 1000436624018349670616879)
    ·
      refine ⟨1500654936027524505925319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1000436624018349670616879 1500654936027524505925319)
      ·
        refine ⟨2250982404041286758887979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1500654936027524505925319 2250982404041286758887979)
        ·
          refine ⟨3376473606061930138331969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2250982404041286758887979 3376473606061930138331969)
          ·
            refine ⟨2532355204546447603748977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3376473606061930138331969 2532355204546447603748977)
            ·
              refine ⟨1899266403409835702811733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2532355204546447603748977 1899266403409835702811733)
              ·
                refine ⟨22257028164959012142325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1899266403409835702811733 22257028164959012142325)
                ·
                  rfl

theorem cell23_1170326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_1170326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170326 prefixEnd_1170326 := by exact prefixLift 1170326
  have htrace : WordTrace (prefixWord ++ tailWord_1170326) baseStart_1170326 baseEnd_1170326 := by
    simpa [prefixWord, tailWord_1170326, baseEnd_1170326] using wordTrace_append hprefix tailTrace_1170326
  have hstable : (prefixWord ++ tailWord_1170326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170326).length < 2 ^ (prefixWord ++ tailWord_1170326).sum := by decide
  have hdescent : baseEnd_1170326 < baseStart_1170326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170336 : List Nat := [2, 1, 1, 4, 1, 1, 6, 1, 2, 1, 3]
def baseStart_1170336 : Nat := 118140960795 + 1170336 * 2 ^ 59
def prefixEnd_1170336 : Nat := 4983230072969 + 3 ^ 40 * 1170336 * 2
def baseEnd_1170336 : Nat := 600944895260438288717729

theorem tailTrace_1170336 : CollatzResearch.WordTrace tailWord_1170336 prefixEnd_1170336 600944895260438288717729 := by
  unfold tailWord_1170336
  simp only [CollatzResearch.WordTrace]
  refine ⟨21342830344040012160425431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28457107125386682880567241 21342830344040012160425431)
  ·
    refine ⟨32014245516060018240638147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21342830344040012160425431 32014245516060018240638147)
    ·
      refine ⟨48021368274090027360957221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32014245516060018240638147 48021368274090027360957221)
      ·
        refine ⟨9004006551391880130179479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48021368274090027360957221 9004006551391880130179479)
        ·
          refine ⟨13506009827087820195269219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9004006551391880130179479 13506009827087820195269219)
          ·
            refine ⟨20259014740631730292903829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13506009827087820195269219 20259014740631730292903829)
            ·
              refine ⟨949641315967112357479867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20259014740631730292903829 949641315967112357479867)
              ·
                refine ⟨1424461973950668536219801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 949641315967112357479867 1424461973950668536219801)
                ·
                  refine ⟨1068346480463001402164851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1424461973950668536219801 1068346480463001402164851)
                  ·
                    refine ⟨1602519720694502103247277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1068346480463001402164851 1602519720694502103247277)
                    ·
                      refine ⟨600944895260438288717729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1602519720694502103247277 600944895260438288717729)
                      ·
                        rfl

theorem cell23_1170336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_1170336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170336 prefixEnd_1170336 := by exact prefixLift 1170336
  have htrace : WordTrace (prefixWord ++ tailWord_1170336) baseStart_1170336 baseEnd_1170336 := by
    simpa [prefixWord, tailWord_1170336, baseEnd_1170336] using wordTrace_append hprefix tailTrace_1170336
  have hstable : (prefixWord ++ tailWord_1170336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170336).length < 2 ^ (prefixWord ++ tailWord_1170336).sum := by decide
  have hdescent : baseEnd_1170336 < baseStart_1170336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170345 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 4, 1, 5]
def baseStart_1170345 : Nat := 118140960795 + 1170345 * 2 ^ 59
def prefixEnd_1170345 : Nat := 4983230072969 + 3 ^ 40 * 1170345 * 2
def baseEnd_1170345 : Nat := 600949516586328753505187

theorem tailTrace_1170345 : CollatzResearch.WordTrace tailWord_1170345 prefixEnd_1170345 600949516586328753505187 := by
  unfold tailWord_1170345
  simp only [CollatzResearch.WordTrace]
  refine ⟨42685988945047418857928489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28457325963364945905285659 42685988945047418857928489)
  ·
    refine ⟨32014491708785564143446367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42685988945047418857928489 32014491708785564143446367)
    ·
      refine ⟨48021737563178346215169551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32014491708785564143446367 48021737563178346215169551)
      ·
        refine ⟨72032606344767519322754327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48021737563178346215169551 72032606344767519322754327)
        ·
          refine ⟨108048909517151278984131491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72032606344767519322754327 108048909517151278984131491)
          ·
            refine ⟨162073364275726918476197237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108048909517151278984131491 162073364275726918476197237)
            ·
              refine ⟨15194377900849398607143491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 162073364275726918476197237 15194377900849398607143491)
              ·
                refine ⟨22791566851274097910715237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15194377900849398607143491 22791566851274097910715237)
                ·
                  refine ⟨4273418784613893358259107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22791566851274097910715237 4273418784613893358259107)
                  ·
                    refine ⟨6410128176920840037388661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4273418784613893358259107 6410128176920840037388661)
                    ·
                      refine ⟨600949516586328753505187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6410128176920840037388661 600949516586328753505187)
                      ·
                        rfl

theorem cell23_1170345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 1, 5].length) (baseStart_1170345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170345 prefixEnd_1170345 := by exact prefixLift 1170345
  have htrace : WordTrace (prefixWord ++ tailWord_1170345) baseStart_1170345 baseEnd_1170345 := by
    simpa [prefixWord, tailWord_1170345, baseEnd_1170345] using wordTrace_append hprefix tailTrace_1170345
  have hstable : (prefixWord ++ tailWord_1170345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170345).length < 2 ^ (prefixWord ++ tailWord_1170345).sum := by decide
  have hdescent : baseEnd_1170345 < baseStart_1170345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170355 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 4]
def baseStart_1170355 : Nat := 118140960795 + 1170355 * 2 ^ 59
def prefixEnd_1170355 : Nat := 4983230072969 + 3 ^ 40 * 1170355 * 2
def baseEnd_1170355 : Nat := 600954651392873714380141

theorem tailTrace_1170355 : CollatzResearch.WordTrace tailWord_1170355 prefixEnd_1170355 600954651392873714380141 := by
  unfold tailWord_1170355
  simp only [CollatzResearch.WordTrace]
  refine ⟨42686353675011190565792519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28457569116674127043861679 42686353675011190565792519)
  ·
    refine ⟨64029530512516785848688779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42686353675011190565792519 64029530512516785848688779)
    ·
      refine ⟨96044295768775178773033169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64029530512516785848688779 96044295768775178773033169)
      ·
        refine ⟨72033221826581384079774877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96044295768775178773033169 72033221826581384079774877)
        ·
          refine ⟨27012458184968019029915579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72033221826581384079774877 27012458184968019029915579)
          ·
            refine ⟨40518687277452028544873369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27012458184968019029915579 40518687277452028544873369)
            ·
              refine ⟨30389015458089021408655027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40518687277452028544873369 30389015458089021408655027)
              ·
                refine ⟨45583523187133532112982541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30389015458089021408655027 45583523187133532112982541)
                ·
                  refine ⟨17093821195175074542368453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45583523187133532112982541 17093821195175074542368453)
                  ·
                    refine ⟨3205091474095326476694085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17093821195175074542368453 3205091474095326476694085)
                    ·
                      refine ⟨600954651392873714380141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3205091474095326476694085 600954651392873714380141)
                      ·
                        rfl

theorem cell23_1170355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 4].length) (baseStart_1170355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170355 prefixEnd_1170355 := by exact prefixLift 1170355
  have htrace : WordTrace (prefixWord ++ tailWord_1170355) baseStart_1170355 baseEnd_1170355 := by
    simpa [prefixWord, tailWord_1170355, baseEnd_1170355] using wordTrace_append hprefix tailTrace_1170355
  have hstable : (prefixWord ++ tailWord_1170355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170355).length < 2 ^ (prefixWord ++ tailWord_1170355).sum := by decide
  have hdescent : baseEnd_1170355 < baseStart_1170355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170359 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 6, 2, 2]
def baseStart_1170359 : Nat := 118140960795 + 1170359 * 2 ^ 59
def prefixEnd_1170359 : Nat := 4983230072969 + 3 ^ 40 * 1170359 * 2
def baseEnd_1170359 : Nat := 600956705315491698730123

theorem tailTrace_1170359 : CollatzResearch.WordTrace tailWord_1170359 prefixEnd_1170359 600956705315491698730123 := by
  unfold tailWord_1170359
  simp only [CollatzResearch.WordTrace]
  refine ⟨42686499566996699248938131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28457666377997799499292087 42686499566996699248938131)
  ·
    refine ⟨64029749350495048873407197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42686499566996699248938131 64029749350495048873407197)
    ·
      refine ⟨24011156006435643327527699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64029749350495048873407197 24011156006435643327527699)
      ·
        refine ⟨36016734009653464991291549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24011156006435643327527699 36016734009653464991291549)
        ·
          refine ⟨13506275253620049371734331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36016734009653464991291549 13506275253620049371734331)
          ·
            refine ⟨20259412880430074057601497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13506275253620049371734331 20259412880430074057601497)
            ·
              refine ⟨15194559660322555543201123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20259412880430074057601497 15194559660322555543201123)
              ·
                refine ⟨22791839490483833314801685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15194559660322555543201123 22791839490483833314801685)
                ·
                  refine ⟨1068367476116429686631329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22791839490483833314801685 1068367476116429686631329)
                  ·
                    refine ⟨801275607087322264973497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1068367476116429686631329 801275607087322264973497)
                    ·
                      refine ⟨600956705315491698730123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 801275607087322264973497 600956705315491698730123)
                      ·
                        rfl

theorem cell23_1170359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 2, 2].length) (baseStart_1170359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170359 prefixEnd_1170359 := by exact prefixLift 1170359
  have htrace : WordTrace (prefixWord ++ tailWord_1170359) baseStart_1170359 baseEnd_1170359 := by
    simpa [prefixWord, tailWord_1170359, baseEnd_1170359] using wordTrace_append hprefix tailTrace_1170359
  have hstable : (prefixWord ++ tailWord_1170359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170359).length < 2 ^ (prefixWord ++ tailWord_1170359).sum := by decide
  have hdescent : baseEnd_1170359 < baseStart_1170359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170375 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_1170375 : Nat := 118140960795 + 1170375 * 2 ^ 59
def prefixEnd_1170375 : Nat := 4983230072969 + 3 ^ 40 * 1170375 * 2
def baseEnd_1170375 : Nat := 600964921005963636130049

theorem tailTrace_1170375 : CollatzResearch.WordTrace tailWord_1170375 prefixEnd_1170375 600964921005963636130049 := by
  unfold tailWord_1170375
  simp only [CollatzResearch.WordTrace]
  refine ⟨42687083134938733981520579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28458055423292489321013719 42687083134938733981520579)
  ·
    refine ⟨64030624702408100972280869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42687083134938733981520579 64030624702408100972280869)
    ·
      refine ⟨12005742131701518932302663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64030624702408100972280869 12005742131701518932302663)
      ·
        refine ⟨18008613197552278398453995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12005742131701518932302663 18008613197552278398453995)
        ·
          refine ⟨27012919796328417597680993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18008613197552278398453995 27012919796328417597680993)
          ·
            refine ⟨20259689847246313198260745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27012919796328417597680993 20259689847246313198260745)
            ·
              refine ⟨15194767385434734898695559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20259689847246313198260745 15194767385434734898695559)
              ·
                refine ⟨22792151078152102348043339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15194767385434734898695559 22792151078152102348043339)
                ·
                  refine ⟨34188226617228153522065009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22792151078152102348043339 34188226617228153522065009)
                  ·
                    refine ⟨25641169962921115141548757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34188226617228153522065009 25641169962921115141548757)
                    ·
                      refine ⟨600964921005963636130049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25641169962921115141548757 600964921005963636130049)
                      ·
                        rfl

theorem cell23_1170375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_1170375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170375 prefixEnd_1170375 := by exact prefixLift 1170375
  have htrace : WordTrace (prefixWord ++ tailWord_1170375) baseStart_1170375 baseEnd_1170375 := by
    simpa [prefixWord, tailWord_1170375, baseEnd_1170375] using wordTrace_append hprefix tailTrace_1170375
  have hstable : (prefixWord ++ tailWord_1170375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170375).length < 2 ^ (prefixWord ++ tailWord_1170375).sum := by decide
  have hdescent : baseEnd_1170375 < baseStart_1170375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170389 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 2, 2, 4]
def baseStart_1170389 : Nat := 118140960795 + 1170389 * 2 ^ 59
def prefixEnd_1170389 : Nat := 4983230072969 + 3 ^ 40 * 1170389 * 2
def baseEnd_1170389 : Nat := 600972109735126581354985

theorem tailTrace_1170389 : CollatzResearch.WordTrace tailWord_1170389 prefixEnd_1170389 600972109735126581354985 := by
  unfold tailWord_1170389
  simp only [CollatzResearch.WordTrace]
  refine ⟨42687593756888014372530221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28458395837925342915020147 42687593756888014372530221)
  ·
    refine ⟨16007847658833005389698833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42687593756888014372530221 16007847658833005389698833)
    ·
      refine ⟨12005885744124754042274125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16007847658833005389698833 12005885744124754042274125)
      ·
        refine ⟨4502207154046782765852797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12005885744124754042274125 4502207154046782765852797)
        ·
          refine ⟨1688327682767543537194799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4502207154046782765852797 1688327682767543537194799)
          ·
            refine ⟨2532491524151315305792199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1688327682767543537194799 2532491524151315305792199)
            ·
              refine ⟨3798737286226972958688299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2532491524151315305792199 3798737286226972958688299)
              ·
                refine ⟨5698105929340459438032449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3798737286226972958688299 5698105929340459438032449)
                ·
                  refine ⟨4273579447005344578524337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5698105929340459438032449 4273579447005344578524337)
                  ·
                    refine ⟨3205184585254008433893253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4273579447005344578524337 3205184585254008433893253)
                    ·
                      refine ⟨600972109735126581354985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3205184585254008433893253 600972109735126581354985)
                      ·
                        rfl

theorem cell23_1170389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_1170389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170389 prefixEnd_1170389 := by exact prefixLift 1170389
  have htrace : WordTrace (prefixWord ++ tailWord_1170389) baseStart_1170389 baseEnd_1170389 := by
    simpa [prefixWord, tailWord_1170389, baseEnd_1170389] using wordTrace_append hprefix tailTrace_1170389
  have hstable : (prefixWord ++ tailWord_1170389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170389).length < 2 ^ (prefixWord ++ tailWord_1170389).sum := by decide
  have hdescent : baseEnd_1170389 < baseStart_1170389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170392 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 1, 5, 3]
def baseStart_1170392 : Nat := 118140960795 + 1170392 * 2 ^ 59
def prefixEnd_1170392 : Nat := 4983230072969 + 3 ^ 40 * 1170392 * 2
def baseEnd_1170392 : Nat := 600973650177090069617471

theorem tailTrace_1170392 : CollatzResearch.WordTrace tailWord_1170392 prefixEnd_1170392 600973650177090069617471 := by
  unfold tailWord_1170392
  simp only [CollatzResearch.WordTrace]
  refine ⟨21343851587938572942444715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28458468783918097256592953 21343851587938572942444715)
  ·
    refine ⟨32015777381907859413667073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21343851587938572942444715 32015777381907859413667073)
    ·
      refine ⟨24011833036430894560250305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32015777381907859413667073 24011833036430894560250305)
      ·
        refine ⟨18008874777323170920187729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24011833036430894560250305 18008874777323170920187729)
        ·
          refine ⟨13506656082992378190140797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18008874777323170920187729 13506656082992378190140797)
          ·
            refine ⟨5064996031122141821302799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13506656082992378190140797 5064996031122141821302799)
            ·
              refine ⟨7597494046683212731954199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5064996031122141821302799 7597494046683212731954199)
              ·
                refine ⟨11396241070024819097931299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7597494046683212731954199 11396241070024819097931299)
                ·
                  refine ⟨17094361605037228646896949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11396241070024819097931299 17094361605037228646896949)
                  ·
                    refine ⟨1602596400472240185646589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17094361605037228646896949 1602596400472240185646589)
                    ·
                      refine ⟨600973650177090069617471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1602596400472240185646589 600973650177090069617471)
                      ·
                        rfl

theorem cell23_1170392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_1170392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170392 prefixEnd_1170392 := by exact prefixLift 1170392
  have htrace : WordTrace (prefixWord ++ tailWord_1170392) baseStart_1170392 baseEnd_1170392 := by
    simpa [prefixWord, tailWord_1170392, baseEnd_1170392] using wordTrace_append hprefix tailTrace_1170392
  have hstable : (prefixWord ++ tailWord_1170392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170392).length < 2 ^ (prefixWord ++ tailWord_1170392).sum := by decide
  have hdescent : baseEnd_1170392 < baseStart_1170392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170469 : List Nat := [1, 3, 1, 2, 2, 2, 2, 3, 2, 2, 3]
def baseStart_1170469 : Nat := 118140960795 + 1170469 * 2 ^ 59
def prefixEnd_1170469 : Nat := 4983230072969 + 3 ^ 40 * 1170469 * 2
def baseEnd_1170469 : Nat := 601013188187486268354617

theorem tailTrace_1170469 : CollatzResearch.WordTrace tailWord_1170469 prefixEnd_1170469 601013188187486268354617 := by
  unfold tailWord_1170469
  simp only [CollatzResearch.WordTrace]
  refine ⟨42690511596598188035442461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28460341064398792023628307 42690511596598188035442461)
  ·
    refine ⟨16008941848724320513290923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42690511596598188035442461 16008941848724320513290923)
    ·
      refine ⟨24013412773086480769936385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16008941848724320513290923 24013412773086480769936385)
      ·
        refine ⟨18010059579814860577452289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24013412773086480769936385 18010059579814860577452289)
        ·
          refine ⟨13507544684861145433089217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18010059579814860577452289 13507544684861145433089217)
          ·
            refine ⟨10130658513645859074816913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13507544684861145433089217 10130658513645859074816913)
            ·
              refine ⟨7597993885234394306112685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10130658513645859074816913 7597993885234394306112685)
              ·
                refine ⟨2849247706962897864792257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7597993885234394306112685 2849247706962897864792257)
                ·
                  refine ⟨2136935780222173398594193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2849247706962897864792257 2136935780222173398594193)
                  ·
                    refine ⟨1602701835166630048945645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2136935780222173398594193 1602701835166630048945645)
                    ·
                      refine ⟨601013188187486268354617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1602701835166630048945645 601013188187486268354617)
                      ·
                        rfl

theorem cell23_1170469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_1170469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170469 prefixEnd_1170469 := by exact prefixLift 1170469
  have htrace : WordTrace (prefixWord ++ tailWord_1170469) baseStart_1170469 baseEnd_1170469 := by
    simpa [prefixWord, tailWord_1170469, baseEnd_1170469] using wordTrace_append hprefix tailTrace_1170469
  have hstable : (prefixWord ++ tailWord_1170469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170469).length < 2 ^ (prefixWord ++ tailWord_1170469).sum := by decide
  have hdescent : baseEnd_1170469 < baseStart_1170469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170486 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_1170486 : Nat := 118140960795 + 1170486 * 2 ^ 59
def prefixEnd_1170486 : Nat := 4983230072969 + 3 ^ 40 * 1170486 * 2
def baseEnd_1170486 : Nat := 601021917358612701842039

theorem tailTrace_1170486 : CollatzResearch.WordTrace tailWord_1170486 prefixEnd_1170486 601021917358612701842039 := by
  unfold tailWord_1170486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2668195727346037496175707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28460754425024399959207541 2668195727346037496175707)
  ·
    refine ⟨4002293591019056244263561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2668195727346037496175707 4002293591019056244263561)
    ·
      refine ⟨3001720193264292183197671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4002293591019056244263561 3001720193264292183197671)
      ·
        refine ⟨4502580289896438274796507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3001720193264292183197671 4502580289896438274796507)
        ·
          refine ⟨6753870434844657412194761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4502580289896438274796507 6753870434844657412194761)
          ·
            refine ⟨5065402826133493059146071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6753870434844657412194761 5065402826133493059146071)
            ·
              refine ⟨7598104239200239588719107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5065402826133493059146071 7598104239200239588719107)
              ·
                refine ⟨11397156358800359383078661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7598104239200239588719107 11397156358800359383078661)
                ·
                  refine ⟨2136966817275067384327249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11397156358800359383078661 2136966817275067384327249)
                  ·
                    refine ⟨1602725112956300538245437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2136966817275067384327249 1602725112956300538245437)
                    ·
                      refine ⟨601021917358612701842039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1602725112956300538245437 601021917358612701842039)
                      ·
                        rfl

theorem cell23_1170486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_1170486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170486 prefixEnd_1170486 := by exact prefixLift 1170486
  have htrace : WordTrace (prefixWord ++ tailWord_1170486) baseStart_1170486 baseEnd_1170486 := by
    simpa [prefixWord, tailWord_1170486, baseEnd_1170486] using wordTrace_append hprefix tailTrace_1170486
  have hstable : (prefixWord ++ tailWord_1170486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170486).length < 2 ^ (prefixWord ++ tailWord_1170486).sum := by decide
  have hdescent : baseEnd_1170486 < baseStart_1170486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170516 : List Nat := [2, 4, 1, 1, 1, 1, 2, 4, 3, 1, 3]
def baseStart_1170516 : Nat := 118140960795 + 1170516 * 2 ^ 59
def prefixEnd_1170516 : Nat := 4983230072969 + 3 ^ 40 * 1170516 * 2
def baseEnd_1170516 : Nat := 601037321778247584466901

theorem tailTrace_1170516 : CollatzResearch.WordTrace tailWord_1170516 prefixEnd_1170516 601037321778247584466901 := by
  unfold tailWord_1170516
  simp only [CollatzResearch.WordTrace]
  refine ⟨21346112913713957531201701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28461483884951943374935601 21346112913713957531201701)
  ·
    refine ⟨4002396171321367037100319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21346112913713957531201701 4002396171321367037100319)
    ·
      refine ⟨6003594256982050555650479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4002396171321367037100319 6003594256982050555650479)
      ·
        refine ⟨9005391385473075833475719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6003594256982050555650479 9005391385473075833475719)
        ·
          refine ⟨13508087078209613750213579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9005391385473075833475719 13508087078209613750213579)
          ·
            refine ⟨20262130617314420625320369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13508087078209613750213579 20262130617314420625320369)
            ·
              refine ⟨15196597962985815468990277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20262130617314420625320369 15196597962985815468990277)
              ·
                refine ⟨2849362118059840400435677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15196597962985815468990277 2849362118059840400435677)
                ·
                  refine ⟨1068510794272440150163379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2849362118059840400435677 1068510794272440150163379)
                  ·
                    refine ⟨1602766191408660225245069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1068510794272440150163379 1602766191408660225245069)
                    ·
                      refine ⟨601037321778247584466901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1602766191408660225245069 601037321778247584466901)
                      ·
                        rfl

theorem cell23_1170516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_1170516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170516 prefixEnd_1170516 := by exact prefixLift 1170516
  have htrace : WordTrace (prefixWord ++ tailWord_1170516) baseStart_1170516 baseEnd_1170516 := by
    simpa [prefixWord, tailWord_1170516, baseEnd_1170516] using wordTrace_append hprefix tailTrace_1170516
  have hstable : (prefixWord ++ tailWord_1170516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170516).length < 2 ^ (prefixWord ++ tailWord_1170516).sum := by decide
  have hdescent : baseEnd_1170516 < baseStart_1170516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170533 : List Nat := [1, 3, 1, 3, 2, 1, 2, 5, 1, 1, 3]
def baseStart_1170533 : Nat := 118140960795 + 1170533 * 2 ^ 59
def prefixEnd_1170533 : Nat := 4983230072969 + 3 ^ 40 * 1170533 * 2
def baseEnd_1170533 : Nat := 601046050949374017954323

theorem tailTrace_1170533 : CollatzResearch.WordTrace tailWord_1170533 prefixEnd_1170533 601046050949374017954323 := by
  unfold tailWord_1170533
  simp only [CollatzResearch.WordTrace]
  refine ⟨42692845868366326965772253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28461897245577551310514835 42692845868366326965772253)
  ·
    refine ⟨16009817200637372612164595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42692845868366326965772253 16009817200637372612164595)
    ·
      refine ⟨24014725800956058918246893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16009817200637372612164595 24014725800956058918246893)
      ·
        refine ⟨9005522175358522094342585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24014725800956058918246893 9005522175358522094342585)
        ·
          refine ⟨6754141631518891570756939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9005522175358522094342585 6754141631518891570756939)
          ·
            refine ⟨10131212447278337356135409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6754141631518891570756939 10131212447278337356135409)
            ·
              refine ⟨7598409335458753017101557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10131212447278337356135409 7598409335458753017101557)
              ·
                refine ⟨712350875199258095353271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7598409335458753017101557 712350875199258095353271)
                ·
                  refine ⟨1068526312798887143029907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 712350875199258095353271 1068526312798887143029907)
                  ·
                    refine ⟨1602789469198330714544861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1068526312798887143029907 1602789469198330714544861)
                    ·
                      refine ⟨601046050949374017954323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1602789469198330714544861 601046050949374017954323)
                      ·
                        rfl

theorem cell23_1170533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_1170533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170533 prefixEnd_1170533 := by exact prefixLift 1170533
  have htrace : WordTrace (prefixWord ++ tailWord_1170533) baseStart_1170533 baseEnd_1170533 := by
    simpa [prefixWord, tailWord_1170533, baseEnd_1170533] using wordTrace_append hprefix tailTrace_1170533
  have hstable : (prefixWord ++ tailWord_1170533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170533).length < 2 ^ (prefixWord ++ tailWord_1170533).sum := by decide
  have hdescent : baseEnd_1170533 < baseStart_1170533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170550 : List Nat := [5, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3]
def baseStart_1170550 : Nat := 118140960795 + 1170550 * 2 ^ 59
def prefixEnd_1170550 : Nat := 4983230072969 + 3 ^ 40 * 1170550 * 2
def baseEnd_1170550 : Nat := 601054780120500451441745

theorem tailTrace_1170550 : CollatzResearch.WordTrace tailWord_1170550 prefixEnd_1170550 601054780120500451441745 := by
  unfold tailWord_1170550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2668341619331546179321319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28462310606203159246094069 2668341619331546179321319)
  ·
    refine ⟨4002512428997319268981979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2668341619331546179321319 4002512428997319268981979)
    ·
      refine ⟨6003768643495978903472969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4002512428997319268981979 6003768643495978903472969)
      ·
        refine ⟨4502826482621984177604727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6003768643495978903472969 4502826482621984177604727)
        ·
          refine ⟨6754239723932976266407091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4502826482621984177604727 6754239723932976266407091)
          ·
            refine ⟨10131359585899464399610637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6754239723932976266407091 10131359585899464399610637)
            ·
              refine ⟨3799259844712299149853989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10131359585899464399610637 3799259844712299149853989)
              ·
                refine ⟨712361220883556090597623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3799259844712299149853989 712361220883556090597623)
                ·
                  refine ⟨1068541831325334135896435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 712361220883556090597623 1068541831325334135896435)
                  ·
                    refine ⟨1602812746988001203844653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1068541831325334135896435 1602812746988001203844653)
                    ·
                      refine ⟨601054780120500451441745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1602812746988001203844653 601054780120500451441745)
                      ·
                        rfl

theorem cell23_1170550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_1170550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170550 prefixEnd_1170550 := by exact prefixLift 1170550
  have htrace : WordTrace (prefixWord ++ tailWord_1170550) baseStart_1170550 baseEnd_1170550 := by
    simpa [prefixWord, tailWord_1170550, baseEnd_1170550] using wordTrace_append hprefix tailTrace_1170550
  have hstable : (prefixWord ++ tailWord_1170550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170550).length < 2 ^ (prefixWord ++ tailWord_1170550).sum := by decide
  have hdescent : baseEnd_1170550 < baseStart_1170550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170552 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 3, 1, 6]
def baseStart_1170552 : Nat := 118140960795 + 1170552 * 2 ^ 59
def prefixEnd_1170552 : Nat := 4983230072969 + 3 ^ 40 * 1170552 * 2
def baseEnd_1170552 : Nat := 601055807081809443616735

theorem tailTrace_1170552 : CollatzResearch.WordTrace tailWord_1170552 prefixEnd_1170552 601055807081809443616735 := by
  unfold tailWord_1170552
  simp only [CollatzResearch.WordTrace]
  refine ⟨21346769427648746605356955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28462359236864995473809273 21346769427648746605356955)
  ·
    refine ⟨32020154141473119908035433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21346769427648746605356955 32020154141473119908035433)
    ·
      refine ⟨24015115606104839931026575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32020154141473119908035433 24015115606104839931026575)
      ·
        refine ⟨36022673409157259896539863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24015115606104839931026575 36022673409157259896539863)
        ·
          refine ⟨54034010113735889844809795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36022673409157259896539863 54034010113735889844809795)
          ·
            refine ⟨81051015170603834767214693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54034010113735889844809795 81051015170603834767214693)
            ·
              refine ⟨15197065344488219018852755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81051015170603834767214693 15197065344488219018852755)
              ·
                refine ⟨22795598016732328528279133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15197065344488219018852755 22795598016732328528279133)
                ·
                  refine ⟨8548349256274623198104675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22795598016732328528279133 8548349256274623198104675)
                  ·
                    refine ⟨12822523884411934797157013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8548349256274623198104675 12822523884411934797157013)
                    ·
                      refine ⟨601055807081809443616735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12822523884411934797157013 601055807081809443616735)
                      ·
                        rfl

theorem cell23_1170552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_1170552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170552 prefixEnd_1170552 := by exact prefixLift 1170552
  have htrace : WordTrace (prefixWord ++ tailWord_1170552) baseStart_1170552 baseEnd_1170552 := by
    simpa [prefixWord, tailWord_1170552, baseEnd_1170552] using wordTrace_append hprefix tailTrace_1170552
  have hstable : (prefixWord ++ tailWord_1170552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170552).length < 2 ^ (prefixWord ++ tailWord_1170552).sum := by decide
  have hdescent : baseEnd_1170552 < baseStart_1170552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170569 : List Nat := [1, 2, 1, 1, 4, 3, 1, 3, 1, 2, 4]
def baseStart_1170569 : Nat := 118140960795 + 1170569 * 2 ^ 59
def prefixEnd_1170569 : Nat := 4983230072969 + 3 ^ 40 * 1170569 * 2
def baseEnd_1170569 : Nat := 601064536252935877104157

theorem tailTrace_1170569 : CollatzResearch.WordTrace tailWord_1170569 prefixEnd_1170569 601064536252935877104157 := by
  unfold tailWord_1170569
  simp only [CollatzResearch.WordTrace]
  refine ⟨42694158896235905114082761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28462772597490603409388507 42694158896235905114082761)
  ·
    refine ⟨32020619172176928835562071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42694158896235905114082761 32020619172176928835562071)
    ·
      refine ⟨48030928758265393253343107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32020619172176928835562071 48030928758265393253343107)
      ·
        refine ⟨72046393137398089880014661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48030928758265393253343107 72046393137398089880014661)
        ·
          refine ⟨13508698713262141852502749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72046393137398089880014661 13508698713262141852502749)
          ·
            refine ⟨5065762017473303194688531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13508698713262141852502749 5065762017473303194688531)
            ·
              refine ⟨7598643026209954792032797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5065762017473303194688531 7598643026209954792032797)
              ·
                refine ⟨2849491134828733047012299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7598643026209954792032797 2849491134828733047012299)
                ·
                  refine ⟨4274236702243099570518449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2849491134828733047012299 4274236702243099570518449)
                  ·
                    refine ⟨3205677526682324677888837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4274236702243099570518449 3205677526682324677888837)
                    ·
                      refine ⟨601064536252935877104157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3205677526682324677888837 601064536252935877104157)
                      ·
                        rfl

theorem cell23_1170569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 2, 4].length) (baseStart_1170569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170569 prefixEnd_1170569 := by exact prefixLift 1170569
  have htrace : WordTrace (prefixWord ++ tailWord_1170569) baseStart_1170569 baseEnd_1170569 := by
    simpa [prefixWord, tailWord_1170569, baseEnd_1170569] using wordTrace_append hprefix tailTrace_1170569
  have hstable : (prefixWord ++ tailWord_1170569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170569).length < 2 ^ (prefixWord ++ tailWord_1170569).sum := by decide
  have hdescent : baseEnd_1170569 < baseStart_1170569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170572 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 2, 2, 7]
def baseStart_1170572 : Nat := 118140960795 + 1170572 * 2 ^ 59
def prefixEnd_1170572 : Nat := 4983230072969 + 3 ^ 40 * 1170572 * 2
def baseEnd_1170572 : Nat := 601066076694899365366643

theorem tailTrace_1170572 : CollatzResearch.WordTrace tailWord_1170572 prefixEnd_1170572 601066076694899365366643 := by
  unfold tailWord_1170572
  simp only [CollatzResearch.WordTrace]
  refine ⟨21347134157612518313220985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28462845543483357750961313 21347134157612518313220985)
  ·
    refine ⟨16010350618209388734915739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21347134157612518313220985 16010350618209388734915739)
    ·
      refine ⟨24015525927314083102373609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16010350618209388734915739 24015525927314083102373609)
      ·
        refine ⟨18011644445485562326780207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24015525927314083102373609 18011644445485562326780207)
        ·
          refine ⟨27017466668228343490170311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18011644445485562326780207 27017466668228343490170311)
          ·
            refine ⟨40526200002342515235255467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27017466668228343490170311 40526200002342515235255467)
            ·
              refine ⟨60789300003513772852883201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40526200002342515235255467 60789300003513772852883201)
              ·
                refine ⟨45591975002635329639662401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60789300003513772852883201 45591975002635329639662401)
                ·
                  refine ⟨34193981251976497229746801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45591975002635329639662401 34193981251976497229746801)
                  ·
                    refine ⟨25645485938982372922310101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34193981251976497229746801 25645485938982372922310101)
                    ·
                      refine ⟨601066076694899365366643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25645485938982372922310101 601066076694899365366643)
                      ·
                        rfl

theorem cell23_1170572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_1170572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170572 prefixEnd_1170572 := by exact prefixLift 1170572
  have htrace : WordTrace (prefixWord ++ tailWord_1170572) baseStart_1170572 baseEnd_1170572 := by
    simpa [prefixWord, tailWord_1170572, baseEnd_1170572] using wordTrace_append hprefix tailTrace_1170572
  have hstable : (prefixWord ++ tailWord_1170572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170572).length < 2 ^ (prefixWord ++ tailWord_1170572).sum := by decide
  have hdescent : baseEnd_1170572 < baseStart_1170572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170586 : List Nat := [3, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1170586 : Nat := 118140960795 + 1170586 * 2 ^ 59
def prefixEnd_1170586 : Nat := 4983230072969 + 3 ^ 40 * 1170586 * 2
def baseEnd_1170586 : Nat := 601073265424062310591579

theorem tailTrace_1170586 : CollatzResearch.WordTrace tailWord_1170586 prefixEnd_1170586 601073265424062310591579 := by
  unfold tailWord_1170586
  simp only [CollatzResearch.WordTrace]
  refine ⟨10673694734293579254362903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28463185958116211344967741 10673694734293579254362903)
  ·
    refine ⟨16010542101440368881544355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10673694734293579254362903 16010542101440368881544355)
    ·
      refine ⟨24015813152160553322316533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16010542101440368881544355 24015813152160553322316533)
      ·
        refine ⟨2251482483015051873967175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24015813152160553322316533 2251482483015051873967175)
        ·
          refine ⟨3377223724522577810950763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2251482483015051873967175 3377223724522577810950763)
          ·
            refine ⟨5065835586783866716426145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3377223724522577810950763 5065835586783866716426145)
            ·
              refine ⟨3799376690087900037319609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5065835586783866716426145 3799376690087900037319609)
              ·
                refine ⟨2849532517565925027989707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3799376690087900037319609 2849532517565925027989707)
                ·
                  refine ⟨4274298776348887541984561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2849532517565925027989707 4274298776348887541984561)
                  ·
                    refine ⟨3205724082261665656488421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4274298776348887541984561 3205724082261665656488421)
                    ·
                      refine ⟨601073265424062310591579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3205724082261665656488421 601073265424062310591579)
                      ·
                        rfl

theorem cell23_1170586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1170586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170586 prefixEnd_1170586 := by exact prefixLift 1170586
  have htrace : WordTrace (prefixWord ++ tailWord_1170586) baseStart_1170586 baseEnd_1170586 := by
    simpa [prefixWord, tailWord_1170586, baseEnd_1170586] using wordTrace_append hprefix tailTrace_1170586
  have hstable : (prefixWord ++ tailWord_1170586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170586).length < 2 ^ (prefixWord ++ tailWord_1170586).sum := by decide
  have hdescent : baseEnd_1170586 < baseStart_1170586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170590 : List Nat := [4, 3, 1, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_1170590 : Nat := 118140960795 + 1170590 * 2 ^ 59
def prefixEnd_1170590 : Nat := 4983230072969 + 3 ^ 40 * 1170590 * 2
def baseEnd_1170590 : Nat := 601075319346680294941561

theorem tailTrace_1170590 : CollatzResearch.WordTrace tailWord_1170590 prefixEnd_1170590 601075319346680294941561 := by
  unfold tailWord_1170590
  simp only [CollatzResearch.WordTrace]
  refine ⟨5336865603644978212574653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28463283219439883800398149 5336865603644978212574653)
  ·
    refine ⟨2001324601366866829715495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5336865603644978212574653 2001324601366866829715495)
    ·
      refine ⟨3001986902050300244573243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2001324601366866829715495 3001986902050300244573243)
      ·
        refine ⟨4502980353075450366859865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3001986902050300244573243 4502980353075450366859865)
        ·
          refine ⟨3377235264806587775144899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4502980353075450366859865 3377235264806587775144899)
          ·
            refine ⟨5065852897209881662717349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3377235264806587775144899 5065852897209881662717349)
            ·
              refine ⟨949847418226852811759503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5065852897209881662717349 949847418226852811759503)
              ·
                refine ⟨1424771127340279217639255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 949847418226852811759503 1424771127340279217639255)
                ·
                  refine ⟨2137156691010418826458883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1424771127340279217639255 2137156691010418826458883)
                  ·
                    refine ⟨3205735036515628239688325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2137156691010418826458883 3205735036515628239688325)
                    ·
                      refine ⟨601075319346680294941561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3205735036515628239688325 601075319346680294941561)
                      ·
                        rfl

theorem cell23_1170590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_1170590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170590 prefixEnd_1170590 := by exact prefixLift 1170590
  have htrace : WordTrace (prefixWord ++ tailWord_1170590) baseStart_1170590 baseEnd_1170590 := by
    simpa [prefixWord, tailWord_1170590, baseEnd_1170590] using wordTrace_append hprefix tailTrace_1170590
  have hstable : (prefixWord ++ tailWord_1170590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170590).length < 2 ^ (prefixWord ++ tailWord_1170590).sum := by decide
  have hdescent : baseEnd_1170590 < baseStart_1170590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170616 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 3, 3, 2]
def baseStart_1170616 : Nat := 118140960795 + 1170616 * 2 ^ 59
def prefixEnd_1170616 : Nat := 4983230072969 + 3 ^ 40 * 1170616 * 2
def baseEnd_1170616 : Nat := 601088669843697193216441

theorem tailTrace_1170616 : CollatzResearch.WordTrace tailWord_1170616 prefixEnd_1170616 601088669843697193216441 := by
  unfold tailWord_1170616
  simp only [CollatzResearch.WordTrace]
  refine ⟨21347936563532816070521851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28463915418043754760695801 21347936563532816070521851)
  ·
    refine ⟨32021904845299224105782777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21347936563532816070521851 32021904845299224105782777)
    ·
      refine ⟨24016428633974418079337083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32021904845299224105782777 24016428633974418079337083)
      ·
        refine ⟨36024642950961627119005625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24016428633974418079337083 36024642950961627119005625)
        ·
          refine ⟨27018482213221220339254219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36024642950961627119005625 27018482213221220339254219)
          ·
            refine ⟨40527723319831830508881329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27018482213221220339254219 40527723319831830508881329)
            ·
              refine ⟨30395792489873872881660997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40527723319831830508881329 30395792489873872881660997)
              ·
                refine ⟨5699211091851351165311437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30395792489873872881660997 5699211091851351165311437)
                ·
                  refine ⟨2137204159444256686991789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5699211091851351165311437 2137204159444256686991789)
                  ·
                    refine ⟨801451559791596257621921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2137204159444256686991789 801451559791596257621921)
                    ·
                      refine ⟨601088669843697193216441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 801451559791596257621921 601088669843697193216441)
                      ·
                        rfl

theorem cell23_1170616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 3, 3, 2].length) (baseStart_1170616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170616 prefixEnd_1170616 := by exact prefixLift 1170616
  have htrace : WordTrace (prefixWord ++ tailWord_1170616) baseStart_1170616 baseEnd_1170616 := by
    simpa [prefixWord, tailWord_1170616, baseEnd_1170616] using wordTrace_append hprefix tailTrace_1170616
  have hstable : (prefixWord ++ tailWord_1170616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170616).length < 2 ^ (prefixWord ++ tailWord_1170616).sum := by decide
  have hdescent : baseEnd_1170616 < baseStart_1170616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170630 : List Nat := [6, 1, 2, 2, 1, 1, 1, 9]
def baseStart_1170630 : Nat := 118140960795 + 1170630 * 2 ^ 59
def prefixEnd_1170630 : Nat := 4983230072969 + 3 ^ 40 * 1170630 * 2
def baseEnd_1170630 : Nat := 22262809576772597720051

theorem tailTrace_1170630 : CollatzResearch.WordTrace tailWord_1170630 prefixEnd_1170630 22262809576772597720051 := by
  unfold tailWord_1170630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1334261992156716016626667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28464255832676608354702229 1334261992156716016626667)
  ·
    refine ⟨2001392988235074024940001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1334261992156716016626667 2001392988235074024940001)
    ·
      refine ⟨1501044741176305518705001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2001392988235074024940001 1501044741176305518705001)
      ·
        refine ⟨1125783555882229139028751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1501044741176305518705001 1125783555882229139028751)
        ·
          refine ⟨1688675333823343708543127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1125783555882229139028751 1688675333823343708543127)
          ·
            refine ⟨2533013000735015562814691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1688675333823343708543127 2533013000735015562814691)
            ·
              refine ⟨3799519501102523344222037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2533013000735015562814691 3799519501102523344222037)
              ·
                refine ⟨22262809576772597720051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3799519501102523344222037 22262809576772597720051)
                ·
                  rfl

theorem cell23_1170630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_1170630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170630 prefixEnd_1170630 := by exact prefixLift 1170630
  have htrace : WordTrace (prefixWord ++ tailWord_1170630) baseStart_1170630 baseEnd_1170630 := by
    simpa [prefixWord, tailWord_1170630, baseEnd_1170630] using wordTrace_append hprefix tailTrace_1170630
  have hstable : (prefixWord ++ tailWord_1170630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170630).length < 2 ^ (prefixWord ++ tailWord_1170630).sum := by decide
  have hdescent : baseEnd_1170630 < baseStart_1170630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170649 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 1, 6, 3]
def baseStart_1170649 : Nat := 118140960795 + 1170649 * 2 ^ 59
def prefixEnd_1170649 : Nat := 4983230072969 + 3 ^ 40 * 1170649 * 2
def baseEnd_1170649 : Nat := 601105614705295564103789

theorem tailTrace_1170649 : CollatzResearch.WordTrace tailWord_1170649 prefixEnd_1170649 601105614705295564103789 := by
  unfold tailWord_1170649
  simp only [CollatzResearch.WordTrace]
  refine ⟨42697076735946078776995001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28464717823964052517996667 42697076735946078776995001)
  ·
    refine ⟨32022807551959559082746251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42697076735946078776995001 32022807551959559082746251)
    ·
      refine ⟨48034211327939338624119377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32022807551959559082746251 48034211327939338624119377)
      ·
        refine ⟨36025658495954503968089533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48034211327939338624119377 36025658495954503968089533)
        ·
          refine ⟨13509621935982938988033575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36025658495954503968089533 13509621935982938988033575)
          ·
            refine ⟨20264432903974408482050363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13509621935982938988033575 20264432903974408482050363)
            ·
              refine ⟨30396649355961612723075545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20264432903974408482050363 30396649355961612723075545)
              ·
                refine ⟨22797487016971209542306659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30396649355961612723075545 22797487016971209542306659)
                ·
                  refine ⟨34196230525456814313459989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22797487016971209542306659 34196230525456814313459989)
                  ·
                    refine ⟨1602948305880788170943437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34196230525456814313459989 1602948305880788170943437)
                    ·
                      refine ⟨601105614705295564103789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1602948305880788170943437 601105614705295564103789)
                      ·
                        rfl

theorem cell23_1170649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_1170649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170649 prefixEnd_1170649 := by exact prefixLift 1170649
  have htrace : WordTrace (prefixWord ++ tailWord_1170649) baseStart_1170649 baseEnd_1170649 := by
    simpa [prefixWord, tailWord_1170649, baseEnd_1170649] using wordTrace_append hprefix tailTrace_1170649
  have hstable : (prefixWord ++ tailWord_1170649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170649).length < 2 ^ (prefixWord ++ tailWord_1170649).sum := by decide
  have hdescent : baseEnd_1170649 < baseStart_1170649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170674 : List Nat := [3, 2, 1, 3, 4, 1, 2, 1, 2, 1, 3]
def baseStart_1170674 : Nat := 118140960795 + 1170674 * 2 ^ 59
def prefixEnd_1170674 : Nat := 4983230072969 + 3 ^ 40 * 1170674 * 2
def baseEnd_1170674 : Nat := 601118451721657966291175

theorem tailTrace_1170674 : CollatzResearch.WordTrace tailWord_1170674 prefixEnd_1170674 601118451721657966291175 := by
  unfold tailWord_1170674
  simp only [CollatzResearch.WordTrace]
  refine ⟨10674497140213877011663769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28465325707237005364436717 10674497140213877011663769)
  ·
    refine ⟨8005872855160407758747827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10674497140213877011663769 8005872855160407758747827)
    ·
      refine ⟨12008809282740611638121741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8005872855160407758747827 12008809282740611638121741)
      ·
        refine ⟨4503303481027729364295653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12008809282740611638121741 4503303481027729364295653)
        ·
          refine ⟨844369402692699255805435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4503303481027729364295653 844369402692699255805435)
          ·
            refine ⟨1266554104039048883708153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844369402692699255805435 1266554104039048883708153)
            ·
              refine ⟨949915578029286662781115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1266554104039048883708153 949915578029286662781115)
              ·
                refine ⟨1424873367043929994171673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 949915578029286662781115 1424873367043929994171673)
                ·
                  refine ⟨1068655025282947495628755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1424873367043929994171673 1068655025282947495628755)
                  ·
                    refine ⟨1602982537924421243443133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1068655025282947495628755 1602982537924421243443133)
                    ·
                      refine ⟨601118451721657966291175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1602982537924421243443133 601118451721657966291175)
                      ·
                        rfl

theorem cell23_1170674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_1170674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170674 prefixEnd_1170674 := by exact prefixLift 1170674
  have htrace : WordTrace (prefixWord ++ tailWord_1170674) baseStart_1170674 baseEnd_1170674 := by
    simpa [prefixWord, tailWord_1170674, baseEnd_1170674] using wordTrace_append hprefix tailTrace_1170674
  have hstable : (prefixWord ++ tailWord_1170674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170674).length < 2 ^ (prefixWord ++ tailWord_1170674).sum := by decide
  have hdescent : baseEnd_1170674 < baseStart_1170674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170716 : List Nat := [2, 2, 3, 1, 1, 1, 4, 2, 2, 5]
def baseStart_1170716 : Nat := 118140960795 + 1170716 * 2 ^ 59
def prefixEnd_1170716 : Nat := 4983230072969 + 3 ^ 40 * 1170716 * 2
def baseEnd_1170716 : Nat := 200380005969715600655327

theorem tailTrace_1170716 : CollatzResearch.WordTrace tailWord_1170716 prefixEnd_1170716 200380005969715600655327 := by
  unfold tailWord_1170716
  simp only [CollatzResearch.WordTrace]
  refine ⟨21349760213351674609842001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28466346951135566146456001 21349760213351674609842001)
  ·
    refine ⟨16012320160013755957381501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21349760213351674609842001 16012320160013755957381501)
    ·
      refine ⟨6004620060005158484018063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16012320160013755957381501 6004620060005158484018063)
      ·
        refine ⟨9006930090007737726027095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6004620060005158484018063 9006930090007737726027095)
        ·
          refine ⟨13510395135011606589040643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9006930090007737726027095 13510395135011606589040643)
          ·
            refine ⟨20265592702517409883560965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13510395135011606589040643 20265592702517409883560965)
            ·
              refine ⟨3799798631722014353167681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20265592702517409883560965 3799798631722014353167681)
              ·
                refine ⟨2849848973791510764875761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3799798631722014353167681 2849848973791510764875761)
                ·
                  refine ⟨2137386730343633073656821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2849848973791510764875761 2137386730343633073656821)
                  ·
                    refine ⟨200380005969715600655327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2137386730343633073656821 200380005969715600655327)
                    ·
                      rfl

theorem cell23_1170716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_1170716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170716 prefixEnd_1170716 := by exact prefixLift 1170716
  have htrace : WordTrace (prefixWord ++ tailWord_1170716) baseStart_1170716 baseEnd_1170716 := by
    simpa [prefixWord, tailWord_1170716, baseEnd_1170716] using wordTrace_append hprefix tailTrace_1170716
  have hstable : (prefixWord ++ tailWord_1170716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170716).length < 2 ^ (prefixWord ++ tailWord_1170716).sum := by decide
  have hdescent : baseEnd_1170716 < baseStart_1170716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170753 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1170753 : Nat := 118140960795 + 1170753 * 2 ^ 59
def prefixEnd_1170753 : Nat := 4983230072969 + 3 ^ 40 * 1170753 * 2
def baseEnd_1170753 : Nat := 601159016693363157203311

theorem tailTrace_1170753 : CollatzResearch.WordTrace tailWord_1170753 prefixEnd_1170753 601159016693363157203311 := by
  unfold tailWord_1170753
  simp only [CollatzResearch.WordTrace]
  refine ⟨42700869927569304538780913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28467246618379536359187275 42700869927569304538780913)
  ·
    refine ⟨32025652445676978404085685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42700869927569304538780913 32025652445676978404085685)
    ·
      refine ⟨3002404916782216725383033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32025652445676978404085685 3002404916782216725383033)
      ·
        refine ⟨2251803687586662544037275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3002404916782216725383033 2251803687586662544037275)
        ·
          refine ⟨3377705531379993816055913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2251803687586662544037275 3377705531379993816055913)
          ·
            refine ⟨2533279148534995362041935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3377705531379993816055913 2533279148534995362041935)
            ·
              refine ⟨3799918722802493043062903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2533279148534995362041935 3799918722802493043062903)
              ·
                refine ⟨5699878084203739564594355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3799918722802493043062903 5699878084203739564594355)
                ·
                  refine ⟨8549817126305609346891533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5699878084203739564594355 8549817126305609346891533)
                  ·
                    refine ⟨3206181422364603505084325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8549817126305609346891533 3206181422364603505084325)
                    ·
                      refine ⟨601159016693363157203311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3206181422364603505084325 601159016693363157203311)
                      ·
                        rfl

theorem cell23_1170753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1170753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170753 prefixEnd_1170753 := by exact prefixLift 1170753
  have htrace : WordTrace (prefixWord ++ tailWord_1170753) baseStart_1170753 baseEnd_1170753 := by
    simpa [prefixWord, tailWord_1170753, baseEnd_1170753] using wordTrace_append hprefix tailTrace_1170753
  have hstable : (prefixWord ++ tailWord_1170753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170753).length < 2 ^ (prefixWord ++ tailWord_1170753).sum := by decide
  have hdescent : baseEnd_1170753 < baseStart_1170753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170813 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 1, 5, 2]
def baseStart_1170813 : Nat := 118140960795 + 1170813 * 2 ^ 59
def prefixEnd_1170813 : Nat := 4983230072969 + 3 ^ 40 * 1170813 * 2
def baseEnd_1170813 : Nat := 601189825532632922453035

theorem tailTrace_1170813 : CollatzResearch.WordTrace tailWord_1170813 prefixEnd_1170813 601189825532632922453035 := by
  unfold tailWord_1170813
  simp only [CollatzResearch.WordTrace]
  refine ⟨42703058307351934785965093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28468705538234623190643395 42703058307351934785965093)
  ·
    refine ⟨8006823432628487772368455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42703058307351934785965093 8006823432628487772368455)
    ·
      refine ⟨12010235148942731658552683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8006823432628487772368455 12010235148942731658552683)
      ·
        refine ⟨18015352723414097487829025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12010235148942731658552683 18015352723414097487829025)
        ·
          refine ⟨13511514542560573115871769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18015352723414097487829025 13511514542560573115871769)
          ·
            refine ⟨10133635906920429836903827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13511514542560573115871769 10133635906920429836903827)
            ·
              refine ⟨15200453860380644755355741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10133635906920429836903827 15200453860380644755355741)
              ·
                refine ⟨5700170197642741783258403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15200453860380644755355741 5700170197642741783258403)
                ·
                  refine ⟨8550255296464112674887605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5700170197642741783258403 8550255296464112674887605)
                  ·
                    refine ⟨801586434043510563270713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8550255296464112674887605 801586434043510563270713)
                    ·
                      refine ⟨601189825532632922453035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 801586434043510563270713 601189825532632922453035)
                      ·
                        rfl

theorem cell23_1170813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_1170813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170813 prefixEnd_1170813 := by exact prefixLift 1170813
  have htrace : WordTrace (prefixWord ++ tailWord_1170813) baseStart_1170813 baseEnd_1170813 := by
    simpa [prefixWord, tailWord_1170813, baseEnd_1170813] using wordTrace_append hprefix tailTrace_1170813
  have hstable : (prefixWord ++ tailWord_1170813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170813).length < 2 ^ (prefixWord ++ tailWord_1170813).sum := by decide
  have hdescent : baseEnd_1170813 < baseStart_1170813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170823 : List Nat := [1, 1, 4, 2, 2, 2, 2, 3, 1, 5]
def baseStart_1170823 : Nat := 118140960795 + 1170823 * 2 ^ 59
def prefixEnd_1170823 : Nat := 4983230072969 + 3 ^ 40 * 1170823 * 2
def baseEnd_1170823 : Nat := 200398320113059294442663

theorem tailTrace_1170823 : CollatzResearch.WordTrace tailWord_1170823 prefixEnd_1170823 200398320113059294442663 := by
  unfold tailWord_1170823
  simp only [CollatzResearch.WordTrace]
  refine ⟨42703423037315706493829123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28468948691543804329219415 42703423037315706493829123)
  ·
    refine ⟨64055134555973559740743685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42703423037315706493829123 64055134555973559740743685)
    ·
      refine ⟨12010337729245042451389441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64055134555973559740743685 12010337729245042451389441)
      ·
        refine ⟨9007753296933781838542081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12010337729245042451389441 9007753296933781838542081)
        ·
          refine ⟨6755814972700336378906561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9007753296933781838542081 6755814972700336378906561)
          ·
            refine ⟨5066861229525252284179921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6755814972700336378906561 5066861229525252284179921)
            ·
              refine ⟨3800145922143939213134941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5066861229525252284179921 3800145922143939213134941)
              ·
                refine ⟨1425054720803977204925603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3800145922143939213134941 1425054720803977204925603)
                ·
                  refine ⟨2137582081205965807388405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1425054720803977204925603 2137582081205965807388405)
                  ·
                    refine ⟨200398320113059294442663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2137582081205965807388405 200398320113059294442663)
                    ·
                      rfl

theorem cell23_1170823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_1170823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170823 prefixEnd_1170823 := by exact prefixLift 1170823
  have htrace : WordTrace (prefixWord ++ tailWord_1170823) baseStart_1170823 baseEnd_1170823 := by
    simpa [prefixWord, tailWord_1170823, baseEnd_1170823] using wordTrace_append hprefix tailTrace_1170823
  have hstable : (prefixWord ++ tailWord_1170823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170823).length < 2 ^ (prefixWord ++ tailWord_1170823).sum := by decide
  have hdescent : baseEnd_1170823 < baseStart_1170823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170844 : List Nat := [2, 2, 3, 4, 2, 1, 2, 1, 6]
def baseStart_1170844 : Nat := 118140960795 + 1170844 * 2 ^ 59
def prefixEnd_1170844 : Nat := 4983230072969 + 3 ^ 40 * 1170844 * 2
def baseEnd_1170844 : Nat := 66800638159213589018377

theorem tailTrace_1170844 : CollatzResearch.WordTrace tailWord_1170844 prefixEnd_1170844 66800638159213589018377 := by
  unfold tailWord_1170844
  simp only [CollatzResearch.WordTrace]
  refine ⟨21352094485119813540171793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28469459313493084720229057 21352094485119813540171793)
  ·
    refine ⟨16014070863839860155128845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21352094485119813540171793 16014070863839860155128845)
    ·
      refine ⟨6005276573939947558173317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16014070863839860155128845 6005276573939947558173317)
      ·
        refine ⟨1125989357613740167157497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6005276573939947558173317 1125989357613740167157497)
        ·
          refine ⟨844492018210305125368123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1125989357613740167157497 844492018210305125368123)
          ·
            refine ⟨1266738027315457688052185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844492018210305125368123 1266738027315457688052185)
            ·
              refine ⟨950053520486593266039139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1266738027315457688052185 950053520486593266039139)
              ·
                refine ⟨1425080280729889899058709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950053520486593266039139 1425080280729889899058709)
                ·
                  refine ⟨66800638159213589018377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1425080280729889899058709 66800638159213589018377)
                  ·
                    rfl

theorem cell23_1170844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 6].length) (baseStart_1170844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170844 prefixEnd_1170844 := by exact prefixLift 1170844
  have htrace : WordTrace (prefixWord ++ tailWord_1170844) baseStart_1170844 baseEnd_1170844 := by
    simpa [prefixWord, tailWord_1170844, baseEnd_1170844] using wordTrace_append hprefix tailTrace_1170844
  have hstable : (prefixWord ++ tailWord_1170844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170844).length < 2 ^ (prefixWord ++ tailWord_1170844).sum := by decide
  have hdescent : baseEnd_1170844 < baseStart_1170844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170860 : List Nat := [2, 2, 1, 1, 1, 1, 4, 4, 3, 2, 2]
def baseStart_1170860 : Nat := 118140960795 + 1170860 * 2 ^ 59
def prefixEnd_1170860 : Nat := 4983230072969 + 3 ^ 40 * 1170860 * 2
def baseEnd_1170860 : Nat := 601213959123394238565319

theorem tailTrace_1170860 : CollatzResearch.WordTrace tailWord_1170860 prefixEnd_1170860 601213959123394238565319 := by
  unfold tailWord_1170860
  simp only [CollatzResearch.WordTrace]
  refine ⟨21352386269090830906463017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28469848358787774541950689 21352386269090830906463017)
  ·
    refine ⟨16014289701818123179847263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21352386269090830906463017 16014289701818123179847263)
    ·
      refine ⟨24021434552727184769770895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16014289701818123179847263 24021434552727184769770895)
      ·
        refine ⟨36032151829090777154656343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24021434552727184769770895 36032151829090777154656343)
        ·
          refine ⟨54048227743636165731984515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36032151829090777154656343 54048227743636165731984515)
          ·
            refine ⟨81072341615454248597976773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54048227743636165731984515 81072341615454248597976773)
            ·
              refine ⟨15201064052897671612120645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81072341615454248597976773 15201064052897671612120645)
              ·
                refine ⟨2850199509918313427272621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15201064052897671612120645 2850199509918313427272621)
                ·
                  refine ⟨1068824816219367535227233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2850199509918313427272621 1068824816219367535227233)
                  ·
                    refine ⟨801618612164525651420425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1068824816219367535227233 801618612164525651420425)
                    ·
                      refine ⟨601213959123394238565319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 801618612164525651420425 601213959123394238565319)
                      ·
                        rfl

theorem cell23_1170860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 2, 2].length) (baseStart_1170860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170860 prefixEnd_1170860 := by exact prefixLift 1170860
  have htrace : WordTrace (prefixWord ++ tailWord_1170860) baseStart_1170860 baseEnd_1170860 := by
    simpa [prefixWord, tailWord_1170860, baseEnd_1170860] using wordTrace_append hprefix tailTrace_1170860
  have hstable : (prefixWord ++ tailWord_1170860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170860).length < 2 ^ (prefixWord ++ tailWord_1170860).sum := by decide
  have hdescent : baseEnd_1170860 < baseStart_1170860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170882 : List Nat := [3, 5, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1170882 : Nat := 118140960795 + 1170882 * 2 ^ 59
def prefixEnd_1170882 : Nat := 4983230072969 + 3 ^ 40 * 1170882 * 2
def baseEnd_1170882 : Nat := 200408418565931050830073

theorem tailTrace_1170882 : CollatzResearch.WordTrace tailWord_1170882 prefixEnd_1170882 200408418565931050830073 := by
  unfold tailWord_1170882
  simp only [CollatzResearch.WordTrace]
  refine ⟨10676393736025489892556725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28470383296067973046817933 10676393736025489892556725)
  ·
    refine ⟨1000911912752389677427193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10676393736025489892556725 1000911912752389677427193)
    ·
      refine ⟨750683934564292258070395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1000911912752389677427193 750683934564292258070395)
      ·
        refine ⟨1126025901846438387105593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 750683934564292258070395 1126025901846438387105593)
        ·
          refine ⟨844519426384828790329195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1126025901846438387105593 844519426384828790329195)
          ·
            refine ⟨1266779139577243185493793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844519426384828790329195 1266779139577243185493793)
            ·
              refine ⟨950084354682932389120345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1266779139577243185493793 950084354682932389120345)
              ·
                refine ⟨712563266012199291840259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 950084354682932389120345 712563266012199291840259)
                ·
                  refine ⟨1068844899018298937760389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 712563266012199291840259 1068844899018298937760389)
                  ·
                    refine ⟨200408418565931050830073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1068844899018298937760389 200408418565931050830073)
                    ·
                      rfl

theorem cell23_1170882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1170882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170882 prefixEnd_1170882 := by exact prefixLift 1170882
  have htrace : WordTrace (prefixWord ++ tailWord_1170882) baseStart_1170882 baseEnd_1170882 := by
    simpa [prefixWord, tailWord_1170882, baseEnd_1170882] using wordTrace_append hprefix tailTrace_1170882
  have hstable : (prefixWord ++ tailWord_1170882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170882).length < 2 ^ (prefixWord ++ tailWord_1170882).sum := by decide
  have hdescent : baseEnd_1170882 < baseStart_1170882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170900 : List Nat := [2, 4, 1, 2, 3, 2, 1, 8]
def baseStart_1170900 : Nat := 118140960795 + 1170900 * 2 ^ 59
def prefixEnd_1170900 : Nat := 4983230072969 + 3 ^ 40 * 1170900 * 2
def baseEnd_1170900 : Nat := 22267944383317558595005

theorem tailTrace_1170900 : CollatzResearch.WordTrace tailWord_1170900 prefixEnd_1170900 22267944383317558595005 := by
  unfold tailWord_1170900
  simp only [CollatzResearch.WordTrace]
  refine ⟨21353115729018374322191077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28470820972024499096254769 21353115729018374322191077)
  ·
    refine ⟨4003709199190945185410827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21353115729018374322191077 4003709199190945185410827)
    ·
      refine ⟨6005563798786417778116241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4003709199190945185410827 6005563798786417778116241)
      ·
        refine ⟨4504172849089813333587181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6005563798786417778116241 4504172849089813333587181)
        ·
          refine ⟨1689064818408680000095193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4504172849089813333587181 1689064818408680000095193)
          ·
            refine ⟨1266798613806510000071395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1689064818408680000095193 1266798613806510000071395)
            ·
              refine ⟨1900197920709765000107093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1266798613806510000071395 1900197920709765000107093)
              ·
                refine ⟨22267944383317558595005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1900197920709765000107093 22267944383317558595005)
                ·
                  rfl

theorem cell23_1170900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 8].length) (baseStart_1170900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170900 prefixEnd_1170900 := by exact prefixLift 1170900
  have htrace : WordTrace (prefixWord ++ tailWord_1170900) baseStart_1170900 baseEnd_1170900 := by
    simpa [prefixWord, tailWord_1170900, baseEnd_1170900] using wordTrace_append hprefix tailTrace_1170900
  have hstable : (prefixWord ++ tailWord_1170900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170900).length < 2 ^ (prefixWord ++ tailWord_1170900).sum := by decide
  have hdescent : baseEnd_1170900 < baseStart_1170900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170920 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 3, 3, 2]
def baseStart_1170920 : Nat := 118140960795 + 1170920 * 2 ^ 59
def prefixEnd_1170920 : Nat := 4983230072969 + 3 ^ 40 * 1170920 * 2
def baseEnd_1170920 : Nat := 601244767962664003815043

theorem tailTrace_1170920 : CollatzResearch.WordTrace tailWord_1170920 prefixEnd_1170920 601244767962664003815043 := by
  unfold tailWord_1170920
  simp only [CollatzResearch.WordTrace]
  refine ⟨21353480458982146030055107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28471307278642861373406809 21353480458982146030055107)
  ·
    refine ⟨32030220688473219045082661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21353480458982146030055107 32030220688473219045082661)
    ·
      refine ⟨6005666379088728570952999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32030220688473219045082661 6005666379088728570952999)
      ·
        refine ⟨9008499568633092856429499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6005666379088728570952999 9008499568633092856429499)
        ·
          refine ⟨13512749352949639284644249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9008499568633092856429499 13512749352949639284644249)
          ·
            refine ⟨10134562014712229463483187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13512749352949639284644249 10134562014712229463483187)
            ·
              refine ⟨15201843022068344195224781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10134562014712229463483187 15201843022068344195224781)
              ·
                refine ⟨5700691133275629073209293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15201843022068344195224781 5700691133275629073209293)
                ·
                  refine ⟨2137759174978360902453485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5700691133275629073209293 2137759174978360902453485)
                  ·
                    refine ⟨801659690616885338420057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2137759174978360902453485 801659690616885338420057)
                    ·
                      refine ⟨601244767962664003815043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 801659690616885338420057 601244767962664003815043)
                      ·
                        rfl

theorem cell23_1170920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_1170920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170920 prefixEnd_1170920 := by exact prefixLift 1170920
  have htrace : WordTrace (prefixWord ++ tailWord_1170920) baseStart_1170920 baseEnd_1170920 := by
    simpa [prefixWord, tailWord_1170920, baseEnd_1170920] using wordTrace_append hprefix tailTrace_1170920
  have hstable : (prefixWord ++ tailWord_1170920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170920).length < 2 ^ (prefixWord ++ tailWord_1170920).sum := by decide
  have hdescent : baseEnd_1170920 < baseStart_1170920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170963 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 4]
def baseStart_1170963 : Nat := 118140960795 + 1170963 * 2 ^ 59
def prefixEnd_1170963 : Nat := 4983230072969 + 3 ^ 40 * 1170963 * 2
def baseEnd_1170963 : Nat := 601266847630807335577345

theorem tailTrace_1170963 : CollatzResearch.WordTrace tailWord_1170963 prefixEnd_1170963 601266847630807335577345 := by
  unfold tailWord_1170963
  simp only [CollatzResearch.WordTrace]
  refine ⟨42708529256808510403925543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28472352837872340269283695 42708529256808510403925543)
  ·
    refine ⟨64062793885212765605888315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42708529256808510403925543 64062793885212765605888315)
    ·
      refine ⟨96094190827819148408832473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64062793885212765605888315 96094190827819148408832473)
      ·
        refine ⟨72070643120864361306624355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96094190827819148408832473 72070643120864361306624355)
        ·
          refine ⟨108105964681296541959936533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72070643120864361306624355 108105964681296541959936533)
          ·
            refine ⟨5067467094435775404372025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 108105964681296541959936533 5067467094435775404372025)
            ·
              refine ⟨3800600320826831553279019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5067467094435775404372025 3800600320826831553279019)
              ·
                refine ⟨5700900481240247329918529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3800600320826831553279019 5700900481240247329918529)
                ·
                  refine ⟨4275675360930185497438897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5700900481240247329918529 4275675360930185497438897)
                  ·
                    refine ⟨3206756520697639123079173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4275675360930185497438897 3206756520697639123079173)
                    ·
                      refine ⟨601266847630807335577345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3206756520697639123079173 601266847630807335577345)
                      ·
                        rfl

theorem cell23_1170963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 4].length) (baseStart_1170963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170963 prefixEnd_1170963 := by exact prefixLift 1170963
  have htrace : WordTrace (prefixWord ++ tailWord_1170963) baseStart_1170963 baseEnd_1170963 := by
    simpa [prefixWord, tailWord_1170963, baseEnd_1170963] using wordTrace_append hprefix tailTrace_1170963
  have hstable : (prefixWord ++ tailWord_1170963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170963).length < 2 ^ (prefixWord ++ tailWord_1170963).sum := by decide
  have hdescent : baseEnd_1170963 < baseStart_1170963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170973 : List Nat := [1, 4, 2, 2, 1, 1, 1, 4, 7]
def baseStart_1170973 : Nat := 118140960795 + 1170973 * 2 ^ 59
def prefixEnd_1170973 : Nat := 4983230072969 + 3 ^ 40 * 1170973 * 2
def baseEnd_1170973 : Nat := 66807998048594699605811

theorem tailTrace_1170973 : CollatzResearch.WordTrace tailWord_1170973 prefixEnd_1170973 66807998048594699605811 := by
  unfold tailWord_1170973
  simp only [CollatzResearch.WordTrace]
  refine ⟨42708893986772282111789573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28472595991181521407859715 42708893986772282111789573)
  ·
    refine ⟨8007917622519802895960545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42708893986772282111789573 8007917622519802895960545)
    ·
      refine ⟨6005938216889852171970409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8007917622519802895960545 6005938216889852171970409)
      ·
        refine ⟨4504453662667389128977807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6005938216889852171970409 4504453662667389128977807)
        ·
          refine ⟨6756680494001083693466711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4504453662667389128977807 6756680494001083693466711)
          ·
            refine ⟨10135020741001625540200067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6756680494001083693466711 10135020741001625540200067)
            ·
              refine ⟨15202531111502438310300101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10135020741001625540200067 15202531111502438310300101)
              ·
                refine ⟨2850474583406707183181269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15202531111502438310300101 2850474583406707183181269)
                ·
                  refine ⟨66807998048594699605811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2850474583406707183181269 66807998048594699605811)
                  ·
                    rfl

theorem cell23_1170973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_1170973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1170973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1170973 prefixEnd_1170973 := by exact prefixLift 1170973
  have htrace : WordTrace (prefixWord ++ tailWord_1170973) baseStart_1170973 baseEnd_1170973 := by
    simpa [prefixWord, tailWord_1170973, baseEnd_1170973] using wordTrace_append hprefix tailTrace_1170973
  have hstable : (prefixWord ++ tailWord_1170973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170973).length < 2 ^ (prefixWord ++ tailWord_1170973).sum := by decide
  have hdescent : baseEnd_1170973 < baseStart_1170973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171007 : List Nat := [1, 1, 2, 2, 3, 4, 3, 2, 5]
def baseStart_1171007 : Nat := 118140960795 + 1171007 * 2 ^ 59
def prefixEnd_1171007 : Nat := 4983230072969 + 3 ^ 40 * 1171007 * 2
def baseEnd_1171007 : Nat := 66809937864400573714127

theorem tailTrace_1171007 : CollatzResearch.WordTrace tailWord_1171007 prefixEnd_1171007 66809937864400573714127 := by
  unfold tailWord_1171007
  simp only [CollatzResearch.WordTrace]
  refine ⟨42710134068649105918527275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28473422712432737279018183 42710134068649105918527275)
  ·
    refine ⟨64065201102973658877790913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42710134068649105918527275 64065201102973658877790913)
    ·
      refine ⟨48048900827230244158343185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64065201102973658877790913 48048900827230244158343185)
      ·
        refine ⟨36036675620422683118757389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48048900827230244158343185 36036675620422683118757389)
        ·
          refine ⟨13513753357658506169534021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36036675620422683118757389 13513753357658506169534021)
          ·
            refine ⟨2533828754560969906787629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13513753357658506169534021 2533828754560969906787629)
            ·
              refine ⟨950185782960363715045361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2533828754560969906787629 950185782960363715045361)
              ·
                refine ⟨712639337220272786284021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 950185782960363715045361 712639337220272786284021)
                ·
                  refine ⟨66809937864400573714127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 712639337220272786284021 66809937864400573714127)
                  ·
                    rfl

theorem cell23_1171007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 5].length) (baseStart_1171007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171007 prefixEnd_1171007 := by exact prefixLift 1171007
  have htrace : WordTrace (prefixWord ++ tailWord_1171007) baseStart_1171007 baseEnd_1171007 := by
    simpa [prefixWord, tailWord_1171007, baseEnd_1171007] using wordTrace_append hprefix tailTrace_1171007
  have hstable : (prefixWord ++ tailWord_1171007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171007).length < 2 ^ (prefixWord ++ tailWord_1171007).sum := by decide
  have hdescent : baseEnd_1171007 < baseStart_1171007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171013 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 1, 2, 5]
def baseStart_1171013 : Nat := 118140960795 + 1171013 * 2 ^ 59
def prefixEnd_1171013 : Nat := 4983230072969 + 3 ^ 40 * 1171013 * 2
def baseEnd_1171013 : Nat := 601292521663532139952115

theorem tailTrace_1171013 : CollatzResearch.WordTrace tailWord_1171013 prefixEnd_1171013 601292521663532139952115 := by
  unfold tailWord_1171013
  simp only [CollatzResearch.WordTrace]
  refine ⟨42710352906627368943245693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28473568604418245962163795 42710352906627368943245693)
  ·
    refine ⟨16016382339985263353717135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42710352906627368943245693 16016382339985263353717135)
    ·
      refine ⟨24024573509977895030575703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16016382339985263353717135 24024573509977895030575703)
      ·
        refine ⟨36036860264966842545863555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24024573509977895030575703 36036860264966842545863555)
        ·
          refine ⟨54055290397450263818795333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36036860264966842545863555 54055290397450263818795333)
          ·
            refine ⟨10135366949521924466024125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54055290397450263818795333 10135366949521924466024125)
            ·
              refine ⟨3800762606070721674759047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10135366949521924466024125 3800762606070721674759047)
              ·
                refine ⟨5701143909106082512138571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3800762606070721674759047 5701143909106082512138571)
                ·
                  refine ⟨8551715863659123768207857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5701143909106082512138571 8551715863659123768207857)
                  ·
                    refine ⟨6413786897744342826155893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8551715863659123768207857 6413786897744342826155893)
                    ·
                      refine ⟨601292521663532139952115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6413786897744342826155893 601292521663532139952115)
                      ·
                        rfl

theorem cell23_1171013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_1171013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171013 prefixEnd_1171013 := by exact prefixLift 1171013
  have htrace : WordTrace (prefixWord ++ tailWord_1171013) baseStart_1171013 baseEnd_1171013 := by
    simpa [prefixWord, tailWord_1171013, baseEnd_1171013] using wordTrace_append hprefix tailTrace_1171013
  have hstable : (prefixWord ++ tailWord_1171013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171013).length < 2 ^ (prefixWord ++ tailWord_1171013).sum := by decide
  have hdescent : baseEnd_1171013 < baseStart_1171013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171023 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 4]
def baseStart_1171023 : Nat := 118140960795 + 1171023 * 2 ^ 59
def prefixEnd_1171023 : Nat := 4983230072969 + 3 ^ 40 * 1171023 * 2
def baseEnd_1171023 : Nat := 601297656470077100827069

theorem tailTrace_1171023 : CollatzResearch.WordTrace tailWord_1171023 prefixEnd_1171023 601297656470077100827069 := by
  unfold tailWord_1171023
  simp only [CollatzResearch.WordTrace]
  refine ⟨42710717636591140651109723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28473811757727427100739815 42710717636591140651109723)
  ·
    refine ⟨64066076454886710976664585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42710717636591140651109723 64066076454886710976664585)
    ·
      refine ⟨48049557341165033232498439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64066076454886710976664585 48049557341165033232498439)
      ·
        refine ⟨72074336011747549848747659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48049557341165033232498439 72074336011747549848747659)
        ·
          refine ⟨108111504017621324773121489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72074336011747549848747659 108111504017621324773121489)
          ·
            refine ⟨81083628013215993579841117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108111504017621324773121489 81083628013215993579841117)
            ·
              refine ⟨30406360504955997592440419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81083628013215993579841117 30406360504955997592440419)
              ·
                refine ⟨45609540757433996388660629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30406360504955997592440419 45609540757433996388660629)
                ·
                  refine ⟨2137947223004718580718467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45609540757433996388660629 2137947223004718580718467)
                  ·
                    refine ⟨3206920834507077871077701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2137947223004718580718467 3206920834507077871077701)
                    ·
                      refine ⟨601297656470077100827069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3206920834507077871077701 601297656470077100827069)
                      ·
                        rfl

theorem cell23_1171023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 4].length) (baseStart_1171023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171023 prefixEnd_1171023 := by exact prefixLift 1171023
  have htrace : WordTrace (prefixWord ++ tailWord_1171023) baseStart_1171023 baseEnd_1171023 := by
    simpa [prefixWord, tailWord_1171023, baseEnd_1171023] using wordTrace_append hprefix tailTrace_1171023
  have hstable : (prefixWord ++ tailWord_1171023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171023).length < 2 ^ (prefixWord ++ tailWord_1171023).sum := by decide
  have hdescent : baseEnd_1171023 < baseStart_1171023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171040 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 4, 4, 2]
def baseStart_1171040 : Nat := 118140960795 + 1171040 * 2 ^ 59
def prefixEnd_1171040 : Nat := 4983230072969 + 3 ^ 40 * 1171040 * 2
def baseEnd_1171040 : Nat := 601306385641203534314491

theorem tailTrace_1171040 : CollatzResearch.WordTrace tailWord_1171040 prefixEnd_1171040 601306385641203534314491 := by
  unfold tailWord_1171040
  simp only [CollatzResearch.WordTrace]
  refine ⟨21355668838764776277239287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28474225118353035036319049 21355668838764776277239287)
  ·
    refine ⟨32033503258147164415858931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21355668838764776277239287 32033503258147164415858931)
    ·
      refine ⟨48050254887220746623788397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32033503258147164415858931 48050254887220746623788397)
      ·
        refine ⟨18018845582707779983920649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48050254887220746623788397 18018845582707779983920649)
        ·
          refine ⟨13514134187030834987940487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18018845582707779983920649 13514134187030834987940487)
          ·
            refine ⟨20271201280546252481910731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13514134187030834987940487 20271201280546252481910731)
            ·
              refine ⟨30406801920819378722866097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20271201280546252481910731 30406801920819378722866097)
              ·
                refine ⟨22805101440614534042149573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30406801920819378722866097 22805101440614534042149573)
                ·
                  refine ⟨4275956520115225132903045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22805101440614534042149573 4275956520115225132903045)
                  ·
                    refine ⟨801741847521604712419321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4275956520115225132903045 801741847521604712419321)
                    ·
                      refine ⟨601306385641203534314491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 801741847521604712419321 601306385641203534314491)
                      ·
                        rfl

theorem cell23_1171040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_1171040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171040 prefixEnd_1171040 := by exact prefixLift 1171040
  have htrace : WordTrace (prefixWord ++ tailWord_1171040) baseStart_1171040 baseEnd_1171040 := by
    simpa [prefixWord, tailWord_1171040, baseEnd_1171040] using wordTrace_append hprefix tailTrace_1171040
  have hstable : (prefixWord ++ tailWord_1171040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171040).length < 2 ^ (prefixWord ++ tailWord_1171040).sum := by decide
  have hdescent : baseEnd_1171040 < baseStart_1171040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171067 : List Nat := [1, 1, 1, 1, 1, 4, 5, 4, 1, 4]
def baseStart_1171067 : Nat := 118140960795 + 1171067 * 2 ^ 59
def prefixEnd_1171067 : Nat := 4983230072969 + 3 ^ 40 * 1171067 * 2
def baseEnd_1171067 : Nat := 200440083206291642892289

theorem tailTrace_1171067 : CollatzResearch.WordTrace tailWord_1171067 prefixEnd_1171067 200440083206291642892289 := by
  unfold tailWord_1171067
  simp only [CollatzResearch.WordTrace]
  refine ⟨42712322448431736165711455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28474881632287824110474303 42712322448431736165711455)
  ·
    refine ⟨64068483672647604248567183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42712322448431736165711455 64068483672647604248567183)
    ·
      refine ⟨96102725508971406372850775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64068483672647604248567183 96102725508971406372850775)
      ·
        refine ⟨144154088263457109559276163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96102725508971406372850775 144154088263457109559276163)
        ·
          refine ⟨216231132395185664338914245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144154088263457109559276163 216231132395185664338914245)
          ·
            refine ⟨40543337324097312063546421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 216231132395185664338914245 40543337324097312063546421)
            ·
              refine ⟨3800937874134123005957477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40543337324097312063546421 3800937874134123005957477)
              ·
                refine ⟨712675851400148063617027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3800937874134123005957477 712675851400148063617027)
                ·
                  refine ⟨1069013777100222095425541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 712675851400148063617027 1069013777100222095425541)
                  ·
                    refine ⟨200440083206291642892289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1069013777100222095425541 200440083206291642892289)
                    ·
                      rfl

theorem cell23_1171067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 1, 4].length) (baseStart_1171067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171067 prefixEnd_1171067 := by exact prefixLift 1171067
  have htrace : WordTrace (prefixWord ++ tailWord_1171067) baseStart_1171067 baseEnd_1171067 := by
    simpa [prefixWord, tailWord_1171067, baseEnd_1171067] using wordTrace_append hprefix tailTrace_1171067
  have hstable : (prefixWord ++ tailWord_1171067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171067).length < 2 ^ (prefixWord ++ tailWord_1171067).sum := by decide
  have hdescent : baseEnd_1171067 < baseStart_1171067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171113 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 1, 7, 4]
def baseStart_1171113 : Nat := 118140960795 + 1171113 * 2 ^ 59
def prefixEnd_1171113 : Nat := 4983230072969 + 3 ^ 40 * 1171113 * 2
def baseEnd_1171113 : Nat := 601343869728981748701655

theorem tailTrace_1171113 : CollatzResearch.WordTrace tailWord_1171113 prefixEnd_1171113 601343869728981748701655 := by
  unfold tailWord_1171113
  simp only [CollatzResearch.WordTrace]
  refine ⟨42714000206265086021885993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28476000137510057347923995 42714000206265086021885993)
  ·
    refine ⟨32035500154698814516414495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42714000206265086021885993 32035500154698814516414495)
    ·
      refine ⟨48053250232048221774621743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32035500154698814516414495 48053250232048221774621743)
      ·
        refine ⟨72079875348072332661932615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48053250232048221774621743 72079875348072332661932615)
        ·
          refine ⟨108119813022108498992898923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72079875348072332661932615 108119813022108498992898923)
          ·
            refine ⟨162179719533162748489348385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108119813022108498992898923 162179719533162748489348385)
            ·
              refine ⟨121634789649872061367011289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162179719533162748489348385 121634789649872061367011289)
              ·
                refine ⟨91226092237404046025258467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121634789649872061367011289 91226092237404046025258467)
                ·
                  refine ⟨136839138356106069037887701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91226092237404046025258467 136839138356106069037887701)
                  ·
                    refine ⟨3207167305221235993075493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 136839138356106069037887701 3207167305221235993075493)
                    ·
                      refine ⟨601343869728981748701655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3207167305221235993075493 601343869728981748701655)
                      ·
                        rfl

theorem cell23_1171113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 7, 4].length) (baseStart_1171113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171113 prefixEnd_1171113 := by exact prefixLift 1171113
  have htrace : WordTrace (prefixWord ++ tailWord_1171113) baseStart_1171113 baseEnd_1171113 := by
    simpa [prefixWord, tailWord_1171113, baseEnd_1171113] using wordTrace_append hprefix tailTrace_1171113
  have hstable : (prefixWord ++ tailWord_1171113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171113).length < 2 ^ (prefixWord ++ tailWord_1171113).sum := by decide
  have hdescent : baseEnd_1171113 < baseStart_1171113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171150 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_1171150 : Nat := 118140960795 + 1171150 * 2 ^ 59
def prefixEnd_1171150 : Nat := 4983230072969 + 3 ^ 40 * 1171150 * 2
def baseEnd_1171150 : Nat := 601362868513198103938985

theorem tailTrace_1171150 : CollatzResearch.WordTrace tailWord_1171150 prefixEnd_1171150 601362868513198103938985 := by
  unfold tailWord_1171150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5339418713391380167622863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28476899804754027560655269 5339418713391380167622863)
  ·
    refine ⟨8009128070087070251434295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5339418713391380167622863 8009128070087070251434295)
    ·
      refine ⟨12013692105130605377151443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8009128070087070251434295 12013692105130605377151443)
      ·
        refine ⟨18020538157695908065727165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12013692105130605377151443 18020538157695908065727165)
        ·
          refine ⟨6757701809135965524647687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18020538157695908065727165 6757701809135965524647687)
          ·
            refine ⟨10136552713703948286971531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6757701809135965524647687 10136552713703948286971531)
            ·
              refine ⟨15204829070555922430457297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10136552713703948286971531 15204829070555922430457297)
              ·
                refine ⟨11403621802916941822842973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15204829070555922430457297 11403621802916941822842973)
                ·
                  refine ⟨4276358176093853183566115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11403621802916941822842973 4276358176093853183566115)
                  ·
                    refine ⟨6414537264140779775349173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4276358176093853183566115 6414537264140779775349173)
                    ·
                      refine ⟨601362868513198103938985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6414537264140779775349173 601362868513198103938985)
                      ·
                        rfl

theorem cell23_1171150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_1171150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171150 prefixEnd_1171150 := by exact prefixLift 1171150
  have htrace : WordTrace (prefixWord ++ tailWord_1171150) baseStart_1171150 baseEnd_1171150 := by
    simpa [prefixWord, tailWord_1171150, baseEnd_1171150] using wordTrace_append hprefix tailTrace_1171150
  have hstable : (prefixWord ++ tailWord_1171150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171150).length < 2 ^ (prefixWord ++ tailWord_1171150).sum := by decide
  have hdescent : baseEnd_1171150 < baseStart_1171150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171160 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 3, 2, 4]
def baseStart_1171160 : Nat := 118140960795 + 1171160 * 2 ^ 59
def prefixEnd_1171160 : Nat := 4983230072969 + 3 ^ 40 * 1171160 * 2
def baseEnd_1171160 : Nat := 601368003319743064813939

theorem tailTrace_1171160 : CollatzResearch.WordTrace tailWord_1171160 prefixEnd_1171160 601368003319743064813939 := by
  unfold tailWord_1171160
  simp only [CollatzResearch.WordTrace]
  refine ⟨21357857218547406524423467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28477142958063208699231289 21357857218547406524423467)
  ·
    refine ⟨32036785827821109786635201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21357857218547406524423467 32036785827821109786635201)
    ·
      refine ⟨24027589370865832339976401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32036785827821109786635201 24027589370865832339976401)
      ·
        refine ⟨18020692028149374254982301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24027589370865832339976401 18020692028149374254982301)
        ·
          refine ⟨6757759510556015345618363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18020692028149374254982301 6757759510556015345618363)
          ·
            refine ⟨10136639265834023018427545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6757759510556015345618363 10136639265834023018427545)
            ·
              refine ⟨7602479449375517263820659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10136639265834023018427545 7602479449375517263820659)
              ·
                refine ⟨11403719174063275895730989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7602479449375517263820659 11403719174063275895730989)
                ·
                  refine ⟨4276394690273728460899121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11403719174063275895730989 4276394690273728460899121)
                  ·
                    refine ⟨3207296017705296345674341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4276394690273728460899121 3207296017705296345674341)
                    ·
                      refine ⟨601368003319743064813939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3207296017705296345674341 601368003319743064813939)
                      ·
                        rfl

theorem cell23_1171160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_1171160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171160 prefixEnd_1171160 := by exact prefixLift 1171160
  have htrace : WordTrace (prefixWord ++ tailWord_1171160) baseStart_1171160 baseEnd_1171160 := by
    simpa [prefixWord, tailWord_1171160, baseEnd_1171160] using wordTrace_append hprefix tailTrace_1171160
  have hstable : (prefixWord ++ tailWord_1171160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171160).length < 2 ^ (prefixWord ++ tailWord_1171160).sum := by decide
  have hdescent : baseEnd_1171160 < baseStart_1171160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171167 : List Nat := [1, 1, 2, 3, 2, 2, 1, 5, 1, 2, 3]
def baseStart_1171167 : Nat := 118140960795 + 1171167 * 2 ^ 59
def prefixEnd_1171167 : Nat := 4983230072969 + 3 ^ 40 * 1171167 * 2
def baseEnd_1171167 : Nat := 601371597684324537426407

theorem tailTrace_1171167 : CollatzResearch.WordTrace tailWord_1171167 prefixEnd_1171167 601371597684324537426407 := by
  unfold tailWord_1171167
  simp only [CollatzResearch.WordTrace]
  refine ⟨42715969748069453244351755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28477313165379635496234503 42715969748069453244351755)
  ·
    refine ⟨64073954622104179866527633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42715969748069453244351755 64073954622104179866527633)
    ·
      refine ⟨48055465966578134899895725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64073954622104179866527633 48055465966578134899895725)
      ·
        refine ⟨18020799737466800587460897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48055465966578134899895725 18020799737466800587460897)
        ·
          refine ⟨13515599803100100440595673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18020799737466800587460897 13515599803100100440595673)
          ·
            refine ⟨10136699852325075330446755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13515599803100100440595673 10136699852325075330446755)
            ·
              refine ⟨15205049778487612995670133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10136699852325075330446755 15205049778487612995670133)
              ·
                refine ⟨1425473416733213718344075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15205049778487612995670133 1425473416733213718344075)
                ·
                  refine ⟨2138210125099820577516113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1425473416733213718344075 2138210125099820577516113)
                  ·
                    refine ⟨1603657593824865433137085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2138210125099820577516113 1603657593824865433137085)
                    ·
                      refine ⟨601371597684324537426407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1603657593824865433137085 601371597684324537426407)
                      ·
                        rfl

theorem cell23_1171167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_1171167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171167 prefixEnd_1171167 := by exact prefixLift 1171167
  have htrace : WordTrace (prefixWord ++ tailWord_1171167) baseStart_1171167 baseEnd_1171167 := by
    simpa [prefixWord, tailWord_1171167, baseEnd_1171167] using wordTrace_append hprefix tailTrace_1171167
  have hstable : (prefixWord ++ tailWord_1171167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171167).length < 2 ^ (prefixWord ++ tailWord_1171167).sum := by decide
  have hdescent : baseEnd_1171167 < baseStart_1171167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171175 : List Nat := [1, 1, 5, 4, 1, 1, 3, 2, 1, 1, 3]
def baseStart_1171175 : Nat := 118140960795 + 1171175 * 2 ^ 59
def prefixEnd_1171175 : Nat := 4983230072969 + 3 ^ 40 * 1171175 * 2
def baseEnd_1171175 : Nat := 601375705529560506126371

theorem tailTrace_1171175 : CollatzResearch.WordTrace tailWord_1171175 prefixEnd_1171175 601375705529560506126371 := by
  unfold tailWord_1171175
  simp only [CollatzResearch.WordTrace]
  refine ⟨42716261532040470610642979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28477507688026980407095319 42716261532040470610642979)
  ·
    refine ⟨64074392298060705915964469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42716261532040470610642979 64074392298060705915964469)
    ·
      refine ⟨6006974277943191179621669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64074392298060705915964469 6006974277943191179621669)
      ·
        refine ⟨1126307677114348346179063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6006974277943191179621669 1126307677114348346179063)
        ·
          refine ⟨1689461515671522519268595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1126307677114348346179063 1689461515671522519268595)
          ·
            refine ⟨2534192273507283778902893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1689461515671522519268595 2534192273507283778902893)
            ·
              refine ⟨950322102565231417088585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2534192273507283778902893 950322102565231417088585)
              ·
                refine ⟨712741576923923562816439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 950322102565231417088585 712741576923923562816439)
                ·
                  refine ⟨1069112365385885344224659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 712741576923923562816439 1069112365385885344224659)
                  ·
                    refine ⟨1603668548078828016336989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1069112365385885344224659 1603668548078828016336989)
                    ·
                      refine ⟨601375705529560506126371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1603668548078828016336989 601375705529560506126371)
                      ·
                        rfl

theorem cell23_1171175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_1171175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171175 prefixEnd_1171175 := by exact prefixLift 1171175
  have htrace : WordTrace (prefixWord ++ tailWord_1171175) baseStart_1171175 baseEnd_1171175 := by
    simpa [prefixWord, tailWord_1171175, baseEnd_1171175] using wordTrace_append hprefix tailTrace_1171175
  have hstable : (prefixWord ++ tailWord_1171175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171175).length < 2 ^ (prefixWord ++ tailWord_1171175).sum := by decide
  have hdescent : baseEnd_1171175 < baseStart_1171175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171181 : List Nat := [1, 5, 1, 2, 1, 2, 3, 1, 3, 2, 2]
def baseStart_1171181 : Nat := 118140960795 + 1171181 * 2 ^ 59
def prefixEnd_1171181 : Nat := 4983230072969 + 3 ^ 40 * 1171181 * 2
def baseEnd_1171181 : Nat := 601378786413487482651343

theorem tailTrace_1171181 : CollatzResearch.WordTrace tailWord_1171181 prefixEnd_1171181 601378786413487482651343 := by
  unfold tailWord_1171181
  simp only [CollatzResearch.WordTrace]
  refine ⟨42716480370018733635361397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28477653580012489090240931 42716480370018733635361397)
  ·
    refine ⟨4004670034689256278315131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42716480370018733635361397 4004670034689256278315131)
    ·
      refine ⟨6007005052033884417472697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4004670034689256278315131 6007005052033884417472697)
      ·
        refine ⟨4505253789025413313104523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6007005052033884417472697 4505253789025413313104523)
        ·
          refine ⟨6757880683538119969656785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4505253789025413313104523 6757880683538119969656785)
          ·
            refine ⟨5068410512653589977242589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6757880683538119969656785 5068410512653589977242589)
            ·
              refine ⟨1900653942245096241465971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5068410512653589977242589 1900653942245096241465971)
              ·
                refine ⟨2850980913367644362198957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1900653942245096241465971 2850980913367644362198957)
                ·
                  refine ⟨1069117842512866635824609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2850980913367644362198957 1069117842512866635824609)
                  ·
                    refine ⟨801838381884649976868457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1069117842512866635824609 801838381884649976868457)
                    ·
                      refine ⟨601378786413487482651343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 801838381884649976868457 601378786413487482651343)
                      ·
                        rfl

theorem cell23_1171181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_1171181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171181 prefixEnd_1171181 := by exact prefixLift 1171181
  have htrace : WordTrace (prefixWord ++ tailWord_1171181) baseStart_1171181 baseEnd_1171181 := by
    simpa [prefixWord, tailWord_1171181, baseEnd_1171181] using wordTrace_append hprefix tailTrace_1171181
  have hstable : (prefixWord ++ tailWord_1171181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171181).length < 2 ^ (prefixWord ++ tailWord_1171181).sum := by decide
  have hdescent : baseEnd_1171181 < baseStart_1171181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171197 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 6, 1, 3]
def baseStart_1171197 : Nat := 118140960795 + 1171197 * 2 ^ 59
def prefixEnd_1171197 : Nat := 4983230072969 + 3 ^ 40 * 1171197 * 2
def baseEnd_1171197 : Nat := 601387002103959420051269

theorem tailTrace_1171197 : CollatzResearch.WordTrace tailWord_1171197 prefixEnd_1171197 601387002103959420051269 := by
  unfold tailWord_1171197
  simp only [CollatzResearch.WordTrace]
  refine ⟨42717063937960768367943845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28478042625307178911962563 42717063937960768367943845)
  ·
    refine ⟨8009449488367644068989471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42717063937960768367943845 8009449488367644068989471)
    ·
      refine ⟨12014174232551466103484207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8009449488367644068989471 12014174232551466103484207)
      ·
        refine ⟨18021261348827199155226311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12014174232551466103484207 18021261348827199155226311)
        ·
          refine ⟨27031892023240798732839467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18021261348827199155226311 27031892023240798732839467)
          ·
            refine ⟨40547838034861198099259201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27031892023240798732839467 40547838034861198099259201)
            ·
              refine ⟨30410878526145898574444401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40547838034861198099259201 30410878526145898574444401)
              ·
                refine ⟨22808158894609423930833301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30410878526145898574444401 22808158894609423930833301)
                ·
                  refine ⟨1069132448184816746757811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22808158894609423930833301 1069132448184816746757811)
                  ·
                    refine ⟨1603698672277225120136717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1069132448184816746757811 1603698672277225120136717)
                    ·
                      refine ⟨601387002103959420051269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1603698672277225120136717 601387002103959420051269)
                      ·
                        rfl

theorem cell23_1171197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_1171197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171197 prefixEnd_1171197 := by exact prefixLift 1171197
  have htrace : WordTrace (prefixWord ++ tailWord_1171197) baseStart_1171197 baseEnd_1171197 := by
    simpa [prefixWord, tailWord_1171197, baseEnd_1171197] using wordTrace_append hprefix tailTrace_1171197
  have hstable : (prefixWord ++ tailWord_1171197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171197).length < 2 ^ (prefixWord ++ tailWord_1171197).sum := by decide
  have hdescent : baseEnd_1171197 < baseStart_1171197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171198 : List Nat := [4, 2, 2, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_1171198 : Nat := 118140960795 + 1171198 * 2 ^ 59
def prefixEnd_1171198 : Nat := 4983230072969 + 3 ^ 40 * 1171198 * 2
def baseEnd_1171198 : Nat := 601387515584613916138765

theorem tailTrace_1171198 : CollatzResearch.WordTrace tailWord_1171198 prefixEnd_1171198 601387515584613916138765 := by
  unfold tailWord_1171198
  simp only [CollatzResearch.WordTrace]
  refine ⟨5339637551369643192341281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28478066940638097025820165 5339637551369643192341281)
  ·
    refine ⟨4004728163527232394255961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5339637551369643192341281 4004728163527232394255961)
    ·
      refine ⟨3003546122645424295691971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4004728163527232394255961 3003546122645424295691971)
      ·
        refine ⟨4505319183968136443537957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3003546122645424295691971 4505319183968136443537957)
        ·
          refine ⟨844747346994025583163367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4505319183968136443537957 844747346994025583163367)
          ·
            refine ⟨1267121020491038374745051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844747346994025583163367 1267121020491038374745051)
            ·
              refine ⟨1900681530736557562117577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267121020491038374745051 1900681530736557562117577)
              ·
                refine ⟨1425511148052418171588183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1900681530736557562117577 1425511148052418171588183)
                ·
                  refine ⟨2138266722078627257382275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1425511148052418171588183 2138266722078627257382275)
                  ·
                    refine ⟨3207400083117940886073413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2138266722078627257382275 3207400083117940886073413)
                    ·
                      refine ⟨601387515584613916138765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3207400083117940886073413 601387515584613916138765)
                      ·
                        rfl

theorem cell23_1171198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_1171198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171198 prefixEnd_1171198 := by exact prefixLift 1171198
  have htrace : WordTrace (prefixWord ++ tailWord_1171198) baseStart_1171198 baseEnd_1171198 := by
    simpa [prefixWord, tailWord_1171198, baseEnd_1171198] using wordTrace_append hprefix tailTrace_1171198
  have hstable : (prefixWord ++ tailWord_1171198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171198).length < 2 ^ (prefixWord ++ tailWord_1171198).sum := by decide
  have hdescent : baseEnd_1171198 < baseStart_1171198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171218 : List Nat := [3, 2, 4, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_1171218 : Nat := 118140960795 + 1171218 * 2 ^ 59
def prefixEnd_1171218 : Nat := 4983230072969 + 3 ^ 40 * 1171218 * 2
def baseEnd_1171218 : Nat := 601397785197703837888673

theorem tailTrace_1171218 : CollatzResearch.WordTrace tailWord_1171218 prefixEnd_1171218 601397785197703837888673 := by
  unfold tailWord_1171218
  simp only [CollatzResearch.WordTrace]
  refine ⟨10679457467721172238614577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28478553247256459302972205 10679457467721172238614577)
  ·
    refine ⟨8009593100790879178960933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10679457467721172238614577 8009593100790879178960933)
    ·
      refine ⟨1501798706398289846055175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8009593100790879178960933 1501798706398289846055175)
      ·
        refine ⟨2252698059597434769082763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1501798706398289846055175 2252698059597434769082763)
        ·
          refine ⟨3379047089396152153624145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2252698059597434769082763 3379047089396152153624145)
          ·
            refine ⟨2534285317047114115218109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3379047089396152153624145 2534285317047114115218109)
            ·
              refine ⟨950356993892667793206791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2534285317047114115218109 950356993892667793206791)
              ·
                refine ⟨1425535490839001689810187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950356993892667793206791 1425535490839001689810187)
                ·
                  refine ⟨2138303236258502534715281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1425535490839001689810187 2138303236258502534715281)
                  ·
                    refine ⟨1603727427193876901036461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2138303236258502534715281 1603727427193876901036461)
                    ·
                      refine ⟨601397785197703837888673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1603727427193876901036461 601397785197703837888673)
                      ·
                        rfl

theorem cell23_1171218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_1171218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171218 prefixEnd_1171218 := by exact prefixLift 1171218
  have htrace : WordTrace (prefixWord ++ tailWord_1171218) baseStart_1171218 baseEnd_1171218 := by
    simpa [prefixWord, tailWord_1171218, baseEnd_1171218] using wordTrace_append hprefix tailTrace_1171218
  have hstable : (prefixWord ++ tailWord_1171218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171218).length < 2 ^ (prefixWord ++ tailWord_1171218).sum := by decide
  have hdescent : baseEnd_1171218 < baseStart_1171218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171224 : List Nat := [2, 1, 2, 3, 1, 1, 2, 5, 1, 3, 2]
def baseStart_1171224 : Nat := 118140960795 + 1171224 * 2 ^ 59
def prefixEnd_1171224 : Nat := 4983230072969 + 3 ^ 40 * 1171224 * 2
def baseEnd_1171224 : Nat := 601400866081630814413645

theorem tailTrace_1171224 : CollatzResearch.WordTrace tailWord_1171224 prefixEnd_1171224 601400866081630814413645 := by
  unfold tailWord_1171224
  simp only [CollatzResearch.WordTrace]
  refine ⟨21359024354431475989588363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28478699139241967986117817 21359024354431475989588363)
  ·
    refine ⟨32038536531647213984382545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21359024354431475989588363 32038536531647213984382545)
    ·
      refine ⟨24028902398735410488286909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32038536531647213984382545 24028902398735410488286909)
      ·
        refine ⟨9010838399525778933107591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24028902398735410488286909 9010838399525778933107591)
        ·
          refine ⟨13516257599288668399661387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9010838399525778933107591 13516257599288668399661387)
          ·
            refine ⟨20274386398933002599492081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13516257599288668399661387 20274386398933002599492081)
            ·
              refine ⟨15205789799199751949619061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20274386398933002599492081 15205789799199751949619061)
              ·
                refine ⟨1425542793674976745276787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15205789799199751949619061 1425542793674976745276787)
                ·
                  refine ⟨2138314190512465117915181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1425542793674976745276787 2138314190512465117915181)
                  ·
                    refine ⟨801867821442174419218193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2138314190512465117915181 801867821442174419218193)
                    ·
                      refine ⟨601400866081630814413645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 801867821442174419218193 601400866081630814413645)
                      ·
                        rfl

theorem cell23_1171224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_1171224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171224 prefixEnd_1171224 := by exact prefixLift 1171224
  have htrace : WordTrace (prefixWord ++ tailWord_1171224) baseStart_1171224 baseEnd_1171224 := by
    simpa [prefixWord, tailWord_1171224, baseEnd_1171224] using wordTrace_append hprefix tailTrace_1171224
  have hstable : (prefixWord ++ tailWord_1171224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171224).length < 2 ^ (prefixWord ++ tailWord_1171224).sum := by decide
  have hdescent : baseEnd_1171224 < baseStart_1171224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171260 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 9]
def baseStart_1171260 : Nat := 118140960795 + 1171260 * 2 ^ 59
def prefixEnd_1171260 : Nat := 4983230072969 + 3 ^ 40 * 1171260 * 2
def baseEnd_1171260 : Nat := 66824372376132519284831

theorem tailTrace_1171260 : CollatzResearch.WordTrace tailWord_1171260 prefixEnd_1171260 66824372376132519284831 := by
  unfold tailWord_1171260
  simp only [CollatzResearch.WordTrace]
  refine ⟨21359680868366265063743617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28479574491155020084991489 21359680868366265063743617)
  ·
    refine ⟨16019760651274698797807713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21359680868366265063743617 16019760651274698797807713)
    ·
      refine ⟨12014820488456024098355785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16019760651274698797807713 12014820488456024098355785)
      ·
        refine ⟨9011115366342018073766839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12014820488456024098355785 9011115366342018073766839)
        ·
          refine ⟨13516673049513027110650259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9011115366342018073766839 13516673049513027110650259)
          ·
            refine ⟨20275009574269540665975389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13516673049513027110650259 20275009574269540665975389)
            ·
              refine ⟨7603128590351077749740771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20275009574269540665975389 7603128590351077749740771)
              ·
                refine ⟨11404692885526616624611157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7603128590351077749740771 11404692885526616624611157)
                ·
                  refine ⟨66824372376132519284831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11404692885526616624611157 66824372376132519284831)
                  ·
                    rfl

theorem cell23_1171260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 9].length) (baseStart_1171260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171260 prefixEnd_1171260 := by exact prefixLift 1171260
  have htrace : WordTrace (prefixWord ++ tailWord_1171260) baseStart_1171260 baseEnd_1171260 := by
    simpa [prefixWord, tailWord_1171260, baseEnd_1171260] using wordTrace_append hprefix tailTrace_1171260
  have hstable : (prefixWord ++ tailWord_1171260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171260).length < 2 ^ (prefixWord ++ tailWord_1171260).sum := by decide
  have hdescent : baseEnd_1171260 < baseStart_1171260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171327 : List Nat := [1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 4]
def baseStart_1171327 : Nat := 118140960795 + 1171327 * 2 ^ 59
def prefixEnd_1171327 : Nat := 4983230072969 + 3 ^ 40 * 1171327 * 2
def baseEnd_1171327 : Nat := 601453754589043911425671

theorem tailTrace_1171327 : CollatzResearch.WordTrace tailWord_1171327 prefixEnd_1171327 601453754589043911425671 := by
  unfold tailWord_1171327
  simp only [CollatzResearch.WordTrace]
  refine ⟨42721805427489800570176235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28481203618326533713450823 42721805427489800570176235)
  ·
    refine ⟨64082708141234700855264353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42721805427489800570176235 64082708141234700855264353)
    ·
      refine ⟨48062031105926025641448265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64082708141234700855264353 48062031105926025641448265)
      ·
        refine ⟨36046523329444519231086199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48062031105926025641448265 36046523329444519231086199)
        ·
          refine ⟨54069784994166778846629299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36046523329444519231086199 54069784994166778846629299)
          ·
            refine ⟨81104677491250168269943949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54069784994166778846629299 81104677491250168269943949)
            ·
              refine ⟨30414254059218813101228981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81104677491250168269943949 30414254059218813101228981)
              ·
                refine ⟨2851336318051763728240217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30414254059218813101228981 2851336318051763728240217)
                ·
                  refine ⟨2138502238538822796180163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2851336318051763728240217 2138502238538822796180163)
                  ·
                    refine ⟨3207753357808234194270245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2138502238538822796180163 3207753357808234194270245)
                    ·
                      refine ⟨601453754589043911425671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3207753357808234194270245 601453754589043911425671)
                      ·
                        rfl

theorem cell23_1171327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_1171327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171327 prefixEnd_1171327 := by exact prefixLift 1171327
  have htrace : WordTrace (prefixWord ++ tailWord_1171327) baseStart_1171327 baseEnd_1171327 := by
    simpa [prefixWord, tailWord_1171327, baseEnd_1171327] using wordTrace_append hprefix tailTrace_1171327
  have hstable : (prefixWord ++ tailWord_1171327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171327).length < 2 ^ (prefixWord ++ tailWord_1171327).sum := by decide
  have hdescent : baseEnd_1171327 < baseStart_1171327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171381 : List Nat := [1, 3, 3, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_1171381 : Nat := 118140960795 + 1171381 * 2 ^ 59
def prefixEnd_1171381 : Nat := 4983230072969 + 3 ^ 40 * 1171381 * 2
def baseEnd_1171381 : Nat := 601481482544386700150423

theorem tailTrace_1171381 : CollatzResearch.WordTrace tailWord_1171381 prefixEnd_1171381 601481482544386700150423 := by
  unfold tailWord_1171381
  simp only [CollatzResearch.WordTrace]
  refine ⟨42723774969294167792641997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28482516646196111861761331 42723774969294167792641997)
  ·
    refine ⟨16021415613485312922240749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42723774969294167792641997 16021415613485312922240749)
    ·
      refine ⟨6008030855056992345840281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16021415613485312922240749 6008030855056992345840281)
      ·
        refine ⟨4506023141292744259380211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6008030855056992345840281 4506023141292744259380211)
        ·
          refine ⟨6759034711939116389070317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4506023141292744259380211 6759034711939116389070317)
          ·
            refine ⟨2534638016977168645901369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6759034711939116389070317 2534638016977168645901369)
            ·
              refine ⟨1900978512732876484426027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2534638016977168645901369 1900978512732876484426027)
              ·
                refine ⟨2851467769099314726639041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1900978512732876484426027 2851467769099314726639041)
                ·
                  refine ⟨2138600826824486044979281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2851467769099314726639041 2138600826824486044979281)
                  ·
                    refine ⟨1603950620118364533734461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2138600826824486044979281 1603950620118364533734461)
                    ·
                      refine ⟨601481482544386700150423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1603950620118364533734461 601481482544386700150423)
                      ·
                        rfl

theorem cell23_1171381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_1171381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171381 prefixEnd_1171381 := by exact prefixLift 1171381
  have htrace : WordTrace (prefixWord ++ tailWord_1171381) baseStart_1171381 baseEnd_1171381 := by
    simpa [prefixWord, tailWord_1171381, baseEnd_1171381] using wordTrace_append hprefix tailTrace_1171381
  have hstable : (prefixWord ++ tailWord_1171381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171381).length < 2 ^ (prefixWord ++ tailWord_1171381).sum := by decide
  have hdescent : baseEnd_1171381 < baseStart_1171381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171434 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_1171434 : Nat := 118140960795 + 1171434 * 2 ^ 59
def prefixEnd_1171434 : Nat := 4983230072969 + 3 ^ 40 * 1171434 * 2
def baseEnd_1171434 : Nat := 601508697019074992787679

theorem tailTrace_1171434 : CollatzResearch.WordTrace tailWord_1171434 prefixEnd_1171434 601508697019074992787679 := by
  unfold tailWord_1171434
  simp only [CollatzResearch.WordTrace]
  refine ⟨10681427009525539461080339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28483805358734771896214237 10681427009525539461080339)
  ·
    refine ⟨16022140514288309191620509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10681427009525539461080339 16022140514288309191620509)
    ·
      refine ⟨6008302692858115946857691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16022140514288309191620509 6008302692858115946857691)
      ·
        refine ⟨9012454039287173920286537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6008302692858115946857691 9012454039287173920286537)
        ·
          refine ⟨6759340529465380440214903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9012454039287173920286537 6759340529465380440214903)
          ·
            refine ⟨10139010794198070660322355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6759340529465380440214903 10139010794198070660322355)
            ·
              refine ⟨15208516191297105990483533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10139010794198070660322355 15208516191297105990483533)
              ·
                refine ⟨5703193571736414746431325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15208516191297105990483533 5703193571736414746431325)
                ·
                  refine ⟨2138697589401155529911747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5703193571736414746431325 2138697589401155529911747)
                  ·
                    refine ⟨3208046384101733294867621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2138697589401155529911747 3208046384101733294867621)
                    ·
                      refine ⟨601508697019074992787679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3208046384101733294867621 601508697019074992787679)
                      ·
                        rfl

theorem cell23_1171434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_1171434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171434 prefixEnd_1171434 := by exact prefixLift 1171434
  have htrace : WordTrace (prefixWord ++ tailWord_1171434) baseStart_1171434 baseEnd_1171434 := by
    simpa [prefixWord, tailWord_1171434, baseEnd_1171434] using wordTrace_append hprefix tailTrace_1171434
  have hstable : (prefixWord ++ tailWord_1171434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171434).length < 2 ^ (prefixWord ++ tailWord_1171434).sum := by decide
  have hdescent : baseEnd_1171434 < baseStart_1171434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171438 : List Nat := [4, 1, 2, 1, 3, 1, 3, 1, 2, 3, 2]
def baseStart_1171438 : Nat := 118140960795 + 1171438 * 2 ^ 59
def prefixEnd_1171438 : Nat := 4983230072969 + 3 ^ 40 * 1171438 * 2
def baseEnd_1171438 : Nat := 601510750941692977137661

theorem tailTrace_1171438 : CollatzResearch.WordTrace tailWord_1171438 prefixEnd_1171438 601510750941692977137661 := by
  unfold tailWord_1171438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5340731741260958315933371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28483902620058444351644645 5340731741260958315933371)
  ·
    refine ⟨8011097611891437473900057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5340731741260958315933371 8011097611891437473900057)
    ·
      refine ⟨6008323208918578105425043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8011097611891437473900057 6008323208918578105425043)
      ·
        refine ⟨9012484813377867158137565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6008323208918578105425043 9012484813377867158137565)
        ·
          refine ⟨3379681805016700184301587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9012484813377867158137565 3379681805016700184301587)
          ·
            refine ⟨5069522707525050276452381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3379681805016700184301587 5069522707525050276452381)
            ·
              refine ⟨1901071015321893853669643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5069522707525050276452381 1901071015321893853669643)
              ·
                refine ⟨2851606522982840780504465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1901071015321893853669643 2851606522982840780504465)
                ·
                  refine ⟨2138704892237130585378349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2851606522982840780504465 2138704892237130585378349)
                  ·
                    refine ⟨802014334588923969516881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2138704892237130585378349 802014334588923969516881)
                    ·
                      refine ⟨601510750941692977137661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 802014334588923969516881 601510750941692977137661)
                      ·
                        rfl

theorem cell23_1171438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_1171438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171438 prefixEnd_1171438 := by exact prefixLift 1171438
  have htrace : WordTrace (prefixWord ++ tailWord_1171438) baseStart_1171438 baseEnd_1171438 := by
    simpa [prefixWord, tailWord_1171438, baseEnd_1171438] using wordTrace_append hprefix tailTrace_1171438
  have hstable : (prefixWord ++ tailWord_1171438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171438).length < 2 ^ (prefixWord ++ tailWord_1171438).sum := by decide
  have hdescent : baseEnd_1171438 < baseStart_1171438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171451 : List Nat := [1, 1, 1, 1, 1, 3, 8, 1, 1, 1, 4]
def baseStart_1171451 : Nat := 118140960795 + 1171451 * 2 ^ 59
def prefixEnd_1171451 : Nat := 4983230072969 + 3 ^ 40 * 1171451 * 2
def baseEnd_1171451 : Nat := 601517426190201426275101

theorem tailTrace_1171451 : CollatzResearch.WordTrace tailWord_1171451 prefixEnd_1171451 601517426190201426275101 := by
  unfold tailWord_1171451
  simp only [CollatzResearch.WordTrace]
  refine ⟨42726328079040569747690207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28484218719360379831793471 42726328079040569747690207)
  ·
    refine ⟨64089492118560854621535311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42726328079040569747690207 64089492118560854621535311)
    ·
      refine ⟨96134238177841281932302967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64089492118560854621535311 96134238177841281932302967)
      ·
        refine ⟨144201357266761922898454451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96134238177841281932302967 144201357266761922898454451)
        ·
          refine ⟨216302035900142884347681677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144201357266761922898454451 216302035900142884347681677)
          ·
            refine ⟨81113263462553581630380629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 216302035900142884347681677 81113263462553581630380629)
            ·
              refine ⟨950546056201799784731023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 81113263462553581630380629 950546056201799784731023)
              ·
                refine ⟨1425819084302699677096535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950546056201799784731023 1425819084302699677096535)
                ·
                  refine ⟨2138728626454049515644803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1425819084302699677096535 2138728626454049515644803)
                  ·
                    refine ⟨3208092939681074273467205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2138728626454049515644803 3208092939681074273467205)
                    ·
                      refine ⟨601517426190201426275101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3208092939681074273467205 601517426190201426275101)
                      ·
                        rfl

theorem cell23_1171451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 1, 1, 4].length) (baseStart_1171451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171451 prefixEnd_1171451 := by exact prefixLift 1171451
  have htrace : WordTrace (prefixWord ++ tailWord_1171451) baseStart_1171451 baseEnd_1171451 := by
    simpa [prefixWord, tailWord_1171451, baseEnd_1171451] using wordTrace_append hprefix tailTrace_1171451
  have hstable : (prefixWord ++ tailWord_1171451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171451).length < 2 ^ (prefixWord ++ tailWord_1171451).sum := by decide
  have hdescent : baseEnd_1171451 < baseStart_1171451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171457 : List Nat := [1, 2, 4, 1, 2, 1, 12]
def baseStart_1171457 : Nat := 118140960795 + 1171457 * 2 ^ 59
def prefixEnd_1171457 : Nat := 4983230072969 + 3 ^ 40 * 1171457 * 2
def baseEnd_1171457 : Nat := 7426179099680597565433

theorem tailTrace_1171457 : CollatzResearch.WordTrace tailWord_1171457 prefixEnd_1171457 7426179099680597565433 := by
  unfold tailWord_1171457
  simp only [CollatzResearch.WordTrace]
  refine ⟨42726546917018832772408625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28484364611345888514939083 42726546917018832772408625)
  ·
    refine ⟨32044910187764124579306469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42726546917018832772408625 32044910187764124579306469)
    ·
      refine ⟨6008420660205773358619963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32044910187764124579306469 6008420660205773358619963)
      ·
        refine ⟨9012630990308660037929945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6008420660205773358619963 9012630990308660037929945)
        ·
          refine ⟨6759473242731495028447459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9012630990308660037929945 6759473242731495028447459)
          ·
            refine ⟨10139209864097242542671189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6759473242731495028447459 10139209864097242542671189)
            ·
              refine ⟨7426179099680597565433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 10139209864097242542671189 7426179099680597565433)
              ·
                rfl

theorem cell23_1171457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 12].length) (baseStart_1171457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171457 prefixEnd_1171457 := by exact prefixLift 1171457
  have htrace : WordTrace (prefixWord ++ tailWord_1171457) baseStart_1171457 baseEnd_1171457 := by
    simpa [prefixWord, tailWord_1171457, baseEnd_1171457] using wordTrace_append hprefix tailTrace_1171457
  have hstable : (prefixWord ++ tailWord_1171457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171457).length < 2 ^ (prefixWord ++ tailWord_1171457).sum := by decide
  have hdescent : baseEnd_1171457 < baseStart_1171457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171461 : List Nat := [1, 3, 1, 1, 2, 4, 3, 2, 2, 4]
def baseStart_1171461 : Nat := 118140960795 + 1171461 * 2 ^ 59
def prefixEnd_1171461 : Nat := 4983230072969 + 3 ^ 40 * 1171461 * 2
def baseEnd_1171461 : Nat := 200507520332248795716685

theorem tailTrace_1171461 : CollatzResearch.WordTrace tailWord_1171461 prefixEnd_1171461 200507520332248795716685 := by
  unfold tailWord_1171461
  simp only [CollatzResearch.WordTrace]
  refine ⟨42726692809004341455554237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28484461872669560970369491 42726692809004341455554237)
  ·
    refine ⟨16022509803376628045832839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42726692809004341455554237 16022509803376628045832839)
    ·
      refine ⟨24033764705064942068749259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16022509803376628045832839 24033764705064942068749259)
      ·
        refine ⟨36050647057597413103123889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24033764705064942068749259 36050647057597413103123889)
        ·
          refine ⟨27037985293198059827342917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36050647057597413103123889 27037985293198059827342917)
          ·
            refine ⟨5069622242474636217626797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27037985293198059827342917 5069622242474636217626797)
            ·
              refine ⟨1901108340927988581610049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5069622242474636217626797 1901108340927988581610049)
              ·
                refine ⟨1425831255695991436207537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1901108340927988581610049 1425831255695991436207537)
                ·
                  refine ⟨1069373441771993577155653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1425831255695991436207537 1069373441771993577155653)
                  ·
                    refine ⟨200507520332248795716685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1069373441771993577155653 200507520332248795716685)
                    ·
                      rfl

theorem cell23_1171461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 4].length) (baseStart_1171461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171461 prefixEnd_1171461 := by exact prefixLift 1171461
  have htrace : WordTrace (prefixWord ++ tailWord_1171461) baseStart_1171461 baseEnd_1171461 := by
    simpa [prefixWord, tailWord_1171461, baseEnd_1171461] using wordTrace_append hprefix tailTrace_1171461
  have hstable : (prefixWord ++ tailWord_1171461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171461).length < 2 ^ (prefixWord ++ tailWord_1171461).sum := by decide
  have hdescent : baseEnd_1171461 < baseStart_1171461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171468 : List Nat := [2, 2, 1, 2, 3, 1, 4, 1, 3, 2, 2]
def baseStart_1171468 : Nat := 118140960795 + 1171468 * 2 ^ 59
def prefixEnd_1171468 : Nat := 4983230072969 + 3 ^ 40 * 1171468 * 2
def baseEnd_1171468 : Nat := 601526155361327859762523

theorem tailTrace_1171468 : CollatzResearch.WordTrace tailWord_1171468 prefixEnd_1171468 601526155361327859762523 := by
  unfold tailWord_1171468
  simp only [CollatzResearch.WordTrace]
  refine ⟨21363474059989490825529529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28484632079985987767372705 21363474059989490825529529)
  ·
    refine ⟨16022605544992118119147147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21363474059989490825529529 16022605544992118119147147)
    ·
      refine ⟨24033908317488177178720721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16022605544992118119147147 24033908317488177178720721)
      ·
        refine ⟨18025431238116132884040541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24033908317488177178720721 18025431238116132884040541)
        ·
          refine ⟨6759536714293549831515203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18025431238116132884040541 6759536714293549831515203)
          ·
            refine ⟨10139305071440324747272805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6759536714293549831515203 10139305071440324747272805)
            ·
              refine ⟨1901119700895060890113651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10139305071440324747272805 1901119700895060890113651)
              ·
                refine ⟨2851679551342591335170477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1901119700895060890113651 2851679551342591335170477)
                ·
                  refine ⟨1069379831753471750688929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2851679551342591335170477 1069379831753471750688929)
                  ·
                    refine ⟨802034873815103813016697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1069379831753471750688929 802034873815103813016697)
                    ·
                      refine ⟨601526155361327859762523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 802034873815103813016697 601526155361327859762523)
                      ·
                        rfl

theorem cell23_1171468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_1171468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171468 prefixEnd_1171468 := by exact prefixLift 1171468
  have htrace : WordTrace (prefixWord ++ tailWord_1171468) baseStart_1171468 baseEnd_1171468 := by
    simpa [prefixWord, tailWord_1171468, baseEnd_1171468] using wordTrace_append hprefix tailTrace_1171468
  have hstable : (prefixWord ++ tailWord_1171468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171468).length < 2 ^ (prefixWord ++ tailWord_1171468).sum := by decide
  have hdescent : baseEnd_1171468 < baseStart_1171468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171502 : List Nat := [4, 1, 3, 1, 1, 2, 3, 3, 1, 2, 2]
def baseStart_1171502 : Nat := 118140960795 + 1171502 * 2 ^ 59
def prefixEnd_1171502 : Nat := 4983230072969 + 3 ^ 40 * 1171502 * 2
def baseEnd_1171502 : Nat := 601543613703580726737367

theorem tailTrace_1171502 : CollatzResearch.WordTrace tailWord_1171502 prefixEnd_1171502 601543613703580726737367 := by
  unfold tailWord_1171502
  simp only [CollatzResearch.WordTrace]
  refine ⟨5341023525231975682224595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28485458801237203638531173 5341023525231975682224595)
  ·
    refine ⟨8011535287847963523336893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5341023525231975682224595 8011535287847963523336893)
    ·
      refine ⟨3004325732942986321251335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8011535287847963523336893 3004325732942986321251335)
      ·
        refine ⟨4506488599414479481877003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3004325732942986321251335 4506488599414479481877003)
        ·
          refine ⟨6759732899121719222815505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4506488599414479481877003 6759732899121719222815505)
          ·
            refine ⟨5069799674341289417111629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6759732899121719222815505 5069799674341289417111629)
            ·
              refine ⟨1901174877877983531416861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5069799674341289417111629 1901174877877983531416861)
              ·
                refine ⟨712940579204243824281323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1901174877877983531416861 712940579204243824281323)
                ·
                  refine ⟨1069410868806365736421985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 712940579204243824281323 1069410868806365736421985)
                  ·
                    refine ⟨802058151604774302316489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1069410868806365736421985 802058151604774302316489)
                    ·
                      refine ⟨601543613703580726737367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 802058151604774302316489 601543613703580726737367)
                      ·
                        rfl

theorem cell23_1171502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_1171502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171502 prefixEnd_1171502 := by exact prefixLift 1171502
  have htrace : WordTrace (prefixWord ++ tailWord_1171502) baseStart_1171502 baseEnd_1171502 := by
    simpa [prefixWord, tailWord_1171502, baseEnd_1171502] using wordTrace_append hprefix tailTrace_1171502
  have hstable : (prefixWord ++ tailWord_1171502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171502).length < 2 ^ (prefixWord ++ tailWord_1171502).sum := by decide
  have hdescent : baseEnd_1171502 < baseStart_1171502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171508 : List Nat := [2, 5, 1, 2, 3, 1, 9]
def baseStart_1171508 : Nat := 118140960795 + 1171508 * 2 ^ 59
def prefixEnd_1171508 : Nat := 4983230072969 + 3 ^ 40 * 1171508 * 2
def baseEnd_1171508 : Nat := 7426502402314909916819

theorem tailTrace_1171508 : CollatzResearch.WordTrace tailWord_1171508 prefixEnd_1171508 7426502402314909916819 := by
  unfold tailWord_1171508
  simp only [CollatzResearch.WordTrace]
  refine ⟨21364203519917034241257589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28485604693222712321676785 21364203519917034241257589)
  ·
    refine ⟨2002894079992221960117899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21364203519917034241257589 2002894079992221960117899)
    ·
      refine ⟨3004341119988332940176849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2002894079992221960117899 3004341119988332940176849)
      ·
        refine ⟨2253255839991249705132637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3004341119988332940176849 2253255839991249705132637)
        ·
          refine ⟨844970939996718639424739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2253255839991249705132637 844970939996718639424739)
          ·
            refine ⟨1267456409995077959137109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844970939996718639424739 1267456409995077959137109)
            ·
              refine ⟨7426502402314909916819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1267456409995077959137109 7426502402314909916819)
              ·
                rfl

theorem cell23_1171508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 9].length) (baseStart_1171508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171508 prefixEnd_1171508 := by exact prefixLift 1171508
  have htrace : WordTrace (prefixWord ++ tailWord_1171508) baseStart_1171508 baseEnd_1171508 := by
    simpa [prefixWord, tailWord_1171508, baseEnd_1171508] using wordTrace_append hprefix tailTrace_1171508
  have hstable : (prefixWord ++ tailWord_1171508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171508).length < 2 ^ (prefixWord ++ tailWord_1171508).sum := by decide
  have hdescent : baseEnd_1171508 < baseStart_1171508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171544 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 2, 1, 5]
def baseStart_1171544 : Nat := 118140960795 + 1171544 * 2 ^ 59
def prefixEnd_1171544 : Nat := 4983230072969 + 3 ^ 40 * 1171544 * 2
def baseEnd_1171544 : Nat := 601565179891069562412173

theorem tailTrace_1171544 : CollatzResearch.WordTrace tailWord_1171544 prefixEnd_1171544 601565179891069562412173 := by
  unfold tailWord_1171544
  simp only [CollatzResearch.WordTrace]
  refine ⟨21364860033851823315412843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28486480045135764420550457 21364860033851823315412843)
  ·
    refine ⟨32047290050777734973119265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21364860033851823315412843 32047290050777734973119265)
    ·
      refine ⟨24035467538083301229839449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32047290050777734973119265 24035467538083301229839449)
      ·
        refine ⟨18026600653562475922379587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24035467538083301229839449 18026600653562475922379587)
        ·
          refine ⟨27039900980343713883569381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18026600653562475922379587 27039900980343713883569381)
          ·
            refine ⟨5069981433814446353169259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27039900980343713883569381 5069981433814446353169259)
            ·
              refine ⟨7604972150721669529753889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5069981433814446353169259 7604972150721669529753889)
              ·
                refine ⟨5703729113041252147315417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7604972150721669529753889 5703729113041252147315417)
                ·
                  refine ⟨4277796834780939110486563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5703729113041252147315417 4277796834780939110486563)
                  ·
                    refine ⟨6416695252171408665729845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4277796834780939110486563 6416695252171408665729845)
                    ·
                      refine ⟨601565179891069562412173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6416695252171408665729845 601565179891069562412173)
                      ·
                        rfl

theorem cell23_1171544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_1171544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171544 prefixEnd_1171544 := by exact prefixLift 1171544
  have htrace : WordTrace (prefixWord ++ tailWord_1171544) baseStart_1171544 baseEnd_1171544 := by
    simpa [prefixWord, tailWord_1171544, baseEnd_1171544] using wordTrace_append hprefix tailTrace_1171544
  have hstable : (prefixWord ++ tailWord_1171544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171544).length < 2 ^ (prefixWord ++ tailWord_1171544).sum := by decide
  have hdescent : baseEnd_1171544 < baseStart_1171544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171562 : List Nat := [3, 1, 3, 2, 3, 1, 3, 1, 1, 3, 2]
def baseStart_1171562 : Nat := 118140960795 + 1171562 * 2 ^ 59
def prefixEnd_1171562 : Nat := 4983230072969 + 3 ^ 40 * 1171562 * 2
def baseEnd_1171562 : Nat := 601574422542850491987091

theorem tailTrace_1171562 : CollatzResearch.WordTrace tailWord_1171562 prefixEnd_1171562 601574422542850491987091 := by
  unfold tailWord_1171562
  simp only [CollatzResearch.WordTrace]
  refine ⟨10682594145409608926245235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28486917721092290469987293 10682594145409608926245235)
  ·
    refine ⟨16023891218114413389367853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10682594145409608926245235 16023891218114413389367853)
    ·
      refine ⟨6008959206792905021012945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16023891218114413389367853 6008959206792905021012945)
      ·
        refine ⟨4506719405094678765759709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6008959206792905021012945 4506719405094678765759709)
        ·
          refine ⟨1690019776910504537159891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4506719405094678765759709 1690019776910504537159891)
          ·
            refine ⟨2535029665365756805739837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1690019776910504537159891 2535029665365756805739837)
            ·
              refine ⟨950636124512158802152439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2535029665365756805739837 950636124512158802152439)
              ·
                refine ⟨1425954186768238203228659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950636124512158802152439 1425954186768238203228659)
                ·
                  refine ⟨2138931280152357304842989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1425954186768238203228659 2138931280152357304842989)
                  ·
                    refine ⟨802099230057133989316121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2138931280152357304842989 802099230057133989316121)
                    ·
                      refine ⟨601574422542850491987091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 802099230057133989316121 601574422542850491987091)
                      ·
                        rfl

theorem cell23_1171562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_1171562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171562 prefixEnd_1171562 := by exact prefixLift 1171562
  have htrace : WordTrace (prefixWord ++ tailWord_1171562) baseStart_1171562 baseEnd_1171562 := by
    simpa [prefixWord, tailWord_1171562, baseEnd_1171562] using wordTrace_append hprefix tailTrace_1171562
  have hstable : (prefixWord ++ tailWord_1171562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171562).length < 2 ^ (prefixWord ++ tailWord_1171562).sum := by decide
  have hdescent : baseEnd_1171562 < baseStart_1171562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171575 : List Nat := [1, 1, 3, 1, 1, 6, 2, 2, 2, 2, 2]
def baseStart_1171575 : Nat := 118140960795 + 1171575 * 2 ^ 59
def prefixEnd_1171575 : Nat := 4983230072969 + 3 ^ 40 * 1171575 * 2
def baseEnd_1171575 : Nat := 601581097791358941124531

theorem tailTrace_1171575 : CollatzResearch.WordTrace tailWord_1171575 prefixEnd_1171575 601581097791358941124531 := by
  unfold tailWord_1171575
  simp only [CollatzResearch.WordTrace]
  refine ⟨42730850730591338925204179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28487233820394225950136119 42730850730591338925204179)
  ·
    refine ⟨64096276095887008387806269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42730850730591338925204179 64096276095887008387806269)
    ·
      refine ⟨24036103535957628145427351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64096276095887008387806269 24036103535957628145427351)
      ·
        refine ⟨36054155303936442218141027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24036103535957628145427351 36054155303936442218141027)
        ·
          refine ⟨54081232955904663327211541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36054155303936442218141027 54081232955904663327211541)
          ·
            refine ⟨2535057794808031093463041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 54081232955904663327211541 2535057794808031093463041)
            ·
              refine ⟨1901293346106023320097281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2535057794808031093463041 1901293346106023320097281)
              ·
                refine ⟨1425970009579517490072961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1901293346106023320097281 1425970009579517490072961)
                ·
                  refine ⟨1069477507184638117554721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1425970009579517490072961 1069477507184638117554721)
                  ·
                    refine ⟨802108130388478588166041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1069477507184638117554721 802108130388478588166041)
                    ·
                      refine ⟨601581097791358941124531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 802108130388478588166041 601581097791358941124531)
                      ·
                        rfl

theorem cell23_1171575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 2, 2].length) (baseStart_1171575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171575 prefixEnd_1171575 := by exact prefixLift 1171575
  have htrace : WordTrace (prefixWord ++ tailWord_1171575) baseStart_1171575 baseEnd_1171575 := by
    simpa [prefixWord, tailWord_1171575, baseEnd_1171575] using wordTrace_append hprefix tailTrace_1171575
  have hstable : (prefixWord ++ tailWord_1171575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171575).length < 2 ^ (prefixWord ++ tailWord_1171575).sum := by decide
  have hdescent : baseEnd_1171575 < baseStart_1171575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171626 : List Nat := [3, 1, 5, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_1171626 : Nat := 118140960795 + 1171626 * 2 ^ 59
def prefixEnd_1171626 : Nat := 4983230072969 + 3 ^ 40 * 1171626 * 2
def baseEnd_1171626 : Nat := 601607285304738241586797

theorem tailTrace_1171626 : CollatzResearch.WordTrace tailWord_1171626 prefixEnd_1171626 601607285304738241586797 := by
  unfold tailWord_1171626
  simp only [CollatzResearch.WordTrace]
  refine ⟨10683177713351643658827683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28488473902271049756873821 10683177713351643658827683)
  ·
    refine ⟨16024766570027465488241525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10683177713351643658827683 16024766570027465488241525)
    ·
      refine ⟨1502321865940074889522643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16024766570027465488241525 1502321865940074889522643)
      ·
        refine ⟨2253482798910112334283965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1502321865940074889522643 2253482798910112334283965)
        ·
          refine ⟨845056049591292125356487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2253482798910112334283965 845056049591292125356487)
          ·
            refine ⟨1267584074386938188034731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845056049591292125356487 1267584074386938188034731)
            ·
              refine ⟨1901376111580407282052097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267584074386938188034731 1901376111580407282052097)
              ·
                refine ⟨1426032083685305461539073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1901376111580407282052097 1426032083685305461539073)
                ·
                  refine ⟨1069524062763979096154305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1426032083685305461539073 1069524062763979096154305)
                  ·
                    refine ⟨802143047072984322115729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1069524062763979096154305 802143047072984322115729)
                    ·
                      refine ⟨601607285304738241586797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 802143047072984322115729 601607285304738241586797)
                      ·
                        rfl

theorem cell23_1171626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_1171626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171626 prefixEnd_1171626 := by exact prefixLift 1171626
  have htrace : WordTrace (prefixWord ++ tailWord_1171626) baseStart_1171626 baseEnd_1171626 := by
    simpa [prefixWord, tailWord_1171626, baseEnd_1171626] using wordTrace_append hprefix tailTrace_1171626
  have hstable : (prefixWord ++ tailWord_1171626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171626).length < 2 ^ (prefixWord ++ tailWord_1171626).sum := by decide
  have hdescent : baseEnd_1171626 < baseStart_1171626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171648 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 2, 4, 2]
def baseStart_1171648 : Nat := 118140960795 + 1171648 * 2 ^ 59
def prefixEnd_1171648 : Nat := 4983230072969 + 3 ^ 40 * 1171648 * 2
def baseEnd_1171648 : Nat := 601618581879137155511695

theorem tailTrace_1171648 : CollatzResearch.WordTrace tailWord_1171648 prefixEnd_1171648 601618581879137155511695 := by
  unfold tailWord_1171648
  simp only [CollatzResearch.WordTrace]
  refine ⟨21366756629663436196305799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28489008839551248261741065 21366756629663436196305799)
  ·
    refine ⟨32050134944495154294458699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21366756629663436196305799 32050134944495154294458699)
    ·
      refine ⟨48075202416742731441688049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32050134944495154294458699 48075202416742731441688049)
      ·
        refine ⟨36056401812557048581266037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48075202416742731441688049 36056401812557048581266037)
        ·
          refine ⟨3380287669927223304493691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36056401812557048581266037 3380287669927223304493691)
          ·
            refine ⟨5070431504890834956740537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3380287669927223304493691 5070431504890834956740537)
            ·
              refine ⟨3802823628668126217555403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5070431504890834956740537 3802823628668126217555403)
              ·
                refine ⟨5704235443002189326333105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3802823628668126217555403 5704235443002189326333105)
                ·
                  refine ⟨4278176582251641994749829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5704235443002189326333105 4278176582251641994749829)
                  ·
                    refine ⟨802158109172182874015593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4278176582251641994749829 802158109172182874015593)
                    ·
                      refine ⟨601618581879137155511695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 802158109172182874015593 601618581879137155511695)
                      ·
                        rfl

theorem cell23_1171648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 2, 4, 2].length) (baseStart_1171648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171648 prefixEnd_1171648 := by exact prefixLift 1171648
  have htrace : WordTrace (prefixWord ++ tailWord_1171648) baseStart_1171648 baseEnd_1171648 := by
    simpa [prefixWord, tailWord_1171648, baseEnd_1171648] using wordTrace_append hprefix tailTrace_1171648
  have hstable : (prefixWord ++ tailWord_1171648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171648).length < 2 ^ (prefixWord ++ tailWord_1171648).sum := by decide
  have hdescent : baseEnd_1171648 < baseStart_1171648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171731 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 6, 4]
def baseStart_1171731 : Nat := 118140960795 + 1171731 * 2 ^ 59
def prefixEnd_1171731 : Nat := 4983230072969 + 3 ^ 40 * 1171731 * 2
def baseEnd_1171731 : Nat := 200553733591153443591271

theorem tailTrace_1171731 : CollatzResearch.WordTrace tailWord_1171731 prefixEnd_1171731 200553733591153443591271 := by
  unfold tailWord_1171731
  simp only [CollatzResearch.WordTrace]
  refine ⟨42736540518026177567883047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28491027012017451711922031 42736540518026177567883047)
  ·
    refine ⟨64104810777039266351824571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42736540518026177567883047 64104810777039266351824571)
    ·
      refine ⟨96157216165558899527736857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64104810777039266351824571 96157216165558899527736857)
      ·
        refine ⟨72117912124169174645802643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96157216165558899527736857 72117912124169174645802643)
        ·
          refine ⟨108176868186253761968703965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72117912124169174645802643 108176868186253761968703965)
          ·
            refine ⟨40566325569845160738263987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108176868186253761968703965 40566325569845160738263987)
            ·
              refine ⟨60849488354767741107395981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40566325569845160738263987 60849488354767741107395981)
              ·
                refine ⟨22818558133037902915273493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60849488354767741107395981 22818558133037902915273493)
                ·
                  refine ⟨1069619912486151699153445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22818558133037902915273493 1069619912486151699153445)
                  ·
                    refine ⟨200553733591153443591271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1069619912486151699153445 200553733591153443591271)
                    ·
                      rfl

theorem cell23_1171731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 4].length) (baseStart_1171731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171731 prefixEnd_1171731 := by exact prefixLift 1171731
  have htrace : WordTrace (prefixWord ++ tailWord_1171731) baseStart_1171731 baseEnd_1171731 := by
    simpa [prefixWord, tailWord_1171731, baseEnd_1171731] using wordTrace_append hprefix tailTrace_1171731
  have hstable : (prefixWord ++ tailWord_1171731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171731).length < 2 ^ (prefixWord ++ tailWord_1171731).sum := by decide
  have hdescent : baseEnd_1171731 < baseStart_1171731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171735 : List Nat := [1, 1, 3, 4, 1, 3, 3, 1, 1, 5]
def baseStart_1171735 : Nat := 118140960795 + 1171735 * 2 ^ 59
def prefixEnd_1171735 : Nat := 4983230072969 + 3 ^ 40 * 1171735 * 2
def baseEnd_1171735 : Nat := 200554418232026105041265

theorem tailTrace_1171735 : CollatzResearch.WordTrace tailWord_1171735 prefixEnd_1171735 200554418232026105041265 := by
  unfold tailWord_1171735
  simp only [CollatzResearch.WordTrace]
  refine ⟨42736686410011686251028659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28491124273341124167352439 42736686410011686251028659)
  ·
    refine ⟨64105029615017529376542989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42736686410011686251028659 64105029615017529376542989)
    ·
      refine ⟨24039386105631573516203621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64105029615017529376542989 24039386105631573516203621)
      ·
        refine ⟨4507384894805920034288179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24039386105631573516203621 4507384894805920034288179)
        ·
          refine ⟨6761077342208880051432269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4507384894805920034288179 6761077342208880051432269)
          ·
            refine ⟨2535404003328330019287101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6761077342208880051432269 2535404003328330019287101)
            ·
              refine ⟨950776501248123757232663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2535404003328330019287101 950776501248123757232663)
              ·
                refine ⟨1426164751872185635848995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950776501248123757232663 1426164751872185635848995)
                ·
                  refine ⟨2139247127808278453773493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426164751872185635848995 2139247127808278453773493)
                  ·
                    refine ⟨200554418232026105041265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2139247127808278453773493 200554418232026105041265)
                    ·
                      rfl

theorem cell23_1171735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 1, 5].length) (baseStart_1171735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171735 prefixEnd_1171735 := by exact prefixLift 1171735
  have htrace : WordTrace (prefixWord ++ tailWord_1171735) baseStart_1171735 baseEnd_1171735 := by
    simpa [prefixWord, tailWord_1171735, baseEnd_1171735] using wordTrace_append hprefix tailTrace_1171735
  have hstable : (prefixWord ++ tailWord_1171735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171735).length < 2 ^ (prefixWord ++ tailWord_1171735).sum := by decide
  have hdescent : baseEnd_1171735 < baseStart_1171735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171788 : List Nat := [2, 2, 1, 3, 2, 1, 1, 4, 1, 3, 3]
def baseStart_1171788 : Nat := 118140960795 + 1171788 * 2 ^ 59
def prefixEnd_1171788 : Nat := 4983230072969 + 3 ^ 40 * 1171788 * 2
def baseEnd_1171788 : Nat := 601690469170766607761051

theorem tailTrace_1171788 : CollatzResearch.WordTrace tailWord_1171788 prefixEnd_1171788 601690469170766607761051 := by
  unfold tailWord_1171788
  simp only [CollatzResearch.WordTrace]
  refine ⟨21369309739409838151354009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28492412985879784201805345 21369309739409838151354009)
  ·
    refine ⟨16026982304557378613515507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21369309739409838151354009 16026982304557378613515507)
    ·
      refine ⟨24040473456836067920273261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16026982304557378613515507 24040473456836067920273261)
      ·
        refine ⟨9015177546313525470102473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24040473456836067920273261 9015177546313525470102473)
        ·
          refine ⟨6761383159735144102576855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9015177546313525470102473 6761383159735144102576855)
          ·
            refine ⟨10142074739602716153865283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6761383159735144102576855 10142074739602716153865283)
            ·
              refine ⟨15213112109404074230797925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10142074739602716153865283 15213112109404074230797925)
              ·
                refine ⟨2852458520513263918274611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15213112109404074230797925 2852458520513263918274611)
                ·
                  refine ⟨4278687780769895877411917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2852458520513263918274611 4278687780769895877411917)
                  ·
                    refine ⟨1604507917788710954029469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4278687780769895877411917 1604507917788710954029469)
                    ·
                      refine ⟨601690469170766607761051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1604507917788710954029469 601690469170766607761051)
                      ·
                        rfl

theorem cell23_1171788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_1171788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171788 prefixEnd_1171788 := by exact prefixLift 1171788
  have htrace : WordTrace (prefixWord ++ tailWord_1171788) baseStart_1171788 baseEnd_1171788 := by
    simpa [prefixWord, tailWord_1171788, baseEnd_1171788] using wordTrace_append hprefix tailTrace_1171788
  have hstable : (prefixWord ++ tailWord_1171788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171788).length < 2 ^ (prefixWord ++ tailWord_1171788).sum := by decide
  have hdescent : baseEnd_1171788 < baseStart_1171788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171792 : List Nat := [2, 1, 1, 1, 1, 8, 2, 1, 1, 2, 3]
def baseStart_1171792 : Nat := 118140960795 + 1171792 * 2 ^ 59
def prefixEnd_1171792 : Nat := 4983230072969 + 3 ^ 40 * 1171792 * 2
def baseEnd_1171792 : Nat := 601692523093384592111033

theorem tailTrace_1171792 : CollatzResearch.WordTrace tailWord_1171792 prefixEnd_1171792 601692523093384592111033 := by
  unfold tailWord_1171792
  simp only [CollatzResearch.WordTrace]
  refine ⟨21369382685402592492926815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28492510247203456657235753 21369382685402592492926815)
  ·
    refine ⟨32054074028103888739390223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21369382685402592492926815 32054074028103888739390223)
    ·
      refine ⟨48081111042155833109085335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32054074028103888739390223 48081111042155833109085335)
      ·
        refine ⟨72121666563233749663628003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48081111042155833109085335 72121666563233749663628003)
        ·
          refine ⟨108182499844850624495442005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72121666563233749663628003 108182499844850624495442005)
          ·
            refine ⟨1267763670056843255805961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 108182499844850624495442005 1267763670056843255805961)
            ·
              refine ⟨950822752542632441854471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1267763670056843255805961 950822752542632441854471)
              ·
                refine ⟨1426234128813948662781707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950822752542632441854471 1426234128813948662781707)
                ·
                  refine ⟨2139351193220922994172561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426234128813948662781707 2139351193220922994172561)
                  ·
                    refine ⟨1604513394915692245629421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2139351193220922994172561 1604513394915692245629421)
                    ·
                      refine ⟨601692523093384592111033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1604513394915692245629421 601692523093384592111033)
                      ·
                        rfl

theorem cell23_1171792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 1, 2, 3].length) (baseStart_1171792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171792 prefixEnd_1171792 := by exact prefixLift 1171792
  have htrace : WordTrace (prefixWord ++ tailWord_1171792) baseStart_1171792 baseEnd_1171792 := by
    simpa [prefixWord, tailWord_1171792, baseEnd_1171792] using wordTrace_append hprefix tailTrace_1171792
  have hstable : (prefixWord ++ tailWord_1171792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171792).length < 2 ^ (prefixWord ++ tailWord_1171792).sum := by decide
  have hdescent : baseEnd_1171792 < baseStart_1171792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171848 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_1171848 : Nat := 118140960795 + 1171848 * 2 ^ 59
def prefixEnd_1171848 : Nat := 4983230072969 + 3 ^ 40 * 1171848 * 2
def baseEnd_1171848 : Nat := 601721278010036373010775

theorem tailTrace_1171848 : CollatzResearch.WordTrace tailWord_1171848 prefixEnd_1171848 601721278010036373010775 := by
  unfold tailWord_1171848
  simp only [CollatzResearch.WordTrace]
  refine ⟨21370403929301153274946099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28493871905734871033261465 21370403929301153274946099)
  ·
    refine ⟨32055605893951729912419149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21370403929301153274946099 32055605893951729912419149)
    ·
      refine ⟨12020852210231898717157181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32055605893951729912419149 12020852210231898717157181)
      ·
        refine ⟨4507819578836962018933943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12020852210231898717157181 4507819578836962018933943)
        ·
          refine ⟨6761729368255443028400915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4507819578836962018933943 6761729368255443028400915)
          ·
            refine ⟨10142594052383164542601373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6761729368255443028400915 10142594052383164542601373)
            ·
              refine ⟨3803472769643686703475515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10142594052383164542601373 3803472769643686703475515)
              ·
                refine ⟨5705209154465530055213273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3803472769643686703475515 5705209154465530055213273)
                ·
                  refine ⟨4278906865849147541409955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5705209154465530055213273 4278906865849147541409955)
                  ·
                    refine ⟨6418360298773721312114933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4278906865849147541409955 6418360298773721312114933)
                    ·
                      refine ⟨601721278010036373010775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6418360298773721312114933 601721278010036373010775)
                      ·
                        rfl

theorem cell23_1171848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_1171848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171848 prefixEnd_1171848 := by exact prefixLift 1171848
  have htrace : WordTrace (prefixWord ++ tailWord_1171848) baseStart_1171848 baseEnd_1171848 := by
    simpa [prefixWord, tailWord_1171848, baseEnd_1171848] using wordTrace_append hprefix tailTrace_1171848
  have hstable : (prefixWord ++ tailWord_1171848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171848).length < 2 ^ (prefixWord ++ tailWord_1171848).sum := by decide
  have hdescent : baseEnd_1171848 < baseStart_1171848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171861 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_1171861 : Nat := 118140960795 + 1171861 * 2 ^ 59
def prefixEnd_1171861 : Nat := 4983230072969 + 3 ^ 40 * 1171861 * 2
def baseEnd_1171861 : Nat := 601727953258544822148215

theorem tailTrace_1171861 : CollatzResearch.WordTrace tailWord_1171861 prefixEnd_1171861 601727953258544822148215 := by
  unfold tailWord_1171861
  simp only [CollatzResearch.WordTrace]
  refine ⟨42741282007555209770115437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28494188005036806513410291 42741282007555209770115437)
  ·
    refine ⟨16027980752833203663793289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42741282007555209770115437 16027980752833203663793289)
    ·
      refine ⟨12020985564624902747844967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16027980752833203663793289 12020985564624902747844967)
      ·
        refine ⟨18031478346937354121767451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12020985564624902747844967 18031478346937354121767451)
        ·
          refine ⟨27047217520406031182651177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18031478346937354121767451 27047217520406031182651177)
          ·
            refine ⟨20285413140304523386988383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27047217520406031182651177 20285413140304523386988383)
            ·
              refine ⟨30428119710456785080482575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20285413140304523386988383 30428119710456785080482575)
              ·
                refine ⟨45642179565685177620723863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30428119710456785080482575 45642179565685177620723863)
                ·
                  refine ⟨68463269348527766431085795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45642179565685177620723863 68463269348527766431085795)
                  ·
                    refine ⟨102694904022791649646628693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68463269348527766431085795 102694904022791649646628693)
                    ·
                      refine ⟨601727953258544822148215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 102694904022791649646628693 601727953258544822148215)
                      ·
                        rfl

theorem cell23_1171861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_1171861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171861 prefixEnd_1171861 := by exact prefixLift 1171861
  have htrace : WordTrace (prefixWord ++ tailWord_1171861) baseStart_1171861 baseEnd_1171861 := by
    simpa [prefixWord, tailWord_1171861, baseEnd_1171861] using wordTrace_append hprefix tailTrace_1171861
  have hstable : (prefixWord ++ tailWord_1171861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171861).length < 2 ^ (prefixWord ++ tailWord_1171861).sum := by decide
  have hdescent : baseEnd_1171861 < baseStart_1171861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171873 : List Nat := [1, 2, 3, 5, 2, 1, 2, 1, 2, 1, 3]
def baseStart_1171873 : Nat := 118140960795 + 1171873 * 2 ^ 59
def prefixEnd_1171873 : Nat := 4983230072969 + 3 ^ 40 * 1171873 * 2
def baseEnd_1171873 : Nat := 601734115026398775198161

theorem tailTrace_1171873 : CollatzResearch.WordTrace tailWord_1171873 prefixEnd_1171873 601734115026398775198161 := by
  unfold tailWord_1171873
  simp only [CollatzResearch.WordTrace]
  refine ⟨42741719683511735819552273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28494479789007823879701515 42741719683511735819552273)
  ·
    refine ⟨32056289762633801864664205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42741719683511735819552273 32056289762633801864664205)
    ·
      refine ⟨12021108660987675699249077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32056289762633801864664205 12021108660987675699249077)
      ·
        refine ⟨1126978936967594596804601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12021108660987675699249077 1126978936967594596804601)
        ·
          refine ⟨845234202725695947603451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1126978936967594596804601 845234202725695947603451)
          ·
            refine ⟨1267851304088543921405177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845234202725695947603451 1267851304088543921405177)
            ·
              refine ⟨950888478066407941053883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1267851304088543921405177 950888478066407941053883)
              ·
                refine ⟨1426332717099611911580825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950888478066407941053883 1426332717099611911580825)
                ·
                  refine ⟨1069749537824708933685619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1426332717099611911580825 1069749537824708933685619)
                  ·
                    refine ⟨1604624306737063400528429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1069749537824708933685619 1604624306737063400528429)
                    ·
                      refine ⟨601734115026398775198161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1604624306737063400528429 601734115026398775198161)
                      ·
                        rfl

theorem cell23_1171873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_1171873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171873 prefixEnd_1171873 := by exact prefixLift 1171873
  have htrace : WordTrace (prefixWord ++ tailWord_1171873) baseStart_1171873 baseEnd_1171873 := by
    simpa [prefixWord, tailWord_1171873, baseEnd_1171873] using wordTrace_append hprefix tailTrace_1171873
  have hstable : (prefixWord ++ tailWord_1171873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171873).length < 2 ^ (prefixWord ++ tailWord_1171873).sum := by decide
  have hdescent : baseEnd_1171873 < baseStart_1171873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171879 : List Nat := [1, 1, 6, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_1171879 : Nat := 118140960795 + 1171879 * 2 ^ 59
def prefixEnd_1171879 : Nat := 4983230072969 + 3 ^ 40 * 1171879 * 2
def baseEnd_1171879 : Nat := 601737195910325751723133

theorem tailTrace_1171879 : CollatzResearch.WordTrace tailWord_1171879 prefixEnd_1171879 601737195910325751723133 := by
  unfold tailWord_1171879
  simp only [CollatzResearch.WordTrace]
  refine ⟨42741938521489998844270691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28494625680993332562847127 42741938521489998844270691)
  ·
    refine ⟨64112907782234998266406037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42741938521489998844270691 64112907782234998266406037)
    ·
      refine ⟨3005292552292265543737783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 64112907782234998266406037 3005292552292265543737783)
      ·
        refine ⟨4507938828438398315606675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3005292552292265543737783 4507938828438398315606675)
        ·
          refine ⟨6761908242657597473410013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4507938828438398315606675 6761908242657597473410013)
          ·
            refine ⟨2535715590996599052528755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6761908242657597473410013 2535715590996599052528755)
            ·
              refine ⟨3803573386494898578793133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2535715590996599052528755 3803573386494898578793133)
              ·
                refine ⟨1426340019935586967047425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3803573386494898578793133 1426340019935586967047425)
                ·
                  refine ⟨1069755014951690225285569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1426340019935586967047425 1069755014951690225285569)
                  ·
                    refine ⟨802316261213767668964177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1069755014951690225285569 802316261213767668964177)
                    ·
                      refine ⟨601737195910325751723133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 802316261213767668964177 601737195910325751723133)
                      ·
                        rfl

theorem cell23_1171879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_1171879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171879 prefixEnd_1171879 := by exact prefixLift 1171879
  have htrace : WordTrace (prefixWord ++ tailWord_1171879) baseStart_1171879 baseEnd_1171879 := by
    simpa [prefixWord, tailWord_1171879, baseEnd_1171879] using wordTrace_append hprefix tailTrace_1171879
  have hstable : (prefixWord ++ tailWord_1171879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171879).length < 2 ^ (prefixWord ++ tailWord_1171879).sum := by decide
  have hdescent : baseEnd_1171879 < baseStart_1171879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171881 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 3, 7]
def baseStart_1171881 : Nat := 118140960795 + 1171881 * 2 ^ 59
def prefixEnd_1171881 : Nat := 4983230072969 + 3 ^ 40 * 1171881 * 2
def baseEnd_1171881 : Nat := 200579407623878247966041

theorem tailTrace_1171881 : CollatzResearch.WordTrace tailWord_1171881 prefixEnd_1171881 200579407623878247966041 := by
  unfold tailWord_1171881
  simp only [CollatzResearch.WordTrace]
  refine ⟨42742011467482753185843497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28494674311655168790562331 42742011467482753185843497)
  ·
    refine ⟨32056508600612064889382623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42742011467482753185843497 32056508600612064889382623)
    ·
      refine ⟨48084762900918097334073935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32056508600612064889382623 48084762900918097334073935)
      ·
        refine ⟨72127144351377146001110903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48084762900918097334073935 72127144351377146001110903)
        ·
          refine ⟨108190716527065719001666355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72127144351377146001110903 108190716527065719001666355)
          ·
            refine ⟨162286074790598578502499533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108190716527065719001666355 162286074790598578502499533)
            ·
              refine ⟨60857278046474466938437325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162286074790598578502499533 60857278046474466938437325)
              ·
                refine ⟨22821479267427925101913997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60857278046474466938437325 22821479267427925101913997)
                ·
                  refine ⟨8558054725285471913217749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22821479267427925101913997 8558054725285471913217749)
                  ·
                    refine ⟨200579407623878247966041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8558054725285471913217749 200579407623878247966041)
                    ·
                      rfl

theorem cell23_1171881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 7].length) (baseStart_1171881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171881 prefixEnd_1171881 := by exact prefixLift 1171881
  have htrace : WordTrace (prefixWord ++ tailWord_1171881) baseStart_1171881 baseEnd_1171881 := by
    simpa [prefixWord, tailWord_1171881, baseEnd_1171881] using wordTrace_append hprefix tailTrace_1171881
  have hstable : (prefixWord ++ tailWord_1171881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171881).length < 2 ^ (prefixWord ++ tailWord_1171881).sum := by decide
  have hdescent : baseEnd_1171881 < baseStart_1171881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171918 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_1171918 : Nat := 118140960795 + 1171918 * 2 ^ 59
def prefixEnd_1171918 : Nat := 4983230072969 + 3 ^ 40 * 1171918 * 2
def baseEnd_1171918 : Nat := 601757221655851099135453

theorem tailTrace_1171918 : CollatzResearch.WordTrace tailWord_1171918 prefixEnd_1171918 601757221655851099135453 := by
  unfold tailWord_1171918
  simp only [CollatzResearch.WordTrace]
  refine ⟨5342920121043588563117551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28495573978899139003293605 5342920121043588563117551)
  ·
    refine ⟨8014380181565382844676327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5342920121043588563117551 8014380181565382844676327)
    ·
      refine ⟨12021570272348074267014491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8014380181565382844676327 12021570272348074267014491)
      ·
        refine ⟨18032355408522111400521737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12021570272348074267014491 18032355408522111400521737)
        ·
          refine ⟨13524266556391583550391303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18032355408522111400521737 13524266556391583550391303)
          ·
            refine ⟨20286399834587375325586955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13524266556391583550391303 20286399834587375325586955)
            ·
              refine ⟨30429599751881062988380433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20286399834587375325586955 30429599751881062988380433)
              ·
                refine ⟨22822199813910797241285325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30429599751881062988380433 22822199813910797241285325)
                ·
                  refine ⟨8558324930216548965481997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22822199813910797241285325 8558324930216548965481997)
                  ·
                    refine ⟨3209371848831205862055749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8558324930216548965481997 3209371848831205862055749)
                    ·
                      refine ⟨601757221655851099135453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3209371848831205862055749 601757221655851099135453)
                      ·
                        rfl

theorem cell23_1171918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_1171918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171918 prefixEnd_1171918 := by exact prefixLift 1171918
  have htrace : WordTrace (prefixWord ++ tailWord_1171918) baseStart_1171918 baseEnd_1171918 := by
    simpa [prefixWord, tailWord_1171918, baseEnd_1171918] using wordTrace_append hprefix tailTrace_1171918
  have hstable : (prefixWord ++ tailWord_1171918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171918).length < 2 ^ (prefixWord ++ tailWord_1171918).sum := by decide
  have hdescent : baseEnd_1171918 < baseStart_1171918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171935 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 1, 6, 2]
def baseStart_1171935 : Nat := 118140960795 + 1171935 * 2 ^ 59
def prefixEnd_1171935 : Nat := 4983230072969 + 3 ^ 40 * 1171935 * 2
def baseEnd_1171935 : Nat := 601765950826977532622875

theorem tailTrace_1171935 : CollatzResearch.WordTrace tailWord_1171935 prefixEnd_1171935 601765950826977532622875 := by
  unfold tailWord_1171935
  simp only [CollatzResearch.WordTrace]
  refine ⟨42743981009287120408309259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28495987339524746938872839 42743981009287120408309259)
  ·
    refine ⟨64115971513930680612463889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42743981009287120408309259 64115971513930680612463889)
    ·
      refine ⟨48086978635448010459347917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64115971513930680612463889 48086978635448010459347917)
      ·
        refine ⟨18032616988293003922255469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48086978635448010459347917 18032616988293003922255469)
        ·
          refine ⟨6762231370609876470845801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18032616988293003922255469 6762231370609876470845801)
          ·
            refine ⟨5071673527957407353134351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6762231370609876470845801 5071673527957407353134351)
            ·
              refine ⟨7607510291936111029701527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5071673527957407353134351 7607510291936111029701527)
              ·
                refine ⟨11411265437904166544552291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7607510291936111029701527 11411265437904166544552291)
                ·
                  refine ⟨17116898156856249816828437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11411265437904166544552291 17116898156856249816828437)
                  ·
                    refine ⟨802354601102636710163833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17116898156856249816828437 802354601102636710163833)
                    ·
                      refine ⟨601765950826977532622875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 802354601102636710163833 601765950826977532622875)
                      ·
                        rfl

theorem cell23_1171935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_1171935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171935 prefixEnd_1171935 := by exact prefixLift 1171935
  have htrace : WordTrace (prefixWord ++ tailWord_1171935) baseStart_1171935 baseEnd_1171935 := by
    simpa [prefixWord, tailWord_1171935, baseEnd_1171935] using wordTrace_append hprefix tailTrace_1171935
  have hstable : (prefixWord ++ tailWord_1171935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171935).length < 2 ^ (prefixWord ++ tailWord_1171935).sum := by decide
  have hdescent : baseEnd_1171935 < baseStart_1171935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171968 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 3]
def baseStart_1171968 : Nat := 118140960795 + 1171968 * 2 ^ 59
def prefixEnd_1171968 : Nat := 4983230072969 + 3 ^ 40 * 1171968 * 2
def baseEnd_1171968 : Nat := 601782895688575903510223

theorem tailTrace_1171968 : CollatzResearch.WordTrace tailWord_1171968 prefixEnd_1171968 601782895688575903510223 := by
  unfold tailWord_1171968
  simp only [CollatzResearch.WordTrace]
  refine ⟨21372592309083783522130279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28496789745445044696173705 21372592309083783522130279)
  ·
    refine ⟨32058888463625675283195419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21372592309083783522130279 32058888463625675283195419)
    ·
      refine ⟨48088332695438512924793129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32058888463625675283195419 48088332695438512924793129)
      ·
        refine ⟨36066249521578884693594847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48088332695438512924793129 36066249521578884693594847)
        ·
          refine ⟨54099374282368327040392271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36066249521578884693594847 54099374282368327040392271)
          ·
            refine ⟨81149061423552490560588407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54099374282368327040392271 81149061423552490560588407)
            ·
              refine ⟨121723592135328735840882611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81149061423552490560588407 121723592135328735840882611)
              ·
                refine ⟨182585388202993103761323917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121723592135328735840882611 182585388202993103761323917)
                ·
                  refine ⟨68469520576122413910496469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182585388202993103761323917 68469520576122413910496469)
                  ·
                    refine ⟨1604754388502869076027261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 68469520576122413910496469 1604754388502869076027261)
                    ·
                      refine ⟨601782895688575903510223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1604754388502869076027261 601782895688575903510223)
                      ·
                        rfl

theorem cell23_1171968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_1171968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171968 prefixEnd_1171968 := by exact prefixLift 1171968
  have htrace : WordTrace (prefixWord ++ tailWord_1171968) baseStart_1171968 baseEnd_1171968 := by
    simpa [prefixWord, tailWord_1171968, baseEnd_1171968] using wordTrace_append hprefix tailTrace_1171968
  have hstable : (prefixWord ++ tailWord_1171968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171968).length < 2 ^ (prefixWord ++ tailWord_1171968).sum := by decide
  have hdescent : baseEnd_1171968 < baseStart_1171968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171975 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 8]
def baseStart_1171975 : Nat := 118140960795 + 1171975 * 2 ^ 59
def prefixEnd_1171975 : Nat := 4983230072969 + 3 ^ 40 * 1171975 * 2
def baseEnd_1171975 : Nat := 66865165561461930680299

theorem tailTrace_1171975 : CollatzResearch.WordTrace tailWord_1171975 prefixEnd_1171975 66865165561461930680299 := by
  unfold tailWord_1171975
  simp only [CollatzResearch.WordTrace]
  refine ⟨42745439929142207239765379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28496959952761471493176919 42745439929142207239765379)
  ·
    refine ⟨64118159893713310859648069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42745439929142207239765379 64118159893713310859648069)
    ·
      refine ⟨12022154980071245786184013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64118159893713310859648069 12022154980071245786184013)
      ·
        refine ⟨4508308117526717169819005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12022154980071245786184013 4508308117526717169819005)
        ·
          refine ⟨1690615544072518938682127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4508308117526717169819005 1690615544072518938682127)
          ·
            refine ⟨2535923316108778408023191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1690615544072518938682127 2535923316108778408023191)
            ·
              refine ⟨3803884974163167612034787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2535923316108778408023191 3803884974163167612034787)
              ·
                refine ⟨5705827461244751418052181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3803884974163167612034787 5705827461244751418052181)
                ·
                  refine ⟨66865165561461930680299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5705827461244751418052181 66865165561461930680299)
                  ·
                    rfl

theorem cell23_1171975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 8].length) (baseStart_1171975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171975 prefixEnd_1171975 := by exact prefixLift 1171975
  have htrace : WordTrace (prefixWord ++ tailWord_1171975) baseStart_1171975 baseEnd_1171975 := by
    simpa [prefixWord, tailWord_1171975, baseEnd_1171975] using wordTrace_append hprefix tailTrace_1171975
  have hstable : (prefixWord ++ tailWord_1171975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171975).length < 2 ^ (prefixWord ++ tailWord_1171975).sum := by decide
  have hdescent : baseEnd_1171975 < baseStart_1171975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171978 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_1171978 : Nat := 118140960795 + 1171978 * 2 ^ 59
def prefixEnd_1171978 : Nat := 4983230072969 + 3 ^ 40 * 1171978 * 2
def baseEnd_1171978 : Nat := 601788030495120864385177

theorem tailTrace_1171978 : CollatzResearch.WordTrace tailWord_1171978 prefixEnd_1171978 601788030495120864385177 := by
  unfold tailWord_1171978
  simp only [CollatzResearch.WordTrace]
  refine ⟨10686387337032834688031147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28497032898754225834749725 10686387337032834688031147)
  ·
    refine ⟨16029581005549252032046721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10686387337032834688031147 16029581005549252032046721)
    ·
      refine ⟨12022185754161939024035041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16029581005549252032046721 12022185754161939024035041)
      ·
        refine ⟨9016639315621454268026281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12022185754161939024035041 9016639315621454268026281)
        ·
          refine ⟨6762479486716090701019711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9016639315621454268026281 6762479486716090701019711)
          ·
            refine ⟨10143719230074136051529567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6762479486716090701019711 10143719230074136051529567)
            ·
              refine ⟨15215578845111204077294351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10143719230074136051529567 15215578845111204077294351)
              ·
                refine ⟨22823368267666806115941527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15215578845111204077294351 22823368267666806115941527)
                ·
                  refine ⟨34235052401500209173912291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22823368267666806115941527 34235052401500209173912291)
                  ·
                    refine ⟨51352578602250313760868437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34235052401500209173912291 51352578602250313760868437)
                    ·
                      refine ⟨601788030495120864385177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 51352578602250313760868437 601788030495120864385177)
                      ·
                        rfl

theorem cell23_1171978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_1171978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171978 prefixEnd_1171978 := by exact prefixLift 1171978
  have htrace : WordTrace (prefixWord ++ tailWord_1171978) baseStart_1171978 baseEnd_1171978 := by
    simpa [prefixWord, tailWord_1171978, baseEnd_1171978] using wordTrace_append hprefix tailTrace_1171978
  have hstable : (prefixWord ++ tailWord_1171978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171978).length < 2 ^ (prefixWord ++ tailWord_1171978).sum := by decide
  have hdescent : baseEnd_1171978 < baseStart_1171978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
