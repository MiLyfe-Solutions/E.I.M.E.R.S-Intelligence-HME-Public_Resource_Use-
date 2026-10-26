import V185TrunkScan23Chunk0486

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2880581 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 3, 2, 3]
def baseStart_2880581 : Nat := 118140960795 + 2880581 * 2 ^ 59
def prefixEnd_2880581 : Nat := 4983230072969 + 3 ^ 40 * 2880581 * 2
def baseEnd_2880581 : Nat := 1479122617209099447289955

theorem tailTrace_2880581 : CollatzResearch.WordTrace tailWord_2880581 prefixEnd_2880581 1479122617209099447289955 := by
  unfold tailWord_2880581
  simp only [CollatzResearch.WordTrace]
  refine ⟨105063420377154475912649597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70042280251436317275099731 105063420377154475912649597)
  ·
    refine ⟨39398782641432928467243599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105063420377154475912649597 39398782641432928467243599)
    ·
      refine ⟨59098173962149392700865399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39398782641432928467243599 59098173962149392700865399)
      ·
        refine ⟨88647260943224089051298099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59098173962149392700865399 88647260943224089051298099)
        ·
          refine ⟨132970891414836133576947149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88647260943224089051298099 132970891414836133576947149)
          ·
            refine ⟨49864084280563550091355181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132970891414836133576947149 49864084280563550091355181)
            ·
              refine ⟨18699031605211331284258193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49864084280563550091355181 18699031605211331284258193)
              ·
                refine ⟨14024273703908498463193645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18699031605211331284258193 14024273703908498463193645)
                ·
                  refine ⟨5259102638965686923697617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14024273703908498463193645 5259102638965686923697617)
                  ·
                    refine ⟨3944326979224265192773213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5259102638965686923697617 3944326979224265192773213)
                    ·
                      refine ⟨1479122617209099447289955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3944326979224265192773213 1479122617209099447289955)
                      ·
                        rfl

theorem cell23_2880581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_2880581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880581 prefixEnd_2880581 := by exact prefixLift 2880581
  have htrace : WordTrace (prefixWord ++ tailWord_2880581) baseStart_2880581 baseEnd_2880581 := by
    simpa [prefixWord, tailWord_2880581, baseEnd_2880581] using wordTrace_append hprefix tailTrace_2880581
  have hstable : (prefixWord ++ tailWord_2880581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880581).length < 2 ^ (prefixWord ++ tailWord_2880581).sum := by decide
  have hdescent : baseEnd_2880581 < baseStart_2880581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880606 : List Nat := [4, 4, 1, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_2880606 : Nat := 118140960795 + 2880606 * 2 ^ 59
def prefixEnd_2880606 : Nat := 4983230072969 + 3 ^ 40 * 2880606 * 2
def baseEnd_2880606 : Nat := 1479135454225461849477341

theorem tailTrace_2880606 : CollatzResearch.WordTrace tailWord_2880606 prefixEnd_2880606 1479135454225461849477341 := by
  unfold tailWord_2880606
  simp only [CollatzResearch.WordTrace]
  refine ⟨13133041525257988147788709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70042888134709270121539781 13133041525257988147788709)
  ·
    refine ⟨2462445285985872777710383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13133041525257988147788709 2462445285985872777710383)
    ·
      refine ⟨3693667928978809166565575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2462445285985872777710383 3693667928978809166565575)
      ·
        refine ⟨5540501893468213749848363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3693667928978809166565575 5540501893468213749848363)
        ·
          refine ⟨8310752840202320624772545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5540501893468213749848363 8310752840202320624772545)
          ·
            refine ⟨6233064630151740468579409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8310752840202320624772545 6233064630151740468579409)
            ·
              refine ⟨4674798472613805351434557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6233064630151740468579409 4674798472613805351434557)
              ·
                refine ⟨1753049427230177006787959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4674798472613805351434557 1753049427230177006787959)
                ·
                  refine ⟨2629574140845265510181939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1753049427230177006787959 2629574140845265510181939)
                  ·
                    refine ⟨3944361211267898265272909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2629574140845265510181939 3944361211267898265272909)
                    ·
                      refine ⟨1479135454225461849477341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3944361211267898265272909 1479135454225461849477341)
                      ·
                        rfl

theorem cell23_2880606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_2880606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880606 prefixEnd_2880606 := by exact prefixLift 2880606
  have htrace : WordTrace (prefixWord ++ tailWord_2880606) baseStart_2880606 baseEnd_2880606 := by
    simpa [prefixWord, tailWord_2880606, baseEnd_2880606] using wordTrace_append hprefix tailTrace_2880606
  have hstable : (prefixWord ++ tailWord_2880606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880606).length < 2 ^ (prefixWord ++ tailWord_2880606).sum := by decide
  have hdescent : baseEnd_2880606 < baseStart_2880606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880615 : List Nat := [1, 1, 5, 1, 1, 3, 4, 1, 1, 2, 3]
def baseStart_2880615 : Nat := 118140960795 + 2880615 * 2 ^ 59
def prefixEnd_2880615 : Nat := 4983230072969 + 3 ^ 40 * 2880615 * 2
def baseEnd_2880615 : Nat := 1479140075551352314264799

theorem tailTrace_2880615 : CollatzResearch.WordTrace tailWord_2880615 prefixEnd_2880615 1479140075551352314264799 := by
  unfold tailWord_2880615
  simp only [CollatzResearch.WordTrace]
  refine ⟨105064660459031299719387299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70043106972687533146258199 105064660459031299719387299)
  ·
    refine ⟨157596990688546949579080949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105064660459031299719387299 157596990688546949579080949)
    ·
      refine ⟨14774717877051276523038839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 157596990688546949579080949 14774717877051276523038839)
      ·
        refine ⟨22162076815576914784558259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14774717877051276523038839 22162076815576914784558259)
        ·
          refine ⟨33243115223365372176837389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22162076815576914784558259 33243115223365372176837389)
          ·
            refine ⟨12466168208762014566314021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33243115223365372176837389 12466168208762014566314021)
            ·
              refine ⟨2337406539142877731183879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12466168208762014566314021 2337406539142877731183879)
              ·
                refine ⟨3506109808714316596775819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2337406539142877731183879 3506109808714316596775819)
                ·
                  refine ⟨5259164713071474895163729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3506109808714316596775819 5259164713071474895163729)
                  ·
                    refine ⟨3944373534803606171372797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5259164713071474895163729 3944373534803606171372797)
                    ·
                      refine ⟨1479140075551352314264799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3944373534803606171372797 1479140075551352314264799)
                      ·
                        rfl

theorem cell23_2880615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_2880615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880615 prefixEnd_2880615 := by exact prefixLift 2880615
  have htrace : WordTrace (prefixWord ++ tailWord_2880615) baseStart_2880615 baseEnd_2880615 := by
    simpa [prefixWord, tailWord_2880615, baseEnd_2880615] using wordTrace_append hprefix tailTrace_2880615
  have hstable : (prefixWord ++ tailWord_2880615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880615).length < 2 ^ (prefixWord ++ tailWord_2880615).sum := by decide
  have hdescent : baseEnd_2880615 < baseStart_2880615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880629 : List Nat := [1, 3, 4, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_2880629 : Nat := 118140960795 + 2880629 * 2 ^ 59
def prefixEnd_2880629 : Nat := 4983230072969 + 3 ^ 40 * 2880629 * 2
def baseEnd_2880629 : Nat := 1479147264280515259489735

theorem tailTrace_2880629 : CollatzResearch.WordTrace tailWord_2880629 prefixEnd_2880629 1479147264280515259489735 := by
  unfold tailWord_2880629
  simp only [CollatzResearch.WordTrace]
  refine ⟨105065171080980580110396941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70043447387320386740264627 105065171080980580110396941)
  ·
    refine ⟨39399439155367717541398853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105065171080980580110396941 39399439155367717541398853)
    ·
      refine ⟨7387394841631447039012285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39399439155367717541398853 7387394841631447039012285)
      ·
        refine ⟨2770273065611792639629607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7387394841631447039012285 2770273065611792639629607)
        ·
          refine ⟨4155409598417688959444411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2770273065611792639629607 4155409598417688959444411)
          ·
            refine ⟨6233114397626533439166617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4155409598417688959444411 6233114397626533439166617)
            ·
              refine ⟨4674835798219900079374963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6233114397626533439166617 4674835798219900079374963)
              ·
                refine ⟨7012253697329850119062445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4674835798219900079374963 7012253697329850119062445)
                ·
                  refine ⟨2629595136498693794648417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7012253697329850119062445 2629595136498693794648417)
                  ·
                    refine ⟨1972196352374020345986313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2629595136498693794648417 1972196352374020345986313)
                    ·
                      refine ⟨1479147264280515259489735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1972196352374020345986313 1479147264280515259489735)
                      ·
                        rfl

theorem cell23_2880629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_2880629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880629 prefixEnd_2880629 := by exact prefixLift 2880629
  have htrace : WordTrace (prefixWord ++ tailWord_2880629) baseStart_2880629 baseEnd_2880629 := by
    simpa [prefixWord, tailWord_2880629, baseEnd_2880629] using wordTrace_append hprefix tailTrace_2880629
  have hstable : (prefixWord ++ tailWord_2880629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880629).length < 2 ^ (prefixWord ++ tailWord_2880629).sum := by decide
  have hdescent : baseEnd_2880629 < baseStart_2880629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880645 : List Nat := [1, 3, 1, 1, 6, 2, 1, 1, 1, 3, 3]
def baseStart_2880645 : Nat := 118140960795 + 2880645 * 2 ^ 59
def prefixEnd_2880645 : Nat := 4983230072969 + 3 ^ 40 * 2880645 * 2
def baseEnd_2880645 : Nat := 1479155479970987196889661

theorem tailTrace_2880645 : CollatzResearch.WordTrace tailWord_2880645 prefixEnd_2880645 1479155479970987196889661 := by
  unfold tailWord_2880645
  simp only [CollatzResearch.WordTrace]
  refine ⟨105065754648922614842979389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70043836432615076561986259 105065754648922614842979389)
  ·
    refine ⟨39399657993345980566117271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105065754648922614842979389 39399657993345980566117271)
    ·
      refine ⟨59099486990018970849175907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39399657993345980566117271 59099486990018970849175907)
      ·
        refine ⟨88649230485028456273763861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59099486990018970849175907 88649230485028456273763861)
        ·
          refine ⟨4155432678985708887832681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88649230485028456273763861 4155432678985708887832681)
          ·
            refine ⟨3116574509239281665874511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4155432678985708887832681 3116574509239281665874511)
            ·
              refine ⟨4674861763858922498811767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3116574509239281665874511 4674861763858922498811767)
              ·
                refine ⟨7012292645788383748217651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4674861763858922498811767 7012292645788383748217651)
                ·
                  refine ⟨10518438968682575622326477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7012292645788383748217651 10518438968682575622326477)
                  ·
                    refine ⟨3944414613255965858372429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10518438968682575622326477 3944414613255965858372429)
                    ·
                      refine ⟨1479155479970987196889661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3944414613255965858372429 1479155479970987196889661)
                      ·
                        rfl

theorem cell23_2880645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 3, 3].length) (baseStart_2880645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880645 prefixEnd_2880645 := by exact prefixLift 2880645
  have htrace : WordTrace (prefixWord ++ tailWord_2880645) baseStart_2880645 baseEnd_2880645 := by
    simpa [prefixWord, tailWord_2880645, baseEnd_2880645] using wordTrace_append hprefix tailTrace_2880645
  have hstable : (prefixWord ++ tailWord_2880645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880645).length < 2 ^ (prefixWord ++ tailWord_2880645).sum := by decide
  have hdescent : baseEnd_2880645 < baseStart_2880645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880691 : List Nat := [1, 1, 1, 2, 3, 2, 5, 1, 7]
def baseStart_2880691 : Nat := 118140960795 + 2880691 * 2 ^ 59
def prefixEnd_2880691 : Nat := 4983230072969 + 3 ^ 40 * 2880691 * 2
def baseEnd_2880691 : Nat := 164353233342343779657161

theorem tailTrace_2880691 : CollatzResearch.WordTrace tailWord_2880691 prefixEnd_2880691 164353233342343779657161 := by
  unfold tailWord_2880691
  simp only [CollatzResearch.WordTrace]
  refine ⟨105067432406755964699153927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70044954937837309799435951 105067432406755964699153927)
  ·
    refine ⟨157601148610133947048730891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105067432406755964699153927 157601148610133947048730891)
    ·
      refine ⟨236401722915200920573096337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157601148610133947048730891 236401722915200920573096337)
      ·
        refine ⟨177301292186400690429822253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236401722915200920573096337 177301292186400690429822253)
        ·
          refine ⟨66487984569900258911183345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177301292186400690429822253 66487984569900258911183345)
          ·
            refine ⟨49865988427425194183387509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66487984569900258911183345 49865988427425194183387509)
            ·
              refine ⟨4674936415071111954692579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49865988427425194183387509 4674936415071111954692579)
              ·
                refine ⟨7012404622606667932038869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4674936415071111954692579 7012404622606667932038869)
                ·
                  refine ⟨164353233342343779657161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7012404622606667932038869 164353233342343779657161)
                  ·
                    rfl

theorem cell23_2880691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 7].length) (baseStart_2880691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880691 prefixEnd_2880691 := by exact prefixLift 2880691
  have htrace : WordTrace (prefixWord ++ tailWord_2880691) baseStart_2880691 baseEnd_2880691 := by
    simpa [prefixWord, tailWord_2880691, baseEnd_2880691] using wordTrace_append hprefix tailTrace_2880691
  have hstable : (prefixWord ++ tailWord_2880691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880691).length < 2 ^ (prefixWord ++ tailWord_2880691).sum := by decide
  have hdescent : baseEnd_2880691 < baseStart_2880691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880758 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_2880758 : Nat := 118140960795 + 2880758 * 2 ^ 59
def prefixEnd_2880758 : Nat := 4983230072969 + 3 ^ 40 * 2880758 * 2
def baseEnd_2880758 : Nat := 1479213503284945254776641

theorem tailTrace_2880758 : CollatzResearch.WordTrace tailWord_2880758 prefixEnd_2880758 1479213503284945254776641 := by
  unfold tailWord_2880758
  simp only [CollatzResearch.WordTrace]
  refine ⟨6566867256094577196365183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70046584065008823427895285 6566867256094577196365183)
  ·
    refine ⟨9850300884141865794547775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6566867256094577196365183 9850300884141865794547775)
    ·
      refine ⟨14775451326212798691821663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9850300884141865794547775 14775451326212798691821663)
      ·
        refine ⟨22163176989319198037732495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14775451326212798691821663 22163176989319198037732495)
        ·
          refine ⟨33244765483978797056598743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22163176989319198037732495 33244765483978797056598743)
          ·
            refine ⟨49867148225968195584898115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33244765483978797056598743 49867148225968195584898115)
            ·
              refine ⟨74800722338952293377347173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49867148225968195584898115 74800722338952293377347173)
              ·
                refine ⟨14025135438553555008252595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74800722338952293377347173 14025135438553555008252595)
                ·
                  refine ⟨21037703157830332512378893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14025135438553555008252595 21037703157830332512378893)
                  ·
                    refine ⟨7889138684186374692142085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21037703157830332512378893 7889138684186374692142085)
                    ·
                      refine ⟨1479213503284945254776641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7889138684186374692142085 1479213503284945254776641)
                      ·
                        rfl

theorem cell23_2880758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_2880758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880758 prefixEnd_2880758 := by exact prefixLift 2880758
  have htrace : WordTrace (prefixWord ++ tailWord_2880758) baseStart_2880758 baseEnd_2880758 := by
    simpa [prefixWord, tailWord_2880758, baseEnd_2880758] using wordTrace_append hprefix tailTrace_2880758
  have hstable : (prefixWord ++ tailWord_2880758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880758).length < 2 ^ (prefixWord ++ tailWord_2880758).sum := by decide
  have hdescent : baseEnd_2880758 < baseStart_2880758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880802 : List Nat := [3, 3, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_2880802 : Nat := 118140960795 + 2880802 * 2 ^ 59
def prefixEnd_2880802 : Nat := 4983230072969 + 3 ^ 40 * 2880802 * 2
def baseEnd_2880802 : Nat := 493078698811247694208813

theorem tailTrace_2880802 : CollatzResearch.WordTrace tailWord_2880802 prefixEnd_2880802 493078698811247694208813 := by
  unfold tailWord_2880802
  simp only [CollatzResearch.WordTrace]
  refine ⟨26267870227338457664111165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70047653939569220437629773 26267870227338457664111165)
  ·
    refine ⟨9850451335251921624041687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26267870227338457664111165 9850451335251921624041687)
    ·
      refine ⟨14775677002877882436062531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9850451335251921624041687 14775677002877882436062531)
      ·
        refine ⟨22163515504316823654093797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14775677002877882436062531 22163515504316823654093797)
        ·
          refine ⟨4155659157059404435142587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22163515504316823654093797 4155659157059404435142587)
          ·
            refine ⟨6233488735589106652713881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4155659157059404435142587 6233488735589106652713881)
            ·
              refine ⟨4675116551691829989535411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6233488735589106652713881 4675116551691829989535411)
              ·
                refine ⟨7012674827537744984303117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4675116551691829989535411 7012674827537744984303117)
                ·
                  refine ⟨2629753060326654369113669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7012674827537744984303117 2629753060326654369113669)
                  ·
                    refine ⟨493078698811247694208813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2629753060326654369113669 493078698811247694208813)
                    ·
                      rfl

theorem cell23_2880802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_2880802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880802 prefixEnd_2880802 := by exact prefixLift 2880802
  have htrace : WordTrace (prefixWord ++ tailWord_2880802) baseStart_2880802 baseEnd_2880802 := by
    simpa [prefixWord, tailWord_2880802, baseEnd_2880802] using wordTrace_append hprefix tailTrace_2880802
  have hstable : (prefixWord ++ tailWord_2880802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880802).length < 2 ^ (prefixWord ++ tailWord_2880802).sum := by decide
  have hdescent : baseEnd_2880802 < baseStart_2880802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880835 : List Nat := [1, 1, 1, 3, 1, 3, 1, 5, 2, 3, 2]
def baseStart_2880835 : Nat := 118140960795 + 2880835 * 2 ^ 59
def prefixEnd_2880835 : Nat := 4983230072969 + 3 ^ 40 * 2880835 * 2
def baseEnd_2880835 : Nat := 1479253041295341453513787

theorem tailTrace_2880835 : CollatzResearch.WordTrace tailWord_2880835 prefixEnd_2880835 1479253041295341453513787 := by
  unfold tailWord_2880835
  simp only [CollatzResearch.WordTrace]
  refine ⟨105072684518234277292395959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70048456345489518194930639 105072684518234277292395959)
  ·
    refine ⟨157609026777351415938593939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105072684518234277292395959 157609026777351415938593939)
    ·
      refine ⟨236413540166027123907890909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157609026777351415938593939 236413540166027123907890909)
      ·
        refine ⟨88655077562260171465459091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236413540166027123907890909 88655077562260171465459091)
        ·
          refine ⟨132982616343390257198188637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88655077562260171465459091 132982616343390257198188637)
          ·
            refine ⟨49868481128771346449320739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132982616343390257198188637 49868481128771346449320739)
            ·
              refine ⟨74802721693157019673981109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49868481128771346449320739 74802721693157019673981109)
              ·
                refine ⟨7012755158733470594435729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74802721693157019673981109 7012755158733470594435729)
                ·
                  refine ⟨5259566369050102945826797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7012755158733470594435729 5259566369050102945826797)
                  ·
                    refine ⟨1972337388393788604685049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5259566369050102945826797 1972337388393788604685049)
                    ·
                      refine ⟨1479253041295341453513787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1972337388393788604685049 1479253041295341453513787)
                      ·
                        rfl

theorem cell23_2880835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 3, 2].length) (baseStart_2880835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880835 prefixEnd_2880835 := by exact prefixLift 2880835
  have htrace : WordTrace (prefixWord ++ tailWord_2880835) baseStart_2880835 baseEnd_2880835 := by
    simpa [prefixWord, tailWord_2880835, baseEnd_2880835] using wordTrace_append hprefix tailTrace_2880835
  have hstable : (prefixWord ++ tailWord_2880835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880835).length < 2 ^ (prefixWord ++ tailWord_2880835).sum := by decide
  have hdescent : baseEnd_2880835 < baseStart_2880835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880836 : List Nat := [2, 3, 4, 1, 1, 3, 1, 3, 1, 4]
def baseStart_2880836 : Nat := 118140960795 + 2880836 * 2 ^ 59
def prefixEnd_2880836 : Nat := 4983230072969 + 3 ^ 40 * 2880836 * 2
def baseEnd_2880836 : Nat := 493084518258665316533761

theorem tailTrace_2880836 : CollatzResearch.WordTrace tailWord_2880836 prefixEnd_2880836 493084518258665316533761 := by
  unfold tailWord_2880836
  simp only [CollatzResearch.WordTrace]
  refine ⟨52536360495615327231591181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70048480660820436308788241 52536360495615327231591181)
  ·
    refine ⟨19701135185855747711846693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52536360495615327231591181 19701135185855747711846693)
    ·
      refine ⟨3693962847347952695971255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19701135185855747711846693 3693962847347952695971255)
      ·
        refine ⟨5540944271021929043956883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3693962847347952695971255 5540944271021929043956883)
        ·
          refine ⟨8311416406532893565935325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5540944271021929043956883 8311416406532893565935325)
          ·
            refine ⟨3116781152449835087225747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8311416406532893565935325 3116781152449835087225747)
            ·
              refine ⟨4675171728674752630838621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3116781152449835087225747 4675171728674752630838621)
              ·
                refine ⟨1753189398253032236564483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4675171728674752630838621 1753189398253032236564483)
                ·
                  refine ⟨2629784097379548354846725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1753189398253032236564483 2629784097379548354846725)
                  ·
                    refine ⟨493084518258665316533761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2629784097379548354846725 493084518258665316533761)
                    ·
                      rfl

theorem cell23_2880836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_2880836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880836 prefixEnd_2880836 := by exact prefixLift 2880836
  have htrace : WordTrace (prefixWord ++ tailWord_2880836) baseStart_2880836 baseEnd_2880836 := by
    simpa [prefixWord, tailWord_2880836, baseEnd_2880836] using wordTrace_append hprefix tailTrace_2880836
  have hstable : (prefixWord ++ tailWord_2880836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880836).length < 2 ^ (prefixWord ++ tailWord_2880836).sum := by decide
  have hdescent : baseEnd_2880836 < baseStart_2880836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880852 : List Nat := [2, 4, 1, 1, 2, 1, 3, 2, 2, 3, 2]
def baseStart_2880852 : Nat := 118140960795 + 2880852 * 2 ^ 59
def prefixEnd_2880852 : Nat := 4983230072969 + 3 ^ 40 * 2880852 * 2
def baseEnd_2880852 : Nat := 1479261770466467887001209

theorem tailTrace_2880852 : CollatzResearch.WordTrace tailWord_2880852 prefixEnd_2880852 1479261770466467887001209 := by
  unfold tailWord_2880852
  simp only [CollatzResearch.WordTrace]
  refine ⟨52536652279586344597882405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70048869706115126130509873 52536652279586344597882405)
  ·
    refine ⟨9850622302422439612102951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52536652279586344597882405 9850622302422439612102951)
    ·
      refine ⟨14775933453633659418154427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9850622302422439612102951 14775933453633659418154427)
      ·
        refine ⟨22163900180450489127231641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14775933453633659418154427 22163900180450489127231641)
        ·
          refine ⟨16622925135337866845423731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22163900180450489127231641 16622925135337866845423731)
          ·
            refine ⟨24934387703006800268135597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16622925135337866845423731 24934387703006800268135597)
            ·
              refine ⟨9350395388627550100550849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24934387703006800268135597 9350395388627550100550849)
              ·
                refine ⟨7012796541470662575413137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9350395388627550100550849 7012796541470662575413137)
                ·
                  refine ⟨5259597406102996931559853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7012796541470662575413137 5259597406102996931559853)
                  ·
                    refine ⟨1972349027288623849334945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5259597406102996931559853 1972349027288623849334945)
                    ·
                      refine ⟨1479261770466467887001209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1972349027288623849334945 1479261770466467887001209)
                      ·
                        rfl

theorem cell23_2880852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_2880852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880852 prefixEnd_2880852 := by exact prefixLift 2880852
  have htrace : WordTrace (prefixWord ++ tailWord_2880852) baseStart_2880852 baseEnd_2880852 := by
    simpa [prefixWord, tailWord_2880852, baseEnd_2880852] using wordTrace_append hprefix tailTrace_2880852
  have hstable : (prefixWord ++ tailWord_2880852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880852).length < 2 ^ (prefixWord ++ tailWord_2880852).sum := by decide
  have hdescent : baseEnd_2880852 < baseStart_2880852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880882 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 5, 2, 2]
def baseStart_2880882 : Nat := 118140960795 + 2880882 * 2 ^ 59
def prefixEnd_2880882 : Nat := 4983230072969 + 3 ^ 40 * 2880882 * 2
def baseEnd_2880882 : Nat := 1479277174886102769626071

theorem tailTrace_2880882 : CollatzResearch.WordTrace tailWord_2880882 prefixEnd_2880882 1479277174886102769626071 := by
  unfold tailWord_2880882
  simp only [CollatzResearch.WordTrace]
  refine ⟨26268599687266001079839225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70049599166042669546237933 26268599687266001079839225)
  ·
    refine ⟨19701449765449500809879419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26268599687266001079839225 19701449765449500809879419)
    ·
      refine ⟨29552174648174251214819129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19701449765449500809879419 29552174648174251214819129)
      ·
        refine ⟨22164130986130688411114347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29552174648174251214819129 22164130986130688411114347)
        ·
          refine ⟨33246196479196032616671521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22164130986130688411114347 33246196479196032616671521)
          ·
            refine ⟨24934647359397024462503641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33246196479196032616671521 24934647359397024462503641)
            ·
              refine ⟨18700985519547768346877731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24934647359397024462503641 18700985519547768346877731)
              ·
                refine ⟨28051478279321652520316597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18700985519547768346877731 28051478279321652520316597)
                ·
                  refine ⟨2629826088686404923779681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28051478279321652520316597 2629826088686404923779681)
                  ·
                    refine ⟨1972369566514803692834761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2629826088686404923779681 1972369566514803692834761)
                    ·
                      refine ⟨1479277174886102769626071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1972369566514803692834761 1479277174886102769626071)
                      ·
                        rfl

theorem cell23_2880882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_2880882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880882 prefixEnd_2880882 := by exact prefixLift 2880882
  have htrace : WordTrace (prefixWord ++ tailWord_2880882) baseStart_2880882 baseEnd_2880882 := by
    simpa [prefixWord, tailWord_2880882, baseEnd_2880882] using wordTrace_append hprefix tailTrace_2880882
  have hstable : (prefixWord ++ tailWord_2880882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880882).length < 2 ^ (prefixWord ++ tailWord_2880882).sum := by decide
  have hdescent : baseEnd_2880882 < baseStart_2880882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880910 : List Nat := [4, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3]
def baseStart_2880910 : Nat := 118140960795 + 2880910 * 2 ^ 59
def prefixEnd_2880910 : Nat := 4983230072969 + 3 ^ 40 * 2880910 * 2
def baseEnd_2880910 : Nat := 1479291552344428660075943

theorem tailTrace_2880910 : CollatzResearch.WordTrace tailWord_2880910 prefixEnd_2880910 1479291552344428660075943 := by
  unfold tailWord_2880910
  simp only [CollatzResearch.WordTrace]
  refine ⟨13134427499120320637672023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70050279995308376734250789 13134427499120320637672023)
  ·
    refine ⟨19701641248680480956508035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13134427499120320637672023 19701641248680480956508035)
    ·
      refine ⟨29552461873020721434762053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19701641248680480956508035 29552461873020721434762053)
      ·
        refine ⟨5541086601191385269017885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29552461873020721434762053 5541086601191385269017885)
        ·
          refine ⟨2077907475446769475881707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5541086601191385269017885 2077907475446769475881707)
          ·
            refine ⟨3116861213170154213822561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2077907475446769475881707 3116861213170154213822561)
            ·
              refine ⟨2337645909877615660366921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3116861213170154213822561 2337645909877615660366921)
              ·
                refine ⟨1753234432408211745275191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2337645909877615660366921 1753234432408211745275191)
                ·
                  refine ⟨2629851648612317617912787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1753234432408211745275191 2629851648612317617912787)
                  ·
                    refine ⟨3944777472918476426869181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2629851648612317617912787 3944777472918476426869181)
                    ·
                      refine ⟨1479291552344428660075943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3944777472918476426869181 1479291552344428660075943)
                      ·
                        rfl

theorem cell23_2880910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_2880910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880910 prefixEnd_2880910 := by exact prefixLift 2880910
  have htrace : WordTrace (prefixWord ++ tailWord_2880910) baseStart_2880910 baseEnd_2880910 := by
    simpa [prefixWord, tailWord_2880910, baseEnd_2880910] using wordTrace_append hprefix tailTrace_2880910
  have hstable : (prefixWord ++ tailWord_2880910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880910).length < 2 ^ (prefixWord ++ tailWord_2880910).sum := by decide
  have hdescent : baseEnd_2880910 < baseStart_2880910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880982 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_2880982 : Nat := 118140960795 + 2880982 * 2 ^ 59
def prefixEnd_2880982 : Nat := 4983230072969 + 3 ^ 40 * 2880982 * 2
def baseEnd_2880982 : Nat := 493109507650517459458537

theorem tailTrace_2880982 : CollatzResearch.WordTrace tailWord_2880982 prefixEnd_2880982 493109507650517459458537 := by
  unfold tailWord_2880982
  simp only [CollatzResearch.WordTrace]
  refine ⟨6567377878043857587374825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70052030699134480931998133 6567377878043857587374825)
  ·
    refine ⟨4925533408532893190531119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6567377878043857587374825 4925533408532893190531119)
    ·
      refine ⟨7388300112799339785796679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4925533408532893190531119 7388300112799339785796679)
      ·
        refine ⟨11082450169199009678695019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7388300112799339785796679 11082450169199009678695019)
        ·
          refine ⟨16623675253798514518042529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11082450169199009678695019 16623675253798514518042529)
          ·
            refine ⟨12467756440348885888531897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16623675253798514518042529 12467756440348885888531897)
            ·
              refine ⟨9350817330261664416398923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12467756440348885888531897 9350817330261664416398923)
              ·
                refine ⟨14026225995392496624598385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9350817330261664416398923 14026225995392496624598385)
                ·
                  refine ⟨10519669496544372468448789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14026225995392496624598385 10519669496544372468448789)
                  ·
                    refine ⟨493109507650517459458537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10519669496544372468448789 493109507650517459458537)
                    ·
                      rfl

theorem cell23_2880982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_2880982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880982 prefixEnd_2880982 := by exact prefixLift 2880982
  have htrace : WordTrace (prefixWord ++ tailWord_2880982) baseStart_2880982 baseEnd_2880982 := by
    simpa [prefixWord, tailWord_2880982, baseEnd_2880982] using wordTrace_append hprefix tailTrace_2880982
  have hstable : (prefixWord ++ tailWord_2880982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880982).length < 2 ^ (prefixWord ++ tailWord_2880982).sum := by decide
  have hdescent : baseEnd_2880982 < baseStart_2880982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880985 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 2, 2, 4]
def baseStart_2880985 : Nat := 118140960795 + 2880985 * 2 ^ 59
def prefixEnd_2880985 : Nat := 4983230072969 + 3 ^ 40 * 2880985 * 2
def baseEnd_2880985 : Nat := 1479330063393515866638097

theorem tailTrace_2880985 : CollatzResearch.WordTrace tailWord_2880985 prefixEnd_2880985 1479330063393515866638097 := by
  unfold tailWord_2880985
  simp only [CollatzResearch.WordTrace]
  refine ⟨105078155467690852910356409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70052103645127235273570939 105078155467690852910356409)
  ·
    refine ⟨78808616600768139682767307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105078155467690852910356409 78808616600768139682767307)
    ·
      refine ⟨118212924901152209524150961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78808616600768139682767307 118212924901152209524150961)
      ·
        refine ⟨88659693675864157143113221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118212924901152209524150961 88659693675864157143113221)
        ·
          refine ⟨16623692564224529464333729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88659693675864157143113221 16623692564224529464333729)
          ·
            refine ⟨12467769423168397098250297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16623692564224529464333729 12467769423168397098250297)
            ·
              refine ⟨9350827067376297823687723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12467769423168397098250297 9350827067376297823687723)
              ·
                refine ⟨14026240601064446735531585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9350827067376297823687723 14026240601064446735531585)
                ·
                  refine ⟨10519680450798335051648689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14026240601064446735531585 10519680450798335051648689)
                  ·
                    refine ⟨7889760338098751288736517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10519680450798335051648689 7889760338098751288736517)
                    ·
                      refine ⟨1479330063393515866638097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7889760338098751288736517 1479330063393515866638097)
                      ·
                        rfl

theorem cell23_2880985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_2880985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880985 prefixEnd_2880985 := by exact prefixLift 2880985
  have htrace : WordTrace (prefixWord ++ tailWord_2880985) baseStart_2880985 baseEnd_2880985 := by
    simpa [prefixWord, tailWord_2880985, baseEnd_2880985] using wordTrace_append hprefix tailTrace_2880985
  have hstable : (prefixWord ++ tailWord_2880985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880985).length < 2 ^ (prefixWord ++ tailWord_2880985).sum := by decide
  have hdescent : baseEnd_2880985 < baseStart_2880985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880989 : List Nat := [1, 4, 3, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_2880989 : Nat := 118140960795 + 2880989 * 2 ^ 59
def prefixEnd_2880989 : Nat := 4983230072969 + 3 ^ 40 * 2880989 * 2
def baseEnd_2880989 : Nat := 1479332117316133850988079

theorem tailTrace_2880989 : CollatzResearch.WordTrace tailWord_2880989 prefixEnd_2880989 1479332117316133850988079 := by
  unfold tailWord_2880989
  simp only [CollatzResearch.WordTrace]
  refine ⟨105078301359676361593502021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70052200906450907729001347 105078301359676361593502021)
  ·
    refine ⟨19702181504939317798781629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105078301359676361593502021 19702181504939317798781629)
    ·
      refine ⟨7388318064352244174543111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19702181504939317798781629 7388318064352244174543111)
      ·
        refine ⟨11082477096528366261814667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7388318064352244174543111 11082477096528366261814667)
        ·
          refine ⟨16623715644792549392722001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11082477096528366261814667 16623715644792549392722001)
          ·
            refine ⟨12467786733594412044541501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16623715644792549392722001 12467786733594412044541501)
            ·
              refine ⟨4675420025097904516703063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12467786733594412044541501 4675420025097904516703063)
              ·
                refine ⟨7013130037646856775054595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4675420025097904516703063 7013130037646856775054595)
                ·
                  refine ⟨10519695056470285162581893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7013130037646856775054595 10519695056470285162581893)
                  ·
                    refine ⟨1972442823088178467984105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10519695056470285162581893 1972442823088178467984105)
                    ·
                      refine ⟨1479332117316133850988079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1972442823088178467984105 1479332117316133850988079)
                      ·
                        rfl

theorem cell23_2880989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_2880989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880989 prefixEnd_2880989 := by exact prefixLift 2880989
  have htrace : WordTrace (prefixWord ++ tailWord_2880989) baseStart_2880989 baseEnd_2880989 := by
    simpa [prefixWord, tailWord_2880989, baseEnd_2880989] using wordTrace_append hprefix tailTrace_2880989
  have hstable : (prefixWord ++ tailWord_2880989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880989).length < 2 ^ (prefixWord ++ tailWord_2880989).sum := by decide
  have hdescent : baseEnd_2880989 < baseStart_2880989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880995 : List Nat := [1, 1, 1, 6, 2, 1, 2, 2, 7]
def baseStart_2880995 : Nat := 118140960795 + 2880995 * 2 ^ 59
def prefixEnd_2880995 : Nat := 4983230072969 + 3 ^ 40 * 2880995 * 2
def baseEnd_2880995 : Nat := 164370577577784536390339

theorem tailTrace_2880995 : CollatzResearch.WordTrace tailWord_2880995 prefixEnd_2880995 164370577577784536390339 := by
  unfold tailWord_2880995
  simp only [CollatzResearch.WordTrace]
  refine ⟨105078520197654624618220439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70052346798436416412146959 105078520197654624618220439)
  ·
    refine ⟨157617780296481936927330659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105078520197654624618220439 157617780296481936927330659)
    ·
      refine ⟨236426670444722905390995989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157617780296481936927330659 236426670444722905390995989)
      ·
        refine ⟨11082500177096386190202937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 236426670444722905390995989 11082500177096386190202937)
        ·
          refine ⟨8311875132822289642652203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11082500177096386190202937 8311875132822289642652203)
          ·
            refine ⟨12467812699233434463978305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8311875132822289642652203 12467812699233434463978305)
            ·
              refine ⟨9350859524425075847983729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12467812699233434463978305 9350859524425075847983729)
              ·
                refine ⟨7013144643318806885987797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9350859524425075847983729 7013144643318806885987797)
                ·
                  refine ⟨164370577577784536390339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7013144643318806885987797 164370577577784536390339)
                  ·
                    rfl

theorem cell23_2880995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 7].length) (baseStart_2880995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880995 prefixEnd_2880995 := by exact prefixLift 2880995
  have htrace : WordTrace (prefixWord ++ tailWord_2880995) baseStart_2880995 baseEnd_2880995 := by
    simpa [prefixWord, tailWord_2880995, baseEnd_2880995] using wordTrace_append hprefix tailTrace_2880995
  have hstable : (prefixWord ++ tailWord_2880995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880995).length < 2 ^ (prefixWord ++ tailWord_2880995).sum := by decide
  have hdescent : baseEnd_2880995 < baseStart_2880995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881082 : List Nat := [3, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3]
def baseStart_2881082 : Nat := 118140960795 + 2881082 * 2 ^ 59
def prefixEnd_2881082 : Nat := 4983230072969 + 3 ^ 40 * 2881082 * 2
def baseEnd_2881082 : Nat := 1479379871017001987125151

theorem tailTrace_2881082 : CollatzResearch.WordTrace tailWord_2881082 prefixEnd_2881082 1479379871017001987125151 := by
  unfold tailWord_2881082
  simp only [CollatzResearch.WordTrace]
  refine ⟨26270423337084859619159375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70054462232226292317758333 26270423337084859619159375)
  ·
    refine ⟨39405635005627289428739063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26270423337084859619159375 39405635005627289428739063)
    ·
      refine ⟨59108452508440934143108595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39405635005627289428739063 59108452508440934143108595)
      ·
        refine ⟨88662678762661401214662893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59108452508440934143108595 88662678762661401214662893)
        ·
          refine ⟨33248504535998025455498585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88662678762661401214662893 33248504535998025455498585)
          ·
            refine ⟨24936378401998519091623939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33248504535998025455498585 24936378401998519091623939)
            ·
              refine ⟨37404567602997778637435909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24936378401998519091623939 37404567602997778637435909)
              ·
                refine ⟨7013356425562083494519233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37404567602997778637435909 7013356425562083494519233)
                ·
                  refine ⟨5260017319171562620889425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7013356425562083494519233 5260017319171562620889425)
                  ·
                    refine ⟨3945012989378671965667069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5260017319171562620889425 3945012989378671965667069)
                    ·
                      refine ⟨1479379871017001987125151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3945012989378671965667069 1479379871017001987125151)
                      ·
                        rfl

theorem cell23_2881082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_2881082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881082 prefixEnd_2881082 := by exact prefixLift 2881082
  have htrace : WordTrace (prefixWord ++ tailWord_2881082) baseStart_2881082 baseEnd_2881082 := by
    simpa [prefixWord, tailWord_2881082, baseEnd_2881082] using wordTrace_append hprefix tailTrace_2881082
  have hstable : (prefixWord ++ tailWord_2881082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881082).length < 2 ^ (prefixWord ++ tailWord_2881082).sum := by decide
  have hdescent : baseEnd_2881082 < baseStart_2881082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881110 : List Nat := [5, 2, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_2881110 : Nat := 118140960795 + 2881110 * 2 ^ 59
def prefixEnd_2881110 : Nat := 4983230072969 + 3 ^ 40 * 2881110 * 2
def baseEnd_2881110 : Nat := 493131416158442625858341

theorem tailTrace_2881110 : CollatzResearch.WordTrace tailWord_2881110 prefixEnd_2881110 493131416158442625858341 := by
  unfold tailWord_2881110
  simp only [CollatzResearch.WordTrace]
  refine ⟨6567669662014874953666049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70055143061491999505771189 6567669662014874953666049)
  ·
    refine ⟨4925752246511156215249537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6567669662014874953666049 4925752246511156215249537)
    ·
      refine ⟨3694314184883367161437153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4925752246511156215249537 3694314184883367161437153)
      ·
        refine ⟨2770735638662525371077865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3694314184883367161437153 2770735638662525371077865)
        ·
          refine ⟨2078051728996894028308399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2770735638662525371077865 2078051728996894028308399)
          ·
            refine ⟨3117077593495341042462599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2078051728996894028308399 3117077593495341042462599)
            ·
              refine ⟨4675616390243011563693899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3117077593495341042462599 4675616390243011563693899)
              ·
                refine ⟨7013424585364517345540849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4675616390243011563693899 7013424585364517345540849)
                ·
                  refine ⟨5260068439023388009155637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7013424585364517345540849 5260068439023388009155637)
                  ·
                    refine ⟨493131416158442625858341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5260068439023388009155637 493131416158442625858341)
                    ·
                      rfl

theorem cell23_2881110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_2881110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881110 prefixEnd_2881110 := by exact prefixLift 2881110
  have htrace : WordTrace (prefixWord ++ tailWord_2881110) baseStart_2881110 baseEnd_2881110 := by
    simpa [prefixWord, tailWord_2881110, baseEnd_2881110] using wordTrace_append hprefix tailTrace_2881110
  have hstable : (prefixWord ++ tailWord_2881110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881110).length < 2 ^ (prefixWord ++ tailWord_2881110).sum := by decide
  have hdescent : baseEnd_2881110 < baseStart_2881110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881116 : List Nat := [2, 2, 4, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_2881116 : Nat := 118140960795 + 2881116 * 2 ^ 59
def prefixEnd_2881116 : Nat := 4983230072969 + 3 ^ 40 * 2881116 * 2
def baseEnd_2881116 : Nat := 1479397329359254854099995

theorem tailTrace_2881116 : CollatzResearch.WordTrace tailWord_2881116 prefixEnd_2881116 1479397329359254854099995 := by
  unfold tailWord_2881116
  simp only [CollatzResearch.WordTrace]
  refine ⟨52541466715108131141687601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70055288953477508188916801 52541466715108131141687601)
  ·
    refine ⟨39406100036331098356265701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52541466715108131141687601 39406100036331098356265701)
    ·
      refine ⟨7388643756812080941799819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39406100036331098356265701 7388643756812080941799819)
      ·
        refine ⟨11082965635218121412699729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7388643756812080941799819 11082965635218121412699729)
        ·
          refine ⟨8312224226413591059524797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11082965635218121412699729 8312224226413591059524797)
          ·
            refine ⟨3117084084905096647321799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8312224226413591059524797 3117084084905096647321799)
            ·
              refine ⟨4675626127357644970982699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3117084084905096647321799 4675626127357644970982699)
              ·
                refine ⟨7013439191036467456474049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4675626127357644970982699 7013439191036467456474049)
                ·
                  refine ⟨5260079393277350592355537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7013439191036467456474049 5260079393277350592355537)
                  ·
                    refine ⟨3945059544958012944266653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5260079393277350592355537 3945059544958012944266653)
                    ·
                      refine ⟨1479397329359254854099995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3945059544958012944266653 1479397329359254854099995)
                      ·
                        rfl

theorem cell23_2881116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_2881116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881116 prefixEnd_2881116 := by exact prefixLift 2881116
  have htrace : WordTrace (prefixWord ++ tailWord_2881116) baseStart_2881116 baseEnd_2881116 := by
    simpa [prefixWord, tailWord_2881116, baseEnd_2881116] using wordTrace_append hprefix tailTrace_2881116
  have hstable : (prefixWord ++ tailWord_2881116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881116).length < 2 ^ (prefixWord ++ tailWord_2881116).sum := by decide
  have hdescent : baseEnd_2881116 < baseStart_2881116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881169 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 5, 2, 2]
def baseStart_2881169 : Nat := 118140960795 + 2881169 * 2 ^ 59
def prefixEnd_2881169 : Nat := 4983230072969 + 3 ^ 40 * 2881169 * 2
def baseEnd_2881169 : Nat := 1479424543833943146737251

theorem tailTrace_2881169 : CollatzResearch.WordTrace tailWord_2881169 prefixEnd_2881169 1479424543833943146737251 := by
  unfold tailWord_2881169
  simp only [CollatzResearch.WordTrace]
  refine ⟨105084866499024252335054561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70056577666016168223369707 105084866499024252335054561)
  ·
    refine ⟨78813649874268189251290921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105084866499024252335054561 78813649874268189251290921)
    ·
      refine ⟨59110237405701141938468191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78813649874268189251290921 59110237405701141938468191)
      ·
        refine ⟨88665356108551712907702287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59110237405701141938468191 88665356108551712907702287)
        ·
          refine ⟨132998034162827569361553431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88665356108551712907702287 132998034162827569361553431)
          ·
            refine ⟨199497051244241354042330147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132998034162827569361553431 199497051244241354042330147)
            ·
              refine ⟨299245576866362031063495221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199497051244241354042330147 299245576866362031063495221)
              ·
                refine ⟨28054272831221440412202677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 299245576866362031063495221 28054272831221440412202677)
                ·
                  refine ⟨2630088077927010038644001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28054272831221440412202677 2630088077927010038644001)
                  ·
                    refine ⟨1972566058445257528983001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2630088077927010038644001 1972566058445257528983001)
                    ·
                      refine ⟨1479424543833943146737251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1972566058445257528983001 1479424543833943146737251)
                      ·
                        rfl

theorem cell23_2881169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 2, 2].length) (baseStart_2881169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881169 prefixEnd_2881169 := by exact prefixLift 2881169
  have htrace : WordTrace (prefixWord ++ tailWord_2881169) baseStart_2881169 baseEnd_2881169 := by
    simpa [prefixWord, tailWord_2881169, baseEnd_2881169] using wordTrace_append hprefix tailTrace_2881169
  have hstable : (prefixWord ++ tailWord_2881169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881169).length < 2 ^ (prefixWord ++ tailWord_2881169).sum := by decide
  have hdescent : baseEnd_2881169 < baseStart_2881169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881180 : List Nat := [2, 2, 3, 2, 3, 2, 1, 3, 1, 1, 3]
def baseStart_2881180 : Nat := 118140960795 + 2881180 * 2 ^ 59
def prefixEnd_2881180 : Nat := 4983230072969 + 3 ^ 40 * 2881180 * 2
def baseEnd_2881180 : Nat := 1479430192121142603699701

theorem tailTrace_2881180 : CollatzResearch.WordTrace tailWord_2881180 prefixEnd_2881180 1479430192121142603699701 := by
  unfold tailWord_2881180
  simp only [CollatzResearch.WordTrace]
  refine ⟨52542633850992200606852497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70056845134656267475803329 52542633850992200606852497)
  ·
    refine ⟨39406975388244150455139373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52542633850992200606852497 39406975388244150455139373)
    ·
      refine ⟨14777615770591556420677265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39406975388244150455139373 14777615770591556420677265)
      ·
        refine ⟨11083211827943667315507949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14777615770591556420677265 11083211827943667315507949)
        ·
          refine ⟨4156204435478875243315481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11083211827943667315507949 4156204435478875243315481)
          ·
            refine ⟨3117153326609156432486611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4156204435478875243315481 3117153326609156432486611)
            ·
              refine ⟨4675729989913734648729917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3117153326609156432486611 4675729989913734648729917)
              ·
                refine ⟨1753398746217650493273719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4675729989913734648729917 1753398746217650493273719)
                ·
                  refine ⟨2630098119326475739910579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1753398746217650493273719 2630098119326475739910579)
                  ·
                    refine ⟨3945147178989713609865869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2630098119326475739910579 3945147178989713609865869)
                    ·
                      refine ⟨1479430192121142603699701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3945147178989713609865869 1479430192121142603699701)
                      ·
                        rfl

theorem cell23_2881180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_2881180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881180 prefixEnd_2881180 := by exact prefixLift 2881180
  have htrace : WordTrace (prefixWord ++ tailWord_2881180) baseStart_2881180 baseEnd_2881180 := by
    simpa [prefixWord, tailWord_2881180, baseEnd_2881180] using wordTrace_append hprefix tailTrace_2881180
  have hstable : (prefixWord ++ tailWord_2881180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881180).length < 2 ^ (prefixWord ++ tailWord_2881180).sum := by decide
  have hdescent : baseEnd_2881180 < baseStart_2881180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881189 : List Nat := [1, 3, 1, 2, 1, 2, 4, 3, 1, 2, 3]
def baseStart_2881189 : Nat := 118140960795 + 2881189 * 2 ^ 59
def prefixEnd_2881189 : Nat := 4983230072969 + 3 ^ 40 * 2881189 * 2
def baseEnd_2881189 : Nat := 1479434813447033068487159

theorem tailTrace_2881189 : CollatzResearch.WordTrace tailWord_2881189 prefixEnd_2881189 1479434813447033068487159 := by
  unfold tailWord_2881189
  simp only [CollatzResearch.WordTrace]
  refine ⟨105085595958951795750782621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70057063972634530500521747 105085595958951795750782621)
  ·
    refine ⟨39407098484606923406543483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105085595958951795750782621 39407098484606923406543483)
    ·
      refine ⟨59110647726910385109815225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39407098484606923406543483 59110647726910385109815225)
      ·
        refine ⟨44332985795182788832361419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59110647726910385109815225 44332985795182788832361419)
        ·
          refine ⟨66499478692774183248542129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44332985795182788832361419 66499478692774183248542129)
          ·
            refine ⟨49874609019580637436406597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66499478692774183248542129 49874609019580637436406597)
            ·
              refine ⟨9351489191171369519326237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49874609019580637436406597 9351489191171369519326237)
              ·
                refine ⟨3506808446689263569747339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9351489191171369519326237 3506808446689263569747339)
                ·
                  refine ⟨5260212670033895354621009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3506808446689263569747339 5260212670033895354621009)
                  ·
                    refine ⟨3945159502525421515965757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5260212670033895354621009 3945159502525421515965757)
                    ·
                      refine ⟨1479434813447033068487159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3945159502525421515965757 1479434813447033068487159)
                      ·
                        rfl

theorem cell23_2881189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_2881189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881189 prefixEnd_2881189 := by exact prefixLift 2881189
  have htrace : WordTrace (prefixWord ++ tailWord_2881189) baseStart_2881189 baseEnd_2881189 := by
    simpa [prefixWord, tailWord_2881189, baseEnd_2881189] using wordTrace_append hprefix tailTrace_2881189
  have hstable : (prefixWord ++ tailWord_2881189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881189).length < 2 ^ (prefixWord ++ tailWord_2881189).sum := by decide
  have hdescent : baseEnd_2881189 < baseStart_2881189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881206 : List Nat := [5, 1, 3, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_2881206 : Nat := 118140960795 + 2881206 * 2 ^ 59
def prefixEnd_2881206 : Nat := 4983230072969 + 3 ^ 40 * 2881206 * 2
def baseEnd_2881206 : Nat := 1479443542618159501974581

theorem tailTrace_2881206 : CollatzResearch.WordTrace tailWord_2881206 prefixEnd_2881206 1479443542618159501974581 := by
  unfold tailWord_2881206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6567888499993137978384467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70057477333260138436100981 6567888499993137978384467)
  ·
    refine ⟨9851832749989706967576701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6567888499993137978384467 9851832749989706967576701)
    ·
      refine ⟨3694437281246140112841263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9851832749989706967576701 3694437281246140112841263)
      ·
        refine ⟨5541655921869210169261895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3694437281246140112841263 5541655921869210169261895)
        ·
          refine ⟨8312483882803815253892843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5541655921869210169261895 8312483882803815253892843)
          ·
            refine ⟨12468725824205722880839265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8312483882803815253892843 12468725824205722880839265)
            ·
              refine ⟨9351544368154292160629449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12468725824205722880839265 9351544368154292160629449)
              ·
                refine ⟨7013658276115719120472087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9351544368154292160629449 7013658276115719120472087)
                ·
                  refine ⟨10520487414173578680708131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7013658276115719120472087 10520487414173578680708131)
                  ·
                    refine ⟨15780731121260368021062197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10520487414173578680708131 15780731121260368021062197)
                    ·
                      refine ⟨1479443542618159501974581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15780731121260368021062197 1479443542618159501974581)
                      ·
                        rfl

theorem cell23_2881206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_2881206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881206 prefixEnd_2881206 := by exact prefixLift 2881206
  have htrace : WordTrace (prefixWord ++ tailWord_2881206) baseStart_2881206 baseEnd_2881206 := by
    simpa [prefixWord, tailWord_2881206, baseEnd_2881206] using wordTrace_append hprefix tailTrace_2881206
  have hstable : (prefixWord ++ tailWord_2881206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881206).length < 2 ^ (prefixWord ++ tailWord_2881206).sum := by decide
  have hdescent : baseEnd_2881206 < baseStart_2881206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881236 : List Nat := [2, 4, 1, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_2881236 : Nat := 118140960795 + 2881236 * 2 ^ 59
def prefixEnd_2881236 : Nat := 4983230072969 + 3 ^ 40 * 2881236 * 2
def baseEnd_2881236 : Nat := 1479458947037794384599443

theorem tailTrace_2881236 : CollatzResearch.WordTrace tailWord_2881236 prefixEnd_2881236 1479458947037794384599443 := by
  unfold tailWord_2881236
  simp only [CollatzResearch.WordTrace]
  refine ⟨52543655094890761388871781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70058206793187681851829041 52543655094890761388871781)
  ·
    refine ⟨9851935330292017760413459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52543655094890761388871781 9851935330292017760413459)
    ·
      refine ⟨14777902995438026640620189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9851935330292017760413459 14777902995438026640620189)
      ·
        refine ⟨5541713623289259990232571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14777902995438026640620189 5541713623289259990232571)
        ·
          refine ⟨8312570434933889985348857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5541713623289259990232571 8312570434933889985348857)
          ·
            refine ⟨6234427826200417489011643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8312570434933889985348857 6234427826200417489011643)
            ·
              refine ⟨9351641739300626233517465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6234427826200417489011643 9351641739300626233517465)
              ·
                refine ⟨7013731304475469675138099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9351641739300626233517465 7013731304475469675138099)
                ·
                  refine ⟨10520596956713204512707149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7013731304475469675138099 10520596956713204512707149)
                  ·
                    refine ⟨3945223858767451692265181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10520596956713204512707149 3945223858767451692265181)
                    ·
                      refine ⟨1479458947037794384599443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3945223858767451692265181 1479458947037794384599443)
                      ·
                        rfl

theorem cell23_2881236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_2881236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881236 prefixEnd_2881236 := by exact prefixLift 2881236
  have htrace : WordTrace (prefixWord ++ tailWord_2881236) baseStart_2881236 baseEnd_2881236 := by
    simpa [prefixWord, tailWord_2881236, baseEnd_2881236] using wordTrace_append hprefix tailTrace_2881236
  have hstable : (prefixWord ++ tailWord_2881236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881236).length < 2 ^ (prefixWord ++ tailWord_2881236).sum := by decide
  have hdescent : baseEnd_2881236 < baseStart_2881236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881252 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 2, 6]
def baseStart_2881252 : Nat := 118140960795 + 2881252 * 2 ^ 59
def prefixEnd_2881252 : Nat := 4983230072969 + 3 ^ 40 * 2881252 * 2
def baseEnd_2881252 : Nat := 493155720909422107333123

theorem tailTrace_2881252 : CollatzResearch.WordTrace tailWord_2881252 prefixEnd_2881252 493155720909422107333123 := by
  unfold tailWord_2881252
  simp only [CollatzResearch.WordTrace]
  refine ⟨52543946878861778755163005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70058595838482371673550673 52543946878861778755163005)
  ·
    refine ⟨19703980079573167033186127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52543946878861778755163005 19703980079573167033186127)
    ·
      refine ⟨29555970119359750549779191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19703980079573167033186127 29555970119359750549779191)
      ·
        refine ⟨44333955179039625824668787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29555970119359750549779191 44333955179039625824668787)
        ·
          refine ⟨66500932768559438737003181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44333955179039625824668787 66500932768559438737003181)
          ·
            refine ⟨24937849788209789526376193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66500932768559438737003181 24937849788209789526376193)
            ·
              refine ⟨18703387341157342144782145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24937849788209789526376193 18703387341157342144782145)
              ·
                refine ⟨14027540505868006608586609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18703387341157342144782145 14027540505868006608586609)
                ·
                  refine ⟨10520655379401004956439957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14027540505868006608586609 10520655379401004956439957)
                  ·
                    refine ⟨493155720909422107333123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10520655379401004956439957 493155720909422107333123)
                    ·
                      rfl

theorem cell23_2881252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_2881252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881252 prefixEnd_2881252 := by exact prefixLift 2881252
  have htrace : WordTrace (prefixWord ++ tailWord_2881252) baseStart_2881252 baseEnd_2881252 := by
    simpa [prefixWord, tailWord_2881252, baseEnd_2881252] using wordTrace_append hprefix tailTrace_2881252
  have hstable : (prefixWord ++ tailWord_2881252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881252).length < 2 ^ (prefixWord ++ tailWord_2881252).sum := by decide
  have hdescent : baseEnd_2881252 < baseStart_2881252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881276 : List Nat := [2, 2, 2, 1, 3, 1, 4, 1, 1, 4, 2]
def baseStart_2881276 : Nat := 118140960795 + 2881276 * 2 ^ 59
def prefixEnd_2881276 : Nat := 4983230072969 + 3 ^ 40 * 2881276 * 2
def baseEnd_2881276 : Nat := 1479479486263974228099259

theorem tailTrace_2881276 : CollatzResearch.WordTrace tailWord_2881276 prefixEnd_2881276 1479479486263974228099259 := by
  unfold tailWord_2881276
  simp only [CollatzResearch.WordTrace]
  refine ⟨52544384554818304804599841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70059179406424406406133121 52544384554818304804599841)
  ·
    refine ⟨39408288416113728603449881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52544384554818304804599841 39408288416113728603449881)
    ·
      refine ⟨29556216312085296452587411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39408288416113728603449881 29556216312085296452587411)
      ·
        refine ⟨44334324468127944678881117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29556216312085296452587411 44334324468127944678881117)
        ·
          refine ⟨16625371675547979254580419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44334324468127944678881117 16625371675547979254580419)
          ·
            refine ⟨24938057513321968881870629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16625371675547979254580419 24938057513321968881870629)
            ·
              refine ⟨4675885783747869165350743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24938057513321968881870629 4675885783747869165350743)
              ·
                refine ⟨7013828675621803748026115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4675885783747869165350743 7013828675621803748026115)
                ·
                  refine ⟨10520743013432705622039173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7013828675621803748026115 10520743013432705622039173)
                  ·
                    refine ⟨1972639315018632304132345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10520743013432705622039173 1972639315018632304132345)
                    ·
                      refine ⟨1479479486263974228099259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1972639315018632304132345 1479479486263974228099259)
                      ·
                        rfl

theorem cell23_2881276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_2881276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881276 prefixEnd_2881276 := by exact prefixLift 2881276
  have htrace : WordTrace (prefixWord ++ tailWord_2881276) baseStart_2881276 baseEnd_2881276 := by
    simpa [prefixWord, tailWord_2881276, baseEnd_2881276] using wordTrace_append hprefix tailTrace_2881276
  have hstable : (prefixWord ++ tailWord_2881276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881276).length < 2 ^ (prefixWord ++ tailWord_2881276).sum := by decide
  have hdescent : baseEnd_2881276 < baseStart_2881276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881316 : List Nat := [2, 3, 1, 3, 2, 1, 2, 4, 5]
def baseStart_2881316 : Nat := 118140960795 + 2881316 * 2 ^ 59
def prefixEnd_2881316 : Nat := 4983230072969 + 3 ^ 40 * 2881316 * 2
def baseEnd_2881316 : Nat := 164388891721128230177675

theorem tailTrace_2881316 : CollatzResearch.WordTrace tailWord_2881316 prefixEnd_2881316 164388891721128230177675 := by
  unfold tailWord_2881316
  simp only [CollatzResearch.WordTrace]
  refine ⟨52545114014745848220327901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70060152019661130960437201 52545114014745848220327901)
  ·
    refine ⟨19704417755529693082622963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52545114014745848220327901 19704417755529693082622963)
    ·
      refine ⟨29556626633294539623934445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19704417755529693082622963 29556626633294539623934445)
      ·
        refine ⟨11083734987485452358975417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29556626633294539623934445 11083734987485452358975417)
        ·
          refine ⟨8312801240614089269231563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11083734987485452358975417 8312801240614089269231563)
          ·
            refine ⟨12469201860921133903847345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8312801240614089269231563 12469201860921133903847345)
            ·
              refine ⟨9351901395690850427885509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12469201860921133903847345 9351901395690850427885509)
              ·
                refine ⟨1753481511692034455228533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9351901395690850427885509 1753481511692034455228533)
                ·
                  refine ⟨164388891721128230177675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1753481511692034455228533 164388891721128230177675)
                  ·
                    rfl

theorem cell23_2881316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_2881316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881316 prefixEnd_2881316 := by exact prefixLift 2881316
  have htrace : WordTrace (prefixWord ++ tailWord_2881316) baseStart_2881316 baseEnd_2881316 := by
    simpa [prefixWord, tailWord_2881316, baseEnd_2881316] using wordTrace_append hprefix tailTrace_2881316
  have hstable : (prefixWord ++ tailWord_2881316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881316).length < 2 ^ (prefixWord ++ tailWord_2881316).sum := by decide
  have hdescent : baseEnd_2881316 < baseStart_2881316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881349 : List Nat := [1, 3, 1, 1, 1, 2, 4, 3, 2, 1, 4]
def baseStart_2881349 : Nat := 118140960795 + 2881349 * 2 ^ 59
def prefixEnd_2881349 : Nat := 4983230072969 + 3 ^ 40 * 2881349 * 2
def baseEnd_2881349 : Nat := 1479516970351752442486423

theorem tailTrace_2881349 : CollatzResearch.WordTrace tailWord_2881349 prefixEnd_2881349 1479516970351752442486423 := by
  unfold tailWord_2881349
  simp only [CollatzResearch.WordTrace]
  refine ⟨105091431638372143076607101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70060954425581428717738067 105091431638372143076607101)
  ·
    refine ⟨39409286864389553653727663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105091431638372143076607101 39409286864389553653727663)
    ·
      refine ⟨59113930296584330480591495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39409286864389553653727663 59113930296584330480591495)
      ·
        refine ⟨88670895444876495720887243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59113930296584330480591495 88670895444876495720887243)
        ·
          refine ⟨133006343167314743581330865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88670895444876495720887243 133006343167314743581330865)
          ·
            refine ⟨99754757375486057685998149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133006343167314743581330865 99754757375486057685998149)
            ·
              refine ⟨18704017007903635816124653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99754757375486057685998149 18704017007903635816124653)
              ·
                refine ⟨7014006377963863431046745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18704017007903635816124653 7014006377963863431046745)
                ·
                  refine ⟨5260504783472897573285059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7014006377963863431046745 5260504783472897573285059)
                  ·
                    refine ⟨7890757175209346359927589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5260504783472897573285059 7890757175209346359927589)
                    ·
                      refine ⟨1479516970351752442486423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7890757175209346359927589 1479516970351752442486423)
                      ·
                        rfl

theorem cell23_2881349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_2881349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881349 prefixEnd_2881349 := by exact prefixLift 2881349
  have htrace : WordTrace (prefixWord ++ tailWord_2881349) baseStart_2881349 baseEnd_2881349 := by
    simpa [prefixWord, tailWord_2881349, baseEnd_2881349] using wordTrace_append hprefix tailTrace_2881349
  have hstable : (prefixWord ++ tailWord_2881349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881349).length < 2 ^ (prefixWord ++ tailWord_2881349).sum := by decide
  have hdescent : baseEnd_2881349 < baseStart_2881349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881350 : List Nat := [6, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_2881350 : Nat := 118140960795 + 2881350 * 2 ^ 59
def prefixEnd_2881350 : Nat := 4983230072969 + 3 ^ 40 * 2881350 * 2
def baseEnd_2881350 : Nat := 164390831536934104285991

theorem tailTrace_2881350 : CollatzResearch.WordTrace tailWord_2881350 prefixEnd_2881350 164390831536934104285991 := by
  unfold tailWord_2881350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3284108378480266257731047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70060978740912346831595669 3284108378480266257731047)
  ·
    refine ⟨4926162567720399386596571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3284108378480266257731047 4926162567720399386596571)
    ·
      refine ⟨7389243851580599079894857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4926162567720399386596571 7389243851580599079894857)
      ·
        refine ⟨5541932888685449309921143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7389243851580599079894857 5541932888685449309921143)
        ·
          refine ⟨8312899333028173964881715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5541932888685449309921143 8312899333028173964881715)
          ·
            refine ⟨12469348999542260947322573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8312899333028173964881715 12469348999542260947322573)
            ·
              refine ⟨4676005874828347855245965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12469348999542260947322573 4676005874828347855245965)
              ·
                refine ⟨1753502203060630445717237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4676005874828347855245965 1753502203060630445717237)
                ·
                  refine ⟨164390831536934104285991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1753502203060630445717237 164390831536934104285991)
                  ·
                    rfl

theorem cell23_2881350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_2881350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881350 prefixEnd_2881350 := by exact prefixLift 2881350
  have htrace : WordTrace (prefixWord ++ tailWord_2881350) baseStart_2881350 baseEnd_2881350 := by
    simpa [prefixWord, tailWord_2881350, baseEnd_2881350] using wordTrace_append hprefix tailTrace_2881350
  have hstable : (prefixWord ++ tailWord_2881350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881350).length < 2 ^ (prefixWord ++ tailWord_2881350).sum := by decide
  have hdescent : baseEnd_2881350 < baseStart_2881350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881376 : List Nat := [2, 1, 1, 3, 3, 2, 3, 1, 3, 4]
def baseStart_2881376 : Nat := 118140960795 + 2881376 * 2 ^ 59
def prefixEnd_2881376 : Nat := 4983230072969 + 3 ^ 40 * 2881376 * 2
def baseEnd_2881376 : Nat := 493176944776474612282933

theorem tailTrace_2881376 : CollatzResearch.WordTrace tailWord_2881376 prefixEnd_2881376 493176944776474612282933 := by
  unfold tailWord_2881376
  simp only [CollatzResearch.WordTrace]
  refine ⟨52546208204637163343919991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70061610939516217791893321 52546208204637163343919991)
  ·
    refine ⟨78819312306955745015879987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52546208204637163343919991 78819312306955745015879987)
    ·
      refine ⟨118228968460433617523819981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78819312306955745015879987 118228968460433617523819981)
      ·
        refine ⟨44335863172662606571432493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118228968460433617523819981 44335863172662606571432493)
        ·
          refine ⟨16625948689748477464287185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44335863172662606571432493 16625948689748477464287185)
          ·
            refine ⟨12469461517311358098215389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16625948689748477464287185 12469461517311358098215389)
            ·
              refine ⟨4676048068991759286830771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12469461517311358098215389 4676048068991759286830771)
              ·
                refine ⟨7014072103487638930246157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4676048068991759286830771 7014072103487638930246157)
                ·
                  refine ⟨2630277038807864598842309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7014072103487638930246157 2630277038807864598842309)
                  ·
                    refine ⟨493176944776474612282933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2630277038807864598842309 493176944776474612282933)
                    ·
                      rfl

theorem cell23_2881376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 3, 4].length) (baseStart_2881376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881376 prefixEnd_2881376 := by exact prefixLift 2881376
  have htrace : WordTrace (prefixWord ++ tailWord_2881376) baseStart_2881376 baseEnd_2881376 := by
    simpa [prefixWord, tailWord_2881376, baseEnd_2881376] using wordTrace_append hprefix tailTrace_2881376
  have hstable : (prefixWord ++ tailWord_2881376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881376).length < 2 ^ (prefixWord ++ tailWord_2881376).sum := by decide
  have hdescent : baseEnd_2881376 < baseStart_2881376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881436 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 3, 5]
def baseStart_2881436 : Nat := 118140960795 + 2881436 * 2 ^ 59
def prefixEnd_2881436 : Nat := 4983230072969 + 3 ^ 40 * 2881436 * 2
def baseEnd_2881436 : Nat := 493187214389564534032841

theorem tailTrace_2881436 : CollatzResearch.WordTrace tailWord_2881436 prefixEnd_2881436 493187214389564534032841 := by
  unfold tailWord_2881436
  simp only [CollatzResearch.WordTrace]
  refine ⟨52547302394528478467512081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70063069859371304623349441 52547302394528478467512081)
  ·
    refine ⟨39410476795896358850634061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52547302394528478467512081 39410476795896358850634061)
    ·
      refine ⟨14778928798461134568987773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39410476795896358850634061 14778928798461134568987773)
      ·
        refine ⟨5542098299422925463370415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14778928798461134568987773 5542098299422925463370415)
        ·
          refine ⟨8313147449134388195055623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5542098299422925463370415 8313147449134388195055623)
          ·
            refine ⟨12469721173701582292583435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8313147449134388195055623 12469721173701582292583435)
            ·
              refine ⟨18704581760552373438875153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12469721173701582292583435 18704581760552373438875153)
              ·
                refine ⟨14028436320414280079156365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18704581760552373438875153 14028436320414280079156365)
                ·
                  refine ⟨5260663620155355029683637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14028436320414280079156365 5260663620155355029683637)
                  ·
                    refine ⟨493187214389564534032841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5260663620155355029683637 493187214389564534032841)
                    ·
                      rfl

theorem cell23_2881436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_2881436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881436 prefixEnd_2881436 := by exact prefixLift 2881436
  have htrace : WordTrace (prefixWord ++ tailWord_2881436) baseStart_2881436 baseEnd_2881436 := by
    simpa [prefixWord, tailWord_2881436, baseEnd_2881436] using wordTrace_append hprefix tailTrace_2881436
  have hstable : (prefixWord ++ tailWord_2881436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881436).length < 2 ^ (prefixWord ++ tailWord_2881436).sum := by decide
  have hdescent : baseEnd_2881436 < baseStart_2881436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881454 : List Nat := [4, 1, 5, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_2881454 : Nat := 118140960795 + 2881454 * 2 ^ 59
def prefixEnd_2881454 : Nat := 4983230072969 + 3 ^ 40 * 2881454 * 2
def baseEnd_2881454 : Nat := 1479570885820474531673441

theorem tailTrace_2881454 : CollatzResearch.WordTrace tailWord_2881454 prefixEnd_2881454 1479570885820474531673441 := by
  unfold tailWord_2881454
  simp only [CollatzResearch.WordTrace]
  refine ⟨13136907662873968251147427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70063507535327830672786277 13136907662873968251147427)
  ·
    refine ⟨19705361494310952376721141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13136907662873968251147427 19705361494310952376721141)
    ·
      refine ⟨1847377640091651785317607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19705361494310952376721141 1847377640091651785317607)
      ·
        refine ⟨2771066460137477677976411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1847377640091651785317607 2771066460137477677976411)
        ·
          refine ⟨4156599690206216516964617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2771066460137477677976411 4156599690206216516964617)
          ·
            refine ⟨3117449767654662387723463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4156599690206216516964617 3117449767654662387723463)
            ·
              refine ⟨4676174651481993581585195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3117449767654662387723463 4676174651481993581585195)
              ·
                refine ⟨7014261977222990372377793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4676174651481993581585195 7014261977222990372377793)
                ·
                  refine ⟨5260696482917242779283345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7014261977222990372377793 5260696482917242779283345)
                  ·
                    refine ⟨3945522362187932084462509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5260696482917242779283345 3945522362187932084462509)
                    ·
                      refine ⟨1479570885820474531673441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3945522362187932084462509 1479570885820474531673441)
                      ·
                        rfl

theorem cell23_2881454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_2881454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881454 prefixEnd_2881454 := by exact prefixLift 2881454
  have htrace : WordTrace (prefixWord ++ tailWord_2881454) baseStart_2881454 baseEnd_2881454 := by
    simpa [prefixWord, tailWord_2881454, baseEnd_2881454] using wordTrace_append hprefix tailTrace_2881454
  have hstable : (prefixWord ++ tailWord_2881454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881454).length < 2 ^ (prefixWord ++ tailWord_2881454).sum := by decide
  have hdescent : baseEnd_2881454 < baseStart_2881454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881470 : List Nat := [4, 2, 1, 1, 1, 5, 2, 1, 1, 5]
def baseStart_2881470 : Nat := 118140960795 + 2881470 * 2 ^ 59
def prefixEnd_2881470 : Nat := 4983230072969 + 3 ^ 40 * 2881470 * 2
def baseEnd_2881470 : Nat := 493193033836982156357789

theorem tailTrace_2881470 : CollatzResearch.WordTrace tailWord_2881470 prefixEnd_2881470 493193033836982156357789 := by
  unfold tailWord_2881470
  simp only [CollatzResearch.WordTrace]
  refine ⟨13136980608866722592720233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70063896580622520494507909 13136980608866722592720233)
  ·
    refine ⟨9852735456650041944540175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13136980608866722592720233 9852735456650041944540175)
    ·
      refine ⟨14779103184975062916810263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9852735456650041944540175 14779103184975062916810263)
      ·
        refine ⟨22168654777462594375215395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14779103184975062916810263 22168654777462594375215395)
        ·
          refine ⟨33252982166193891562823093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22168654777462594375215395 33252982166193891562823093)
          ·
            refine ⟨3117467078080677334014665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33252982166193891562823093 3117467078080677334014665)
            ·
              refine ⟨2338100308560508000510999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3117467078080677334014665 2338100308560508000510999)
              ·
                refine ⟨3507150462840762000766499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2338100308560508000510999 3507150462840762000766499)
                ·
                  refine ⟨5260725694261143001149749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3507150462840762000766499 5260725694261143001149749)
                  ·
                    refine ⟨493193033836982156357789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5260725694261143001149749 493193033836982156357789)
                    ·
                      rfl

theorem cell23_2881470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_2881470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881470 prefixEnd_2881470 := by exact prefixLift 2881470
  have htrace : WordTrace (prefixWord ++ tailWord_2881470) baseStart_2881470 baseEnd_2881470 := by
    simpa [prefixWord, tailWord_2881470, baseEnd_2881470] using wordTrace_append hprefix tailTrace_2881470
  have hstable : (prefixWord ++ tailWord_2881470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881470).length < 2 ^ (prefixWord ++ tailWord_2881470).sum := by decide
  have hdescent : baseEnd_2881470 < baseStart_2881470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881503 : List Nat := [1, 1, 2, 3, 4, 3, 1, 1, 1, 2, 4]
def baseStart_2881503 : Nat := 118140960795 + 2881503 * 2 ^ 59
def prefixEnd_2881503 : Nat := 4983230072969 + 3 ^ 40 * 2881503 * 2
def baseEnd_2881503 : Nat := 1479596046372544839960715

theorem tailTrace_2881503 : CollatzResearch.WordTrace tailWord_2881503 prefixEnd_2881503 1479596046372544839960715 := by
  unfold tailWord_2881503
  simp only [CollatzResearch.WordTrace]
  refine ⟨105097048479814227377713163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70064698986542818251808775 105097048479814227377713163)
  ·
    refine ⟨157645572719721341066569745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105097048479814227377713163 157645572719721341066569745)
    ·
      refine ⟨118234179539791005799927309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157645572719721341066569745 118234179539791005799927309)
      ·
        refine ⟨44337817327421627174972741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118234179539791005799927309 44337817327421627174972741)
        ·
          refine ⟨8313340748891555095307389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44337817327421627174972741 8313340748891555095307389)
          ·
            refine ⟨3117502780834333160740271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8313340748891555095307389 3117502780834333160740271)
            ·
              refine ⟨4676254171251499741110407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3117502780834333160740271 4676254171251499741110407)
              ·
                refine ⟨7014381256877249611665611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4676254171251499741110407 7014381256877249611665611)
                ·
                  refine ⟨10521571885315874417498417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7014381256877249611665611 10521571885315874417498417)
                  ·
                    refine ⟨7891178913986905813123813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10521571885315874417498417 7891178913986905813123813)
                    ·
                      refine ⟨1479596046372544839960715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7891178913986905813123813 1479596046372544839960715)
                      ·
                        rfl

theorem cell23_2881503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_2881503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881503 prefixEnd_2881503 := by exact prefixLift 2881503
  have htrace : WordTrace (prefixWord ++ tailWord_2881503) baseStart_2881503 baseEnd_2881503 := by
    simpa [prefixWord, tailWord_2881503, baseEnd_2881503] using wordTrace_append hprefix tailTrace_2881503
  have hstable : (prefixWord ++ tailWord_2881503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881503).length < 2 ^ (prefixWord ++ tailWord_2881503).sum := by decide
  have hdescent : baseEnd_2881503 < baseStart_2881503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881516 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 2, 7, 2]
def baseStart_2881516 : Nat := 118140960795 + 2881516 * 2 ^ 59
def prefixEnd_2881516 : Nat := 4983230072969 + 3 ^ 40 * 2881516 * 2
def baseEnd_2881516 : Nat := 1479602721621053289098155

theorem tailTrace_2881516 : CollatzResearch.WordTrace tailWord_2881516 prefixEnd_2881516 1479602721621053289098155 := by
  unfold tailWord_2881516
  simp only [CollatzResearch.WordTrace]
  refine ⟨52548761314383565298968201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70065015085844753731957601 52548761314383565298968201)
  ·
    refine ⟨39411570985787673974226151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52548761314383565298968201 39411570985787673974226151)
    ·
      refine ⟨59117356478681510961339227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39411570985787673974226151 59117356478681510961339227)
      ·
        refine ⟨88676034718022266442008841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59117356478681510961339227 88676034718022266442008841)
        ·
          refine ⟨66507026038516699831506631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88676034718022266442008841 66507026038516699831506631)
          ·
            refine ⟨99760539057775049747259947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66507026038516699831506631 99760539057775049747259947)
            ·
              refine ⟨149640808586662574620889921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99760539057775049747259947 149640808586662574620889921)
              ·
                refine ⟨112230606439996930965667441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149640808586662574620889921 112230606439996930965667441)
                ·
                  refine ⟨84172954829997698224250581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112230606439996930965667441 84172954829997698224250581)
                  ·
                    refine ⟨1972803628828071052130873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 84172954829997698224250581 1972803628828071052130873)
                    ·
                      refine ⟨1479602721621053289098155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1972803628828071052130873 1479602721621053289098155)
                      ·
                        rfl

theorem cell23_2881516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 7, 2].length) (baseStart_2881516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881516 prefixEnd_2881516 := by exact prefixLift 2881516
  have htrace : WordTrace (prefixWord ++ tailWord_2881516) baseStart_2881516 baseEnd_2881516 := by
    simpa [prefixWord, tailWord_2881516, baseEnd_2881516] using wordTrace_append hprefix tailTrace_2881516
  have hstable : (prefixWord ++ tailWord_2881516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881516).length < 2 ^ (prefixWord ++ tailWord_2881516).sum := by decide
  have hdescent : baseEnd_2881516 < baseStart_2881516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881519 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 5]
def baseStart_2881519 : Nat := 118140960795 + 2881519 * 2 ^ 59
def prefixEnd_2881519 : Nat := 4983230072969 + 3 ^ 40 * 2881519 * 2
def baseEnd_2881519 : Nat := 1479604262063016777360641

theorem tailTrace_2881519 : CollatzResearch.WordTrace tailWord_2881519 prefixEnd_2881519 1479604262063016777360641 := by
  unfold tailWord_2881519
  simp only [CollatzResearch.WordTrace]
  refine ⟨105097632047756262110295611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70065088031837508073530407 105097632047756262110295611)
  ·
    refine ⟨157646448071634393165443417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105097632047756262110295611 157646448071634393165443417)
    ·
      refine ⟨118234836053725794874082563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157646448071634393165443417 118234836053725794874082563)
      ·
        refine ⟨177352254080588692311123845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118234836053725794874082563 177352254080588692311123845)
        ·
          refine ⟨33253547640110379808335721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177352254080588692311123845 33253547640110379808335721)
          ·
            refine ⟨24940160730082784856251791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33253547640110379808335721 24940160730082784856251791)
            ·
              refine ⟨37410241095124177284377687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24940160730082784856251791 37410241095124177284377687)
              ·
                refine ⟨56115361642686265926566531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37410241095124177284377687 56115361642686265926566531)
                ·
                  refine ⟨84173042464029398889849797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56115361642686265926566531 84173042464029398889849797)
                  ·
                    refine ⟨15782445462005512291846837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84173042464029398889849797 15782445462005512291846837)
                    ·
                      refine ⟨1479604262063016777360641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15782445462005512291846837 1479604262063016777360641)
                      ·
                        rfl

theorem cell23_2881519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_2881519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881519 prefixEnd_2881519 := by exact prefixLift 2881519
  have htrace : WordTrace (prefixWord ++ tailWord_2881519) baseStart_2881519 baseEnd_2881519 := by
    simpa [prefixWord, tailWord_2881519, baseEnd_2881519] using wordTrace_append hprefix tailTrace_2881519
  have hstable : (prefixWord ++ tailWord_2881519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881519).length < 2 ^ (prefixWord ++ tailWord_2881519).sum := by decide
  have hdescent : baseEnd_2881519 < baseStart_2881519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881539 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 4, 6]
def baseStart_2881539 : Nat := 118140960795 + 2881539 * 2 ^ 59
def prefixEnd_2881539 : Nat := 4983230072969 + 3 ^ 40 * 2881539 * 2
def baseEnd_2881539 : Nat := 493204843892035566370183

theorem tailTrace_2881539 : CollatzResearch.WordTrace tailWord_2881539 prefixEnd_2881539 493204843892035566370183 := by
  unfold tailWord_2881539
  simp only [CollatzResearch.WordTrace]
  refine ⟨105098361507683805526023671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70065574338455870350682447 105098361507683805526023671)
  ·
    refine ⟨157647542261525708289035507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105098361507683805526023671 157647542261525708289035507)
    ·
      refine ⟨236471313392288562433553261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157647542261525708289035507 236471313392288562433553261)
      ·
        refine ⟨88676742522108210912582473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236471313392288562433553261 88676742522108210912582473)
        ·
          refine ⟨66507556891581158184436855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88676742522108210912582473 66507556891581158184436855)
          ·
            refine ⟨99761335337371737276655283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66507556891581158184436855 99761335337371737276655283)
            ·
              refine ⟨149642003006057605914982925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99761335337371737276655283 149642003006057605914982925)
              ·
                refine ⟨56115751127271602218118597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149642003006057605914982925 56115751127271602218118597)
                ·
                  refine ⟨10521703336363425415897237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56115751127271602218118597 10521703336363425415897237)
                  ·
                    refine ⟨493204843892035566370183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10521703336363425415897237 493204843892035566370183)
                    ·
                      rfl

theorem cell23_2881539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 6].length) (baseStart_2881539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881539 prefixEnd_2881539 := by exact prefixLift 2881539
  have htrace : WordTrace (prefixWord ++ tailWord_2881539) baseStart_2881539 baseEnd_2881539 := by
    simpa [prefixWord, tailWord_2881539, baseEnd_2881539] using wordTrace_append hprefix tailTrace_2881539
  have hstable : (prefixWord ++ tailWord_2881539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881539).length < 2 ^ (prefixWord ++ tailWord_2881539).sum := by decide
  have hdescent : baseEnd_2881539 < baseStart_2881539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881563 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 6, 2, 2]
def baseStart_2881563 : Nat := 118140960795 + 2881563 * 2 ^ 59
def prefixEnd_2881563 : Nat := 4983230072969 + 3 ^ 40 * 2881563 * 2
def baseEnd_2881563 : Nat := 1479626855211814605210439

theorem tailTrace_2881563 : CollatzResearch.WordTrace tailWord_2881563 prefixEnd_2881563 1479626855211814605210439 := by
  unfold tailWord_2881563
  simp only [CollatzResearch.WordTrace]
  refine ⟨105099236859596857624897343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70066157906397905083264895 105099236859596857624897343)
  ·
    refine ⟨157648855289395286437346015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105099236859596857624897343 157648855289395286437346015)
    ·
      refine ⟨236473282934092929656019023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157648855289395286437346015 236473282934092929656019023)
      ·
        refine ⟨354709924401139394484028535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236473282934092929656019023 354709924401139394484028535)
        ·
          refine ⟨532064886601709091726042803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354709924401139394484028535 532064886601709091726042803)
          ·
            refine ⟨798097329902563637589064205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532064886601709091726042803 798097329902563637589064205)
            ·
              refine ⟨299286498713461364095899077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 798097329902563637589064205 299286498713461364095899077)
              ·
                refine ⟨56116218508774005767981077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 299286498713461364095899077 56116218508774005767981077)
                ·
                  refine ⟨2630447742598781520374113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56116218508774005767981077 2630447742598781520374113)
                  ·
                    refine ⟨1972835806949086140280585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2630447742598781520374113 1972835806949086140280585)
                    ·
                      refine ⟨1479626855211814605210439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1972835806949086140280585 1479626855211814605210439)
                      ·
                        rfl

theorem cell23_2881563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 2, 2].length) (baseStart_2881563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881563 prefixEnd_2881563 := by exact prefixLift 2881563
  have htrace : WordTrace (prefixWord ++ tailWord_2881563) baseStart_2881563 baseEnd_2881563 := by
    simpa [prefixWord, tailWord_2881563, baseEnd_2881563] using wordTrace_append hprefix tailTrace_2881563
  have hstable : (prefixWord ++ tailWord_2881563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881563).length < 2 ^ (prefixWord ++ tailWord_2881563).sum := by decide
  have hdescent : baseEnd_2881563 < baseStart_2881563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881579 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 7]
def baseStart_2881579 : Nat := 118140960795 + 2881579 * 2 ^ 59
def prefixEnd_2881579 : Nat := 4983230072969 + 3 ^ 40 * 2881579 * 2
def baseEnd_2881579 : Nat := 1479635070902286542610365

theorem tailTrace_2881579 : CollatzResearch.WordTrace tailWord_2881579 prefixEnd_2881579 1479635070902286542610365 := by
  unfold tailWord_2881579
  simp only [CollatzResearch.WordTrace]
  refine ⟨105099820427538892357479791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70066546951692594904986527 105099820427538892357479791)
  ·
    refine ⟨157649730641308338536219687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105099820427538892357479791 157649730641308338536219687)
    ·
      refine ⟨236474595961962507804329531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157649730641308338536219687 236474595961962507804329531)
      ·
        refine ⟨354711893942943761706494297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236474595961962507804329531 354711893942943761706494297)
        ·
          refine ⟨266033920457207821279870723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354711893942943761706494297 266033920457207821279870723)
          ·
            refine ⟨399050880685811731919806085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266033920457207821279870723 399050880685811731919806085)
            ·
              refine ⟨74822040128589699734963641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 399050880685811731919806085 74822040128589699734963641)
              ·
                refine ⟨56116530096442274801222731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74822040128589699734963641 56116530096442274801222731)
                ·
                  refine ⟨84174795144663412201834097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56116530096442274801222731 84174795144663412201834097)
                  ·
                    refine ⟨63131096358497559151375573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84174795144663412201834097 63131096358497559151375573)
                    ·
                      refine ⟨1479635070902286542610365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63131096358497559151375573 1479635070902286542610365)
                      ·
                        rfl

theorem cell23_2881579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 7].length) (baseStart_2881579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881579 prefixEnd_2881579 := by exact prefixLift 2881579
  have htrace : WordTrace (prefixWord ++ tailWord_2881579) baseStart_2881579 baseEnd_2881579 := by
    simpa [prefixWord, tailWord_2881579, baseEnd_2881579] using wordTrace_append hprefix tailTrace_2881579
  have hstable : (prefixWord ++ tailWord_2881579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881579).length < 2 ^ (prefixWord ++ tailWord_2881579).sum := by decide
  have hdescent : baseEnd_2881579 < baseStart_2881579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881597 : List Nat := [1, 4, 1, 3, 1, 1, 4, 2, 2, 2, 2]
def baseStart_2881597 : Nat := 118140960795 + 2881597 * 2 ^ 59
def prefixEnd_2881597 : Nat := 4983230072969 + 3 ^ 40 * 2881597 * 2
def baseEnd_2881597 : Nat := 1479644313554067472185283

theorem tailTrace_2881597 : CollatzResearch.WordTrace tailWord_2881597 prefixEnd_2881597 1479644313554067472185283 := by
  unfold tailWord_2881597
  simp only [CollatzResearch.WordTrace]
  refine ⟨105100476941473681431635045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70066984627649120954423363 105100476941473681431635045)
  ·
    refine ⟨19706339426526315268431571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105100476941473681431635045 19706339426526315268431571)
    ·
      refine ⟨29559509139789472902647357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19706339426526315268431571 29559509139789472902647357)
      ·
        refine ⟨11084815927421052338492759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29559509139789472902647357 11084815927421052338492759)
        ·
          refine ⟨16627223891131578507739139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11084815927421052338492759 16627223891131578507739139)
          ·
            refine ⟨24940835836697367761608709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16627223891131578507739139 24940835836697367761608709)
            ·
              refine ⟨4676406719380756455301633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24940835836697367761608709 4676406719380756455301633)
              ·
                refine ⟨3507305039535567341476225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4676406719380756455301633 3507305039535567341476225)
                ·
                  refine ⟨2630478779651675506107169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3507305039535567341476225 2630478779651675506107169)
                  ·
                    refine ⟨1972859084738756629580377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2630478779651675506107169 1972859084738756629580377)
                    ·
                      refine ⟨1479644313554067472185283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1972859084738756629580377 1479644313554067472185283)
                      ·
                        rfl

theorem cell23_2881597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_2881597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881597 prefixEnd_2881597 := by exact prefixLift 2881597
  have htrace : WordTrace (prefixWord ++ tailWord_2881597) baseStart_2881597 baseEnd_2881597 := by
    simpa [prefixWord, tailWord_2881597, baseEnd_2881597] using wordTrace_append hprefix tailTrace_2881597
  have hstable : (prefixWord ++ tailWord_2881597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881597).length < 2 ^ (prefixWord ++ tailWord_2881597).sum := by decide
  have hdescent : baseEnd_2881597 < baseStart_2881597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881697 : List Nat := [1, 2, 3, 3, 1, 2, 3, 3, 1, 4]
def baseStart_2881697 : Nat := 118140960795 + 2881697 * 2 ^ 59
def prefixEnd_2881697 : Nat := 4983230072969 + 3 ^ 40 * 2881697 * 2
def baseEnd_2881697 : Nat := 493231887206505693644941

theorem tailTrace_2881697 : CollatzResearch.WordTrace tailWord_2881697 prefixEnd_2881697 493231887206505693644941 := by
  unfold tailWord_2881697
  simp only [CollatzResearch.WordTrace]
  refine ⟨105104124241111398510275345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70069416160740932340183563 105104124241111398510275345)
  ·
    refine ⟨78828093180833548882706509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105104124241111398510275345 78828093180833548882706509)
    ·
      refine ⟨29560534942812580831014941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78828093180833548882706509 29560534942812580831014941)
      ·
        refine ⟨11085200603554717811630603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29560534942812580831014941 11085200603554717811630603)
        ·
          refine ⟨16627800905332076717445905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11085200603554717811630603 16627800905332076717445905)
          ·
            refine ⟨12470850678999057538084429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16627800905332076717445905 12470850678999057538084429)
            ·
              refine ⟨4676569004624646576781661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12470850678999057538084429 4676569004624646576781661)
              ·
                refine ⟨1753713376734242466293123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4676569004624646576781661 1753713376734242466293123)
                ·
                  refine ⟨2630570065101363699439685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1753713376734242466293123 2630570065101363699439685)
                  ·
                    refine ⟨493231887206505693644941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2630570065101363699439685 493231887206505693644941)
                    ·
                      rfl

theorem cell23_2881697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_2881697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881697 prefixEnd_2881697 := by exact prefixLift 2881697
  have htrace : WordTrace (prefixWord ++ tailWord_2881697) baseStart_2881697 baseEnd_2881697 := by
    simpa [prefixWord, tailWord_2881697, baseEnd_2881697] using wordTrace_append hprefix tailTrace_2881697
  have hstable : (prefixWord ++ tailWord_2881697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881697).length < 2 ^ (prefixWord ++ tailWord_2881697).sum := by decide
  have hdescent : baseEnd_2881697 < baseStart_2881697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881743 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 4]
def baseStart_2881743 : Nat := 118140960795 + 2881743 * 2 ^ 59
def prefixEnd_2881743 : Nat := 4983230072969 + 3 ^ 40 * 2881743 * 2
def baseEnd_2881743 : Nat := 1479719281729623900959611

theorem tailTrace_2881743 : CollatzResearch.WordTrace tailWord_2881743 prefixEnd_2881743 1479719281729623900959611 := by
  unfold tailWord_2881743
  simp only [CollatzResearch.WordTrace]
  refine ⟨105105801998944748366449883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70070534665963165577633255 105105801998944748366449883)
  ·
    refine ⟨157658702998417122549674825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105105801998944748366449883 157658702998417122549674825)
    ·
      refine ⟨118244027248812841912256119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157658702998417122549674825 118244027248812841912256119)
      ·
        refine ⟨177366040873219262868384179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118244027248812841912256119 177366040873219262868384179)
        ·
          refine ⟨266049061309828894302576269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177366040873219262868384179 266049061309828894302576269)
          ·
            refine ⟨99768397991185835363466101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266049061309828894302576269 99768397991185835363466101)
            ·
              refine ⟨9353287311673672065324947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99768397991185835363466101 9353287311673672065324947)
              ·
                refine ⟨14029930967510508097987421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9353287311673672065324947 14029930967510508097987421)
                ·
                  refine ⟨5261224112816440536745283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14029930967510508097987421 5261224112816440536745283)
                  ·
                    refine ⟨7891836169224660805117925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5261224112816440536745283 7891836169224660805117925)
                    ·
                      refine ⟨1479719281729623900959611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7891836169224660805117925 1479719281729623900959611)
                      ·
                        rfl

theorem cell23_2881743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 4].length) (baseStart_2881743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881743 prefixEnd_2881743 := by exact prefixLift 2881743
  have htrace : WordTrace (prefixWord ++ tailWord_2881743) baseStart_2881743 baseEnd_2881743 := by
    simpa [prefixWord, tailWord_2881743, baseEnd_2881743] using wordTrace_append hprefix tailTrace_2881743
  have hstable : (prefixWord ++ tailWord_2881743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881743).length < 2 ^ (prefixWord ++ tailWord_2881743).sum := by decide
  have hdescent : baseEnd_2881743 < baseStart_2881743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881753 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 6, 4]
def baseStart_2881753 : Nat := 118140960795 + 2881753 * 2 ^ 59
def prefixEnd_2881753 : Nat := 4983230072969 + 3 ^ 40 * 2881753 * 2
def baseEnd_2881753 : Nat := 493241472178722953944855

theorem tailTrace_2881753 : CollatzResearch.WordTrace tailWord_2881753 prefixEnd_2881753 493241472178722953944855 := by
  unfold tailWord_2881753
  simp only [CollatzResearch.WordTrace]
  refine ⟨105106166728908520074313913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70070777819272346716209275 105106166728908520074313913)
  ·
    refine ⟨78829625046681390055735435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105106166728908520074313913 78829625046681390055735435)
    ·
      refine ⟨118244437570022085083603153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78829625046681390055735435 118244437570022085083603153)
      ·
        refine ⟨88683328177516563812702365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118244437570022085083603153 88683328177516563812702365)
        ·
          refine ⟨33256248066568711429763387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88683328177516563812702365 33256248066568711429763387)
          ·
            refine ⟨49884372099853067144645081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33256248066568711429763387 49884372099853067144645081)
            ·
              refine ⟨37413279074889800358483811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49884372099853067144645081 37413279074889800358483811)
              ·
                refine ⟨56119918612334700537725717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37413279074889800358483811 56119918612334700537725717)
                ·
                  refine ⟨2630621184953189087705893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56119918612334700537725717 2630621184953189087705893)
                  ·
                    refine ⟨493241472178722953944855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2630621184953189087705893 493241472178722953944855)
                    ·
                      rfl

theorem cell23_2881753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 4].length) (baseStart_2881753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881753 prefixEnd_2881753 := by exact prefixLift 2881753
  have htrace : WordTrace (prefixWord ++ tailWord_2881753) baseStart_2881753 baseEnd_2881753 := by
    simpa [prefixWord, tailWord_2881753, baseEnd_2881753] using wordTrace_append hprefix tailTrace_2881753
  have hstable : (prefixWord ++ tailWord_2881753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881753).length < 2 ^ (prefixWord ++ tailWord_2881753).sum := by decide
  have hdescent : baseEnd_2881753 < baseStart_2881753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881794 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_2881794 : Nat := 118140960795 + 2881794 * 2 ^ 59
def prefixEnd_2881794 : Nat := 4983230072969 + 3 ^ 40 * 2881794 * 2
def baseEnd_2881794 : Nat := 1479745469243003201421877

theorem tailTrace_2881794 : CollatzResearch.WordTrace tailWord_2881794 prefixEnd_2881794 1479745469243003201421877 := by
  unfold tailWord_2881794
  simp only [CollatzResearch.WordTrace]
  refine ⟨26276915530439996019139109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70071774747839989384370957 26276915530439996019139109)
  ·
    refine ⟨4926921661957499253588583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26276915530439996019139109 4926921661957499253588583)
    ·
      refine ⟨7390382492936248880382875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4926921661957499253588583 7390382492936248880382875)
      ·
        refine ⟨11085573739404373320574313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7390382492936248880382875 11085573739404373320574313)
        ·
          refine ⟨8314180304553279990430735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11085573739404373320574313 8314180304553279990430735)
          ·
            refine ⟨12471270456829919985646103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8314180304553279990430735 12471270456829919985646103)
            ·
              refine ⟨18706905685244879978469155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12471270456829919985646103 18706905685244879978469155)
              ·
                refine ⟨28060358527867319967703733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18706905685244879978469155 28060358527867319967703733)
                ·
                  refine ⟨2630658611987561246972225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28060358527867319967703733 2630658611987561246972225)
                  ·
                    refine ⟨1972993958990670935229169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2630658611987561246972225 1972993958990670935229169)
                    ·
                      refine ⟨1479745469243003201421877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1972993958990670935229169 1479745469243003201421877)
                      ·
                        rfl

theorem cell23_2881794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_2881794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881794 prefixEnd_2881794 := by exact prefixLift 2881794
  have htrace : WordTrace (prefixWord ++ tailWord_2881794) baseStart_2881794 baseEnd_2881794 := by
    simpa [prefixWord, tailWord_2881794, baseEnd_2881794] using wordTrace_append hprefix tailTrace_2881794
  have hstable : (prefixWord ++ tailWord_2881794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881794).length < 2 ^ (prefixWord ++ tailWord_2881794).sum := by decide
  have hdescent : baseEnd_2881794 < baseStart_2881794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881800 : List Nat := [2, 1, 3, 2, 3, 2, 3, 7]
def baseStart_2881800 : Nat := 118140960795 + 2881800 * 2 ^ 59
def prefixEnd_2881800 : Nat := 4983230072969 + 3 ^ 40 * 2881800 * 2
def baseEnd_2881800 : Nat := 54805501856552969553587

theorem tailTrace_2881800 : CollatzResearch.WordTrace tailWord_2881800 prefixEnd_2881800 54805501856552969553587 := by
  unfold tailWord_2881800
  simp only [CollatzResearch.WordTrace]
  refine ⟨52553940479869123550637427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70071920639825498067516569 52553940479869123550637427)
  ·
    refine ⟨78830910719803685325956141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52553940479869123550637427 78830910719803685325956141)
    ·
      refine ⟨29561591519926381997233553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78830910719803685325956141 29561591519926381997233553)
      ·
        refine ⟨22171193639944786497925165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29561591519926381997233553 22171193639944786497925165)
        ·
          refine ⟨8314197614979294936721937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22171193639944786497925165 8314197614979294936721937)
          ·
            refine ⟨6235648211234471202541453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8314197614979294936721937 6235648211234471202541453)
            ·
              refine ⟨2338368079212926700953045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6235648211234471202541453 2338368079212926700953045)
              ·
                refine ⟨54805501856552969553587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2338368079212926700953045 54805501856552969553587)
                ·
                  rfl

theorem cell23_2881800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 7].length) (baseStart_2881800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881800 prefixEnd_2881800 := by exact prefixLift 2881800
  have htrace : WordTrace (prefixWord ++ tailWord_2881800) baseStart_2881800 baseEnd_2881800 := by
    simpa [prefixWord, tailWord_2881800, baseEnd_2881800] using wordTrace_append hprefix tailTrace_2881800
  have hstable : (prefixWord ++ tailWord_2881800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881800).length < 2 ^ (prefixWord ++ tailWord_2881800).sum := by decide
  have hdescent : baseEnd_2881800 < baseStart_2881800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881821 : List Nat := [1, 4, 2, 3, 3, 1, 1, 2, 2, 4]
def baseStart_2881821 : Nat := 118140960795 + 2881821 * 2 ^ 59
def prefixEnd_2881821 : Nat := 4983230072969 + 3 ^ 40 * 2881821 * 2
def baseEnd_2881821 : Nat := 493253111073558198594751

theorem tailTrace_2881821 : CollatzResearch.WordTrace tailWord_2881821 prefixEnd_2881821 493253111073558198594751 := by
  unfold tailWord_2881821
  simp only [CollatzResearch.WordTrace]
  refine ⟨105108646892662167687789317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70072431261774778458526211 105108646892662167687789317)
  ·
    refine ⟨19707871292374156441460497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105108646892662167687789317 19707871292374156441460497)
    ·
      refine ⟨14780903469280617331095373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19707871292374156441460497 14780903469280617331095373)
      ·
        refine ⟨5542838800980231499160765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14780903469280617331095373 5542838800980231499160765)
        ·
          refine ⟨2078564550367586812185287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5542838800980231499160765 2078564550367586812185287)
          ·
            refine ⟨3117846825551380218277931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2078564550367586812185287 3117846825551380218277931)
            ·
              refine ⟨4676770238327070327416897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3117846825551380218277931 4676770238327070327416897)
              ·
                refine ⟨3507577678745302745562673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4676770238327070327416897 3507577678745302745562673)
                ·
                  refine ⟨2630683259058977059172005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3507577678745302745562673 2630683259058977059172005)
                  ·
                    refine ⟨493253111073558198594751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2630683259058977059172005 493253111073558198594751)
                    ·
                      rfl

theorem cell23_2881821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_2881821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881821 prefixEnd_2881821 := by exact prefixLift 2881821
  have htrace : WordTrace (prefixWord ++ tailWord_2881821) baseStart_2881821 baseEnd_2881821 := by
    simpa [prefixWord, tailWord_2881821, baseEnd_2881821] using wordTrace_append hprefix tailTrace_2881821
  have hstable : (prefixWord ++ tailWord_2881821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881821).length < 2 ^ (prefixWord ++ tailWord_2881821).sum := by decide
  have hdescent : baseEnd_2881821 < baseStart_2881821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881843 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 2, 6]
def baseStart_2881843 : Nat := 118140960795 + 2881843 * 2 ^ 59
def prefixEnd_2881843 : Nat := 4983230072969 + 3 ^ 40 * 2881843 * 2
def baseEnd_2881843 : Nat := 493256876598357836569717

theorem tailTrace_2881843 : CollatzResearch.WordTrace tailWord_2881843 prefixEnd_2881843 493256876598357836569717 := by
  unfold tailWord_2881843
  simp only [CollatzResearch.WordTrace]
  refine ⟨105109449298582465445090183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70072966199054976963393455 105109449298582465445090183)
  ·
    refine ⟨157664173947873698167635275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105109449298582465445090183 157664173947873698167635275)
    ·
      refine ⟨236496260921810547251452913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157664173947873698167635275 236496260921810547251452913)
      ·
        refine ⟨177372195691357910438589685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236496260921810547251452913 177372195691357910438589685)
        ·
          refine ⟨16628643346064804103617783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 177372195691357910438589685 16628643346064804103617783)
          ·
            refine ⟨24942965019097206155426675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16628643346064804103617783 24942965019097206155426675)
            ·
              refine ⟨37414447528645809233140013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24942965019097206155426675 37414447528645809233140013)
              ·
                refine ⟨14030417823242178462427505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37414447528645809233140013 14030417823242178462427505)
                ·
                  refine ⟨10522813367431633846820629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14030417823242178462427505 10522813367431633846820629)
                  ·
                    refine ⟨493256876598357836569717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10522813367431633846820629 493256876598357836569717)
                    ·
                      rfl

theorem cell23_2881843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 6].length) (baseStart_2881843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881843 prefixEnd_2881843 := by exact prefixLift 2881843
  have htrace : WordTrace (prefixWord ++ tailWord_2881843) baseStart_2881843 baseEnd_2881843 := by
    simpa [prefixWord, tailWord_2881843, baseEnd_2881843] using wordTrace_append hprefix tailTrace_2881843
  have hstable : (prefixWord ++ tailWord_2881843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881843).length < 2 ^ (prefixWord ++ tailWord_2881843).sum := by decide
  have hdescent : baseEnd_2881843 < baseStart_2881843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881844 : List Nat := [2, 5, 1, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_2881844 : Nat := 118140960795 + 2881844 * 2 ^ 59
def prefixEnd_2881844 : Nat := 4983230072969 + 3 ^ 40 * 2881844 * 2
def baseEnd_2881844 : Nat := 1479771143275728005796647

theorem tailTrace_2881844 : CollatzResearch.WordTrace tailWord_2881844 prefixEnd_2881844 1479771143275728005796647 := by
  unfold tailWord_2881844
  simp only [CollatzResearch.WordTrace]
  refine ⟨52554742885789421307938293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70072990514385895077251057 52554742885789421307938293)
  ·
    refine ⟨4927007145542758247619215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52554742885789421307938293 4927007145542758247619215)
    ·
      refine ⟨7390510718314137371428823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4927007145542758247619215 7390510718314137371428823)
      ·
        refine ⟨11085766077471206057143235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7390510718314137371428823 11085766077471206057143235)
        ·
          refine ⟨16628649116206809085714853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11085766077471206057143235 16628649116206809085714853)
          ·
            refine ⟨3117871709288776703571535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16628649116206809085714853 3117871709288776703571535)
            ·
              refine ⟨4676807563933165055357303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3117871709288776703571535 4676807563933165055357303)
              ·
                refine ⟨7015211345899747583035955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4676807563933165055357303 7015211345899747583035955)
                ·
                  refine ⟨10522817018849621374553933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7015211345899747583035955 10522817018849621374553933)
                  ·
                    refine ⟨3946056382068608015457725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10522817018849621374553933 3946056382068608015457725)
                    ·
                      refine ⟨1479771143275728005796647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3946056382068608015457725 1479771143275728005796647)
                      ·
                        rfl

theorem cell23_2881844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_2881844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881844 prefixEnd_2881844 := by exact prefixLift 2881844
  have htrace : WordTrace (prefixWord ++ tailWord_2881844) baseStart_2881844 baseEnd_2881844 := by
    simpa [prefixWord, tailWord_2881844, baseEnd_2881844] using wordTrace_append hprefix tailTrace_2881844
  have hstable : (prefixWord ++ tailWord_2881844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881844).length < 2 ^ (prefixWord ++ tailWord_2881844).sum := by decide
  have hdescent : baseEnd_2881844 < baseStart_2881844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881854 : List Nat := [4, 2, 1, 2, 1, 2, 1, 4, 1, 3, 2]
def baseStart_2881854 : Nat := 118140960795 + 2881854 * 2 ^ 59
def prefixEnd_2881854 : Nat := 4983230072969 + 3 ^ 40 * 2881854 * 2
def baseEnd_2881854 : Nat := 1479776278082272966671601

theorem tailTrace_2881854 : CollatzResearch.WordTrace tailWord_2881854 prefixEnd_2881854 1479776278082272966671601 := by
  unfold tailWord_2881854
  simp only [CollatzResearch.WordTrace]
  refine ⟨13138731312692826790467577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70073233667695076215827077 13138731312692826790467577)
  ·
    refine ⟨9854048484519620092850683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13138731312692826790467577 9854048484519620092850683)
    ·
      refine ⟨14781072726779430139276025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9854048484519620092850683 14781072726779430139276025)
      ·
        refine ⟨11085804545084572604457019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14781072726779430139276025 11085804545084572604457019)
        ·
          refine ⟨16628706817626858906685529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11085804545084572604457019 16628706817626858906685529)
          ·
            refine ⟨12471530113220144180014147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16628706817626858906685529 12471530113220144180014147)
            ·
              refine ⟨18707295169830216270021221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12471530113220144180014147 18707295169830216270021221)
              ·
                refine ⟨3507617844343165550628979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18707295169830216270021221 3507617844343165550628979)
                ·
                  refine ⟨5261426766514748325943469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3507617844343165550628979 5261426766514748325943469)
                  ·
                    refine ⟨1973035037443030622228801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5261426766514748325943469 1973035037443030622228801)
                    ·
                      refine ⟨1479776278082272966671601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1973035037443030622228801 1479776278082272966671601)
                      ·
                        rfl

theorem cell23_2881854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_2881854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881854 prefixEnd_2881854 := by exact prefixLift 2881854
  have htrace : WordTrace (prefixWord ++ tailWord_2881854) baseStart_2881854 baseEnd_2881854 := by
    simpa [prefixWord, tailWord_2881854, baseEnd_2881854] using wordTrace_append hprefix tailTrace_2881854
  have hstable : (prefixWord ++ tailWord_2881854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881854).length < 2 ^ (prefixWord ++ tailWord_2881854).sum := by decide
  have hdescent : baseEnd_2881854 < baseStart_2881854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881903 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 1, 7]
def baseStart_2881903 : Nat := 118140960795 + 2881903 * 2 ^ 59
def prefixEnd_2881903 : Nat := 4983230072969 + 3 ^ 40 * 2881903 * 2
def baseEnd_2881903 : Nat := 493267146211447758319625

theorem tailTrace_2881903 : CollatzResearch.WordTrace tailWord_2881903 prefixEnd_2881903 493267146211447758319625 := by
  unfold tailWord_2881903
  simp only [CollatzResearch.WordTrace]
  refine ⟨105111637678365095692274363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70074425118910063794849575 105111637678365095692274363)
  ·
    refine ⟨157667456517547643538411545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105111637678365095692274363 157667456517547643538411545)
    ·
      refine ⟨118250592388160732653808659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157667456517547643538411545 118250592388160732653808659)
      ·
        refine ⟨177375888582241098980712989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118250592388160732653808659 177375888582241098980712989)
        ·
          refine ⟨66515958218340412117767371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177375888582241098980712989 66515958218340412117767371)
          ·
            refine ⟨99773937327510618176651057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66515958218340412117767371 99773937327510618176651057)
            ·
              refine ⟨74830452995632963632488293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99773937327510618176651057 74830452995632963632488293)
              ·
                refine ⟨14030709936681180681091555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74830452995632963632488293 14030709936681180681091555)
                ·
                  refine ⟨21046064905021771021637333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14030709936681180681091555 21046064905021771021637333)
                  ·
                    refine ⟨493267146211447758319625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21046064905021771021637333 493267146211447758319625)
                    ·
                      rfl

theorem cell23_2881903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 7].length) (baseStart_2881903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881903 prefixEnd_2881903 := by exact prefixLift 2881903
  have htrace : WordTrace (prefixWord ++ tailWord_2881903) baseStart_2881903 baseEnd_2881903 := by
    simpa [prefixWord, tailWord_2881903, baseEnd_2881903] using wordTrace_append hprefix tailTrace_2881903
  have hstable : (prefixWord ++ tailWord_2881903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881903).length < 2 ^ (prefixWord ++ tailWord_2881903).sum := by decide
  have hdescent : baseEnd_2881903 < baseStart_2881903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881913 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 3, 1, 7]
def baseStart_2881913 : Nat := 118140960795 + 2881913 * 2 ^ 59
def prefixEnd_2881913 : Nat := 4983230072969 + 3 ^ 40 * 2881913 * 2
def baseEnd_2881913 : Nat := 1479806573440888235833829

theorem tailTrace_2881913 : CollatzResearch.WordTrace tailWord_2881913 prefixEnd_2881913 1479806573440888235833829 := by
  unfold tailWord_2881913
  simp only [CollatzResearch.WordTrace]
  refine ⟨105112002408328867400138393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70074668272219244933425595 105112002408328867400138393)
  ·
    refine ⟨78834001806246650550103795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105112002408328867400138393 78834001806246650550103795)
    ·
      refine ⟨118251002709369975825155693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78834001806246650550103795 118251002709369975825155693)
      ·
        refine ⟨44344126016013740934433385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118251002709369975825155693 44344126016013740934433385)
        ·
          refine ⟨33258094512010305700825039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44344126016013740934433385 33258094512010305700825039)
          ·
            refine ⟨49887141768015458551237559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33258094512010305700825039 49887141768015458551237559)
            ·
              refine ⟨74830712652023187826856339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49887141768015458551237559 74830712652023187826856339)
              ·
                refine ⟨112246068978034781740284509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74830712652023187826856339 112246068978034781740284509)
                ·
                  refine ⟨42092275866763043152606691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112246068978034781740284509 42092275866763043152606691)
                  ·
                    refine ⟨63138413800144564728910037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42092275866763043152606691 63138413800144564728910037)
                    ·
                      refine ⟨1479806573440888235833829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63138413800144564728910037 1479806573440888235833829)
                      ·
                        rfl

theorem cell23_2881913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_2881913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881913 prefixEnd_2881913 := by exact prefixLift 2881913
  have htrace : WordTrace (prefixWord ++ tailWord_2881913) baseStart_2881913 baseEnd_2881913 := by
    simpa [prefixWord, tailWord_2881913, baseEnd_2881913] using wordTrace_append hprefix tailTrace_2881913
  have hstable : (prefixWord ++ tailWord_2881913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881913).length < 2 ^ (prefixWord ++ tailWord_2881913).sum := by decide
  have hdescent : baseEnd_2881913 < baseStart_2881913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881957 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 2, 4, 2]
def baseStart_2881957 : Nat := 118140960795 + 2881957 * 2 ^ 59
def prefixEnd_2881957 : Nat := 4983230072969 + 3 ^ 40 * 2881957 * 2
def baseEnd_2881957 : Nat := 1479829166589686063683627

theorem tailTrace_2881957 : CollatzResearch.WordTrace tailWord_2881957 prefixEnd_2881957 1479829166589686063683627 := by
  unfold tailWord_2881957
  simp only [CollatzResearch.WordTrace]
  refine ⟨105113607220169462914740125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70075738146779641943160083 105113607220169462914740125)
  ·
    refine ⟨39417602707563548593027547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105113607220169462914740125 39417602707563548593027547)
    ·
      refine ⟨59126404061345322889541321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39417602707563548593027547 59126404061345322889541321)
      ·
        refine ⟨44344803046008992167155991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59126404061345322889541321 44344803046008992167155991)
        ·
          refine ⟨66517204569013488250733987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44344803046008992167155991 66517204569013488250733987)
          ·
            refine ⟨99775806853520232376100981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66517204569013488250733987 99775806853520232376100981)
            ·
              refine ⟨9353981892517521785259467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99775806853520232376100981 9353981892517521785259467)
              ·
                refine ⟨14030972838776282677889201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9353981892517521785259467 14030972838776282677889201)
                ·
                  refine ⟨10523229629082212008416901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14030972838776282677889201 10523229629082212008416901)
                  ·
                    refine ⟨1973105555452914751578169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10523229629082212008416901 1973105555452914751578169)
                    ·
                      refine ⟨1479829166589686063683627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1973105555452914751578169 1479829166589686063683627)
                      ·
                        rfl

theorem cell23_2881957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_2881957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881957 prefixEnd_2881957 := by exact prefixLift 2881957
  have htrace : WordTrace (prefixWord ++ tailWord_2881957) baseStart_2881957 baseEnd_2881957 := by
    simpa [prefixWord, tailWord_2881957, baseEnd_2881957] using wordTrace_append hprefix tailTrace_2881957
  have hstable : (prefixWord ++ tailWord_2881957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881957).length < 2 ^ (prefixWord ++ tailWord_2881957).sum := by decide
  have hdescent : baseEnd_2881957 < baseStart_2881957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881977 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 1, 4, 3]
def baseStart_2881977 : Nat := 118140960795 + 2881977 * 2 ^ 59
def prefixEnd_2881977 : Nat := 4983230072969 + 3 ^ 40 * 2881977 * 2
def baseEnd_2881977 : Nat := 1479839436202775985433535

theorem tailTrace_2881977 : CollatzResearch.WordTrace tailWord_2881977 prefixEnd_2881977 1479839436202775985433535 := by
  unfold tailWord_2881977
  simp only [CollatzResearch.WordTrace]
  refine ⟨105114336680097006330468185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70076224453398004220312123 105114336680097006330468185)
  ·
    refine ⟨78835752510072754747851139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105114336680097006330468185 78835752510072754747851139)
    ·
      refine ⟨118253628765109132121776709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78835752510072754747851139 118253628765109132121776709)
      ·
        refine ⟨22172555393457962272833133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118253628765109132121776709 22172555393457962272833133)
        ·
          refine ⟨8314708272546735852312425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22172555393457962272833133 8314708272546735852312425)
          ·
            refine ⟨6236031204410051889234319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8314708272546735852312425 6236031204410051889234319)
            ·
              refine ⟨9354046806615077833851479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6236031204410051889234319 9354046806615077833851479)
              ·
                refine ⟨14031070209922616750777219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9354046806615077833851479 14031070209922616750777219)
                ·
                  refine ⟨21046605314883925126165829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14031070209922616750777219 21046605314883925126165829)
                  ·
                    refine ⟨3946238496540735961156093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21046605314883925126165829 3946238496540735961156093)
                    ·
                      refine ⟨1479839436202775985433535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3946238496540735961156093 1479839436202775985433535)
                      ·
                        rfl

theorem cell23_2881977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_2881977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2881977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2881977 prefixEnd_2881977 := by exact prefixLift 2881977
  have htrace : WordTrace (prefixWord ++ tailWord_2881977) baseStart_2881977 baseEnd_2881977 := by
    simpa [prefixWord, tailWord_2881977, baseEnd_2881977] using wordTrace_append hprefix tailTrace_2881977
  have hstable : (prefixWord ++ tailWord_2881977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881977).length < 2 ^ (prefixWord ++ tailWord_2881977).sum := by decide
  have hdescent : baseEnd_2881977 < baseStart_2881977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882017 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 3, 5, 2]
def baseStart_2882017 : Nat := 118140960795 + 2882017 * 2 ^ 59
def prefixEnd_2882017 : Nat := 4983230072969 + 3 ^ 40 * 2882017 * 2
def baseEnd_2882017 : Nat := 1479859975428955828933351

theorem tailTrace_2882017 : CollatzResearch.WordTrace tailWord_2882017 prefixEnd_2882017 1479859975428955828933351 := by
  unfold tailWord_2882017
  simp only [CollatzResearch.WordTrace]
  refine ⟨105115795599952093161924305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70077197066634728774616203 105115795599952093161924305)
  ·
    refine ⟨78836846699964069871443229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105115795599952093161924305 78836846699964069871443229)
    ·
      refine ⟨29563817512486526201791211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78836846699964069871443229 29563817512486526201791211)
      ·
        refine ⟨44345726268729789302686817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29563817512486526201791211 44345726268729789302686817)
        ·
          refine ⟨33259294701547341977015113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44345726268729789302686817 33259294701547341977015113)
          ·
            refine ⟨24944471026160506482761335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33259294701547341977015113 24944471026160506482761335)
            ·
              refine ⟨37416706539240759724142003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24944471026160506482761335 37416706539240759724142003)
              ·
                refine ⟨56125059808861139586213005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37416706539240759724142003 56125059808861139586213005)
                ·
                  refine ⟨21046897428322927344829877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56125059808861139586213005 21046897428322927344829877)
                  ·
                    refine ⟨1973146633905274438577801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21046897428322927344829877 1973146633905274438577801)
                    ·
                      refine ⟨1479859975428955828933351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1973146633905274438577801 1479859975428955828933351)
                      ·
                        rfl

theorem cell23_2882017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_2882017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882017 prefixEnd_2882017 := by exact prefixLift 2882017
  have htrace : WordTrace (prefixWord ++ tailWord_2882017) baseStart_2882017 baseEnd_2882017 := by
    simpa [prefixWord, tailWord_2882017, baseEnd_2882017] using wordTrace_append hprefix tailTrace_2882017
  have hstable : (prefixWord ++ tailWord_2882017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882017).length < 2 ^ (prefixWord ++ tailWord_2882017).sum := by decide
  have hdescent : baseEnd_2882017 < baseStart_2882017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882024 : List Nat := [2, 1, 4, 1, 1, 3, 2, 2, 3, 1, 3]
def baseStart_2882024 : Nat := 118140960795 + 2882024 * 2 ^ 59
def prefixEnd_2882024 : Nat := 4983230072969 + 3 ^ 40 * 2882024 * 2
def baseEnd_2882024 : Nat := 1479863569793537301545819

theorem tailTrace_2882024 : CollatzResearch.WordTrace tailWord_2882024 prefixEnd_2882024 1479863569793537301545819 := by
  unfold tailWord_2882024
  simp only [CollatzResearch.WordTrace]
  refine ⟨52558025455463366678714563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70077367273951155571619417 52558025455463366678714563)
  ·
    refine ⟨78837038183195050018071845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52558025455463366678714563 78837038183195050018071845)
    ·
      refine ⟨14781944659349071878388471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78837038183195050018071845 14781944659349071878388471)
      ·
        refine ⟨22172916989023607817582707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14781944659349071878388471 22172916989023607817582707)
        ·
          refine ⟨33259375483535411726374061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22172916989023607817582707 33259375483535411726374061)
          ·
            refine ⟨12472265806325779397390273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33259375483535411726374061 12472265806325779397390273)
            ·
              refine ⟨9354199354744334548042705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12472265806325779397390273 9354199354744334548042705)
              ·
                refine ⟨7015649516058250911032029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9354199354744334548042705 7015649516058250911032029)
                ·
                  refine ⟨2630868568521844091637011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7015649516058250911032029 2630868568521844091637011)
                  ·
                    refine ⟨3946302852782766137455517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2630868568521844091637011 3946302852782766137455517)
                    ·
                      refine ⟨1479863569793537301545819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3946302852782766137455517 1479863569793537301545819)
                      ·
                        rfl

theorem cell23_2882024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_2882024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882024 prefixEnd_2882024 := by exact prefixLift 2882024
  have htrace : WordTrace (prefixWord ++ tailWord_2882024) baseStart_2882024 baseEnd_2882024 := by
    simpa [prefixWord, tailWord_2882024, baseEnd_2882024] using wordTrace_append hprefix tailTrace_2882024
  have hstable : (prefixWord ++ tailWord_2882024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882024).length < 2 ^ (prefixWord ++ tailWord_2882024).sum := by decide
  have hdescent : baseEnd_2882024 < baseStart_2882024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882027 : List Nat := [1, 1, 1, 1, 2, 3, 6, 2, 1, 5]
def baseStart_2882027 : Nat := 118140960795 + 2882027 * 2 ^ 59
def prefixEnd_2882027 : Nat := 4983230072969 + 3 ^ 40 * 2882027 * 2
def baseEnd_2882027 : Nat := 493288370078500263269435

theorem tailTrace_2882027 : CollatzResearch.WordTrace tailWord_2882027 prefixEnd_2882027 493288370078500263269435 := by
  unfold tailWord_2882027
  simp only [CollatzResearch.WordTrace]
  refine ⟨105116160329915864869788335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70077440219943909913192223 105116160329915864869788335)
  ·
    refine ⟨157674240494873797304682503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105116160329915864869788335 157674240494873797304682503)
    ·
      refine ⟨236511360742310695957023755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157674240494873797304682503 236511360742310695957023755)
      ·
        refine ⟨354767041113466043935535633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236511360742310695957023755 354767041113466043935535633)
        ·
          refine ⟨266075280835099532951651725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354767041113466043935535633 266075280835099532951651725)
          ·
            refine ⟨99778230313162324856869397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266075280835099532951651725 99778230313162324856869397)
            ·
              refine ⟨4677104545929483977665753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99778230313162324856869397 4677104545929483977665753)
              ·
                refine ⟨3507828409447112983249315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4677104545929483977665753 3507828409447112983249315)
                ·
                  refine ⟨5261742614170669474873973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3507828409447112983249315 5261742614170669474873973)
                  ·
                    refine ⟨493288370078500263269435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5261742614170669474873973 493288370078500263269435)
                    ·
                      rfl

theorem cell23_2882027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 5].length) (baseStart_2882027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882027 prefixEnd_2882027 := by exact prefixLift 2882027
  have htrace : WordTrace (prefixWord ++ tailWord_2882027) baseStart_2882027 baseEnd_2882027 := by
    simpa [prefixWord, tailWord_2882027, baseEnd_2882027] using wordTrace_append hprefix tailTrace_2882027
  have hstable : (prefixWord ++ tailWord_2882027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882027).length < 2 ^ (prefixWord ++ tailWord_2882027).sum := by decide
  have hdescent : baseEnd_2882027 < baseStart_2882027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882040 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 3, 6]
def baseStart_2882040 : Nat := 118140960795 + 2882040 * 2 ^ 59
def prefixEnd_2882040 : Nat := 4983230072969 + 3 ^ 40 * 2882040 * 2
def baseEnd_2882040 : Nat := 493290595161336412981915

theorem tailTrace_2882040 : CollatzResearch.WordTrace tailWord_2882040 prefixEnd_2882040 493290595161336412981915 := by
  unfold tailWord_2882040
  simp only [CollatzResearch.WordTrace]
  refine ⟨52558317239434384045005787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70077756319245845393341049 52558317239434384045005787)
  ·
    refine ⟨78837475859151576067508681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52558317239434384045005787 78837475859151576067508681)
    ·
      refine ⟨59128106894363682050631511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78837475859151576067508681 59128106894363682050631511)
      ·
        refine ⟨88692160341545523075947267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59128106894363682050631511 88692160341545523075947267)
        ·
          refine ⟨133038240512318284613920901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88692160341545523075947267 133038240512318284613920901)
          ·
            refine ⟨24944670096059678365110169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133038240512318284613920901 24944670096059678365110169)
            ·
              refine ⟨18708502572044758773832627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24944670096059678365110169 18708502572044758773832627)
              ·
                refine ⟨28062753858067138160748941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18708502572044758773832627 28062753858067138160748941)
                ·
                  refine ⟨10523532696775176810280853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28062753858067138160748941 10523532696775176810280853)
                  ·
                    refine ⟨493290595161336412981915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10523532696775176810280853 493290595161336412981915)
                    ·
                      rfl

theorem cell23_2882040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_2882040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882040 prefixEnd_2882040 := by exact prefixLift 2882040
  have htrace : WordTrace (prefixWord ++ tailWord_2882040) baseStart_2882040 baseEnd_2882040 := by
    simpa [prefixWord, tailWord_2882040, baseEnd_2882040] using wordTrace_append hprefix tailTrace_2882040
  have hstable : (prefixWord ++ tailWord_2882040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882040).length < 2 ^ (prefixWord ++ tailWord_2882040).sum := by decide
  have hdescent : baseEnd_2882040 < baseStart_2882040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882041 : List Nat := [1, 2, 1, 3, 1, 2, 5, 3, 1, 1, 3]
def baseStart_2882041 : Nat := 118140960795 + 2882041 * 2 ^ 59
def prefixEnd_2882041 : Nat := 4983230072969 + 3 ^ 40 * 2882041 * 2
def baseEnd_2882041 : Nat := 1479872298964663735033241

theorem tailTrace_2882041 : CollatzResearch.WordTrace tailWord_2882041 prefixEnd_2882041 1479872298964663735033241 := by
  unfold tailWord_2882041
  simp only [CollatzResearch.WordTrace]
  refine ⟨105116670951865145260797977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70077780634576763507198651 105116670951865145260797977)
  ·
    refine ⟨78837503213898858945598483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105116670951865145260797977 78837503213898858945598483)
    ·
      refine ⟨118256254820848288418397725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78837503213898858945598483 118256254820848288418397725)
      ·
        refine ⟨44346095557818108156899147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118256254820848288418397725 44346095557818108156899147)
        ·
          refine ⟨66519143336727162235348721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44346095557818108156899147 66519143336727162235348721)
          ·
            refine ⟨49889357502545371676511541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66519143336727162235348721 49889357502545371676511541)
            ·
              refine ⟨4677127265863628594672957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49889357502545371676511541 4677127265863628594672957)
              ·
                refine ⟨1753922724698860723002359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4677127265863628594672957 1753922724698860723002359)
                ·
                  refine ⟨2630884087048291084503539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1753922724698860723002359 2630884087048291084503539)
                  ·
                    refine ⟨3946326130572436626755309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2630884087048291084503539 3946326130572436626755309)
                    ·
                      refine ⟨1479872298964663735033241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3946326130572436626755309 1479872298964663735033241)
                      ·
                        rfl

theorem cell23_2882041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 1, 1, 3].length) (baseStart_2882041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882041 prefixEnd_2882041 := by exact prefixLift 2882041
  have htrace : WordTrace (prefixWord ++ tailWord_2882041) baseStart_2882041 baseEnd_2882041 := by
    simpa [prefixWord, tailWord_2882041, baseEnd_2882041] using wordTrace_append hprefix tailTrace_2882041
  have hstable : (prefixWord ++ tailWord_2882041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882041).length < 2 ^ (prefixWord ++ tailWord_2882041).sum := by decide
  have hdescent : baseEnd_2882041 < baseStart_2882041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882047 : List Nat := [1, 1, 2, 2, 1, 2, 3, 5, 1, 1, 4]
def baseStart_2882047 : Nat := 118140960795 + 2882047 * 2 ^ 59
def prefixEnd_2882047 : Nat := 4983230072969 + 3 ^ 40 * 2882047 * 2
def baseEnd_2882047 : Nat := 1479875379848590711558213

theorem tailTrace_2882047 : CollatzResearch.WordTrace tailWord_2882047 prefixEnd_2882047 1479875379848590711558213 := by
  unfold tailWord_2882047
  simp only [CollatzResearch.WordTrace]
  refine ⟨105116889789843408285516395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70077926526562272190344263 105116889789843408285516395)
  ·
    refine ⟨157675334684765112428274593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105116889789843408285516395 157675334684765112428274593)
    ·
      refine ⟨118256501013573834321205945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157675334684765112428274593 118256501013573834321205945)
      ·
        refine ⟨88692375760180375740904459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118256501013573834321205945 88692375760180375740904459)
        ·
          refine ⟨133038563640270563611356689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88692375760180375740904459 133038563640270563611356689)
          ·
            refine ⟨99778922730202922708517517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133038563640270563611356689 99778922730202922708517517)
            ·
              refine ⟨37417096023826096015694069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99778922730202922708517517 37417096023826096015694069)
              ·
                refine ⟨3507852752233696501471319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37417096023826096015694069 3507852752233696501471319)
                ·
                  refine ⟨5261779128350544752206979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3507852752233696501471319 5261779128350544752206979)
                  ·
                    refine ⟨7892668692525817128310469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5261779128350544752206979 7892668692525817128310469)
                    ·
                      refine ⟨1479875379848590711558213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7892668692525817128310469 1479875379848590711558213)
                      ·
                        rfl

theorem cell23_2882047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 1, 4].length) (baseStart_2882047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882047 prefixEnd_2882047 := by exact prefixLift 2882047
  have htrace : WordTrace (prefixWord ++ tailWord_2882047) baseStart_2882047 baseEnd_2882047 := by
    simpa [prefixWord, tailWord_2882047, baseEnd_2882047] using wordTrace_append hprefix tailTrace_2882047
  have hstable : (prefixWord ++ tailWord_2882047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882047).length < 2 ^ (prefixWord ++ tailWord_2882047).sum := by decide
  have hdescent : baseEnd_2882047 < baseStart_2882047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882058 : List Nat := [3, 1, 2, 2, 2, 1, 5, 2, 1, 1, 3]
def baseStart_2882058 : Nat := 118140960795 + 2882058 * 2 ^ 59
def prefixEnd_2882058 : Nat := 4983230072969 + 3 ^ 40 * 2882058 * 2
def baseEnd_2882058 : Nat := 1479881028135790168520663

theorem tailTrace_2882058 : CollatzResearch.WordTrace tailWord_2882058 prefixEnd_2882058 1479881028135790168520663 := by
  unfold tailWord_2882058
  simp only [CollatzResearch.WordTrace]
  refine ⟨26279322748200889291041707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70078193995202371442777885 26279322748200889291041707)
  ·
    refine ⟨39418984122301333936562561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26279322748200889291041707 39418984122301333936562561)
    ·
      refine ⟨29564238091726000452421921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39418984122301333936562561 29564238091726000452421921)
      ·
        refine ⟨22173178568794500339316441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29564238091726000452421921 22173178568794500339316441)
        ·
          refine ⟨16629883926595875254487331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22173178568794500339316441 16629883926595875254487331)
          ·
            refine ⟨24944825889893812881730997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16629883926595875254487331 24944825889893812881730997)
            ·
              refine ⟨2338577427177544957662281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24944825889893812881730997 2338577427177544957662281)
              ·
                refine ⟨1753933070383158718246711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2338577427177544957662281 1753933070383158718246711)
                ·
                  refine ⟨2630899605574738077370067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1753933070383158718246711 2630899605574738077370067)
                  ·
                    refine ⟨3946349408362107116055101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2630899605574738077370067 3946349408362107116055101)
                    ·
                      refine ⟨1479881028135790168520663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3946349408362107116055101 1479881028135790168520663)
                      ·
                        rfl

theorem cell23_2882058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_2882058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882058 prefixEnd_2882058 := by exact prefixLift 2882058
  have htrace : WordTrace (prefixWord ++ tailWord_2882058) baseStart_2882058 baseEnd_2882058 := by
    simpa [prefixWord, tailWord_2882058, baseEnd_2882058] using wordTrace_append hprefix tailTrace_2882058
  have hstable : (prefixWord ++ tailWord_2882058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882058).length < 2 ^ (prefixWord ++ tailWord_2882058).sum := by decide
  have hdescent : baseEnd_2882058 < baseStart_2882058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882067 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 3]
def baseStart_2882067 : Nat := 118140960795 + 2882067 * 2 ^ 59
def prefixEnd_2882067 : Nat := 4983230072969 + 3 ^ 40 * 2882067 * 2
def baseEnd_2882067 : Nat := 1479885649461680633308121

theorem tailTrace_2882067 : CollatzResearch.WordTrace tailWord_2882067 prefixEnd_2882067 1479885649461680633308121 := by
  unfold tailWord_2882067
  simp only [CollatzResearch.WordTrace]
  refine ⟨105117619249770951701244455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70078412833180634467496303 105117619249770951701244455)
  ·
    refine ⟨157676428874656427551866683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105117619249770951701244455 157676428874656427551866683)
    ·
      refine ⟨236514643311984641327800025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157676428874656427551866683 236514643311984641327800025)
      ·
        refine ⟨177385982483988480995850019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236514643311984641327800025 177385982483988480995850019)
        ·
          refine ⟨266078973725982721493775029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177385982483988480995850019 266078973725982721493775029)
          ·
            refine ⟨24944903786810880140041409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 266078973725982721493775029 24944903786810880140041409)
            ·
              refine ⟨18708677840108160105031057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24944903786810880140041409 18708677840108160105031057)
              ·
                refine ⟨14031508380081120078773293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18708677840108160105031057 14031508380081120078773293)
                ·
                  refine ⟨5261815642530420029539985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14031508380081120078773293 5261815642530420029539985)
                  ·
                    refine ⟨3946361731897815022154989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5261815642530420029539985 3946361731897815022154989)
                    ·
                      refine ⟨1479885649461680633308121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3946361731897815022154989 1479885649461680633308121)
                      ·
                        rfl

theorem cell23_2882067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 3].length) (baseStart_2882067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882067 prefixEnd_2882067 := by exact prefixLift 2882067
  have htrace : WordTrace (prefixWord ++ tailWord_2882067) baseStart_2882067 baseEnd_2882067 := by
    simpa [prefixWord, tailWord_2882067, baseEnd_2882067] using wordTrace_append hprefix tailTrace_2882067
  have hstable : (prefixWord ++ tailWord_2882067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882067).length < 2 ^ (prefixWord ++ tailWord_2882067).sum := by decide
  have hdescent : baseEnd_2882067 < baseStart_2882067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882077 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_2882077 : Nat := 118140960795 + 2882077 * 2 ^ 59
def prefixEnd_2882077 : Nat := 4983230072969 + 3 ^ 40 * 2882077 * 2
def baseEnd_2882077 : Nat := 1479890784268225594183075

theorem tailTrace_2882077 : CollatzResearch.WordTrace tailWord_2882077 prefixEnd_2882077 1479890784268225594183075 := by
  unfold tailWord_2882077
  simp only [CollatzResearch.WordTrace]
  refine ⟨105117983979734723409108485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70078655986489815606072323 105117983979734723409108485)
  ·
    refine ⟨19709621996200260639207841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105117983979734723409108485 19709621996200260639207841)
    ·
      refine ⟨14782216497150195479405881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19709621996200260639207841 14782216497150195479405881)
      ·
        refine ⟨11086662372862646609554411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14782216497150195479405881 11086662372862646609554411)
        ·
          refine ⟨16629993559293969914331617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11086662372862646609554411 16629993559293969914331617)
          ·
            refine ⟨12472495169470477435748713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16629993559293969914331617 12472495169470477435748713)
            ·
              refine ⟨9354371377102858076811535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12472495169470477435748713 9354371377102858076811535)
              ·
                refine ⟨14031557065654287115217303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9354371377102858076811535 14031557065654287115217303)
                ·
                  refine ⟨21047335598481430672825955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14031557065654287115217303 21047335598481430672825955)
                  ·
                    refine ⟨31571003397722146009238933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21047335598481430672825955 31571003397722146009238933)
                    ·
                      refine ⟨1479890784268225594183075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31571003397722146009238933 1479890784268225594183075)
                      ·
                        rfl

theorem cell23_2882077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_2882077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882077 prefixEnd_2882077 := by exact prefixLift 2882077
  have htrace : WordTrace (prefixWord ++ tailWord_2882077) baseStart_2882077 baseEnd_2882077 := by
    simpa [prefixWord, tailWord_2882077, baseEnd_2882077] using wordTrace_append hprefix tailTrace_2882077
  have hstable : (prefixWord ++ tailWord_2882077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882077).length < 2 ^ (prefixWord ++ tailWord_2882077).sum := by decide
  have hdescent : baseEnd_2882077 < baseStart_2882077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882097 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 3, 3, 3]
def baseStart_2882097 : Nat := 118140960795 + 2882097 * 2 ^ 59
def prefixEnd_2882097 : Nat := 4983230072969 + 3 ^ 40 * 2882097 * 2
def baseEnd_2882097 : Nat := 1479901053881315515932983

theorem tailTrace_2882097 : CollatzResearch.WordTrace tailWord_2882097 prefixEnd_2882097 1479901053881315515932983 := by
  unfold tailWord_2882097
  simp only [CollatzResearch.WordTrace]
  refine ⟨105118713439662266824836545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70079142293108177883224363 105118713439662266824836545)
  ·
    refine ⟨78839035079746700118627409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105118713439662266824836545 78839035079746700118627409)
    ·
      refine ⟨59129276309810025088970557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78839035079746700118627409 59129276309810025088970557)
      ·
        refine ⟨22173478616178759408363959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59129276309810025088970557 22173478616178759408363959)
        ·
          refine ⟨33260217924268139112545939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22173478616178759408363959 33260217924268139112545939)
          ·
            refine ⟨49890326886402208668818909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33260217924268139112545939 49890326886402208668818909)
            ·
              refine ⟨18708872582400828250807091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49890326886402208668818909 18708872582400828250807091)
              ·
                refine ⟨28063308873601242376210637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18708872582400828250807091 28063308873601242376210637)
                ·
                  refine ⟨10523740827600465891078989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28063308873601242376210637 10523740827600465891078989)
                  ·
                    refine ⟨3946402810350174709154621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10523740827600465891078989 3946402810350174709154621)
                    ·
                      refine ⟨1479901053881315515932983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3946402810350174709154621 1479901053881315515932983)
                      ·
                        rfl

theorem cell23_2882097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_2882097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882097 prefixEnd_2882097 := by exact prefixLift 2882097
  have htrace : WordTrace (prefixWord ++ tailWord_2882097) baseStart_2882097 baseEnd_2882097 := by
    simpa [prefixWord, tailWord_2882097, baseEnd_2882097] using wordTrace_append hprefix tailTrace_2882097
  have hstable : (prefixWord ++ tailWord_2882097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882097).length < 2 ^ (prefixWord ++ tailWord_2882097).sum := by decide
  have hdescent : baseEnd_2882097 < baseStart_2882097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882101 : List Nat := [1, 3, 3, 1, 1, 2, 5, 1, 1, 2, 3]
def baseStart_2882101 : Nat := 118140960795 + 2882101 * 2 ^ 59
def prefixEnd_2882101 : Nat := 4983230072969 + 3 ^ 40 * 2882101 * 2
def baseEnd_2882101 : Nat := 1479903107803933500282965

theorem tailTrace_2882101 : CollatzResearch.WordTrace tailWord_2882101 prefixEnd_2882101 1479903107803933500282965 := by
  unfold tailWord_2882101
  simp only [CollatzResearch.WordTrace]
  refine ⟨105118859331647775507982157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70079239554431850338654771 105118859331647775507982157)
  ·
    refine ⟨39419572249367915815493309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105118859331647775507982157 39419572249367915815493309)
    ·
      refine ⟨14782339593512968430809991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39419572249367915815493309 14782339593512968430809991)
      ·
        refine ⟨22173509390269452646214987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14782339593512968430809991 22173509390269452646214987)
        ·
          refine ⟨33260264085404178969322481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22173509390269452646214987 33260264085404178969322481)
          ·
            refine ⟨24945198064053134226991861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33260264085404178969322481 24945198064053134226991861)
            ·
              refine ⟨2338612318504981333780487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24945198064053134226991861 2338612318504981333780487)
              ·
                refine ⟨3507918477757472000670731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2338612318504981333780487 3507918477757472000670731)
                ·
                  refine ⟨5261877716636208001006097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3507918477757472000670731 5261877716636208001006097)
                  ·
                    refine ⟨3946408287477156000754573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5261877716636208001006097 3946408287477156000754573)
                    ·
                      refine ⟨1479903107803933500282965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3946408287477156000754573 1479903107803933500282965)
                      ·
                        rfl

theorem cell23_2882101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_2882101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882101 prefixEnd_2882101 := by exact prefixLift 2882101
  have htrace : WordTrace (prefixWord ++ tailWord_2882101) baseStart_2882101 baseEnd_2882101 := by
    simpa [prefixWord, tailWord_2882101, baseEnd_2882101] using wordTrace_append hprefix tailTrace_2882101
  have hstable : (prefixWord ++ tailWord_2882101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882101).length < 2 ^ (prefixWord ++ tailWord_2882101).sum := by decide
  have hdescent : baseEnd_2882101 < baseStart_2882101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882107 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 4, 7, 2]
def baseStart_2882107 : Nat := 118140960795 + 2882107 * 2 ^ 59
def prefixEnd_2882107 : Nat := 4983230072969 + 3 ^ 40 * 2882107 * 2
def baseEnd_2882107 : Nat := 1479906188687860476807937

theorem tailTrace_2882107 : CollatzResearch.WordTrace tailWord_2882107 prefixEnd_2882107 1479906188687860476807937 := by
  unfold tailWord_2882107
  simp only [CollatzResearch.WordTrace]
  refine ⟨105119078169626038532700575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70079385446417359021800383 105119078169626038532700575)
  ·
    refine ⟨157678617254439057799050863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105119078169626038532700575 157678617254439057799050863)
    ·
      refine ⟨236517925881658586698576295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157678617254439057799050863 236517925881658586698576295)
      ·
        refine ⟨354776888822487880047864443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236517925881658586698576295 354776888822487880047864443)
        ·
          refine ⟨532165333233731820071796665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354776888822487880047864443 532165333233731820071796665)
          ·
            refine ⟨399123999925298865053847499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 532165333233731820071796665 399123999925298865053847499)
            ·
              refine ⟨598685999887948297580771249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399123999925298865053847499 598685999887948297580771249)
              ·
                refine ⟨449014499915961223185578437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 598685999887948297580771249 449014499915961223185578437)
                ·
                  refine ⟨84190218734242729347295957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 449014499915961223185578437 84190218734242729347295957)
                  ·
                    refine ⟨1973208251583813969077249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 84190218734242729347295957 1973208251583813969077249)
                    ·
                      refine ⟨1479906188687860476807937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1973208251583813969077249 1479906188687860476807937)
                      ·
                        rfl

theorem cell23_2882107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 7, 2].length) (baseStart_2882107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882107 prefixEnd_2882107 := by exact prefixLift 2882107
  have htrace : WordTrace (prefixWord ++ tailWord_2882107) baseStart_2882107 baseEnd_2882107 := by
    simpa [prefixWord, tailWord_2882107, baseEnd_2882107] using wordTrace_append hprefix tailTrace_2882107
  have hstable : (prefixWord ++ tailWord_2882107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882107).length < 2 ^ (prefixWord ++ tailWord_2882107).sum := by decide
  have hdescent : baseEnd_2882107 < baseStart_2882107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882124 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 5, 3, 2]
def baseStart_2882124 : Nat := 118140960795 + 2882124 * 2 ^ 59
def prefixEnd_2882124 : Nat := 4983230072969 + 3 ^ 40 * 2882124 * 2
def baseEnd_2882124 : Nat := 1479914917858986910295359

theorem tailTrace_2882124 : CollatzResearch.WordTrace tailWord_2882124 prefixEnd_2882124 1479914917858986910295359 := by
  unfold tailWord_2882124
  simp only [CollatzResearch.WordTrace]
  refine ⟨52559849105282225218034713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70079798807042966957379617 52559849105282225218034713)
  ·
    refine ⟨39419886828961668913526035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52559849105282225218034713 39419886828961668913526035)
    ·
      refine ⟨59129830243442503370289053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39419886828961668913526035 59129830243442503370289053)
      ·
        refine ⟨22173686341290938763858395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59129830243442503370289053 22173686341290938763858395)
        ·
          refine ⟨33260529511936408145787593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22173686341290938763858395 33260529511936408145787593)
          ·
            refine ⟨24945397133952306109340695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33260529511936408145787593 24945397133952306109340695)
            ·
              refine ⟨37418095700928459164011043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24945397133952306109340695 37418095700928459164011043)
              ·
                refine ⟨56127143551392688746016565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37418095700928459164011043 56127143551392688746016565)
                ·
                  refine ⟨5261919707943064569939053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56127143551392688746016565 5261919707943064569939053)
                  ·
                    refine ⟨1973219890478649213727145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5261919707943064569939053 1973219890478649213727145)
                    ·
                      refine ⟨1479914917858986910295359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1973219890478649213727145 1479914917858986910295359)
                      ·
                        rfl

theorem cell23_2882124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_2882124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882124 prefixEnd_2882124 := by exact prefixLift 2882124
  have htrace : WordTrace (prefixWord ++ tailWord_2882124) baseStart_2882124 baseEnd_2882124 := by
    simpa [prefixWord, tailWord_2882124, baseEnd_2882124] using wordTrace_append hprefix tailTrace_2882124
  have hstable : (prefixWord ++ tailWord_2882124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882124).length < 2 ^ (prefixWord ++ tailWord_2882124).sum := by decide
  have hdescent : baseEnd_2882124 < baseStart_2882124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882158 : List Nat := [4, 1, 2, 2, 2, 2, 1, 3, 1, 3, 2]
def baseStart_2882158 : Nat := 118140960795 + 2882158 * 2 ^ 59
def prefixEnd_2882158 : Nat := 4983230072969 + 3 ^ 40 * 2882158 * 2
def baseEnd_2882158 : Nat := 1479932376201239777270203

theorem tailTrace_2882158 : CollatzResearch.WordTrace tailWord_2882158 prefixEnd_2882158 1479932376201239777270203 := by
  unfold tailWord_2882158
  simp only [CollatzResearch.WordTrace]
  refine ⟨13140117286555159280350891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70080625528294182828538085 13140117286555159280350891)
  ·
    refine ⟨19710175929832738920526337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13140117286555159280350891 19710175929832738920526337)
    ·
      refine ⟨14782631947374554190394753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19710175929832738920526337 14782631947374554190394753)
      ·
        refine ⟨11086973960530915642796065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14782631947374554190394753 11086973960530915642796065)
        ·
          refine ⟨8315230470398186732097049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11086973960530915642796065 8315230470398186732097049)
          ·
            refine ⟨6236422852798640049072787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8315230470398186732097049 6236422852798640049072787)
            ·
              refine ⟨9354634279197960073609181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6236422852798640049072787 9354634279197960073609181)
              ·
                refine ⟨3507987854699235027603443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9354634279197960073609181 3507987854699235027603443)
                ·
                  refine ⟨5261981782048852541405165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3507987854699235027603443 5261981782048852541405165)
                  ·
                    refine ⟨1973243168268319703026937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5261981782048852541405165 1973243168268319703026937)
                    ·
                      refine ⟨1479932376201239777270203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1973243168268319703026937 1479932376201239777270203)
                      ·
                        rfl

theorem cell23_2882158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_2882158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882158 prefixEnd_2882158 := by exact prefixLift 2882158
  have htrace : WordTrace (prefixWord ++ tailWord_2882158) baseStart_2882158 baseEnd_2882158 := by
    simpa [prefixWord, tailWord_2882158, baseEnd_2882158] using wordTrace_append hprefix tailTrace_2882158
  have hstable : (prefixWord ++ tailWord_2882158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882158).length < 2 ^ (prefixWord ++ tailWord_2882158).sum := by decide
  have hdescent : baseEnd_2882158 < baseStart_2882158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882165 : List Nat := [1, 3, 4, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_2882165 : Nat := 118140960795 + 2882165 * 2 ^ 59
def prefixEnd_2882165 : Nat := 4983230072969 + 3 ^ 40 * 2882165 * 2
def baseEnd_2882165 : Nat := 1479935970565821249882671

theorem tailTrace_2882165 : CollatzResearch.WordTrace tailWord_2882165 prefixEnd_2882165 1479935970565821249882671 := by
  unfold tailWord_2882165
  simp only [CollatzResearch.WordTrace]
  refine ⟨105121193603415914438311949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70080795735610609625541299 105121193603415914438311949)
  ·
    refine ⟨39420447601280967914366981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105121193603415914438311949 39420447601280967914366981)
    ·
      refine ⟨7391333925240181483943809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39420447601280967914366981 7391333925240181483943809)
      ·
        refine ⟨5543500443930136112957857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7391333925240181483943809 5543500443930136112957857)
        ·
          refine ⟨4157625332947602084718393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5543500443930136112957857 4157625332947602084718393)
          ·
            refine ⟨3118218999710701563538795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4157625332947602084718393 3118218999710701563538795)
            ·
              refine ⟨4677328499566052345308193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3118218999710701563538795 4677328499566052345308193)
              ·
                refine ⟨3507996374674539258981145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4677328499566052345308193 3507996374674539258981145)
                ·
                  refine ⟨2630997281005904444235859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3507996374674539258981145 2630997281005904444235859)
                  ·
                    refine ⟨3946495921508856666353789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2630997281005904444235859 3946495921508856666353789)
                    ·
                      refine ⟨1479935970565821249882671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3946495921508856666353789 1479935970565821249882671)
                      ·
                        rfl

theorem cell23_2882165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_2882165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882165 prefixEnd_2882165 := by exact prefixLift 2882165
  have htrace : WordTrace (prefixWord ++ tailWord_2882165) baseStart_2882165 baseEnd_2882165 := by
    simpa [prefixWord, tailWord_2882165, baseEnd_2882165] using wordTrace_append hprefix tailTrace_2882165
  have hstable : (prefixWord ++ tailWord_2882165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882165).length < 2 ^ (prefixWord ++ tailWord_2882165).sum := by decide
  have hdescent : baseEnd_2882165 < baseStart_2882165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882167 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 4]
def baseStart_2882167 : Nat := 118140960795 + 2882167 * 2 ^ 59
def prefixEnd_2882167 : Nat := 4983230072969 + 3 ^ 40 * 2882167 * 2
def baseEnd_2882167 : Nat := 1479936997527130242057661

theorem tailTrace_2882167 : CollatzResearch.WordTrace tailWord_2882167 prefixEnd_2882167 1479936997527130242057661 := by
  unfold tailWord_2882167
  simp only [CollatzResearch.WordTrace]
  refine ⟨105121266549408668779884755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70080844366272445853256503 105121266549408668779884755)
  ·
    refine ⟨157681899824113003169827133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105121266549408668779884755 157681899824113003169827133)
    ·
      refine ⟨59130712434042376188685175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157681899824113003169827133 59130712434042376188685175)
      ·
        refine ⟨88696068651063564283027763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59130712434042376188685175 88696068651063564283027763)
        ·
          refine ⟨133044102976595346424541645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88696068651063564283027763 133044102976595346424541645)
          ·
            refine ⟨49891538616223254909203117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133044102976595346424541645 49891538616223254909203117)
            ·
              refine ⟨18709326981083720590951169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49891538616223254909203117 18709326981083720590951169)
              ·
                refine ⟨14031995235812790443213377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18709326981083720590951169 14031995235812790443213377)
                ·
                  refine ⟨10523996426859592832410033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14031995235812790443213377 10523996426859592832410033)
                  ·
                    refine ⟨7892997320144694624307525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10523996426859592832410033 7892997320144694624307525)
                    ·
                      refine ⟨1479936997527130242057661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7892997320144694624307525 1479936997527130242057661)
                      ·
                        rfl

theorem cell23_2882167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_2882167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882167 prefixEnd_2882167 := by exact prefixLift 2882167
  have htrace : WordTrace (prefixWord ++ tailWord_2882167) baseStart_2882167 baseEnd_2882167 := by
    simpa [prefixWord, tailWord_2882167, baseEnd_2882167] using wordTrace_append hprefix tailTrace_2882167
  have hstable : (prefixWord ++ tailWord_2882167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882167).length < 2 ^ (prefixWord ++ tailWord_2882167).sum := by decide
  have hdescent : baseEnd_2882167 < baseStart_2882167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882171 : List Nat := [1, 1, 1, 1, 1, 4, 2, 6, 2, 2, 2]
def baseStart_2882171 : Nat := 118140960795 + 2882171 * 2 ^ 59
def prefixEnd_2882171 : Nat := 4983230072969 + 3 ^ 40 * 2882171 * 2
def baseEnd_2882171 : Nat := 1479939051449748226407643

theorem tailTrace_2882171 : CollatzResearch.WordTrace tailWord_2882171 prefixEnd_2882171 1479939051449748226407643 := by
  unfold tailWord_2882171
  simp only [CollatzResearch.WordTrace]
  refine ⟨105121412441394177463030367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70080941627596118308686911 105121412441394177463030367)
  ·
    refine ⟨157682118662091266194545551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105121412441394177463030367 157682118662091266194545551)
    ·
      refine ⟨236523177993136899291818327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157682118662091266194545551 236523177993136899291818327)
      ·
        refine ⟨354784766989705348937727491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236523177993136899291818327 354784766989705348937727491)
        ·
          refine ⟨532177150484558023406591237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354784766989705348937727491 532177150484558023406591237)
          ·
            refine ⟨99783215715854629388735857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 532177150484558023406591237 99783215715854629388735857)
            ·
              refine ⟨74837411786890972041551893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99783215715854629388735857 74837411786890972041551893)
              ·
                refine ⟨3508003677510514314447745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74837411786890972041551893 3508003677510514314447745)
                ·
                  refine ⟨2631002758132885735835809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3508003677510514314447745 2631002758132885735835809)
                  ·
                    refine ⟨1973252068599664301876857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2631002758132885735835809 1973252068599664301876857)
                    ·
                      refine ⟨1479939051449748226407643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1973252068599664301876857 1479939051449748226407643)
                      ·
                        rfl

theorem cell23_2882171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 2, 2].length) (baseStart_2882171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882171 prefixEnd_2882171 := by exact prefixLift 2882171
  have htrace : WordTrace (prefixWord ++ tailWord_2882171) baseStart_2882171 baseEnd_2882171 := by
    simpa [prefixWord, tailWord_2882171, baseEnd_2882171] using wordTrace_append hprefix tailTrace_2882171
  have hstable : (prefixWord ++ tailWord_2882171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882171).length < 2 ^ (prefixWord ++ tailWord_2882171).sum := by decide
  have hdescent : baseEnd_2882171 < baseStart_2882171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882187 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 3]
def baseStart_2882187 : Nat := 118140960795 + 2882187 * 2 ^ 59
def prefixEnd_2882187 : Nat := 4983230072969 + 3 ^ 40 * 2882187 * 2
def baseEnd_2882187 : Nat := 1479947267140220163807569

theorem tailTrace_2882187 : CollatzResearch.WordTrace tailWord_2882187 prefixEnd_2882187 1479947267140220163807569 := by
  unfold tailWord_2882187
  simp only [CollatzResearch.WordTrace]
  refine ⟨105121996009336212195612815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70081330672890808130408543 105121996009336212195612815)
  ·
    refine ⟨157682994014004318293419223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105121996009336212195612815 157682994014004318293419223)
    ·
      refine ⟨236524491021006477440128835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157682994014004318293419223 236524491021006477440128835)
      ·
        refine ⟨354786736531509716160193253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236524491021006477440128835 354786736531509716160193253)
        ·
          refine ⟨66522513099658071780036235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 354786736531509716160193253 66522513099658071780036235)
          ·
            refine ⟨99783769649487107670054353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66522513099658071780036235 99783769649487107670054353)
            ·
              refine ⟨74837827237115330752540765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99783769649487107670054353 74837827237115330752540765)
              ·
                refine ⟨28064185213918249032202787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74837827237115330752540765 28064185213918249032202787)
                ·
                  refine ⟨42096277820877373548304181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28064185213918249032202787 42096277820877373548304181)
                  ·
                    refine ⟨3946526045707253770153517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42096277820877373548304181 3946526045707253770153517)
                    ·
                      refine ⟨1479947267140220163807569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3946526045707253770153517 1479947267140220163807569)
                      ·
                        rfl

theorem cell23_2882187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 3].length) (baseStart_2882187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882187 prefixEnd_2882187 := by exact prefixLift 2882187
  have htrace : WordTrace (prefixWord ++ tailWord_2882187) baseStart_2882187 baseEnd_2882187 := by
    simpa [prefixWord, tailWord_2882187, baseEnd_2882187] using wordTrace_append hprefix tailTrace_2882187
  have hstable : (prefixWord ++ tailWord_2882187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882187).length < 2 ^ (prefixWord ++ tailWord_2882187).sum := by decide
  have hdescent : baseEnd_2882187 < baseStart_2882187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882194 : List Nat := [3, 2, 3, 1, 2, 1, 2, 2, 7]
def baseStart_2882194 : Nat := 118140960795 + 2882194 * 2 ^ 59
def prefixEnd_2882194 : Nat := 4983230072969 + 3 ^ 40 * 2882194 * 2
def baseEnd_2882194 : Nat := 164438984611644626268893

theorem tailTrace_2882194 : CollatzResearch.WordTrace tailWord_2882194 prefixEnd_2882194 164438984611644626268893 := by
  unfold tailWord_2882194
  simp only [CollatzResearch.WordTrace]
  refine ⟨26280562830077713097779409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70081500880207234927411757 26280562830077713097779409)
  ·
    refine ⟨19710422122558284823334557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26280562830077713097779409 19710422122558284823334557)
    ·
      refine ⟨7391408295959356808750459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19710422122558284823334557 7391408295959356808750459)
      ·
        refine ⟨11087112443939035213125689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7391408295959356808750459 11087112443939035213125689)
        ·
          refine ⟨8315334332954276409844267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11087112443939035213125689 8315334332954276409844267)
          ·
            refine ⟨12473001499431414614766401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8315334332954276409844267 12473001499431414614766401)
            ·
              refine ⟨9354751124573560961074801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12473001499431414614766401 9354751124573560961074801)
              ·
                refine ⟨7016063343430170720806101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9354751124573560961074801 7016063343430170720806101)
                ·
                  refine ⟨164438984611644626268893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7016063343430170720806101 164438984611644626268893)
                  ·
                    rfl

theorem cell23_2882194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_2882194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882194 prefixEnd_2882194 := by exact prefixLift 2882194
  have htrace : WordTrace (prefixWord ++ tailWord_2882194) baseStart_2882194 baseEnd_2882194 := by
    simpa [prefixWord, tailWord_2882194, baseEnd_2882194] using wordTrace_append hprefix tailTrace_2882194
  have hstable : (prefixWord ++ tailWord_2882194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882194).length < 2 ^ (prefixWord ++ tailWord_2882194).sum := by decide
  have hdescent : baseEnd_2882194 < baseStart_2882194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882307 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 7]
def baseStart_2882307 : Nat := 118140960795 + 2882307 * 2 ^ 59
def prefixEnd_2882307 : Nat := 4983230072969 + 3 ^ 40 * 2882307 * 2
def baseEnd_2882307 : Nat := 1480008884818759694307017

theorem tailTrace_2882307 : CollatzResearch.WordTrace tailWord_2882307 prefixEnd_2882307 1480008884818759694307017 := by
  unfold tailWord_2882307
  simp only [CollatzResearch.WordTrace]
  refine ⟨105126372768901472689981175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70084248512600981793320783 105126372768901472689981175)
  ·
    refine ⟨157689559153352209034971763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105126372768901472689981175 157689559153352209034971763)
    ·
      refine ⟨236534338730028313552457645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157689559153352209034971763 236534338730028313552457645)
      ·
        refine ⟨88700377023760617582171617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236534338730028313552457645 88700377023760617582171617)
        ·
          refine ⟨66525282767820463186628713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88700377023760617582171617 66525282767820463186628713)
          ·
            refine ⟨49893962075865347389971535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66525282767820463186628713 49893962075865347389971535)
            ·
              refine ⟨74840943113798021084957303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49893962075865347389971535 74840943113798021084957303)
              ·
                refine ⟨112261414670697031627435955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74840943113798021084957303 112261414670697031627435955)
                ·
                  refine ⟨168392122006045547441153933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112261414670697031627435955 168392122006045547441153933)
                  ·
                    refine ⟨63147045752267080290432725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 168392122006045547441153933 63147045752267080290432725)
                    ·
                      refine ⟨1480008884818759694307017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63147045752267080290432725 1480008884818759694307017)
                      ·
                        rfl

theorem cell23_2882307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_2882307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882307 prefixEnd_2882307 := by exact prefixLift 2882307
  have htrace : WordTrace (prefixWord ++ tailWord_2882307) baseStart_2882307 baseEnd_2882307 := by
    simpa [prefixWord, tailWord_2882307, baseEnd_2882307] using wordTrace_append hprefix tailTrace_2882307
  have hstable : (prefixWord ++ tailWord_2882307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882307).length < 2 ^ (prefixWord ++ tailWord_2882307).sum := by decide
  have hdescent : baseEnd_2882307 < baseStart_2882307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882314 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 3, 5]
def baseStart_2882314 : Nat := 118140960795 + 2882314 * 2 ^ 59
def prefixEnd_2882314 : Nat := 4983230072969 + 3 ^ 40 * 2882314 * 2
def baseEnd_2882314 : Nat := 493337493061113722306495

theorem tailTrace_2882314 : CollatzResearch.WordTrace tailWord_2882314 prefixEnd_2882314 493337493061113722306495 := by
  unfold tailWord_2882314
  simp only [CollatzResearch.WordTrace]
  refine ⟨26281657019969028221371499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70084418719917408590323997 26281657019969028221371499)
  ·
    refine ⟨39422485529953542332057249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26281657019969028221371499 39422485529953542332057249)
    ·
      refine ⟨29566864147465156749042937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39422485529953542332057249 29566864147465156749042937)
      ·
        refine ⟨22175148110598867561782203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29566864147465156749042937 22175148110598867561782203)
        ·
          refine ⟨33262722165898301342673305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22175148110598867561782203 33262722165898301342673305)
          ·
            refine ⟨24947041624423726007004979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33262722165898301342673305 24947041624423726007004979)
            ·
              refine ⟨37420562436635589010507469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24947041624423726007004979 37420562436635589010507469)
              ·
                refine ⟨14032710913738345878940301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37420562436635589010507469 14032710913738345878940301)
                ·
                  refine ⟨5262266592651879704602613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14032710913738345878940301 5262266592651879704602613)
                  ·
                    refine ⟨493337493061113722306495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5262266592651879704602613 493337493061113722306495)
                    ·
                      rfl

theorem cell23_2882314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_2882314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882314 prefixEnd_2882314 := by exact prefixLift 2882314
  have htrace : WordTrace (prefixWord ++ tailWord_2882314) baseStart_2882314 baseEnd_2882314 := by
    simpa [prefixWord, tailWord_2882314, baseEnd_2882314] using wordTrace_append hprefix tailTrace_2882314
  have hstable : (prefixWord ++ tailWord_2882314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882314).length < 2 ^ (prefixWord ++ tailWord_2882314).sum := by decide
  have hdescent : baseEnd_2882314 < baseStart_2882314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882322 : List Nat := [3, 2, 4, 1, 2, 1, 2, 3, 1, 4]
def baseStart_2882322 : Nat := 118140960795 + 2882322 * 2 ^ 59
def prefixEnd_2882322 : Nat := 4983230072969 + 3 ^ 40 * 2882322 * 2
def baseEnd_2882322 : Nat := 493338862342859045206483

theorem tailTrace_2882322 : CollatzResearch.WordTrace tailWord_2882322 prefixEnd_2882322 493338862342859045206483 := by
  unfold tailWord_2882322
  simp only [CollatzResearch.WordTrace]
  refine ⟨26281729965961782562944305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70084613242564753501184813 26281729965961782562944305)
  ·
    refine ⟨19711297474471336922208229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26281729965961782562944305 19711297474471336922208229)
    ·
      refine ⟨3695868276463375672914043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19711297474471336922208229 3695868276463375672914043)
      ·
        refine ⟨5543802414695063509371065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3695868276463375672914043 5543802414695063509371065)
        ·
          refine ⟨4157851811021297632028299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5543802414695063509371065 4157851811021297632028299)
          ·
            refine ⟨6236777716531946448042449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4157851811021297632028299 6236777716531946448042449)
            ·
              refine ⟨4677583287398959836031837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6236777716531946448042449 4677583287398959836031837)
              ·
                refine ⟨1754093732774609938511939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4677583287398959836031837 1754093732774609938511939)
                ·
                  refine ⟨2631140599161914907767909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1754093732774609938511939 2631140599161914907767909)
                  ·
                    refine ⟨493338862342859045206483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2631140599161914907767909 493338862342859045206483)
                    ·
                      rfl

theorem cell23_2882322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_2882322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882322 prefixEnd_2882322 := by exact prefixLift 2882322
  have htrace : WordTrace (prefixWord ++ tailWord_2882322) baseStart_2882322 baseEnd_2882322 := by
    simpa [prefixWord, tailWord_2882322, baseEnd_2882322] using wordTrace_append hprefix tailTrace_2882322
  have hstable : (prefixWord ++ tailWord_2882322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882322).length < 2 ^ (prefixWord ++ tailWord_2882322).sum := by decide
  have hdescent : baseEnd_2882322 < baseStart_2882322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882388 : List Nat := [2, 4, 1, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_2882388 : Nat := 118140960795 + 2882388 * 2 ^ 59
def prefixEnd_2882388 : Nat := 4983230072969 + 3 ^ 40 * 2882388 * 2
def baseEnd_2882388 : Nat := 1480050476751773877394145

theorem tailTrace_2882388 : CollatzResearch.WordTrace tailWord_2882388 prefixEnd_2882388 1480050476751773877394145 := by
  unfold tailWord_2882388
  simp only [CollatzResearch.WordTrace]
  refine ⟨52564663540804011761839909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70086218054405349015786545 52564663540804011761839909)
  ·
    refine ⟨9855874413900752205344983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52564663540804011761839909 9855874413900752205344983)
    ·
      refine ⟨14783811620851128308017475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9855874413900752205344983 14783811620851128308017475)
      ·
        refine ⟨22175717431276692462026213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14783811620851128308017475 22175717431276692462026213)
        ·
          refine ⟨4157947018364379836629915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22175717431276692462026213 4157947018364379836629915)
          ·
            refine ⟨6236920527546569754944873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4157947018364379836629915 6236920527546569754944873)
            ·
              refine ⟨4677690395659927316208655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6236920527546569754944873 4677690395659927316208655)
              ·
                refine ⟨7016535593489890974312983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4677690395659927316208655 7016535593489890974312983)
                ·
                  refine ⟨10524803390234836461469475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7016535593489890974312983 10524803390234836461469475)
                  ·
                    refine ⟨15787205085352254692204213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10524803390234836461469475 15787205085352254692204213)
                    ·
                      refine ⟨1480050476751773877394145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15787205085352254692204213 1480050476751773877394145)
                      ·
                        rfl

theorem cell23_2882388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_2882388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882388 prefixEnd_2882388 := by exact prefixLift 2882388
  have htrace : WordTrace (prefixWord ++ tailWord_2882388) baseStart_2882388 baseEnd_2882388 := by
    simpa [prefixWord, tailWord_2882388, baseEnd_2882388] using wordTrace_append hprefix tailTrace_2882388
  have hstable : (prefixWord ++ tailWord_2882388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882388).length < 2 ^ (prefixWord ++ tailWord_2882388).sum := by decide
  have hdescent : baseEnd_2882388 < baseStart_2882388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882422 : List Nat := [5, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3]
def baseStart_2882422 : Nat := 118140960795 + 2882422 * 2 ^ 59
def prefixEnd_2882422 : Nat := 4983230072969 + 3 ^ 40 * 2882422 * 2
def baseEnd_2882422 : Nat := 1480067935094026744368989

theorem tailTrace_2882422 : CollatzResearch.WordTrace tailWord_2882422 prefixEnd_2882422 1480067935094026744368989 := by
  unfold tailWord_2882422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6570660447717802958151095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70087044775656564886945013 6570660447717802958151095)
  ·
    refine ⟨9855990671576704437226643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6570660447717802958151095 9855990671576704437226643)
    ·
      refine ⟨14783986007365056655839965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9855990671576704437226643 14783986007365056655839965)
      ·
        refine ⟨5543994752761896245939987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14783986007365056655839965 5543994752761896245939987)
        ·
          refine ⟨8315992129142844368909981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5543994752761896245939987 8315992129142844368909981)
          ·
            refine ⟨3118497048428566638341243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8315992129142844368909981 3118497048428566638341243)
            ·
              refine ⟨4677745572642849957511865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3118497048428566638341243 4677745572642849957511865)
              ·
                refine ⟨3508309179482137468133899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4677745572642849957511865 3508309179482137468133899)
                ·
                  refine ⟨5262463769223206202200849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3508309179482137468133899 5262463769223206202200849)
                  ·
                    refine ⟨3946847826917404651650637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5262463769223206202200849 3946847826917404651650637)
                    ·
                      refine ⟨1480067935094026744368989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3946847826917404651650637 1480067935094026744368989)
                      ·
                        rfl

theorem cell23_2882422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_2882422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882422 prefixEnd_2882422 := by exact prefixLift 2882422
  have htrace : WordTrace (prefixWord ++ tailWord_2882422) baseStart_2882422 baseEnd_2882422 := by
    simpa [prefixWord, tailWord_2882422, baseEnd_2882422] using wordTrace_append hprefix tailTrace_2882422
  have hstable : (prefixWord ++ tailWord_2882422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882422).length < 2 ^ (prefixWord ++ tailWord_2882422).sum := by decide
  have hdescent : baseEnd_2882422 < baseStart_2882422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882424 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 4, 3, 4]
def baseStart_2882424 : Nat := 118140960795 + 2882424 * 2 ^ 59
def prefixEnd_2882424 : Nat := 4983230072969 + 3 ^ 40 * 2882424 * 2
def baseEnd_2882424 : Nat := 1480068962055335736543979

theorem tailTrace_2882424 : CollatzResearch.WordTrace tailWord_2882424 prefixEnd_2882424 1480068962055335736543979 := by
  unfold tailWord_2882424
  simp only [CollatzResearch.WordTrace]
  refine ⟨52565320054738800835995163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70087093406318401114660217 52565320054738800835995163)
  ·
    refine ⟨78847980082108201253992745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52565320054738800835995163 78847980082108201253992745)
    ·
      refine ⟨59135985061581150940494559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78847980082108201253992745 59135985061581150940494559)
      ·
        refine ⟨88703977592371726410741839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59135985061581150940494559 88703977592371726410741839)
        ·
          refine ⟨133055966388557589616112759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88703977592371726410741839 133055966388557589616112759)
          ·
            refine ⟨199583949582836384424169139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133055966388557589616112759 199583949582836384424169139)
            ·
              refine ⟨299375924374254576636253709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199583949582836384424169139 299375924374254576636253709)
              ·
                refine ⟨112265971640345466238595141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 299375924374254576636253709 112265971640345466238595141)
                ·
                  refine ⟨21049869682564774919736589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112265971640345466238595141 21049869682564774919736589)
                  ·
                    refine ⟨7893701130961790594901221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21049869682564774919736589 7893701130961790594901221)
                    ·
                      refine ⟨1480068962055335736543979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7893701130961790594901221 1480068962055335736543979)
                      ·
                        rfl

theorem cell23_2882424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_2882424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882424 prefixEnd_2882424 := by exact prefixLift 2882424
  have htrace : WordTrace (prefixWord ++ tailWord_2882424) baseStart_2882424 baseEnd_2882424 := by
    simpa [prefixWord, tailWord_2882424, baseEnd_2882424] using wordTrace_append hprefix tailTrace_2882424
  have hstable : (prefixWord ++ tailWord_2882424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882424).length < 2 ^ (prefixWord ++ tailWord_2882424).sum := by decide
  have hdescent : baseEnd_2882424 < baseStart_2882424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882461 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_2882461 : Nat := 118140960795 + 2882461 * 2 ^ 59
def prefixEnd_2882461 : Nat := 4983230072969 + 3 ^ 40 * 2882461 * 2
def baseEnd_2882461 : Nat := 1480087960839552091781309

theorem tailTrace_2882461 : CollatzResearch.WordTrace tailWord_2882461 prefixEnd_2882461 1480087960839552091781309 := by
  unfold tailWord_2882461
  simp only [CollatzResearch.WordTrace]
  refine ⟨105131989610343556991087237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70087993073562371327391491 105131989610343556991087237)
  ·
    refine ⟨19712248051939416935828857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105131989610343556991087237 19712248051939416935828857)
    ·
      refine ⟨14784186038954562701871643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19712248051939416935828857 14784186038954562701871643)
      ·
        refine ⟨22176279058431844052807465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14784186038954562701871643 22176279058431844052807465)
        ·
          refine ⟨16632209293823883039605599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22176279058431844052807465 16632209293823883039605599)
          ·
            refine ⟨24948313940735824559408399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16632209293823883039605599 24948313940735824559408399)
            ·
              refine ⟨37422470911103736839112599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24948313940735824559408399 37422470911103736839112599)
              ·
                refine ⟨56133706366655605258668899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37422470911103736839112599 56133706366655605258668899)
                ·
                  refine ⟨84200559549983407888003349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56133706366655605258668899 84200559549983407888003349)
                  ·
                    refine ⟨3946901228905472244750157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84200559549983407888003349 3946901228905472244750157)
                    ·
                      refine ⟨1480087960839552091781309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3946901228905472244750157 1480087960839552091781309)
                      ·
                        rfl

theorem cell23_2882461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_2882461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882461 prefixEnd_2882461 := by exact prefixLift 2882461
  have htrace : WordTrace (prefixWord ++ tailWord_2882461) baseStart_2882461 baseEnd_2882461 := by
    simpa [prefixWord, tailWord_2882461, baseEnd_2882461] using wordTrace_append hprefix tailTrace_2882461
  have hstable : (prefixWord ++ tailWord_2882461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882461).length < 2 ^ (prefixWord ++ tailWord_2882461).sum := by decide
  have hdescent : baseEnd_2882461 < baseStart_2882461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882531 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 4]
def baseStart_2882531 : Nat := 118140960795 + 2882531 * 2 ^ 59
def prefixEnd_2882531 : Nat := 4983230072969 + 3 ^ 40 * 2882531 * 2
def baseEnd_2882531 : Nat := 1480123904485366817905987

theorem tailTrace_2882531 : CollatzResearch.WordTrace tailWord_2882531 prefixEnd_2882531 1480123904485366817905987 := by
  unfold tailWord_2882531
  simp only [CollatzResearch.WordTrace]
  refine ⟨105134542720089958946135447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70089695146726639297423631 105134542720089958946135447)
  ·
    refine ⟨157701814080134938419203171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105134542720089958946135447 157701814080134938419203171)
    ·
      refine ⟨236552721120202407628804757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157701814080134938419203171 236552721120202407628804757)
      ·
        refine ⟨11088408802509487857600223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 236552721120202407628804757 11088408802509487857600223)
        ·
          refine ⟨16632613203764231786400335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11088408802509487857600223 16632613203764231786400335)
          ·
            refine ⟨24948919805646347679600503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16632613203764231786400335 24948919805646347679600503)
            ·
              refine ⟨37423379708469521519400755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24948919805646347679600503 37423379708469521519400755)
              ·
                refine ⟨56135069562704282279101133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37423379708469521519400755 56135069562704282279101133)
                ·
                  refine ⟨21050651086014105854662925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56135069562704282279101133 21050651086014105854662925)
                  ·
                    refine ⟨7893994157255289695498597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21050651086014105854662925 7893994157255289695498597)
                    ·
                      refine ⟨1480123904485366817905987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7893994157255289695498597 1480123904485366817905987)
                      ·
                        rfl

theorem cell23_2882531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_2882531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882531 prefixEnd_2882531 := by exact prefixLift 2882531
  have htrace : WordTrace (prefixWord ++ tailWord_2882531) baseStart_2882531 baseEnd_2882531 := by
    simpa [prefixWord, tailWord_2882531, baseEnd_2882531] using wordTrace_append hprefix tailTrace_2882531
  have hstable : (prefixWord ++ tailWord_2882531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882531).length < 2 ^ (prefixWord ++ tailWord_2882531).sum := by decide
  have hdescent : baseEnd_2882531 < baseStart_2882531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882549 : List Nat := [1, 3, 5, 2, 1, 2, 1, 3, 5]
def baseStart_2882549 : Nat := 118140960795 + 2882549 * 2 ^ 59
def prefixEnd_2882549 : Nat := 4983230072969 + 3 ^ 40 * 2882549 * 2
def baseEnd_2882549 : Nat := 164459238570794194164545

theorem tailTrace_2882549 : CollatzResearch.WordTrace tailWord_2882549 prefixEnd_2882549 164459238570794194164545 := by
  unfold tailWord_2882549
  simp only [CollatzResearch.WordTrace]
  refine ⟨105135199234024748020290701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70090132822683165346860467 105135199234024748020290701)
  ·
    refine ⟨39425699712759280507609013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105135199234024748020290701 39425699712759280507609013)
    ·
      refine ⟨3696159348071182547588345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39425699712759280507609013 3696159348071182547588345)
      ·
        refine ⟨2772119511053386910691259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3696159348071182547588345 2772119511053386910691259)
        ·
          refine ⟨4158179266580080366036889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2772119511053386910691259 4158179266580080366036889)
          ·
            refine ⟨3118634449935060274527667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4158179266580080366036889 3118634449935060274527667)
            ·
              refine ⟨4677951674902590411791501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3118634449935060274527667 4677951674902590411791501)
              ·
                refine ⟨1754231878088471404421813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4677951674902590411791501 1754231878088471404421813)
                ·
                  refine ⟨164459238570794194164545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1754231878088471404421813 164459238570794194164545)
                  ·
                    rfl

theorem cell23_2882549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 5].length) (baseStart_2882549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882549 prefixEnd_2882549 := by exact prefixLift 2882549
  have htrace : WordTrace (prefixWord ++ tailWord_2882549) baseStart_2882549 baseEnd_2882549 := by
    simpa [prefixWord, tailWord_2882549, baseEnd_2882549] using wordTrace_append hprefix tailTrace_2882549
  have hstable : (prefixWord ++ tailWord_2882549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882549).length < 2 ^ (prefixWord ++ tailWord_2882549).sum := by decide
  have hdescent : baseEnd_2882549 < baseStart_2882549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882562 : List Nat := [3, 4, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_2882562 : Nat := 118140960795 + 2882562 * 2 ^ 59
def prefixEnd_2882562 : Nat := 4983230072969 + 3 ^ 40 * 2882562 * 2
def baseEnd_2882562 : Nat := 493379940795218732206115

theorem tailTrace_2882562 : CollatzResearch.WordTrace tailWord_2882562 prefixEnd_2882562 493379940795218732206115 := by
  unfold tailWord_2882562
  simp only [CollatzResearch.WordTrace]
  refine ⟨26283918345744412810128485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70090448921985100827009293 26283918345744412810128485)
  ·
    refine ⟨4928234689827077401899091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26283918345744412810128485 4928234689827077401899091)
    ·
      refine ⟨7392352034740616102848637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4928234689827077401899091 7392352034740616102848637)
      ·
        refine ⟨2772132013027731038568239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7392352034740616102848637 2772132013027731038568239)
        ·
          refine ⟨4158198019541596557852359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2772132013027731038568239 4158198019541596557852359)
          ·
            refine ⟨6237297029312394836778539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4158198019541596557852359 6237297029312394836778539)
            ·
              refine ⟨9355945543968592255167809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6237297029312394836778539 9355945543968592255167809)
              ·
                refine ⟨7016959157976444191375857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9355945543968592255167809 7016959157976444191375857)
                ·
                  refine ⟨5262719368482333143531893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7016959157976444191375857 5262719368482333143531893)
                  ·
                    refine ⟨493379940795218732206115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5262719368482333143531893 493379940795218732206115)
                    ·
                      rfl

theorem cell23_2882562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_2882562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882562 prefixEnd_2882562 := by exact prefixLift 2882562
  have htrace : WordTrace (prefixWord ++ tailWord_2882562) baseStart_2882562 baseEnd_2882562 := by
    simpa [prefixWord, tailWord_2882562, baseEnd_2882562] using wordTrace_append hprefix tailTrace_2882562
  have hstable : (prefixWord ++ tailWord_2882562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882562).length < 2 ^ (prefixWord ++ tailWord_2882562).sum := by decide
  have hdescent : baseEnd_2882562 < baseStart_2882562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882568 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 4, 2, 3]
def baseStart_2882568 : Nat := 118140960795 + 2882568 * 2 ^ 59
def prefixEnd_2882568 : Nat := 4983230072969 + 3 ^ 40 * 2882568 * 2
def baseEnd_2882568 : Nat := 1480142903269583173143317

theorem tailTrace_2882568 : CollatzResearch.WordTrace tailWord_2882568 prefixEnd_2882568 1480142903269583173143317 := by
  unfold tailWord_2882568
  simp only [CollatzResearch.WordTrace]
  refine ⟨52567946110477957132616179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70090594813970609510154905 52567946110477957132616179)
  ·
    refine ⟨78851919165716935698924269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52567946110477957132616179 78851919165716935698924269)
    ·
      refine ⟨29569469687143850887096601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78851919165716935698924269 29569469687143850887096601)
      ·
        refine ⟨22177102265357888165322451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29569469687143850887096601 22177102265357888165322451)
        ·
          refine ⟨33265653398036832247983677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22177102265357888165322451 33265653398036832247983677)
          ·
            refine ⟨12474620024263812092993879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33265653398036832247983677 12474620024263812092993879)
            ·
              refine ⟨18711930036395718139490819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12474620024263812092993879 18711930036395718139490819)
              ·
                refine ⟨28067895054593577209236229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18711930036395718139490819 28067895054593577209236229)
                ·
                  refine ⟨5262730322736295726731793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28067895054593577209236229 5262730322736295726731793)
                  ·
                    refine ⟨3947047742052221795048845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5262730322736295726731793 3947047742052221795048845)
                    ·
                      refine ⟨1480142903269583173143317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3947047742052221795048845 1480142903269583173143317)
                      ·
                        rfl

theorem cell23_2882568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_2882568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882568 prefixEnd_2882568 := by exact prefixLift 2882568
  have htrace : WordTrace (prefixWord ++ tailWord_2882568) baseStart_2882568 baseEnd_2882568 := by
    simpa [prefixWord, tailWord_2882568, baseEnd_2882568] using wordTrace_append hprefix tailTrace_2882568
  have hstable : (prefixWord ++ tailWord_2882568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882568).length < 2 ^ (prefixWord ++ tailWord_2882568).sum := by decide
  have hdescent : baseEnd_2882568 < baseStart_2882568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882571 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 8]
def baseStart_2882571 : Nat := 118140960795 + 2882571 * 2 ^ 59
def prefixEnd_2882571 : Nat := 4983230072969 + 3 ^ 40 * 2882571 * 2
def baseEnd_2882571 : Nat := 164460493745727406822867

theorem tailTrace_2882571 : CollatzResearch.WordTrace tailWord_2882571 prefixEnd_2882571 164460493745727406822867 := by
  unfold tailWord_2882571
  simp only [CollatzResearch.WordTrace]
  refine ⟨105136001639945045777591567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70090667759963363851727711 105136001639945045777591567)
  ·
    refine ⟨157704002459917568666387351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105136001639945045777591567 157704002459917568666387351)
    ·
      refine ⟨236556003689876352999581027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157704002459917568666387351 236556003689876352999581027)
      ·
        refine ⟨354834005534814529499371541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236556003689876352999581027 354834005534814529499371541)
        ·
          refine ⟨16632844009444431070283041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 354834005534814529499371541 16632844009444431070283041)
          ·
            refine ⟨12474633007083323302712281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16632844009444431070283041 12474633007083323302712281)
            ·
              refine ⟨9355974755312492477034211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12474633007083323302712281 9355974755312492477034211)
              ·
                refine ⟨14033962132968738715551317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9355974755312492477034211 14033962132968738715551317)
                ·
                  refine ⟨164460493745727406822867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14033962132968738715551317 164460493745727406822867)
                  ·
                    rfl

theorem cell23_2882571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 8].length) (baseStart_2882571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882571 prefixEnd_2882571 := by exact prefixLift 2882571
  have htrace : WordTrace (prefixWord ++ tailWord_2882571) baseStart_2882571 baseEnd_2882571 := by
    simpa [prefixWord, tailWord_2882571, baseEnd_2882571] using wordTrace_append hprefix tailTrace_2882571
  have hstable : (prefixWord ++ tailWord_2882571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882571).length < 2 ^ (prefixWord ++ tailWord_2882571).sum := by decide
  have hdescent : baseEnd_2882571 < baseStart_2882571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882602 : List Nat := [3, 1, 4, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_2882602 : Nat := 118140960795 + 2882602 * 2 ^ 59
def prefixEnd_2882602 : Nat := 4983230072969 + 3 ^ 40 * 2882602 * 2
def baseEnd_2882602 : Nat := 1480160361611836040118161

theorem tailTrace_2882602 : CollatzResearch.WordTrace tailWord_2882602 prefixEnd_2882602 1480160361611836040118161 := by
  unfold tailWord_2882602
  simp only [CollatzResearch.WordTrace]
  refine ⟨26284283075708184517992515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70091421535221825381313373 26284283075708184517992515)
  ·
    refine ⟨39426424613562276776988773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26284283075708184517992515 39426424613562276776988773)
    ·
      refine ⟨7392454615042926895685395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39426424613562276776988773 7392454615042926895685395)
      ·
        refine ⟨11088681922564390343528093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7392454615042926895685395 11088681922564390343528093)
        ·
          refine ⟨4158255720961646378823035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11088681922564390343528093 4158255720961646378823035)
          ·
            refine ⟨6237383581442469568234553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4158255720961646378823035 6237383581442469568234553)
            ·
              refine ⟨4678037686081852176175915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6237383581442469568234553 4678037686081852176175915)
              ·
                refine ⟨7017056529122778264263873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4678037686081852176175915 7017056529122778264263873)
                ·
                  refine ⟨5262792396842083698197905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7017056529122778264263873 5262792396842083698197905)
                  ·
                    refine ⟨3947094297631562773648429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5262792396842083698197905 3947094297631562773648429)
                    ·
                      refine ⟨1480160361611836040118161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3947094297631562773648429 1480160361611836040118161)
                      ·
                        rfl

theorem cell23_2882602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_2882602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882602 prefixEnd_2882602 := by exact prefixLift 2882602
  have htrace : WordTrace (prefixWord ++ tailWord_2882602) baseStart_2882602 baseEnd_2882602 := by
    simpa [prefixWord, tailWord_2882602, baseEnd_2882602] using wordTrace_append hprefix tailTrace_2882602
  have hstable : (prefixWord ++ tailWord_2882602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882602).length < 2 ^ (prefixWord ++ tailWord_2882602).sum := by decide
  have hdescent : baseEnd_2882602 < baseStart_2882602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882618 : List Nat := [3, 1, 1, 1, 3, 1, 2, 5, 1, 5]
def baseStart_2882618 : Nat := 118140960795 + 2882618 * 2 ^ 59
def prefixEnd_2882618 : Nat := 4983230072969 + 3 ^ 40 * 2882618 * 2
def baseEnd_2882618 : Nat := 493389525767435992506029

theorem tailTrace_2882618 : CollatzResearch.WordTrace tailWord_2882618 prefixEnd_2882618 493389525767435992506029 := by
  unfold tailWord_2882618
  simp only [CollatzResearch.WordTrace]
  refine ⟨26284428967693693201138127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70091810580516515203035005 26284428967693693201138127)
  ·
    refine ⟨39426643451540539801707191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26284428967693693201138127 39426643451540539801707191)
    ·
      refine ⟨59139965177310809702560787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39426643451540539801707191 59139965177310809702560787)
      ·
        refine ⟨88709947765966214553841181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59139965177310809702560787 88709947765966214553841181)
        ·
          refine ⟨33266230412237330457690443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88709947765966214553841181 33266230412237330457690443)
          ·
            refine ⟨49899345618355995686535665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33266230412237330457690443 49899345618355995686535665)
            ·
              refine ⟨37424509213766996764901749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49899345618355995686535665 37424509213766996764901749)
              ·
                refine ⟨3508547738790655946709539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37424509213766996764901749 3508547738790655946709539)
                ·
                  refine ⟨5262821608185983920064309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3508547738790655946709539 5262821608185983920064309)
                  ·
                    refine ⟨493389525767435992506029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5262821608185983920064309 493389525767435992506029)
                    ·
                      rfl

theorem cell23_2882618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 1, 5].length) (baseStart_2882618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882618 prefixEnd_2882618 := by exact prefixLift 2882618
  have htrace : WordTrace (prefixWord ++ tailWord_2882618) baseStart_2882618 baseEnd_2882618 := by
    simpa [prefixWord, tailWord_2882618, baseEnd_2882618] using wordTrace_append hprefix tailTrace_2882618
  have hstable : (prefixWord ++ tailWord_2882618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882618).length < 2 ^ (prefixWord ++ tailWord_2882618).sum := by decide
  have hdescent : baseEnd_2882618 < baseStart_2882618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882632 : List Nat := [2, 1, 3, 1, 1, 1, 5, 4, 1, 1, 3]
def baseStart_2882632 : Nat := 118140960795 + 2882632 * 2 ^ 59
def prefixEnd_2882632 : Nat := 4983230072969 + 3 ^ 40 * 2882632 * 2
def baseEnd_2882632 : Nat := 1480175766031470922743023

theorem tailTrace_2882632 : CollatzResearch.WordTrace tailWord_2882632 prefixEnd_2882632 1480175766031470922743023 := by
  unfold tailWord_2882632
  simp only [CollatzResearch.WordTrace]
  refine ⟨52569113246362026597781075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70092150995149368797041433 52569113246362026597781075)
  ·
    refine ⟨78853669869543039896671613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52569113246362026597781075 78853669869543039896671613)
    ·
      refine ⟨29570126201078639961251855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78853669869543039896671613 29570126201078639961251855)
      ·
        refine ⟨44355189301617959941877783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29570126201078639961251855 44355189301617959941877783)
        ·
          refine ⟨66532783952426939912816675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44355189301617959941877783 66532783952426939912816675)
          ·
            refine ⟨99799175928640409869225013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66532783952426939912816675 99799175928640409869225013)
            ·
              refine ⟨9356172743310038425239845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99799175928640409869225013 9356172743310038425239845)
              ·
                refine ⟨1754282389370632204732471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9356172743310038425239845 1754282389370632204732471)
                ·
                  refine ⟨2631423584055948307098707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1754282389370632204732471 2631423584055948307098707)
                  ·
                    refine ⟨3947135376083922460648061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2631423584055948307098707 3947135376083922460648061)
                    ·
                      refine ⟨1480175766031470922743023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3947135376083922460648061 1480175766031470922743023)
                      ·
                        rfl

theorem cell23_2882632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 1, 1, 3].length) (baseStart_2882632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882632 prefixEnd_2882632 := by exact prefixLift 2882632
  have htrace : WordTrace (prefixWord ++ tailWord_2882632) baseStart_2882632 baseEnd_2882632 := by
    simpa [prefixWord, tailWord_2882632, baseEnd_2882632] using wordTrace_append hprefix tailTrace_2882632
  have hstable : (prefixWord ++ tailWord_2882632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882632).length < 2 ^ (prefixWord ++ tailWord_2882632).sum := by decide
  have hdescent : baseEnd_2882632 < baseStart_2882632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882638 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4]
def baseStart_2882638 : Nat := 118140960795 + 2882638 * 2 ^ 59
def prefixEnd_2882638 : Nat := 4983230072969 + 3 ^ 40 * 2882638 * 2
def baseEnd_2882638 : Nat := 1480178846915397899267995

theorem tailTrace_2882638 : CollatzResearch.WordTrace tailWord_2882638 prefixEnd_2882638 1480178846915397899267995 := by
  unfold tailWord_2882638
  simp only [CollatzResearch.WordTrace]
  refine ⟨13142305666337789527535071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70092296887134877480187045 13142305666337789527535071)
  ·
    refine ⟨19713458499506684291302607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13142305666337789527535071 19713458499506684291302607)
    ·
      refine ⟨29570187749260026436953911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19713458499506684291302607 29570187749260026436953911)
      ·
        refine ⟨44355281623890039655430867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29570187749260026436953911 44355281623890039655430867)
        ·
          refine ⟨66532922435835059483146301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44355281623890039655430867 66532922435835059483146301)
          ·
            refine ⟨24949845913438147306179863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66532922435835059483146301 24949845913438147306179863)
            ·
              refine ⟨37424768870157220959269795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24949845913438147306179863 37424768870157220959269795)
              ·
                refine ⟨56137153305235831438904693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37424768870157220959269795 56137153305235831438904693)
                ·
                  refine ⟨5262858122365859197397315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56137153305235831438904693 5262858122365859197397315)
                  ·
                    refine ⟨7894287183548788796095973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5262858122365859197397315 7894287183548788796095973)
                    ·
                      refine ⟨1480178846915397899267995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7894287183548788796095973 1480178846915397899267995)
                      ·
                        rfl

theorem cell23_2882638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_2882638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882638 prefixEnd_2882638 := by exact prefixLift 2882638
  have htrace : WordTrace (prefixWord ++ tailWord_2882638) baseStart_2882638 baseEnd_2882638 := by
    simpa [prefixWord, tailWord_2882638, baseEnd_2882638] using wordTrace_append hprefix tailTrace_2882638
  have hstable : (prefixWord ++ tailWord_2882638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882638).length < 2 ^ (prefixWord ++ tailWord_2882638).sum := by decide
  have hdescent : baseEnd_2882638 < baseStart_2882638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882648 : List Nat := [2, 1, 2, 2, 1, 3, 4, 1, 1, 6]
def baseStart_2882648 : Nat := 118140960795 + 2882648 * 2 ^ 59
def prefixEnd_2882648 : Nat := 4983230072969 + 3 ^ 40 * 2882648 * 2
def baseEnd_2882648 : Nat := 493394660573980953380983

theorem tailTrace_2882648 : CollatzResearch.WordTrace tailWord_2882648 prefixEnd_2882648 493394660573980953380983 := by
  unfold tailWord_2882648
  simp only [CollatzResearch.WordTrace]
  refine ⟨52569405030333043964072299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70092540040444058618763065 52569405030333043964072299)
  ·
    refine ⟨78854107545499565946108449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52569405030333043964072299 78854107545499565946108449)
    ·
      refine ⟨59140580659124674459581337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78854107545499565946108449 59140580659124674459581337)
      ·
        refine ⟨44355435494343505844686003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59140580659124674459581337 44355435494343505844686003)
        ·
          refine ⟨66533153241515258767029005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44355435494343505844686003 66533153241515258767029005)
          ·
            refine ⟨24949932465568222037635877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66533153241515258767029005 24949932465568222037635877)
            ·
              refine ⟨4678112337294041632056727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24949932465568222037635877 4678112337294041632056727)
              ·
                refine ⟨7017168505941062448085091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4678112337294041632056727 7017168505941062448085091)
                ·
                  refine ⟨10525752758911593672127637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7017168505941062448085091 10525752758911593672127637)
                  ·
                    refine ⟨493394660573980953380983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10525752758911593672127637 493394660573980953380983)
                    ·
                      rfl

theorem cell23_2882648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_2882648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882648 prefixEnd_2882648 := by exact prefixLift 2882648
  have htrace : WordTrace (prefixWord ++ tailWord_2882648) baseStart_2882648 baseEnd_2882648 := by
    simpa [prefixWord, tailWord_2882648, baseEnd_2882648] using wordTrace_append hprefix tailTrace_2882648
  have hstable : (prefixWord ++ tailWord_2882648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882648).length < 2 ^ (prefixWord ++ tailWord_2882648).sum := by decide
  have hdescent : baseEnd_2882648 < baseStart_2882648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882668 : List Nat := [2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 4]
def baseStart_2882668 : Nat := 118140960795 + 2882668 * 2 ^ 59
def prefixEnd_2882668 : Nat := 4983230072969 + 3 ^ 40 * 2882668 * 2
def baseEnd_2882668 : Nat := 1480194251335032781892857

theorem tailTrace_2882668 : CollatzResearch.WordTrace tailWord_2882668 prefixEnd_2882668 1480194251335032781892857 := by
  unfold tailWord_2882668
  simp only [CollatzResearch.WordTrace]
  refine ⟨52569769760296815671936329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70093026347062420895915105 52569769760296815671936329)
  ·
    refine ⟨39427327320222611753952247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52569769760296815671936329 39427327320222611753952247)
    ·
      refine ⟨59140990980333917630928371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39427327320222611753952247 59140990980333917630928371)
      ·
        refine ⟨88711486470500876446392557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59140990980333917630928371 88711486470500876446392557)
        ·
          refine ⟨33266807426437828667397209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88711486470500876446392557 33266807426437828667397209)
          ·
            refine ⟨24950105569828371500547907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33266807426437828667397209 24950105569828371500547907)
            ·
              refine ⟨37425158354742557250821861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24950105569828371500547907 37425158354742557250821861)
              ·
                refine ⟨7017217191514229484529099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37425158354742557250821861 7017217191514229484529099)
                ·
                  refine ⟨10525825787271344226793649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7017217191514229484529099 10525825787271344226793649)
                  ·
                    refine ⟨7894369340453508170095237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10525825787271344226793649 7894369340453508170095237)
                    ·
                      refine ⟨1480194251335032781892857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7894369340453508170095237 1480194251335032781892857)
                      ·
                        rfl

theorem cell23_2882668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_2882668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882668 prefixEnd_2882668 := by exact prefixLift 2882668
  have htrace : WordTrace (prefixWord ++ tailWord_2882668) baseStart_2882668 baseEnd_2882668 := by
    simpa [prefixWord, tailWord_2882668, baseEnd_2882668] using wordTrace_append hprefix tailTrace_2882668
  have hstable : (prefixWord ++ tailWord_2882668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882668).length < 2 ^ (prefixWord ++ tailWord_2882668).sum := by decide
  have hdescent : baseEnd_2882668 < baseStart_2882668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882678 : List Nat := [5, 1, 1, 2, 1, 1, 12]
def baseStart_2882678 : Nat := 118140960795 + 2882678 * 2 ^ 59
def prefixEnd_2882678 : Nat := 4983230072969 + 3 ^ 40 * 2882678 * 2
def baseEnd_2882678 : Nat := 18274066495575033861331

theorem tailTrace_2882678 : CollatzResearch.WordTrace tailWord_2882678 prefixEnd_2882678 18274066495575033861331 := by
  unfold tailWord_2882678
  simp only [CollatzResearch.WordTrace]
  refine ⟨6571244015659837690733543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70093269500371602034491125 6571244015659837690733543)
  ·
    refine ⟨9856866023489756536100315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6571244015659837690733543 9856866023489756536100315)
    ·
      refine ⟨14785299035234634804150473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9856866023489756536100315 14785299035234634804150473)
      ·
        refine ⟨11088974276425976103112855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14785299035234634804150473 11088974276425976103112855)
        ·
          refine ⟨16633461414638964154669283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11088974276425976103112855 16633461414638964154669283)
          ·
            refine ⟨24950192121958446232003925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16633461414638964154669283 24950192121958446232003925)
            ·
              refine ⟨18274066495575033861331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 24950192121958446232003925 18274066495575033861331)
              ·
                rfl

theorem cell23_2882678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 12].length) (baseStart_2882678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882678 prefixEnd_2882678 := by exact prefixLift 2882678
  have htrace : WordTrace (prefixWord ++ tailWord_2882678) baseStart_2882678 baseEnd_2882678 := by
    simpa [prefixWord, tailWord_2882678, baseEnd_2882678] using wordTrace_append hprefix tailTrace_2882678
  have hstable : (prefixWord ++ tailWord_2882678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882678).length < 2 ^ (prefixWord ++ tailWord_2882678).sum := by decide
  have hdescent : baseEnd_2882678 < baseStart_2882678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882688 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 3]
def baseStart_2882688 : Nat := 118140960795 + 2882688 * 2 ^ 59
def prefixEnd_2882688 : Nat := 4983230072969 + 3 ^ 40 * 2882688 * 2
def baseEnd_2882688 : Nat := 1480204520948122703642765

theorem tailTrace_2882688 : CollatzResearch.WordTrace tailWord_2882688 prefixEnd_2882688 1480204520948122703642765 := by
  unfold tailWord_2882688
  simp only [CollatzResearch.WordTrace]
  refine ⟨52570134490260587379800359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70093512653680783173067145 52570134490260587379800359)
  ·
    refine ⟨78855201735390881069700539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52570134490260587379800359 78855201735390881069700539)
    ·
      refine ⟨118282802603086321604550809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78855201735390881069700539 118282802603086321604550809)
      ·
        refine ⟨88712101952314741203413107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118282802603086321604550809 88712101952314741203413107)
        ·
          refine ⟨133068152928472111805119661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88712101952314741203413107 133068152928472111805119661)
          ·
            refine ⟨49900557348177041926919873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133068152928472111805119661 49900557348177041926919873)
            ·
              refine ⟨37425418011132781445189905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49900557348177041926919873 37425418011132781445189905)
              ·
                refine ⟨28069063508349586083892429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37425418011132781445189905 28069063508349586083892429)
                ·
                  refine ⟨10525898815631094781459661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28069063508349586083892429 10525898815631094781459661)
                  ·
                    refine ⟨3947212055861660543047373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10525898815631094781459661 3947212055861660543047373)
                    ·
                      refine ⟨1480204520948122703642765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3947212055861660543047373 1480204520948122703642765)
                      ·
                        rfl

theorem cell23_2882688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_2882688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882688 prefixEnd_2882688 := by exact prefixLift 2882688
  have htrace : WordTrace (prefixWord ++ tailWord_2882688) baseStart_2882688 baseEnd_2882688 := by
    simpa [prefixWord, tailWord_2882688, baseEnd_2882688] using wordTrace_append hprefix tailTrace_2882688
  have hstable : (prefixWord ++ tailWord_2882688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882688).length < 2 ^ (prefixWord ++ tailWord_2882688).sum := by decide
  have hdescent : baseEnd_2882688 < baseStart_2882688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882689 : List Nat := [1, 2, 4, 2, 2, 2, 2, 1, 3, 2, 2]
def baseStart_2882689 : Nat := 118140960795 + 2882689 * 2 ^ 59
def prefixEnd_2882689 : Nat := 4983230072969 + 3 ^ 40 * 2882689 * 2
def baseEnd_2882689 : Nat := 1480205034428777199730261

theorem tailTrace_2882689 : CollatzResearch.WordTrace tailWord_2882689 prefixEnd_2882689 1480205034428777199730261 := by
  unfold tailWord_2882689
  simp only [CollatzResearch.WordTrace]
  refine ⟨105140305453517551930387121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70093536969011701286924747 105140305453517551930387121)
  ·
    refine ⟨78855229090138163947790341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105140305453517551930387121 78855229090138163947790341)
    ·
      refine ⟨14785355454400905740210689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78855229090138163947790341 14785355454400905740210689)
      ·
        refine ⟨11089016590800679305158017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14785355454400905740210689 11089016590800679305158017)
        ·
          refine ⟨8316762443100509478868513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11089016590800679305158017 8316762443100509478868513)
          ·
            refine ⟨6237571832325382109151385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8316762443100509478868513 6237571832325382109151385)
            ·
              refine ⟨4678178874244036581863539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6237571832325382109151385 4678178874244036581863539)
              ·
                refine ⟨7017268311366054872795309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4678178874244036581863539 7017268311366054872795309)
                ·
                  refine ⟨2631475616762270577298241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7017268311366054872795309 2631475616762270577298241)
                  ·
                    refine ⟨1973606712571702932973681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2631475616762270577298241 1973606712571702932973681)
                    ·
                      refine ⟨1480205034428777199730261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1973606712571702932973681 1480205034428777199730261)
                      ·
                        rfl

theorem cell23_2882689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_2882689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882689 prefixEnd_2882689 := by exact prefixLift 2882689
  have htrace : WordTrace (prefixWord ++ tailWord_2882689) baseStart_2882689 baseEnd_2882689 := by
    simpa [prefixWord, tailWord_2882689, baseEnd_2882689] using wordTrace_append hprefix tailTrace_2882689
  have hstable : (prefixWord ++ tailWord_2882689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882689).length < 2 ^ (prefixWord ++ tailWord_2882689).sum := by decide
  have hdescent : baseEnd_2882689 < baseStart_2882689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882702 : List Nat := [4, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4]
def baseStart_2882702 : Nat := 118140960795 + 2882702 * 2 ^ 59
def prefixEnd_2882702 : Nat := 4983230072969 + 3 ^ 40 * 2882702 * 2
def baseEnd_2882702 : Nat := 1480211709677285648867701

theorem tailTrace_2882702 : CollatzResearch.WordTrace tailWord_2882702 prefixEnd_2882702 1480211709677285648867701 := by
  unfold tailWord_2882702
  simp only [CollatzResearch.WordTrace]
  refine ⟨13142597450308806893826295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70093853068313636767073573 13142597450308806893826295)
  ·
    refine ⟨19713896175463210340739443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13142597450308806893826295 19713896175463210340739443)
    ·
      refine ⟨29570844263194815511109165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19713896175463210340739443 29570844263194815511109165)
      ·
        refine ⟨11089066598698055816665937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29570844263194815511109165 11089066598698055816665937)
        ·
          refine ⟨8316799949023541862499453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11089066598698055816665937 8316799949023541862499453)
          ·
            refine ⟨3118799980883828198437295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8316799949023541862499453 3118799980883828198437295)
            ·
              refine ⟨4678199971325742297655943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3118799980883828198437295 4678199971325742297655943)
              ·
                refine ⟨7017299956988613446483915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4678199971325742297655943 7017299956988613446483915)
                ·
                  refine ⟨10525949935482920169725873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7017299956988613446483915 10525949935482920169725873)
                  ·
                    refine ⟨7894462451612190127294405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10525949935482920169725873 7894462451612190127294405)
                    ·
                      refine ⟨1480211709677285648867701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7894462451612190127294405 1480211709677285648867701)
                      ·
                        rfl

theorem cell23_2882702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_2882702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882702 prefixEnd_2882702 := by exact prefixLift 2882702
  have htrace : WordTrace (prefixWord ++ tailWord_2882702) baseStart_2882702 baseEnd_2882702 := by
    simpa [prefixWord, tailWord_2882702, baseEnd_2882702] using wordTrace_append hprefix tailTrace_2882702
  have hstable : (prefixWord ++ tailWord_2882702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882702).length < 2 ^ (prefixWord ++ tailWord_2882702).sum := by decide
  have hdescent : baseEnd_2882702 < baseStart_2882702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882766 : List Nat := [4, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2]
def baseStart_2882766 : Nat := 118140960795 + 2882766 * 2 ^ 59
def prefixEnd_2882766 : Nat := 4983230072969 + 3 ^ 40 * 2882766 * 2
def baseEnd_2882766 : Nat := 1480244572439173398467407

theorem tailTrace_2882766 : CollatzResearch.WordTrace tailWord_2882766 prefixEnd_2882766 1480244572439173398467407 := by
  unfold tailWord_2882766
  simp only [CollatzResearch.WordTrace]
  refine ⟨13142889234279824260117519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70095409249492396053960101 13142889234279824260117519)
  ·
    refine ⟨19714333851419736390176279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13142889234279824260117519 19714333851419736390176279)
    ·
      refine ⟨29571500777129604585264419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19714333851419736390176279 29571500777129604585264419)
      ·
        refine ⟨44357251165694406877896629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29571500777129604585264419 44357251165694406877896629)
        ·
          refine ⟨4158492296783850644802809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44357251165694406877896629 4158492296783850644802809)
          ·
            refine ⟨3118869222587887983602107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4158492296783850644802809 3118869222587887983602107)
            ·
              refine ⟨4678303833881831975403161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3118869222587887983602107 4678303833881831975403161)
              ·
                refine ⟨3508727875411373981552371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4678303833881831975403161 3508727875411373981552371)
                ·
                  refine ⟨5263091813117060972328557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3508727875411373981552371 5263091813117060972328557)
                  ·
                    refine ⟨1973659429918897864623209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5263091813117060972328557 1973659429918897864623209)
                    ·
                      refine ⟨1480244572439173398467407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1973659429918897864623209 1480244572439173398467407)
                      ·
                        rfl

theorem cell23_2882766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_2882766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882766 prefixEnd_2882766 := by exact prefixLift 2882766
  have htrace : WordTrace (prefixWord ++ tailWord_2882766) baseStart_2882766 baseEnd_2882766 := by
    simpa [prefixWord, tailWord_2882766, baseEnd_2882766] using wordTrace_append hprefix tailTrace_2882766
  have hstable : (prefixWord ++ tailWord_2882766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882766).length < 2 ^ (prefixWord ++ tailWord_2882766).sum := by decide
  have hdescent : baseEnd_2882766 < baseStart_2882766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882812 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 2, 3, 3]
def baseStart_2882812 : Nat := 118140960795 + 2882812 * 2 ^ 59
def prefixEnd_2882812 : Nat := 4983230072969 + 3 ^ 40 * 2882812 * 2
def baseEnd_2882812 : Nat := 1480268192549280218492195

theorem tailTrace_2882812 : CollatzResearch.WordTrace tailWord_2882812 prefixEnd_2882812 1480268192549280218492195 := by
  unfold tailWord_2882812
  simp only [CollatzResearch.WordTrace]
  refine ⟨52572395816035971968557345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70096527754714629291409793 52572395816035971968557345)
  ·
    refine ⟨39429296862026978976418009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52572395816035971968557345 39429296862026978976418009)
    ·
      refine ⟨29571972646520234232313507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39429296862026978976418009 29571972646520234232313507)
      ·
        refine ⟨44357958969780351348470261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29571972646520234232313507 44357958969780351348470261)
        ·
          refine ⟨4158558653416907938919087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44357958969780351348470261 4158558653416907938919087)
          ·
            refine ⟨6237837980125361908378631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4158558653416907938919087 6237837980125361908378631)
            ·
              refine ⟨9356756970188042862567947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6237837980125361908378631 9356756970188042862567947)
              ·
                refine ⟨14035135455282064293851921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9356756970188042862567947 14035135455282064293851921)
                ·
                  refine ⟨10526351591461548220388941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14035135455282064293851921 10526351591461548220388941)
                  ·
                    refine ⟨3947381846798080582645853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10526351591461548220388941 3947381846798080582645853)
                    ·
                      refine ⟨1480268192549280218492195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3947381846798080582645853 1480268192549280218492195)
                      ·
                        rfl

theorem cell23_2882812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_2882812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882812 prefixEnd_2882812 := by exact prefixLift 2882812
  have htrace : WordTrace (prefixWord ++ tailWord_2882812) baseStart_2882812 baseEnd_2882812 := by
    simpa [prefixWord, tailWord_2882812, baseEnd_2882812] using wordTrace_append hprefix tailTrace_2882812
  have hstable : (prefixWord ++ tailWord_2882812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882812).length < 2 ^ (prefixWord ++ tailWord_2882812).sum := by decide
  have hdescent : baseEnd_2882812 < baseStart_2882812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882852 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 4, 4, 2]
def baseStart_2882852 : Nat := 118140960795 + 2882852 * 2 ^ 59
def prefixEnd_2882852 : Nat := 4983230072969 + 3 ^ 40 * 2882852 * 2
def baseEnd_2882852 : Nat := 1480288731775460061992011

theorem tailTrace_2882852 : CollatzResearch.WordTrace tailWord_2882852 prefixEnd_2882852 1480288731775460061992011 := by
  unfold tailWord_2882852
  simp only [CollatzResearch.WordTrace]
  refine ⟨52573125275963515384285405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70097500367951353845713873 52573125275963515384285405)
  ·
    refine ⟨19714921978486318269107027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52573125275963515384285405 19714921978486318269107027)
    ·
      refine ⟨29572382967729477403660541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19714921978486318269107027 29572382967729477403660541)
      ·
        refine ⟨11089643612898554026372703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29572382967729477403660541 11089643612898554026372703)
        ·
          refine ⟨16634465419347831039559055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11089643612898554026372703 16634465419347831039559055)
          ·
            refine ⟨24951698129021746559338583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16634465419347831039559055 24951698129021746559338583)
            ·
              refine ⟨37427547193532619839007875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24951698129021746559338583 37427547193532619839007875)
              ·
                refine ⟨56141320790298929758511813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37427547193532619839007875 56141320790298929758511813)
                ·
                  refine ⟨10526497648181049329720965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56141320790298929758511813 10526497648181049329720965)
                  ·
                    refine ⟨1973718309033946749322681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10526497648181049329720965 1973718309033946749322681)
                    ·
                      refine ⟨1480288731775460061992011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1973718309033946749322681 1480288731775460061992011)
                      ·
                        rfl

theorem cell23_2882852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_2882852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882852 prefixEnd_2882852 := by exact prefixLift 2882852
  have htrace : WordTrace (prefixWord ++ tailWord_2882852) baseStart_2882852 baseEnd_2882852 := by
    simpa [prefixWord, tailWord_2882852, baseEnd_2882852] using wordTrace_append hprefix tailTrace_2882852
  have hstable : (prefixWord ++ tailWord_2882852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882852).length < 2 ^ (prefixWord ++ tailWord_2882852).sum := by decide
  have hdescent : baseEnd_2882852 < baseStart_2882852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882935 : List Nat := [1, 1, 3, 1, 1, 2, 4, 3, 1, 6]
def baseStart_2882935 : Nat := 118140960795 + 2882935 * 2 ^ 59
def prefixEnd_2882935 : Nat := 4983230072969 + 3 ^ 40 * 2882935 * 2
def baseEnd_2882935 : Nat := 493443783556594412418043

theorem tailTrace_2882935 : CollatzResearch.WordTrace tailWord_2882935 prefixEnd_2882935 493443783556594412418043 := by
  unfold tailWord_2882935
  simp only [CollatzResearch.WordTrace]
  refine ⟨105149277810626335943842259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70099518540417557295894839 105149277810626335943842259)
  ·
    refine ⟨157723916715939503915763389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105149277810626335943842259 157723916715939503915763389)
    ·
      refine ⟨59146468768477313968411271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157723916715939503915763389 59146468768477313968411271)
      ·
        refine ⟨88719703152715970952616907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59146468768477313968411271 88719703152715970952616907)
        ·
          refine ⟨133079554729073956428925361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88719703152715970952616907 133079554729073956428925361)
          ·
            refine ⟨99809666046805467321694021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133079554729073956428925361 99809666046805467321694021)
            ·
              refine ⟨18714312383776025122817629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99809666046805467321694021 18714312383776025122817629)
              ·
                refine ⟨7017867143916009421056611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18714312383776025122817629 7017867143916009421056611)
                ·
                  refine ⟨10526800715874014131584917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7017867143916009421056611 10526800715874014131584917)
                  ·
                    refine ⟨493443783556594412418043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10526800715874014131584917 493443783556594412418043)
                    ·
                      rfl

theorem cell23_2882935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_2882935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882935 prefixEnd_2882935 := by exact prefixLift 2882935
  have htrace : WordTrace (prefixWord ++ tailWord_2882935) baseStart_2882935 baseEnd_2882935 := by
    simpa [prefixWord, tailWord_2882935, baseEnd_2882935] using wordTrace_append hprefix tailTrace_2882935
  have hstable : (prefixWord ++ tailWord_2882935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882935).length < 2 ^ (prefixWord ++ tailWord_2882935).sum := by decide
  have hdescent : baseEnd_2882935 < baseStart_2882935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882952 : List Nat := [2, 1, 3, 3, 1, 3, 1, 2, 1, 6]
def baseStart_2882952 : Nat := 118140960795 + 2882952 * 2 ^ 59
def prefixEnd_2882952 : Nat := 4983230072969 + 3 ^ 40 * 2882952 * 2
def baseEnd_2882952 : Nat := 493446693280303223580517

theorem tailTrace_2882952 : CollatzResearch.WordTrace tailWord_2882952 prefixEnd_2882952 493446693280303223580517 := by
  unfold tailWord_2882952
  simp only [CollatzResearch.WordTrace]
  refine ⟨52574948925782373923605555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70099931901043165231474073 52574948925782373923605555)
  ·
    refine ⟨78862423388673560885408333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52574948925782373923605555 78862423388673560885408333)
    ·
      refine ⟨29573408770752585332028125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78862423388673560885408333 29573408770752585332028125)
      ·
        refine ⟨11090028289032219499510547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29573408770752585332028125 11090028289032219499510547)
        ·
          refine ⟨16635042433548329249265821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11090028289032219499510547 16635042433548329249265821)
          ·
            refine ⟨6238140912580623468474683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16635042433548329249265821 6238140912580623468474683)
            ·
              refine ⟨9357211368870935202712025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6238140912580623468474683 9357211368870935202712025)
              ·
                refine ⟨7017908526653201402034019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9357211368870935202712025 7017908526653201402034019)
                ·
                  refine ⟨10526862789979802103051029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7017908526653201402034019 10526862789979802103051029)
                  ·
                    refine ⟨493446693280303223580517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10526862789979802103051029 493446693280303223580517)
                    ·
                      rfl

theorem cell23_2882952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_2882952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882952 prefixEnd_2882952 := by exact prefixLift 2882952
  have htrace : WordTrace (prefixWord ++ tailWord_2882952) baseStart_2882952 baseEnd_2882952 := by
    simpa [prefixWord, tailWord_2882952, baseEnd_2882952] using wordTrace_append hprefix tailTrace_2882952
  have hstable : (prefixWord ++ tailWord_2882952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882952).length < 2 ^ (prefixWord ++ tailWord_2882952).sum := by decide
  have hdescent : baseEnd_2882952 < baseStart_2882952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882969 : List Nat := [1, 2, 1, 2, 1, 6, 2, 2, 2, 4]
def baseStart_2882969 : Nat := 118140960795 + 2882969 * 2 ^ 59
def prefixEnd_2882969 : Nat := 4983230072969 + 3 ^ 40 * 2882969 * 2
def baseEnd_2882969 : Nat := 493449603004012034742991

theorem tailTrace_2882969 : CollatzResearch.WordTrace tailWord_2882969 prefixEnd_2882969 493449603004012034742991 := by
  unfold tailWord_2882969
  simp only [CollatzResearch.WordTrace]
  refine ⟨105150517892503159750579961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70100345261668773167053307 105150517892503159750579961)
  ·
    refine ⟨78862888419377369812934971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105150517892503159750579961 78862888419377369812934971)
    ·
      refine ⟨118294332629066054719402457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78862888419377369812934971 118294332629066054719402457)
      ·
        refine ⟨88720749471799541039551843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118294332629066054719402457 88720749471799541039551843)
        ·
          refine ⟨133081124207699311559327765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88720749471799541039551843 133081124207699311559327765)
          ·
            refine ⟨6238177697235905229343489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 133081124207699311559327765 6238177697235905229343489)
            ·
              refine ⟨4678633272926928922007617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6238177697235905229343489 4678633272926928922007617)
              ·
                refine ⟨3508974954695196691505713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4678633272926928922007617 3508974954695196691505713)
                ·
                  refine ⟨2631731216021397518629285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3508974954695196691505713 2631731216021397518629285)
                  ·
                    refine ⟨493449603004012034742991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2631731216021397518629285 493449603004012034742991)
                    ·
                      rfl

theorem cell23_2882969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 4].length) (baseStart_2882969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882969 prefixEnd_2882969 := by exact prefixLift 2882969
  have htrace : WordTrace (prefixWord ++ tailWord_2882969) baseStart_2882969 baseEnd_2882969 := by
    simpa [prefixWord, tailWord_2882969, baseEnd_2882969] using wordTrace_append hprefix tailTrace_2882969
  have hstable : (prefixWord ++ tailWord_2882969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882969).length < 2 ^ (prefixWord ++ tailWord_2882969).sum := by decide
  have hdescent : baseEnd_2882969 < baseStart_2882969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882989 : List Nat := [1, 5, 2, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_2882989 : Nat := 118140960795 + 2882989 * 2 ^ 59
def prefixEnd_2882989 : Nat := 4983230072969 + 3 ^ 40 * 2882989 * 2
def baseEnd_2882989 : Nat := 1480359078625126025978881

theorem tailTrace_2882989 : CollatzResearch.WordTrace tailWord_2882989 prefixEnd_2882989 1480359078625126025978881 := by
  unfold tailWord_2882989
  simp only [CollatzResearch.WordTrace]
  refine ⟨105151247352430703166308021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70100831568287135444205347 105151247352430703166308021)
  ·
    refine ⟨9857929439290378421841377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105151247352430703166308021 9857929439290378421841377)
    ·
      refine ⟨7393447079467783816381033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9857929439290378421841377 7393447079467783816381033)
      ·
        refine ⟨5545085309600837862285775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7393447079467783816381033 5545085309600837862285775)
        ·
          refine ⟨8317627964401256793428663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5545085309600837862285775 8317627964401256793428663)
          ·
            refine ⟨12476441946601885190142995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8317627964401256793428663 12476441946601885190142995)
            ·
              refine ⟨18714662919902827785214493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12476441946601885190142995 18714662919902827785214493)
              ·
                refine ⟨7017998594963560419455435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18714662919902827785214493 7017998594963560419455435)
                ·
                  refine ⟨10526997892445340629183153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7017998594963560419455435 10526997892445340629183153)
                  ·
                    refine ⟨7895248419334005471887365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10526997892445340629183153 7895248419334005471887365)
                    ·
                      refine ⟨1480359078625126025978881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7895248419334005471887365 1480359078625126025978881)
                      ·
                        rfl

theorem cell23_2882989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_2882989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2882989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2882989 prefixEnd_2882989 := by exact prefixLift 2882989
  have htrace : WordTrace (prefixWord ++ tailWord_2882989) baseStart_2882989 baseEnd_2882989 := by
    simpa [prefixWord, tailWord_2882989, baseEnd_2882989] using wordTrace_append hprefix tailTrace_2882989
  have hstable : (prefixWord ++ tailWord_2882989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882989).length < 2 ^ (prefixWord ++ tailWord_2882989).sum := by decide
  have hdescent : baseEnd_2882989 < baseStart_2882989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883043 : List Nat := [1, 1, 1, 6, 2, 2, 3, 1, 2, 1, 3]
def baseStart_2883043 : Nat := 118140960795 + 2883043 * 2 ^ 59
def prefixEnd_2883043 : Nat := 4983230072969 + 3 ^ 40 * 2883043 * 2
def baseEnd_2883043 : Nat := 1480386806580468814703633

theorem tailTrace_2883043 : CollatzResearch.WordTrace tailWord_2883043 prefixEnd_2883043 1480386806580468814703633 := by
  unfold tailWord_2883043
  simp only [CollatzResearch.WordTrace]
  refine ⟨105153216894235070388773783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70102144596156713592515855 105153216894235070388773783)
  ·
    refine ⟨157729825341352605583160675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105153216894235070388773783 157729825341352605583160675)
    ·
      refine ⟨236594738012028908374741013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157729825341352605583160675 236594738012028908374741013)
      ·
        refine ⟨11090378344313855080065985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 236594738012028908374741013 11090378344313855080065985)
        ·
          refine ⟨8317783758235391310049489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11090378344313855080065985 8317783758235391310049489)
          ·
            refine ⟨6238337818676543482537117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8317783758235391310049489 6238337818676543482537117)
            ·
              refine ⟨2339376682003703805951419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6238337818676543482537117 2339376682003703805951419)
              ·
                refine ⟨3509065023005555708927129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2339376682003703805951419 3509065023005555708927129)
                ·
                  refine ⟨2631798767254166781695347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3509065023005555708927129 2631798767254166781695347)
                  ·
                    refine ⟨3947698150881250172543021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2631798767254166781695347 3947698150881250172543021)
                    ·
                      refine ⟨1480386806580468814703633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3947698150881250172543021 1480386806580468814703633)
                      ·
                        rfl

theorem cell23_2883043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_2883043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883043 prefixEnd_2883043 := by exact prefixLift 2883043
  have htrace : WordTrace (prefixWord ++ tailWord_2883043) baseStart_2883043 baseEnd_2883043 := by
    simpa [prefixWord, tailWord_2883043, baseEnd_2883043] using wordTrace_append hprefix tailTrace_2883043
  have hstable : (prefixWord ++ tailWord_2883043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883043).length < 2 ^ (prefixWord ++ tailWord_2883043).sum := by decide
  have hdescent : baseEnd_2883043 < baseStart_2883043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883156 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 2, 4, 2]
def baseStart_2883156 : Nat := 118140960795 + 2883156 * 2 ^ 59
def prefixEnd_2883156 : Nat := 4983230072969 + 3 ^ 40 * 2883156 * 2
def baseEnd_2883156 : Nat := 1480444829894426872590613

theorem tailTrace_2883156 : CollatzResearch.WordTrace tailWord_2883156 prefixEnd_2883156 1480444829894426872590613 := by
  unfold tailWord_2883156
  simp only [CollatzResearch.WordTrace]
  refine ⟨52578669171412845343818661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70104892228550460458424881 52578669171412845343818661)
  ·
    refine ⟨9858500469639908501965999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52578669171412845343818661 9858500469639908501965999)
    ·
      refine ⟨14787750704459862752948999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9858500469639908501965999 14787750704459862752948999)
      ·
        refine ⟨22181626056689794129423499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14787750704459862752948999 22181626056689794129423499)
        ·
          refine ⟨33272439085034691194135249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22181626056689794129423499 33272439085034691194135249)
          ·
            refine ⟨24954329313776018395601437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33272439085034691194135249 24954329313776018395601437)
            ·
              refine ⟨9357873492666006898350539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24954329313776018395601437 9357873492666006898350539)
              ·
                refine ⟨14036810238999010347525809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9357873492666006898350539 14036810238999010347525809)
                ·
                  refine ⟨10527607679249257760644357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14036810238999010347525809 10527607679249257760644357)
                  ·
                    refine ⟨1973926439859235830120817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10527607679249257760644357 1973926439859235830120817)
                    ·
                      refine ⟨1480444829894426872590613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1973926439859235830120817 1480444829894426872590613)
                      ·
                        rfl

theorem cell23_2883156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_2883156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883156 prefixEnd_2883156 := by exact prefixLift 2883156
  have htrace : WordTrace (prefixWord ++ tailWord_2883156) baseStart_2883156 baseEnd_2883156 := by
    simpa [prefixWord, tailWord_2883156, baseEnd_2883156] using wordTrace_append hprefix tailTrace_2883156
  have hstable : (prefixWord ++ tailWord_2883156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883156).length < 2 ^ (prefixWord ++ tailWord_2883156).sum := by decide
  have hdescent : baseEnd_2883156 < baseStart_2883156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883176 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_2883176 : Nat := 118140960795 + 2883176 * 2 ^ 59
def prefixEnd_2883176 : Nat := 4983230072969 + 3 ^ 40 * 2883176 * 2
def baseEnd_2883176 : Nat := 1480455099507516794340521

theorem tailTrace_2883176 : CollatzResearch.WordTrace tailWord_2883176 prefixEnd_2883176 1480455099507516794340521 := by
  unfold tailWord_2883176
  simp only [CollatzResearch.WordTrace]
  refine ⟨52579033901376617051682691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70105378535168822735576921 52579033901376617051682691)
  ·
    refine ⟨78868550852064925577524037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52579033901376617051682691 78868550852064925577524037)
    ·
      refine ⟨14787853284762173545785757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78868550852064925577524037 14787853284762173545785757)
      ·
        refine ⟨5545444981785815079669659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14787853284762173545785757 5545444981785815079669659)
        ·
          refine ⟨8318167472678722619504489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5545444981785815079669659 8318167472678722619504489)
          ·
            refine ⟨6238625604509041964628367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8318167472678722619504489 6238625604509041964628367)
            ·
              refine ⟨9357938406763562946942551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6238625604509041964628367 9357938406763562946942551)
              ·
                refine ⟨14036907610145344420413827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9357938406763562946942551 14036907610145344420413827)
                ·
                  refine ⟨21055361415218016630620741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14036907610145344420413827 21055361415218016630620741)
                  ·
                    refine ⟨3947880265353378118241389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21055361415218016630620741 3947880265353378118241389)
                    ·
                      refine ⟨1480455099507516794340521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3947880265353378118241389 1480455099507516794340521)
                      ·
                        rfl

theorem cell23_2883176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_2883176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883176 prefixEnd_2883176 := by exact prefixLift 2883176
  have htrace : WordTrace (prefixWord ++ tailWord_2883176) baseStart_2883176 baseEnd_2883176 := by
    simpa [prefixWord, tailWord_2883176, baseEnd_2883176] using wordTrace_append hprefix tailTrace_2883176
  have hstable : (prefixWord ++ tailWord_2883176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883176).length < 2 ^ (prefixWord ++ tailWord_2883176).sum := by decide
  have hdescent : baseEnd_2883176 < baseStart_2883176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883234 : List Nat := [3, 3, 1, 4, 2, 1, 1, 3, 1, 4]
def baseStart_2883234 : Nat := 118140960795 + 2883234 * 2 ^ 59
def prefixEnd_2883234 : Nat := 4983230072969 + 3 ^ 40 * 2883234 * 2
def baseEnd_2883234 : Nat := 493494960461825855805085

theorem tailTrace_2883234 : CollatzResearch.WordTrace tailWord_2883234 prefixEnd_2883234 493494960461825855805085 := by
  unfold tailWord_2883234
  simp only [CollatzResearch.WordTrace]
  refine ⟨26290045809135777502244189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70106788824362073339317837 26290045809135777502244189)
  ·
    refine ⟨9858767178425916563341571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26290045809135777502244189 9858767178425916563341571)
    ·
      refine ⟨14788150767638874845012357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9858767178425916563341571 14788150767638874845012357)
      ·
        refine ⟨2772778268932289033439817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14788150767638874845012357 2772778268932289033439817)
        ·
          refine ⟨2079583701699216775079863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2772778268932289033439817 2079583701699216775079863)
          ·
            refine ⟨3119375552548825162619795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2079583701699216775079863 3119375552548825162619795)
            ·
              refine ⟨4679063328823237743929693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3119375552548825162619795 4679063328823237743929693)
              ·
                refine ⟨1754648748308714153973635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4679063328823237743929693 1754648748308714153973635)
                ·
                  refine ⟨2631973122463071230960453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1754648748308714153973635 2631973122463071230960453)
                  ·
                    refine ⟨493494960461825855805085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2631973122463071230960453 493494960461825855805085)
                    ·
                      rfl

theorem cell23_2883234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_2883234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883234 prefixEnd_2883234 := by exact prefixLift 2883234
  have htrace : WordTrace (prefixWord ++ tailWord_2883234) baseStart_2883234 baseEnd_2883234 := by
    simpa [prefixWord, tailWord_2883234, baseEnd_2883234] using wordTrace_append hprefix tailTrace_2883234
  have hstable : (prefixWord ++ tailWord_2883234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883234).length < 2 ^ (prefixWord ++ tailWord_2883234).sum := by decide
  have hdescent : baseEnd_2883234 < baseStart_2883234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883279 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 3]
def baseStart_2883279 : Nat := 118140960795 + 2883279 * 2 ^ 59
def prefixEnd_2883279 : Nat := 4983230072969 + 3 ^ 40 * 2883279 * 2
def baseEnd_2883279 : Nat := 1480507988014929891352547

theorem tailTrace_2883279 : CollatzResearch.WordTrace tailWord_2883279 prefixEnd_2883279 1480507988014929891352547 := by
  unfold tailWord_2883279
  simp only [CollatzResearch.WordTrace]
  refine ⟨105161824521380082694364891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70107883014253388462909927 105161824521380082694364891)
  ·
    refine ⟨157742736782070124041547337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105161824521380082694364891 157742736782070124041547337)
    ·
      refine ⟨118307052586552593031160503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157742736782070124041547337 118307052586552593031160503)
      ·
        refine ⟨177460578879828889546740755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118307052586552593031160503 177460578879828889546740755)
        ·
          refine ⟨266190868319743334320111133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177460578879828889546740755 266190868319743334320111133)
          ·
            refine ⟨99821575619903750370041675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266190868319743334320111133 99821575619903750370041675)
            ·
              refine ⟨149732363429855625555062513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99821575619903750370041675 149732363429855625555062513)
              ·
                refine ⟨112299272572391719166296885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149732363429855625555062513 112299272572391719166296885)
                ·
                  refine ⟨10528056803661723671840333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112299272572391719166296885 10528056803661723671840333)
                  ·
                    refine ⟨3948021301373146376940125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10528056803661723671840333 3948021301373146376940125)
                    ·
                      refine ⟨1480507988014929891352547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3948021301373146376940125 1480507988014929891352547)
                      ·
                        rfl

theorem cell23_2883279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 3].length) (baseStart_2883279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883279 prefixEnd_2883279 := by exact prefixLift 2883279
  have htrace : WordTrace (prefixWord ++ tailWord_2883279) baseStart_2883279 baseEnd_2883279 := by
    simpa [prefixWord, tailWord_2883279, baseEnd_2883279] using wordTrace_append hprefix tailTrace_2883279
  have hstable : (prefixWord ++ tailWord_2883279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883279).length < 2 ^ (prefixWord ++ tailWord_2883279).sum := by decide
  have hdescent : baseEnd_2883279 < baseStart_2883279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883296 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 6, 1, 3]
def baseStart_2883296 : Nat := 118140960795 + 2883296 * 2 ^ 59
def prefixEnd_2883296 : Nat := 4983230072969 + 3 ^ 40 * 2883296 * 2
def baseEnd_2883296 : Nat := 1480516717186056324839969

theorem tailTrace_2883296 : CollatzResearch.WordTrace tailWord_2883296 prefixEnd_2883296 1480516717186056324839969 := by
  unfold tailWord_2883296
  simp only [CollatzResearch.WordTrace]
  refine ⟨52581222281159247298866871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70108296374878996398489161 52581222281159247298866871)
  ·
    refine ⟨78871833421738870948300307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52581222281159247298866871 78871833421738870948300307)
    ·
      refine ⟨118307750132608306422450461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78871833421738870948300307 118307750132608306422450461)
      ·
        refine ⟨44365406299728114908418923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118307750132608306422450461 44365406299728114908418923)
        ·
          refine ⟨66548109449592172362628385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44365406299728114908418923 66548109449592172362628385)
          ·
            refine ⟨49911082087194129271971289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66548109449592172362628385 49911082087194129271971289)
            ·
              refine ⟨37433311565395596953978467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49911082087194129271971289 37433311565395596953978467)
              ·
                refine ⟨56149967348093395430967701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37433311565395596953978467 56149967348093395430967701)
                ·
                  refine ⟨2632029719441877910826611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56149967348093395430967701 2632029719441877910826611)
                  ·
                    refine ⟨3948044579162816866239917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2632029719441877910826611 3948044579162816866239917)
                    ·
                      refine ⟨1480516717186056324839969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3948044579162816866239917 1480516717186056324839969)
                      ·
                        rfl

theorem cell23_2883296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_2883296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883296 prefixEnd_2883296 := by exact prefixLift 2883296
  have htrace : WordTrace (prefixWord ++ tailWord_2883296) baseStart_2883296 baseEnd_2883296 := by
    simpa [prefixWord, tailWord_2883296, baseEnd_2883296] using wordTrace_append hprefix tailTrace_2883296
  have hstable : (prefixWord ++ tailWord_2883296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883296).length < 2 ^ (prefixWord ++ tailWord_2883296).sum := by decide
  have hdescent : baseEnd_2883296 < baseStart_2883296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883313 : List Nat := [1, 2, 2, 2, 2, 3, 1, 4, 2, 1, 3]
def baseStart_2883313 : Nat := 118140960795 + 2883313 * 2 ^ 59
def prefixEnd_2883313 : Nat := 4983230072969 + 3 ^ 40 * 2883313 * 2
def baseEnd_2883313 : Nat := 1480525446357182758327391

theorem tailTrace_2883313 : CollatzResearch.WordTrace tailWord_2883313 prefixEnd_2883313 1480525446357182758327391 := by
  unfold tailWord_2883313
  simp only [CollatzResearch.WordTrace]
  refine ⟨105163064603256906501102593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70108709735504604334068395 105163064603256906501102593)
  ·
    refine ⟨78872298452442679875826945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105163064603256906501102593 78872298452442679875826945)
    ·
      refine ⟨59154223839332009906870209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78872298452442679875826945 59154223839332009906870209)
      ·
        refine ⟨44365667879499007430152657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59154223839332009906870209 44365667879499007430152657)
        ·
          refine ⟨33274250909624255572614493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44365667879499007430152657 33274250909624255572614493)
          ·
            refine ⟨12477844091109095839730435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33274250909624255572614493 12477844091109095839730435)
            ·
              refine ⟨18716766136663643759595653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12477844091109095839730435 18716766136663643759595653)
              ·
                refine ⟨3509393650624433204924185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18716766136663643759595653 3509393650624433204924185)
                ·
                  refine ⟨2632045237968324903693139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3509393650624433204924185 2632045237968324903693139)
                  ·
                    refine ⟨3948067856952487355539709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2632045237968324903693139 3948067856952487355539709)
                    ·
                      refine ⟨1480525446357182758327391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3948067856952487355539709 1480525446357182758327391)
                      ·
                        rfl

theorem cell23_2883313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_2883313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883313 prefixEnd_2883313 := by exact prefixLift 2883313
  have htrace : WordTrace (prefixWord ++ tailWord_2883313) baseStart_2883313 baseEnd_2883313 := by
    simpa [prefixWord, tailWord_2883313, baseEnd_2883313] using wordTrace_append hprefix tailTrace_2883313
  have hstable : (prefixWord ++ tailWord_2883313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883313).length < 2 ^ (prefixWord ++ tailWord_2883313).sum := by decide
  have hdescent : baseEnd_2883313 < baseStart_2883313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883319 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 4]
def baseStart_2883319 : Nat := 118140960795 + 2883319 * 2 ^ 59
def prefixEnd_2883319 : Nat := 4983230072969 + 3 ^ 40 * 2883319 * 2
def baseEnd_2883319 : Nat := 1480528527241109734852363

theorem tailTrace_2883319 : CollatzResearch.WordTrace tailWord_2883319 prefixEnd_2883319 1480528527241109734852363 := by
  unfold tailWord_2883319
  simp only [CollatzResearch.WordTrace]
  refine ⟨105163283441235169525821011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70108855627490113017214007 105163283441235169525821011)
  ·
    refine ⟨157744925161852754288731517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105163283441235169525821011 157744925161852754288731517)
    ·
      refine ⟨59154346935694782858274319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157744925161852754288731517 59154346935694782858274319)
      ·
        refine ⟨88731520403542174287411479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59154346935694782858274319 88731520403542174287411479)
        ·
          refine ⟨133097280605313261431117219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88731520403542174287411479 133097280605313261431117219)
          ·
            refine ⟨199645920907969892146675829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133097280605313261431117219 199645920907969892146675829)
            ·
              refine ⟨18716805085122177388750859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 199645920907969892146675829 18716805085122177388750859)
              ·
                refine ⟨28075207627683266083126289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18716805085122177388750859 28075207627683266083126289)
                ·
                  refine ⟨21056405720762449562344717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28075207627683266083126289 21056405720762449562344717)
                  ·
                    refine ⟨7896152145285918585879269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21056405720762449562344717 7896152145285918585879269)
                    ·
                      refine ⟨1480528527241109734852363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7896152145285918585879269 1480528527241109734852363)
                      ·
                        rfl

theorem cell23_2883319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_2883319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883319 prefixEnd_2883319 := by exact prefixLift 2883319
  have htrace : WordTrace (prefixWord ++ tailWord_2883319) baseStart_2883319 baseEnd_2883319 := by
    simpa [prefixWord, tailWord_2883319, baseEnd_2883319] using wordTrace_append hprefix tailTrace_2883319
  have hstable : (prefixWord ++ tailWord_2883319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883319).length < 2 ^ (prefixWord ++ tailWord_2883319).sum := by decide
  have hdescent : baseEnd_2883319 < baseStart_2883319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883329 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 1, 8]
def baseStart_2883329 : Nat := 118140960795 + 2883329 * 2 ^ 59
def prefixEnd_2883329 : Nat := 4983230072969 + 3 ^ 40 * 2883329 * 2
def baseEnd_2883329 : Nat := 493511220682551565242439

theorem tailTrace_2883329 : CollatzResearch.WordTrace tailWord_2883329 prefixEnd_2883329 493511220682551565242439 := by
  unfold tailWord_2883329
  simp only [CollatzResearch.WordTrace]
  refine ⟨105163648171198941233685041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70109098780799294155790027 105163648171198941233685041)
  ·
    refine ⟨78872736128399205925263781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105163648171198941233685041 78872736128399205925263781)
    ·
      refine ⟨14788638024074851110986959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78872736128399205925263781 14788638024074851110986959)
      ·
        refine ⟨22182957036112276666480439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14788638024074851110986959 22182957036112276666480439)
        ·
          refine ⟨33274435554168414999720659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22182957036112276666480439 33274435554168414999720659)
          ·
            refine ⟨49911653331252622499580989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33274435554168414999720659 49911653331252622499580989)
            ·
              refine ⟨18716869999219733437342871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49911653331252622499580989 18716869999219733437342871)
              ·
                refine ⟨28075304998829600156014307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18716869999219733437342871 28075304998829600156014307)
                ·
                  refine ⟨42112957498244400234021461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28075304998829600156014307 42112957498244400234021461)
                  ·
                    refine ⟨493511220682551565242439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42112957498244400234021461 493511220682551565242439)
                    ·
                      rfl

theorem cell23_2883329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_2883329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883329 prefixEnd_2883329 := by exact prefixLift 2883329
  have htrace : WordTrace (prefixWord ++ tailWord_2883329) baseStart_2883329 baseEnd_2883329 := by
    simpa [prefixWord, tailWord_2883329, baseEnd_2883329] using wordTrace_append hprefix tailTrace_2883329
  have hstable : (prefixWord ++ tailWord_2883329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883329).length < 2 ^ (prefixWord ++ tailWord_2883329).sum := by decide
  have hdescent : baseEnd_2883329 < baseStart_2883329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883330 : List Nat := [3, 4, 1, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_2883330 : Nat := 118140960795 + 2883330 * 2 ^ 59
def prefixEnd_2883330 : Nat := 4983230072969 + 3 ^ 40 * 2883330 * 2
def baseEnd_2883330 : Nat := 1480534175528309191814813

theorem tailTrace_2883330 : CollatzResearch.WordTrace tailWord_2883330 prefixEnd_2883330 1480534175528309191814813 := by
  unfold tailWord_2883330
  simp only [CollatzResearch.WordTrace]
  refine ⟨26290921161048829601117861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70109123096130212269647629 26290921161048829601117861)
  ·
    refine ⟨4929547717696655550209599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26290921161048829601117861 4929547717696655550209599)
    ·
      refine ⟨7394321576544983325314399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4929547717696655550209599 7394321576544983325314399)
      ·
        refine ⟨11091482364817474987971599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7394321576544983325314399 11091482364817474987971599)
        ·
          refine ⟨16637223547226212481957399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11091482364817474987971599 16637223547226212481957399)
          ·
            refine ⟨24955835320839318722936099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16637223547226212481957399 24955835320839318722936099)
            ·
              refine ⟨37433752981258978084404149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24955835320839318722936099 37433752981258978084404149)
              ·
                refine ⟨3509414341993029195412889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37433752981258978084404149 3509414341993029195412889)
                ·
                  refine ⟨2632060756494771896559667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3509414341993029195412889 2632060756494771896559667)
                  ·
                    refine ⟨3948091134742157844839501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2632060756494771896559667 3948091134742157844839501)
                    ·
                      refine ⟨1480534175528309191814813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3948091134742157844839501 1480534175528309191814813)
                      ·
                        rfl

theorem cell23_2883330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_2883330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883330 prefixEnd_2883330 := by exact prefixLift 2883330
  have htrace : WordTrace (prefixWord ++ tailWord_2883330) baseStart_2883330 baseEnd_2883330 := by
    simpa [prefixWord, tailWord_2883330, baseEnd_2883330] using wordTrace_append hprefix tailTrace_2883330
  have hstable : (prefixWord ++ tailWord_2883330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883330).length < 2 ^ (prefixWord ++ tailWord_2883330).sum := by decide
  have hdescent : baseEnd_2883330 < baseStart_2883330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883339 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 5]
def baseStart_2883339 : Nat := 118140960795 + 2883339 * 2 ^ 59
def prefixEnd_2883339 : Nat := 4983230072969 + 3 ^ 40 * 2883339 * 2
def baseEnd_2883339 : Nat := 1480538796854199656602271

theorem tailTrace_2883339 : CollatzResearch.WordTrace tailWord_2883339 prefixEnd_2883339 1480538796854199656602271 := by
  unfold tailWord_2883339
  simp only [CollatzResearch.WordTrace]
  refine ⟨105164012901162712941549071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70109341934108475294366047 105164012901162712941549071)
  ·
    refine ⟨157746019351744069412323607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105164012901162712941549071 157746019351744069412323607)
    ·
      refine ⟨236619029027616104118485411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157746019351744069412323607 236619029027616104118485411)
      ·
        refine ⟨354928543541424156177728117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236619029027616104118485411 354928543541424156177728117)
        ·
          refine ⟨33274550957008514641662011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 354928543541424156177728117 33274550957008514641662011)
          ·
            refine ⟨49911826435512771962493017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33274550957008514641662011 49911826435512771962493017)
            ·
              refine ⟨37433869826634578971869763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49911826435512771962493017 37433869826634578971869763)
              ·
                refine ⟨56150804739951868457804645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37433869826634578971869763 56150804739951868457804645)
                ·
                  refine ⟨10528275888740975335838371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56150804739951868457804645 10528275888740975335838371)
                  ·
                    refine ⟨15792413833111463003757557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10528275888740975335838371 15792413833111463003757557)
                    ·
                      refine ⟨1480538796854199656602271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15792413833111463003757557 1480538796854199656602271)
                      ·
                        rfl

theorem cell23_2883339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 5].length) (baseStart_2883339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883339 prefixEnd_2883339 := by exact prefixLift 2883339
  have htrace : WordTrace (prefixWord ++ tailWord_2883339) baseStart_2883339 baseEnd_2883339 := by
    simpa [prefixWord, tailWord_2883339, baseEnd_2883339] using wordTrace_append hprefix tailTrace_2883339
  have hstable : (prefixWord ++ tailWord_2883339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883339).length < 2 ^ (prefixWord ++ tailWord_2883339).sum := by decide
  have hdescent : baseEnd_2883339 < baseStart_2883339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883348 : List Nat := [2, 4, 4, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_2883348 : Nat := 118140960795 + 2883348 * 2 ^ 59
def prefixEnd_2883348 : Nat := 4983230072969 + 3 ^ 40 * 2883348 * 2
def baseEnd_2883348 : Nat := 1480543418180090121389731

theorem tailTrace_2883348 : CollatzResearch.WordTrace tailWord_2883348 prefixEnd_2883348 1480543418180090121389731 := by
  unfold tailWord_2883348
  simp only [CollatzResearch.WordTrace]
  refine ⟨52582170579065053739313349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70109560772086738319084465 52582170579065053739313349)
  ·
    refine ⟨9859156983574697576121253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52582170579065053739313349 9859156983574697576121253)
    ·
      refine ⟨1848591934420255795522735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9859156983574697576121253 1848591934420255795522735)
      ·
        refine ⟨2772887901630383693284103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1848591934420255795522735 2772887901630383693284103)
        ·
          refine ⟨4159331852445575539926155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2772887901630383693284103 4159331852445575539926155)
          ·
            refine ⟨6238997778668363309889233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4159331852445575539926155 6238997778668363309889233)
            ·
              refine ⟨4679248334001272482416925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6238997778668363309889233 4679248334001272482416925)
              ·
                refine ⟨1754718125250477180906347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4679248334001272482416925 1754718125250477180906347)
                ·
                  refine ⟨2632077187875715771359521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1754718125250477180906347 2632077187875715771359521)
                  ·
                    refine ⟨1974057890906786828519641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2632077187875715771359521 1974057890906786828519641)
                    ·
                      refine ⟨1480543418180090121389731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1974057890906786828519641 1480543418180090121389731)
                      ·
                        rfl

theorem cell23_2883348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_2883348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883348 prefixEnd_2883348 := by exact prefixLift 2883348
  have htrace : WordTrace (prefixWord ++ tailWord_2883348) baseStart_2883348 baseEnd_2883348 := by
    simpa [prefixWord, tailWord_2883348, baseEnd_2883348] using wordTrace_append hprefix tailTrace_2883348
  have hstable : (prefixWord ++ tailWord_2883348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883348).length < 2 ^ (prefixWord ++ tailWord_2883348).sum := by decide
  have hdescent : baseEnd_2883348 < baseStart_2883348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883359 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 9]
def baseStart_2883359 : Nat := 118140960795 + 2883359 * 2 ^ 59
def prefixEnd_2883359 : Nat := 4983230072969 + 3 ^ 40 * 2883359 * 2
def baseEnd_2883359 : Nat := 164505451829698842039131

theorem tailTrace_2883359 : CollatzResearch.WordTrace tailWord_2883359 prefixEnd_2883359 164505451829698842039131 := by
  unfold tailWord_2883359
  simp only [CollatzResearch.WordTrace]
  refine ⟨105164742361090256357277131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70109828240726837571518087 105164742361090256357277131)
  ·
    refine ⟨157747113541635384535915697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105164742361090256357277131 157747113541635384535915697)
    ·
      refine ⟨118310335156226538401936773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157747113541635384535915697 118310335156226538401936773)
      ·
        refine ⟨22183187841792475950363145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118310335156226538401936773 22183187841792475950363145)
        ·
          refine ⟨16637390881344356962772359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22183187841792475950363145 16637390881344356962772359)
          ·
            refine ⟨24956086322016535444158539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16637390881344356962772359 24956086322016535444158539)
            ·
              refine ⟨37434129483024803166237809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24956086322016535444158539 37434129483024803166237809)
              ·
                refine ⟨28075597112268602374678357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37434129483024803166237809 28075597112268602374678357)
                ·
                  refine ⟨164505451829698842039131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28075597112268602374678357 164505451829698842039131)
                  ·
                    rfl

theorem cell23_2883359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 9].length) (baseStart_2883359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883359 prefixEnd_2883359 := by exact prefixLift 2883359
  have htrace : WordTrace (prefixWord ++ tailWord_2883359) baseStart_2883359 baseEnd_2883359 := by
    simpa [prefixWord, tailWord_2883359, baseEnd_2883359] using wordTrace_append hprefix tailTrace_2883359
  have hstable : (prefixWord ++ tailWord_2883359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883359).length < 2 ^ (prefixWord ++ tailWord_2883359).sum := by decide
  have hdescent : baseEnd_2883359 < baseStart_2883359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883410 : List Nat := [3, 2, 2, 1, 1, 5, 1, 3, 5]
def baseStart_2883410 : Nat := 118140960795 + 2883410 * 2 ^ 59
def prefixEnd_2883410 : Nat := 4983230072969 + 3 ^ 40 * 2883410 * 2
def baseEnd_2883410 : Nat := 164508361553407653201605

theorem tailTrace_2883410 : CollatzResearch.WordTrace tailWord_2883410 prefixEnd_2883410 164508361553407653201605 := by
  unfold tailWord_2883410
  simp only [CollatzResearch.WordTrace]
  refine ⟨26291650620976373016845921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70111068322603661378255789 26291650620976373016845921)
  ·
    refine ⟨19718737965732279762634441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26291650620976373016845921 19718737965732279762634441)
    ·
      refine ⟨14789053474299209821975831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19718737965732279762634441 14789053474299209821975831)
      ·
        refine ⟨22183580211448814732963747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14789053474299209821975831 22183580211448814732963747)
        ·
          refine ⟨33275370317173222099445621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22183580211448814732963747 33275370317173222099445621)
          ·
            refine ⟨3119565967234989571823027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33275370317173222099445621 3119565967234989571823027)
            ·
              refine ⟨4679348950852484357734541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3119565967234989571823027 4679348950852484357734541)
              ·
                refine ⟨1754755856569681634150453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4679348950852484357734541 1754755856569681634150453)
                ·
                  refine ⟨164508361553407653201605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1754755856569681634150453 164508361553407653201605)
                  ·
                    rfl

theorem cell23_2883410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_2883410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883410 prefixEnd_2883410 := by exact prefixLift 2883410
  have htrace : WordTrace (prefixWord ++ tailWord_2883410) baseStart_2883410 baseEnd_2883410 := by
    simpa [prefixWord, tailWord_2883410, baseEnd_2883410] using wordTrace_append hprefix tailTrace_2883410
  have hstable : (prefixWord ++ tailWord_2883410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883410).length < 2 ^ (prefixWord ++ tailWord_2883410).sum := by decide
  have hdescent : baseEnd_2883410 < baseStart_2883410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883478 : List Nat := [5, 3, 1, 1, 3, 1, 2, 2, 5]
def baseStart_2883478 : Nat := 118140960795 + 2883478 * 2 ^ 59
def prefixEnd_2883478 : Nat := 4983230072969 + 3 ^ 40 * 2883478 * 2
def baseEnd_2883478 : Nat := 164512241185019401418237

theorem tailTrace_2883478 : CollatzResearch.WordTrace tailWord_2883478 prefixEnd_2883478 164512241185019401418237 := by
  unfold tailWord_2883478
  simp only [CollatzResearch.WordTrace]
  refine ⟨6573067665478696230053693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70112721765106093120572725 6573067665478696230053693)
  ·
    refine ⟨2464900374554511086270135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6573067665478696230053693 2464900374554511086270135)
    ·
      refine ⟨3697350561831766629405203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2464900374554511086270135 3697350561831766629405203)
      ·
        refine ⟨5546025842747649944107805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3697350561831766629405203 5546025842747649944107805)
        ·
          refine ⟨2079759691030368729040427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5546025842747649944107805 2079759691030368729040427)
          ·
            refine ⟨3119639536545553093560641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2079759691030368729040427 3119639536545553093560641)
            ·
              refine ⟨2339729652409164820170481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3119639536545553093560641 2339729652409164820170481)
              ·
                refine ⟨1754797239306873615127861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2339729652409164820170481 1754797239306873615127861)
                ·
                  refine ⟨164512241185019401418237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1754797239306873615127861 164512241185019401418237)
                  ·
                    rfl

theorem cell23_2883478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_2883478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883478 prefixEnd_2883478 := by exact prefixLift 2883478
  have htrace : WordTrace (prefixWord ++ tailWord_2883478) baseStart_2883478 baseEnd_2883478 := by
    simpa [prefixWord, tailWord_2883478, baseEnd_2883478] using wordTrace_append hprefix tailTrace_2883478
  have hstable : (prefixWord ++ tailWord_2883478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883478).length < 2 ^ (prefixWord ++ tailWord_2883478).sum := by decide
  have hdescent : baseEnd_2883478 < baseStart_2883478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883487 : List Nat := [1, 1, 2, 5, 3, 1, 1, 4, 1, 4]
def baseStart_2883487 : Nat := 118140960795 + 2883487 * 2 ^ 59
def prefixEnd_2883487 : Nat := 4983230072969 + 3 ^ 40 * 2883487 * 2
def baseEnd_2883487 : Nat := 493538263997021692517197

theorem tailTrace_2883487 : CollatzResearch.WordTrace tailWord_2883487 prefixEnd_2883487 493538263997021692517197 := by
  unfold tailWord_2883487
  simp only [CollatzResearch.WordTrace]
  refine ⟨105169410904626534217936715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70112940603084356145291143 105169410904626534217936715)
  ·
    refine ⟨157754116356939801326905073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105169410904626534217936715 157754116356939801326905073)
    ·
      refine ⟨118315587267704850995178805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157754116356939801326905073 118315587267704850995178805)
      ·
        refine ⟨11092086306347329780798013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118315587267704850995178805 11092086306347329780798013)
        ·
          refine ⟨4159532364880248667799255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11092086306347329780798013 4159532364880248667799255)
          ·
            refine ⟨6239298547320373001698883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4159532364880248667799255 6239298547320373001698883)
            ·
              refine ⟨9358947820980559502548325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6239298547320373001698883 9358947820980559502548325)
              ·
                refine ⟨1754802716433854906727811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9358947820980559502548325 1754802716433854906727811)
                ·
                  refine ⟨2632204074650782360091717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1754802716433854906727811 2632204074650782360091717)
                  ·
                    refine ⟨493538263997021692517197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2632204074650782360091717 493538263997021692517197)
                    ·
                      rfl

theorem cell23_2883487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 1, 4].length) (baseStart_2883487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883487 prefixEnd_2883487 := by exact prefixLift 2883487
  have htrace : WordTrace (prefixWord ++ tailWord_2883487) baseStart_2883487 baseEnd_2883487 := by
    simpa [prefixWord, tailWord_2883487, baseEnd_2883487] using wordTrace_append hprefix tailTrace_2883487
  have hstable : (prefixWord ++ tailWord_2883487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883487).length < 2 ^ (prefixWord ++ tailWord_2883487).sum := by decide
  have hdescent : baseEnd_2883487 < baseStart_2883487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883493 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 7, 1, 3]
def baseStart_2883493 : Nat := 118140960795 + 2883493 * 2 ^ 59
def prefixEnd_2883493 : Nat := 4983230072969 + 3 ^ 40 * 2883493 * 2
def baseEnd_2883493 : Nat := 1480617872874992054076563

theorem tailTrace_2883493 : CollatzResearch.WordTrace tailWord_2883493 prefixEnd_2883493 1480617872874992054076563 := by
  unfold tailWord_2883493
  simp only [CollatzResearch.WordTrace]
  refine ⟨105169629742604797242655133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70113086495069864828436755 105169629742604797242655133)
  ·
    refine ⟨39438611153476798965995675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105169629742604797242655133 39438611153476798965995675)
    ·
      refine ⟨59157916730215198448993513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39438611153476798965995675 59157916730215198448993513)
      ·
        refine ⟨44368437547661398836745135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59157916730215198448993513 44368437547661398836745135)
        ·
          refine ⟨66552656321492098255117703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44368437547661398836745135 66552656321492098255117703)
          ·
            refine ⟨99828984482238147382676555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66552656321492098255117703 99828984482238147382676555)
            ·
              refine ⟨149743476723357221074014833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99828984482238147382676555 149743476723357221074014833)
              ·
                refine ⟨112307607542517915805511125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149743476723357221074014833 112307607542517915805511125)
                ·
                  refine ⟨2632209551777763651691667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 112307607542517915805511125 2632209551777763651691667)
                  ·
                    refine ⟨3948314327666645477537501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2632209551777763651691667 3948314327666645477537501)
                    ·
                      refine ⟨1480617872874992054076563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3948314327666645477537501 1480617872874992054076563)
                      ·
                        rfl

theorem cell23_2883493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_2883493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883493 prefixEnd_2883493 := by exact prefixLift 2883493
  have htrace : WordTrace (prefixWord ++ tailWord_2883493) baseStart_2883493 baseEnd_2883493 := by
    simpa [prefixWord, tailWord_2883493, baseEnd_2883493] using wordTrace_append hprefix tailTrace_2883493
  have hstable : (prefixWord ++ tailWord_2883493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883493).length < 2 ^ (prefixWord ++ tailWord_2883493).sum := by decide
  have hdescent : baseEnd_2883493 < baseStart_2883493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883503 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 1, 5, 2]
def baseStart_2883503 : Nat := 118140960795 + 2883503 * 2 ^ 59
def prefixEnd_2883503 : Nat := 4983230072969 + 3 ^ 40 * 2883503 * 2
def baseEnd_2883503 : Nat := 1480623007681537014951517

theorem tailTrace_2883503 : CollatzResearch.WordTrace tailWord_2883503 prefixEnd_2883503 1480623007681537014951517 := by
  unfold tailWord_2883503
  simp only [CollatzResearch.WordTrace]
  refine ⟨105169994472568568950519163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70113329648379045967012775 105169994472568568950519163)
  ·
    refine ⟨157754991708852853425778745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105169994472568568950519163 157754991708852853425778745)
    ·
      refine ⟨118316243781639640069334059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157754991708852853425778745 118316243781639640069334059)
      ·
        refine ⟨177474365672459460104001089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118316243781639640069334059 177474365672459460104001089)
        ·
          refine ⟨133105774254344595078000817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177474365672459460104001089 133105774254344595078000817)
          ·
            refine ⟨99829330690758446308500613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133105774254344595078000817 99829330690758446308500613)
            ·
              refine ⟨18717999504517208682843865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99829330690758446308500613 18717999504517208682843865)
              ·
                refine ⟨14038499628387906512132899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18717999504517208682843865 14038499628387906512132899)
                ·
                  refine ⟨21057749442581859768199349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14038499628387906512132899 21057749442581859768199349)
                  ·
                    refine ⟨1974164010242049353268689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21057749442581859768199349 1974164010242049353268689)
                    ·
                      refine ⟨1480623007681537014951517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1974164010242049353268689 1480623007681537014951517)
                      ·
                        rfl

theorem cell23_2883503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 5, 2].length) (baseStart_2883503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883503 prefixEnd_2883503 := by exact prefixLift 2883503
  have htrace : WordTrace (prefixWord ++ tailWord_2883503) baseStart_2883503 baseEnd_2883503 := by
    simpa [prefixWord, tailWord_2883503, baseEnd_2883503] using wordTrace_append hprefix tailTrace_2883503
  have hstable : (prefixWord ++ tailWord_2883503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883503).length < 2 ^ (prefixWord ++ tailWord_2883503).sum := by decide
  have hdescent : baseEnd_2883503 < baseStart_2883503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883513 : List Nat := [1, 2, 1, 4, 2, 1, 2, 4, 1, 5]
def baseStart_2883513 : Nat := 118140960795 + 2883513 * 2 ^ 59
def prefixEnd_2883513 : Nat := 4983230072969 + 3 ^ 40 * 2883513 * 2
def baseEnd_2883513 : Nat := 493542714162693991942157

theorem tailTrace_2883513 : CollatzResearch.WordTrace tailWord_2883513 prefixEnd_2883513 493542714162693991942157 := by
  unfold tailWord_2883513
  simp only [CollatzResearch.WordTrace]
  refine ⟨105170359202532340658383193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70113572801688227105588795 105170359202532340658383193)
  ·
    refine ⟨78877769401899255493787395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105170359202532340658383193 78877769401899255493787395)
    ·
      refine ⟨118316654102848883240681093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78877769401899255493787395 118316654102848883240681093)
      ·
        refine ⟨22184372644284165607627705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118316654102848883240681093 22184372644284165607627705)
        ·
          refine ⟨16638279483213124205720779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22184372644284165607627705 16638279483213124205720779)
          ·
            refine ⟨24957419224819686308581169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16638279483213124205720779 24957419224819686308581169)
            ·
              refine ⟨18718064418614764731435877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24957419224819686308581169 18718064418614764731435877)
              ·
                refine ⟨3509637078490268387144227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18718064418614764731435877 3509637078490268387144227)
                ·
                  refine ⟨5264455617735402580716341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3509637078490268387144227 5264455617735402580716341)
                  ·
                    refine ⟨493542714162693991942157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5264455617735402580716341 493542714162693991942157)
                    ·
                      rfl

theorem cell23_2883513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 5].length) (baseStart_2883513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883513 prefixEnd_2883513 := by exact prefixLift 2883513
  have htrace : WordTrace (prefixWord ++ tailWord_2883513) baseStart_2883513 baseEnd_2883513 := by
    simpa [prefixWord, tailWord_2883513, baseEnd_2883513] using wordTrace_append hprefix tailTrace_2883513
  have hstable : (prefixWord ++ tailWord_2883513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883513).length < 2 ^ (prefixWord ++ tailWord_2883513).sum := by decide
  have hdescent : baseEnd_2883513 < baseStart_2883513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883530 : List Nat := [3, 1, 2, 1, 2, 1, 6, 1, 1, 5]
def baseStart_2883530 : Nat := 118140960795 + 2883530 * 2 ^ 59
def prefixEnd_2883530 : Nat := 4983230072969 + 3 ^ 40 * 2883530 * 2
def baseEnd_2883530 : Nat := 493545623886402803104631

theorem tailTrace_2883530 : CollatzResearch.WordTrace tailWord_2883530 prefixEnd_2883530 493545623886402803104631 := by
  unfold tailWord_2883530
  simp only [CollatzResearch.WordTrace]
  refine ⟨26292744810867688140438011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70113986162313835041168029 26292744810867688140438011)
  ·
    refine ⟨39439117216301532210657017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26292744810867688140438011 39439117216301532210657017)
    ·
      refine ⟨29579337912226149157992763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39439117216301532210657017 29579337912226149157992763)
      ·
        refine ⟨44369006868339223736989145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29579337912226149157992763 44369006868339223736989145)
        ·
          refine ⟨33276755151254417802741859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44369006868339223736989145 33276755151254417802741859)
          ·
            refine ⟨49915132726881626704112789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33276755151254417802741859 49915132726881626704112789)
            ·
              refine ⟨2339771846572576251755287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49915132726881626704112789 2339771846572576251755287)
              ·
                refine ⟨3509657769858864377632931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2339771846572576251755287 3509657769858864377632931)
                ·
                  refine ⟨5264486654788296566449397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3509657769858864377632931 5264486654788296566449397)
                  ·
                    refine ⟨493545623886402803104631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5264486654788296566449397 493545623886402803104631)
                    ·
                      rfl

theorem cell23_2883530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_2883530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883530 prefixEnd_2883530 := by exact prefixLift 2883530
  have htrace : WordTrace (prefixWord ++ tailWord_2883530) baseStart_2883530 baseEnd_2883530 := by
    simpa [prefixWord, tailWord_2883530, baseEnd_2883530] using wordTrace_append hprefix tailTrace_2883530
  have hstable : (prefixWord ++ tailWord_2883530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883530).length < 2 ^ (prefixWord ++ tailWord_2883530).sum := by decide
  have hdescent : baseEnd_2883530 < baseStart_2883530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883543 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 4, 4]
def baseStart_2883543 : Nat := 118140960795 + 2883543 * 2 ^ 59
def prefixEnd_2883543 : Nat := 4983230072969 + 3 ^ 40 * 2883543 * 2
def baseEnd_2883543 : Nat := 493547848969238952817111

theorem tailTrace_2883543 : CollatzResearch.WordTrace tailWord_2883543 prefixEnd_2883543 493547848969238952817111 := by
  unfold tailWord_2883543
  simp only [CollatzResearch.WordTrace]
  refine ⟨105171453392423655781975283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70114302261615770521316855 105171453392423655781975283)
  ·
    refine ⟨157757180088635483672962925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105171453392423655781975283 157757180088635483672962925)
    ·
      refine ⟨59158942533238306377361097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157757180088635483672962925 59158942533238306377361097)
      ·
        refine ⟨44369206899928729783020823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59158942533238306377361097 44369206899928729783020823)
        ·
          refine ⟨66553810349893094674531235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44369206899928729783020823 66553810349893094674531235)
          ·
            refine ⟨99830715524839642011796853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66553810349893094674531235 99830715524839642011796853)
            ·
              refine ⟨9359129580453716438605955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99830715524839642011796853 9359129580453716438605955)
              ·
                refine ⟨14038694370680574657908933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9359129580453716438605955 14038694370680574657908933)
                ·
                  refine ⟨2632255194502607748357925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14038694370680574657908933 2632255194502607748357925)
                  ·
                    refine ⟨493547848969238952817111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2632255194502607748357925 493547848969238952817111)
                    ·
                      rfl

theorem cell23_2883543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 4].length) (baseStart_2883543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883543 prefixEnd_2883543 := by exact prefixLift 2883543
  have htrace : WordTrace (prefixWord ++ tailWord_2883543) baseStart_2883543 baseEnd_2883543 := by
    simpa [prefixWord, tailWord_2883543, baseEnd_2883543] using wordTrace_append hprefix tailTrace_2883543
  have hstable : (prefixWord ++ tailWord_2883543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883543).length < 2 ^ (prefixWord ++ tailWord_2883543).sum := by decide
  have hdescent : baseEnd_2883543 < baseStart_2883543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883553 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 5, 2, 3]
def baseStart_2883553 : Nat := 118140960795 + 2883553 * 2 ^ 59
def prefixEnd_2883553 : Nat := 4983230072969 + 3 ^ 40 * 2883553 * 2
def baseEnd_2883553 : Nat := 1480648681714261819326287

theorem tailTrace_2883553 : CollatzResearch.WordTrace tailWord_2883553 prefixEnd_2883553 1480648681714261819326287 := by
  unfold tailWord_2883553
  simp only [CollatzResearch.WordTrace]
  refine ⟨105171818122387427489839313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70114545414924951659892875 105171818122387427489839313)
  ·
    refine ⟨78878863591790570617379485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105171818122387427489839313 78878863591790570617379485)
    ·
      refine ⟨29579573846921463981517307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78878863591790570617379485 29579573846921463981517307)
      ·
        refine ⟨44369360770382195972275961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29579573846921463981517307 44369360770382195972275961)
        ·
          refine ⟨33277020577786646979206971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44369360770382195972275961 33277020577786646979206971)
          ·
            refine ⟨49915530866679970468810457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33277020577786646979206971 49915530866679970468810457)
            ·
              refine ⟨37436648150009977851607843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49915530866679970468810457 37436648150009977851607843)
              ·
                refine ⟨56154972225014966777411765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37436648150009977851607843 56154972225014966777411765)
                ·
                  refine ⟨5264528646095153135382353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56154972225014966777411765 5264528646095153135382353)
                  ·
                    refine ⟨3948396484571364851536765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5264528646095153135382353 3948396484571364851536765)
                    ·
                      refine ⟨1480648681714261819326287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3948396484571364851536765 1480648681714261819326287)
                      ·
                        rfl

theorem cell23_2883553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_2883553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883553 prefixEnd_2883553 := by exact prefixLift 2883553
  have htrace : WordTrace (prefixWord ++ tailWord_2883553) baseStart_2883553 baseEnd_2883553 := by
    simpa [prefixWord, tailWord_2883553, baseEnd_2883553] using wordTrace_append hprefix tailTrace_2883553
  have hstable : (prefixWord ++ tailWord_2883553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883553).length < 2 ^ (prefixWord ++ tailWord_2883553).sum := by decide
  have hdescent : baseEnd_2883553 < baseStart_2883553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883556 : List Nat := [2, 3, 1, 1, 1, 1, 4, 10]
def baseStart_2883556 : Nat := 118140960795 + 2883556 * 2 ^ 59
def prefixEnd_2883556 : Nat := 4983230072969 + 3 ^ 40 * 2883556 * 2
def baseEnd_2883556 : Nat := 54838897116897233614399

theorem tailTrace_2883556 : CollatzResearch.WordTrace tailWord_2883556 prefixEnd_2883556 54838897116897233614399 := by
  unfold tailWord_2883556
  simp only [CollatzResearch.WordTrace]
  refine ⟨52585963770688279501099261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70114618360917706001465681 52585963770688279501099261)
  ·
    refine ⟨19719736414008104812912223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52585963770688279501099261 19719736414008104812912223)
    ·
      refine ⟨29579604621012157219368335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19719736414008104812912223 29579604621012157219368335)
      ·
        refine ⟨44369406931518235829052503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29579604621012157219368335 44369406931518235829052503)
        ·
          refine ⟨66554110397277353743578755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44369406931518235829052503 66554110397277353743578755)
          ·
            refine ⟨99831165595916030615368133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66554110397277353743578755 99831165595916030615368133)
            ·
              refine ⟨18718343549234255740381525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99831165595916030615368133 18718343549234255740381525)
              ·
                refine ⟨54838897116897233614399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18718343549234255740381525 54838897116897233614399)
                ·
                  rfl

theorem cell23_2883556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 10].length) (baseStart_2883556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883556 prefixEnd_2883556 := by exact prefixLift 2883556
  have htrace : WordTrace (prefixWord ++ tailWord_2883556) baseStart_2883556 baseEnd_2883556 := by
    simpa [prefixWord, tailWord_2883556, baseEnd_2883556] using wordTrace_append hprefix tailTrace_2883556
  have hstable : (prefixWord ++ tailWord_2883556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883556).length < 2 ^ (prefixWord ++ tailWord_2883556).sum := by decide
  have hdescent : baseEnd_2883556 < baseStart_2883556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883583 : List Nat := [1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 3]
def baseStart_2883583 : Nat := 118140960795 + 2883583 * 2 ^ 59
def prefixEnd_2883583 : Nat := 4983230072969 + 3 ^ 40 * 2883583 * 2
def baseEnd_2883583 : Nat := 1480664086133896701951149

theorem tailTrace_2883583 : CollatzResearch.WordTrace tailWord_2883583 prefixEnd_2883583 1480664086133896701951149 := by
  unfold tailWord_2883583
  simp only [CollatzResearch.WordTrace]
  refine ⟨105172912312278742613431403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70115274874852495075620935 105172912312278742613431403)
  ·
    refine ⟨157759368468418113920147105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105172912312278742613431403 157759368468418113920147105)
    ·
      refine ⟨118319526351313585440110329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157759368468418113920147105 118319526351313585440110329)
      ·
        refine ⟨88739644763485189080082747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118319526351313585440110329 88739644763485189080082747)
        ·
          refine ⟨133109467145227783620124121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88739644763485189080082747 133109467145227783620124121)
          ·
            refine ⟨99832100358920837715093091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133109467145227783620124121 99832100358920837715093091)
            ·
              refine ⟨149748150538381256572639637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99832100358920837715093091 149748150538381256572639637)
              ·
                refine ⟨7019444556486621401842483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 149748150538381256572639637 7019444556486621401842483)
                ·
                  refine ⟨10529166834729932102763725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7019444556486621401842483 10529166834729932102763725)
                  ·
                    refine ⟨3948437563023724538536397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10529166834729932102763725 3948437563023724538536397)
                    ·
                      refine ⟨1480664086133896701951149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3948437563023724538536397 1480664086133896701951149)
                      ·
                        rfl

theorem cell23_2883583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_2883583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883583 prefixEnd_2883583 := by exact prefixLift 2883583
  have htrace : WordTrace (prefixWord ++ tailWord_2883583) baseStart_2883583 baseEnd_2883583 := by
    simpa [prefixWord, tailWord_2883583, baseEnd_2883583] using wordTrace_append hprefix tailTrace_2883583
  have hstable : (prefixWord ++ tailWord_2883583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883583).length < 2 ^ (prefixWord ++ tailWord_2883583).sum := by decide
  have hdescent : baseEnd_2883583 < baseStart_2883583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883644 : List Nat := [2, 2, 2, 2, 2, 1, 5, 1, 1, 3, 2]
def baseStart_2883644 : Nat := 118140960795 + 2883644 * 2 ^ 59
def prefixEnd_2883644 : Nat := 4983230072969 + 3 ^ 40 * 2883644 * 2
def baseEnd_2883644 : Nat := 1480695408453820963288369

theorem tailTrace_2883644 : CollatzResearch.WordTrace tailWord_2883644 prefixEnd_2883644 1480695408453820963288369 := by
  unfold tailWord_2883644
  simp only [CollatzResearch.WordTrace]
  refine ⟨52587568582528875015700993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70116758110038500020934657 52587568582528875015700993)
  ·
    refine ⟨39440676436896656261775745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52587568582528875015700993 39440676436896656261775745)
    ·
      refine ⟨29580507327672492196331809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39440676436896656261775745 29580507327672492196331809)
      ·
        refine ⟨22185380495754369147248857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29580507327672492196331809 22185380495754369147248857)
        ·
          refine ⟨16639035371815776860436643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22185380495754369147248857 16639035371815776860436643)
          ·
            refine ⟨24958553057723665290654965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16639035371815776860436643 24958553057723665290654965)
            ·
              refine ⟨2339864349161593620998903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24958553057723665290654965 2339864349161593620998903)
              ·
                refine ⟨3509796523742390431498355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2339864349161593620998903 3509796523742390431498355)
                ·
                  refine ⟨5264694785613585647247533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3509796523742390431498355 5264694785613585647247533)
                  ·
                    refine ⟨1974260544605094617717825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5264694785613585647247533 1974260544605094617717825)
                    ·
                      refine ⟨1480695408453820963288369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1974260544605094617717825 1480695408453820963288369)
                      ·
                        rfl

theorem cell23_2883644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_2883644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883644 prefixEnd_2883644 := by exact prefixLift 2883644
  have htrace : WordTrace (prefixWord ++ tailWord_2883644) baseStart_2883644 baseEnd_2883644 := by
    simpa [prefixWord, tailWord_2883644, baseEnd_2883644] using wordTrace_append hprefix tailTrace_2883644
  have hstable : (prefixWord ++ tailWord_2883644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883644).length < 2 ^ (prefixWord ++ tailWord_2883644).sum := by decide
  have hdescent : baseEnd_2883644 < baseStart_2883644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883653 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 2, 2, 4]
def baseStart_2883653 : Nat := 118140960795 + 2883653 * 2 ^ 59
def prefixEnd_2883653 : Nat := 4983230072969 + 3 ^ 40 * 2883653 * 2
def baseEnd_2883653 : Nat := 1480700029779711428075827

theorem tailTrace_2883653 : CollatzResearch.WordTrace tailWord_2883653 prefixEnd_2883653 1480700029779711428075827 := by
  unfold tailWord_2883653
  simp only [CollatzResearch.WordTrace]
  refine ⟨105175465422025144568479613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70116976948016763045653075 105175465422025144568479613)
  ·
    refine ⟨39440799533259429213179855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105175465422025144568479613 39440799533259429213179855)
    ·
      refine ⟨59161199299889143819769783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39440799533259429213179855 59161199299889143819769783)
      ·
        refine ⟨88741798949833715729654675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59161199299889143819769783 88741798949833715729654675)
        ·
          refine ⟨133112698424750573594482013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88741798949833715729654675 133112698424750573594482013)
          ·
            refine ⟨49917261909281465097930755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133112698424750573594482013 49917261909281465097930755)
            ·
              refine ⟨74875892863922197646896133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49917261909281465097930755 74875892863922197646896133)
              ·
                refine ⟨14039229911985412058793025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74875892863922197646896133 14039229911985412058793025)
                ·
                  refine ⟨10529422433989059044094769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14039229911985412058793025 10529422433989059044094769)
                  ·
                    refine ⟨7897066825491794283071077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10529422433989059044094769 7897066825491794283071077)
                    ·
                      refine ⟨1480700029779711428075827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7897066825491794283071077 1480700029779711428075827)
                      ·
                        rfl

theorem cell23_2883653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_2883653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883653 prefixEnd_2883653 := by exact prefixLift 2883653
  have htrace : WordTrace (prefixWord ++ tailWord_2883653) baseStart_2883653 baseEnd_2883653 := by
    simpa [prefixWord, tailWord_2883653, baseEnd_2883653] using wordTrace_append hprefix tailTrace_2883653
  have hstable : (prefixWord ++ tailWord_2883653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883653).length < 2 ^ (prefixWord ++ tailWord_2883653).sum := by decide
  have hdescent : baseEnd_2883653 < baseStart_2883653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883730 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_2883730 : Nat := 118140960795 + 2883730 * 2 ^ 59
def prefixEnd_2883730 : Nat := 4983230072969 + 3 ^ 40 * 2883730 * 2
def baseEnd_2883730 : Nat := 1480739567790107626812973

theorem tailTrace_2883730 : CollatzResearch.WordTrace tailWord_2883730 prefixEnd_2883730 1480739567790107626812973 := by
  unfold tailWord_2883730
  simp only [CollatzResearch.WordTrace]
  refine ⟨26294568460686546679758161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70118849228497457812688429 26294568460686546679758161)
  ·
    refine ⟨19720926345514910009818621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26294568460686546679758161 19720926345514910009818621)
    ·
      refine ⟨7395347379568091253681983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19720926345514910009818621 7395347379568091253681983)
      ·
        refine ⟨11093021069352136880522975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7395347379568091253681983 11093021069352136880522975)
        ·
          refine ⟨16639531604028205320784463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11093021069352136880522975 16639531604028205320784463)
          ·
            refine ⟨24959297406042307981176695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16639531604028205320784463 24959297406042307981176695)
            ·
              refine ⟨37438946109063461971765043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24959297406042307981176695 37438946109063461971765043)
              ·
                refine ⟨56158419163595192957647565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37438946109063461971765043 56158419163595192957647565)
                ·
                  refine ⟨21059407186348197359117837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56158419163595192957647565 21059407186348197359117837)
                  ·
                    refine ⟨7897277694880574009669189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21059407186348197359117837 7897277694880574009669189)
                    ·
                      refine ⟨1480739567790107626812973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7897277694880574009669189 1480739567790107626812973)
                      ·
                        rfl

theorem cell23_2883730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_2883730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883730 prefixEnd_2883730 := by exact prefixLift 2883730
  have htrace : WordTrace (prefixWord ++ tailWord_2883730) baseStart_2883730 baseEnd_2883730 := by
    simpa [prefixWord, tailWord_2883730, baseEnd_2883730] using wordTrace_append hprefix tailTrace_2883730
  have hstable : (prefixWord ++ tailWord_2883730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883730).length < 2 ^ (prefixWord ++ tailWord_2883730).sum := by decide
  have hdescent : baseEnd_2883730 < baseStart_2883730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883767 : List Nat := [1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 3]
def baseStart_2883767 : Nat := 118140960795 + 2883767 * 2 ^ 59
def prefixEnd_2883767 : Nat := 4983230072969 + 3 ^ 40 * 2883767 * 2
def baseEnd_2883767 : Nat := 1480758566574323982050303

theorem tailTrace_2883767 : CollatzResearch.WordTrace tailWord_2883767 prefixEnd_2883767 1480758566574323982050303 := by
  unfold tailWord_2883767
  simp only [CollatzResearch.WordTrace]
  refine ⟨105179623343612142038129555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70119748895741428025419703 105179623343612142038129555)
  ·
    refine ⟨157769435015418213057194333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105179623343612142038129555 157769435015418213057194333)
    ·
      refine ⟨59163538130781829896447875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157769435015418213057194333 59163538130781829896447875)
      ·
        refine ⟨88745307196172744844671813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59163538130781829896447875 88745307196172744844671813)
        ·
          refine ⟨16639745099282389658375965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88745307196172744844671813 16639745099282389658375965)
          ·
            refine ⟨6239904412230896121890987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16639745099282389658375965 6239904412230896121890987)
            ·
              refine ⟨9359856618346344182836481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6239904412230896121890987 9359856618346344182836481)
              ·
                refine ⟨7019892463759758137127361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9359856618346344182836481 7019892463759758137127361)
                ·
                  refine ⟨5264919347819818602845521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7019892463759758137127361 5264919347819818602845521)
                  ·
                    refine ⟨3948689510864863952134141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5264919347819818602845521 3948689510864863952134141)
                    ·
                      refine ⟨1480758566574323982050303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3948689510864863952134141 1480758566574323982050303)
                      ·
                        rfl

theorem cell23_2883767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_2883767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883767 prefixEnd_2883767 := by exact prefixLift 2883767
  have htrace : WordTrace (prefixWord ++ tailWord_2883767) baseStart_2883767 baseEnd_2883767 := by
    simpa [prefixWord, tailWord_2883767, baseEnd_2883767] using wordTrace_append hprefix tailTrace_2883767
  have hstable : (prefixWord ++ tailWord_2883767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883767).length < 2 ^ (prefixWord ++ tailWord_2883767).sum := by decide
  have hdescent : baseEnd_2883767 < baseStart_2883767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883783 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 1, 11]
def baseStart_2883783 : Nat := 118140960795 + 2883783 * 2 ^ 59
def prefixEnd_2883783 : Nat := 4983230072969 + 3 ^ 40 * 2883783 * 2
def baseEnd_2883783 : Nat := 493588927421598639816743

theorem tailTrace_2883783 : CollatzResearch.WordTrace tailWord_2883783 prefixEnd_2883783 493588927421598639816743 := by
  unfold tailWord_2883783
  simp only [CollatzResearch.WordTrace]
  refine ⟨105180206911554176770712003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70120137941036117847141335 105180206911554176770712003)
  ·
    refine ⟨157770310367331265156068005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105180206911554176770712003 157770310367331265156068005)
    ·
      refine ⟨29581933193874612216762751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157770310367331265156068005 29581933193874612216762751)
      ·
        refine ⟨44372899790811918325144127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29581933193874612216762751 44372899790811918325144127)
        ·
          refine ⟨66559349686217877487716191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44372899790811918325144127 66559349686217877487716191)
          ·
            refine ⟨99839024529326816231574287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66559349686217877487716191 99839024529326816231574287)
            ·
              refine ⟨149758536793990224347361431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99839024529326816231574287 149758536793990224347361431)
              ·
                refine ⟨224637805190985336521042147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149758536793990224347361431 224637805190985336521042147)
                ·
                  refine ⟨336956707786478004781563221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224637805190985336521042147 336956707786478004781563221)
                  ·
                    refine ⟨493588927421598639816743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 336956707786478004781563221 493588927421598639816743)
                    ·
                      rfl

theorem cell23_2883783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_2883783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883783 prefixEnd_2883783 := by exact prefixLift 2883783
  have htrace : WordTrace (prefixWord ++ tailWord_2883783) baseStart_2883783 baseEnd_2883783 := by
    simpa [prefixWord, tailWord_2883783, baseEnd_2883783] using wordTrace_append hprefix tailTrace_2883783
  have hstable : (prefixWord ++ tailWord_2883783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883783).length < 2 ^ (prefixWord ++ tailWord_2883783).sum := by decide
  have hdescent : baseEnd_2883783 < baseStart_2883783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883840 : List Nat := [2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 5]
def baseStart_2883840 : Nat := 118140960795 + 2883840 * 2 ^ 59
def prefixEnd_2883840 : Nat := 4983230072969 + 3 ^ 40 * 2883840 * 2
def baseEnd_2883840 : Nat := 1480796050662102196437467

theorem tailTrace_2883840 : CollatzResearch.WordTrace tailWord_2883840 prefixEnd_2883840 1480796050662102196437467 := by
  unfold tailWord_2883840
  simp only [CollatzResearch.WordTrace]
  refine ⟨52591142936173837752768487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70121523914898450337024649 52591142936173837752768487)
  ·
    refine ⟨78886714404260756629152731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52591142936173837752768487 78886714404260756629152731)
    ·
      refine ⟨118330071606391134943729097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78886714404260756629152731 118330071606391134943729097)
      ·
        refine ⟨88747553704793351207796823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118330071606391134943729097 88747553704793351207796823)
        ·
          refine ⟨133121330557190026811695235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88747553704793351207796823 133121330557190026811695235)
          ·
            refine ⟨199681995835785040217542853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133121330557190026811695235 199681995835785040217542853)
            ·
              refine ⟨37440374219209695040789285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 199681995835785040217542853 37440374219209695040789285)
              ·
                refine ⟨7020070166101817820147991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37440374219209695040789285 7020070166101817820147991)
                ·
                  refine ⟨10530105249152726730221987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7020070166101817820147991 10530105249152726730221987)
                  ·
                    refine ⟨15795157873729090095332981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10530105249152726730221987 15795157873729090095332981)
                    ·
                      refine ⟨1480796050662102196437467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15795157873729090095332981 1480796050662102196437467)
                      ·
                        rfl

theorem cell23_2883840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_2883840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883840 prefixEnd_2883840 := by exact prefixLift 2883840
  have htrace : WordTrace (prefixWord ++ tailWord_2883840) baseStart_2883840 baseEnd_2883840 := by
    simpa [prefixWord, tailWord_2883840, baseEnd_2883840] using wordTrace_append hprefix tailTrace_2883840
  have hstable : (prefixWord ++ tailWord_2883840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883840).length < 2 ^ (prefixWord ++ tailWord_2883840).sum := by decide
  have hdescent : baseEnd_2883840 < baseStart_2883840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883850 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_2883850 : Nat := 118140960795 + 2883850 * 2 ^ 59
def prefixEnd_2883850 : Nat := 4983230072969 + 3 ^ 40 * 2883850 * 2
def baseEnd_2883850 : Nat := 1480801185468647157312421

theorem tailTrace_2883850 : CollatzResearch.WordTrace tailWord_2883850 prefixEnd_2883850 1480801185468647157312421 := by
  unfold tailWord_2883850
  simp only [CollatzResearch.WordTrace]
  refine ⟨26295662650577861803350251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70121767068207631475600669 26295662650577861803350251)
  ·
    refine ⟨39443493975866792705025377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26295662650577861803350251 39443493975866792705025377)
    ·
      refine ⟨29582620481900094528769033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39443493975866792705025377 29582620481900094528769033)
      ·
        refine ⟨22186965361425070896576775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29582620481900094528769033 22186965361425070896576775)
        ·
          refine ⟨33280448042137606344865163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22186965361425070896576775 33280448042137606344865163)
          ·
            refine ⟨49920672063206409517297745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33280448042137606344865163 49920672063206409517297745)
            ·
              refine ⟨37440504047404807137973309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49920672063206409517297745 37440504047404807137973309)
              ·
                refine ⟨14040189017776802676739991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37440504047404807137973309 14040189017776802676739991)
                ·
                  refine ⟨21060283526665204015109987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14040189017776802676739991 21060283526665204015109987)
                  ·
                    refine ⟨31590425289997806022664981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21060283526665204015109987 31590425289997806022664981)
                    ·
                      refine ⟨1480801185468647157312421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31590425289997806022664981 1480801185468647157312421)
                      ·
                        rfl

theorem cell23_2883850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_2883850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883850 prefixEnd_2883850 := by exact prefixLift 2883850
  have htrace : WordTrace (prefixWord ++ tailWord_2883850) baseStart_2883850 baseEnd_2883850 := by
    simpa [prefixWord, tailWord_2883850, baseEnd_2883850] using wordTrace_append hprefix tailTrace_2883850
  have hstable : (prefixWord ++ tailWord_2883850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883850).length < 2 ^ (prefixWord ++ tailWord_2883850).sum := by decide
  have hdescent : baseEnd_2883850 < baseStart_2883850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883857 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 3]
def baseStart_2883857 : Nat := 118140960795 + 2883857 * 2 ^ 59
def prefixEnd_2883857 : Nat := 4983230072969 + 3 ^ 40 * 2883857 * 2
def baseEnd_2883857 : Nat := 1480804779833228629924889

theorem tailTrace_2883857 : CollatzResearch.WordTrace tailWord_2883857 prefixEnd_2883857 1480804779833228629924889 := by
  unfold tailWord_2883857
  simp only [CollatzResearch.WordTrace]
  refine ⟨105182905913286087408905825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70121937275524058272603883 105182905913286087408905825)
  ·
    refine ⟨78887179434964565556679369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105182905913286087408905825 78887179434964565556679369)
    ·
      refine ⟨59165384576223424167509527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78887179434964565556679369 59165384576223424167509527)
      ·
        refine ⟨88748076864335136251264291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59165384576223424167509527 88748076864335136251264291)
        ·
          refine ⟨133122115296502704376896437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88748076864335136251264291 133122115296502704376896437)
          ·
            refine ⟨12480198309047128535334041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133122115296502704376896437 12480198309047128535334041)
            ·
              refine ⟨9360148731785346401500531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12480198309047128535334041 9360148731785346401500531)
              ·
                refine ⟨14040223097678019602250797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9360148731785346401500531 14040223097678019602250797)
                ·
                  refine ⟨5265083661629257350844049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14040223097678019602250797 5265083661629257350844049)
                  ·
                    refine ⟨3948812746221943013133037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5265083661629257350844049 3948812746221943013133037)
                    ·
                      refine ⟨1480804779833228629924889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3948812746221943013133037 1480804779833228629924889)
                      ·
                        rfl

theorem cell23_2883857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_2883857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883857 prefixEnd_2883857 := by exact prefixLift 2883857
  have htrace : WordTrace (prefixWord ++ tailWord_2883857) baseStart_2883857 baseEnd_2883857 := by
    simpa [prefixWord, tailWord_2883857, baseEnd_2883857] using wordTrace_append hprefix tailTrace_2883857
  have hstable : (prefixWord ++ tailWord_2883857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883857).length < 2 ^ (prefixWord ++ tailWord_2883857).sum := by decide
  have hdescent : baseEnd_2883857 < baseStart_2883857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883871 : List Nat := [1, 1, 2, 4, 3, 3, 2, 1, 1, 1, 4]
def baseStart_2883871 : Nat := 118140960795 + 2883871 * 2 ^ 59
def prefixEnd_2883871 : Nat := 4983230072969 + 3 ^ 40 * 2883871 * 2
def baseEnd_2883871 : Nat := 1480811968562391575149825

theorem tailTrace_2883871 : CollatzResearch.WordTrace tailWord_2883871 prefixEnd_2883871 1480811968562391575149825 := by
  unfold tailWord_2883871
  simp only [CollatzResearch.WordTrace]
  refine ⟨105183416535235367799915467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70122277690156911866610311 105183416535235367799915467)
  ·
    refine ⟨157775124802853051699873201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105183416535235367799915467 157775124802853051699873201)
    ·
      refine ⟨118331343602139788774904901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157775124802853051699873201 118331343602139788774904901)
      ·
        refine ⟨22187126925401210395294669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118331343602139788774904901 22187126925401210395294669)
        ·
          refine ⟨8320172597025453898235501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22187126925401210395294669 8320172597025453898235501)
          ·
            refine ⟨3120064723884545211838313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8320172597025453898235501 3120064723884545211838313)
            ·
              refine ⟨2340048542913408908878735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3120064723884545211838313 2340048542913408908878735)
              ·
                refine ⟨3510072814370113363318103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2340048542913408908878735 3510072814370113363318103)
                ·
                  refine ⟨5265109221555170044977155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3510072814370113363318103 5265109221555170044977155)
                  ·
                    refine ⟨7897663832332755067465733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5265109221555170044977155 7897663832332755067465733)
                    ·
                      refine ⟨1480811968562391575149825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7897663832332755067465733 1480811968562391575149825)
                      ·
                        rfl

theorem cell23_2883871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_2883871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883871 prefixEnd_2883871 := by exact prefixLift 2883871
  have htrace : WordTrace (prefixWord ++ tailWord_2883871) baseStart_2883871 baseEnd_2883871 := by
    simpa [prefixWord, tailWord_2883871, baseEnd_2883871] using wordTrace_append hprefix tailTrace_2883871
  have hstable : (prefixWord ++ tailWord_2883871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883871).length < 2 ^ (prefixWord ++ tailWord_2883871).sum := by decide
  have hdescent : baseEnd_2883871 < baseStart_2883871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883908 : List Nat := [2, 3, 4, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_2883908 : Nat := 118140960795 + 2883908 * 2 ^ 59
def prefixEnd_2883908 : Nat := 4983230072969 + 3 ^ 40 * 2883908 * 2
def baseEnd_2883908 : Nat := 1480830967346607930387155

theorem tailTrace_2883908 : CollatzResearch.WordTrace tailWord_2883908 prefixEnd_2883908 1480830967346607930387155 := by
  unfold tailWord_2883908
  simp only [CollatzResearch.WordTrace]
  refine ⟨52592383018050661559506189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70123177357400882079341585 52592383018050661559506189)
  ·
    refine ⟨19722143631768998084814821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52592383018050661559506189 19722143631768998084814821)
    ·
      refine ⟨3697901930956687140902779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19722143631768998084814821 3697901930956687140902779)
      ·
        refine ⟨5546852896435030711354169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3697901930956687140902779 5546852896435030711354169)
        ·
          refine ⟨4160139672326273033515627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5546852896435030711354169 4160139672326273033515627)
          ·
            refine ⟨6240209508489409550273441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4160139672326273033515627 6240209508489409550273441)
            ·
              refine ⟨4680157131367057162705081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6240209508489409550273441 4680157131367057162705081)
              ·
                refine ⟨3510117848525292872028811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4680157131367057162705081 3510117848525292872028811)
                ·
                  refine ⟨5265176772787939308043217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3510117848525292872028811 5265176772787939308043217)
                  ·
                    refine ⟨3948882579590954481032413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5265176772787939308043217 3948882579590954481032413)
                    ·
                      refine ⟨1480830967346607930387155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3948882579590954481032413 1480830967346607930387155)
                      ·
                        rfl

theorem cell23_2883908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_2883908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883908 prefixEnd_2883908 := by exact prefixLift 2883908
  have htrace : WordTrace (prefixWord ++ tailWord_2883908) baseStart_2883908 baseEnd_2883908 := by
    simpa [prefixWord, tailWord_2883908, baseEnd_2883908] using wordTrace_append hprefix tailTrace_2883908
  have hstable : (prefixWord ++ tailWord_2883908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883908).length < 2 ^ (prefixWord ++ tailWord_2883908).sum := by decide
  have hdescent : baseEnd_2883908 < baseStart_2883908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883978 : List Nat := [3, 1, 2, 5, 1, 1, 1, 2, 1, 4, 2]
def baseStart_2883978 : Nat := 118140960795 + 2883978 * 2 ^ 59
def prefixEnd_2883978 : Nat := 4983230072969 + 3 ^ 40 * 2883978 * 2
def baseEnd_2883978 : Nat := 1480866910992422656511833

theorem tailTrace_2883978 : CollatzResearch.WordTrace tailWord_2883978 prefixEnd_2883978 1480866910992422656511833 := by
  unfold tailWord_2883978
  simp only [CollatzResearch.WordTrace]
  refine ⟨26296829786461931268515147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70124879430565150049373725 26296829786461931268515147)
  ·
    refine ⟨39445244679692896902772721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26296829786461931268515147 39445244679692896902772721)
    ·
      refine ⟨29583933509769672677079541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39445244679692896902772721 29583933509769672677079541)
      ·
        refine ⟨2773493766540906813476207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29583933509769672677079541 2773493766540906813476207)
        ·
          refine ⟨4160240649811360220214311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2773493766540906813476207 4160240649811360220214311)
          ·
            refine ⟨6240360974717040330321467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4160240649811360220214311 6240360974717040330321467)
            ·
              refine ⟨9360541462075560495482201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6240360974717040330321467 9360541462075560495482201)
              ·
                refine ⟨7020406096556670371611651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9360541462075560495482201 7020406096556670371611651)
                ·
                  refine ⟨10530609144835005557417477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7020406096556670371611651 10530609144835005557417477)
                  ·
                    refine ⟨1974489214656563542015777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10530609144835005557417477 1974489214656563542015777)
                    ·
                      refine ⟨1480866910992422656511833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1974489214656563542015777 1480866910992422656511833)
                      ·
                        rfl

theorem cell23_2883978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_2883978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2883978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2883978 prefixEnd_2883978 := by exact prefixLift 2883978
  have htrace : WordTrace (prefixWord ++ tailWord_2883978) baseStart_2883978 baseEnd_2883978 := by
    simpa [prefixWord, tailWord_2883978, baseEnd_2883978] using wordTrace_append hprefix tailTrace_2883978
  have hstable : (prefixWord ++ tailWord_2883978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883978).length < 2 ^ (prefixWord ++ tailWord_2883978).sum := by decide
  have hdescent : baseEnd_2883978 < baseStart_2883978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884004 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 2, 5, 2]
def baseStart_2884004 : Nat := 118140960795 + 2884004 * 2 ^ 59
def prefixEnd_2884004 : Nat := 4983230072969 + 3 ^ 40 * 2884004 * 2
def baseEnd_2884004 : Nat := 1480880261489439554786713

theorem tailTrace_2884004 : CollatzResearch.WordTrace tailWord_2884004 prefixEnd_2884004 1480880261489439554786713 := by
  unfold tailWord_2884004
  simp only [CollatzResearch.WordTrace]
  refine ⟨52594133721876765757253533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70125511629169021009671377 52594133721876765757253533)
  ·
    refine ⟨19722800145703787158970075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52594133721876765757253533 19722800145703787158970075)
    ·
      refine ⟨29584200218555680738455113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19722800145703787158970075 29584200218555680738455113)
      ·
        refine ⟨22188150163916760553841335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29584200218555680738455113 22188150163916760553841335)
        ·
          refine ⟨33282225245875140830762003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22188150163916760553841335 33282225245875140830762003)
          ·
            refine ⟨49923337868812711246143005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33282225245875140830762003 49923337868812711246143005)
            ·
              refine ⟨18721251700804766717303627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49923337868812711246143005 18721251700804766717303627)
              ·
                refine ⟨28081877551207150075955441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18721251700804766717303627 28081877551207150075955441)
                ·
                  refine ⟨21061408163405362556966581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28081877551207150075955441 21061408163405362556966581)
                  ·
                    refine ⟨1974507015319252739715617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21061408163405362556966581 1974507015319252739715617)
                    ·
                      refine ⟨1480880261489439554786713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1974507015319252739715617 1480880261489439554786713)
                      ·
                        rfl

theorem cell23_2884004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_2884004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884004 prefixEnd_2884004 := by exact prefixLift 2884004
  have htrace : WordTrace (prefixWord ++ tailWord_2884004) baseStart_2884004 baseEnd_2884004 := by
    simpa [prefixWord, tailWord_2884004, baseEnd_2884004] using wordTrace_append hprefix tailTrace_2884004
  have hstable : (prefixWord ++ tailWord_2884004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884004).length < 2 ^ (prefixWord ++ tailWord_2884004).sum := by decide
  have hdescent : baseEnd_2884004 < baseStart_2884004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884057 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 8]
def baseStart_2884057 : Nat := 118140960795 + 2884057 * 2 ^ 59
def prefixEnd_2884057 : Nat := 4983230072969 + 3 ^ 40 * 2884057 * 2
def baseEnd_2884057 : Nat := 164545275107125316380441

theorem tailTrace_2884057 : CollatzResearch.WordTrace tailWord_2884057 prefixEnd_2884057 164545275107125316380441 := by
  unfold tailWord_2884057
  simp only [CollatzResearch.WordTrace]
  refine ⟨105190200512561521566186425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70126800341707681044124283 105190200512561521566186425)
  ·
    refine ⟨78892650384421141174639819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105190200512561521566186425 78892650384421141174639819)
    ·
      refine ⟨118338975576631711761959729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78892650384421141174639819 118338975576631711761959729)
      ·
        refine ⟨88754231682473783821469797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118338975576631711761959729 88754231682473783821469797)
        ·
          refine ⟨16641418440463834466525587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88754231682473783821469797 16641418440463834466525587)
          ·
            refine ⟨24962127660695751699788381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16641418440463834466525587 24962127660695751699788381)
            ·
              refine ⟨9360797872760906887420643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24962127660695751699788381 9360797872760906887420643)
              ·
                refine ⟨14041196809141360331130965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9360797872760906887420643 14041196809141360331130965)
                ·
                  refine ⟨164545275107125316380441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14041196809141360331130965 164545275107125316380441)
                  ·
                    rfl

theorem cell23_2884057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 8].length) (baseStart_2884057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884057 prefixEnd_2884057 := by exact prefixLift 2884057
  have htrace : WordTrace (prefixWord ++ tailWord_2884057) baseStart_2884057 baseEnd_2884057 := by
    simpa [prefixWord, tailWord_2884057, baseEnd_2884057] using wordTrace_append hprefix tailTrace_2884057
  have hstable : (prefixWord ++ tailWord_2884057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884057).length < 2 ^ (prefixWord ++ tailWord_2884057).sum := by decide
  have hdescent : baseEnd_2884057 < baseStart_2884057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884061 : List Nat := [1, 4, 3, 1, 1, 1, 4, 1, 3, 4]
def baseStart_2884061 : Nat := 118140960795 + 2884061 * 2 ^ 59
def prefixEnd_2884061 : Nat := 4983230072969 + 3 ^ 40 * 2884061 * 2
def baseEnd_2884061 : Nat := 493636509962248610591317

theorem tailTrace_2884061 : CollatzResearch.WordTrace tailWord_2884061 prefixEnd_2884061 493636509962248610591317 := by
  unfold tailWord_2884061
  simp only [CollatzResearch.WordTrace]
  refine ⟨105190346404547030249332037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70126897603031353499554691 105190346404547030249332037)
  ·
    refine ⟨19723189950852568171749757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105190346404547030249332037 19723189950852568171749757)
    ·
      refine ⟨7396196231569713064406159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19723189950852568171749757 7396196231569713064406159)
      ·
        refine ⟨11094294347354569596609239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7396196231569713064406159 11094294347354569596609239)
        ·
          refine ⟨16641441521031854394913859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11094294347354569596609239 16641441521031854394913859)
          ·
            refine ⟨24962162281547781592370789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16641441521031854394913859 24962162281547781592370789)
            ·
              refine ⟨4680405427790209048569523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24962162281547781592370789 4680405427790209048569523)
              ·
                refine ⟨7020608141685313572854285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4680405427790209048569523 7020608141685313572854285)
                ·
                  refine ⟨2632728053131992589820357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7020608141685313572854285 2632728053131992589820357)
                  ·
                    refine ⟨493636509962248610591317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2632728053131992589820357 493636509962248610591317)
                    ·
                      rfl

theorem cell23_2884061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_2884061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884061 prefixEnd_2884061 := by exact prefixLift 2884061
  have htrace : WordTrace (prefixWord ++ tailWord_2884061) baseStart_2884061 baseEnd_2884061 := by
    simpa [prefixWord, tailWord_2884061, baseEnd_2884061] using wordTrace_append hprefix tailTrace_2884061
  have hstable : (prefixWord ++ tailWord_2884061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884061).length < 2 ^ (prefixWord ++ tailWord_2884061).sum := by decide
  have hdescent : baseEnd_2884061 < baseStart_2884061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884087 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 7, 5]
def baseStart_2884087 : Nat := 118140960795 + 2884087 * 2 ^ 59
def prefixEnd_2884087 : Nat := 4983230072969 + 3 ^ 40 * 2884087 * 2
def baseEnd_2884087 : Nat := 493640960127920910016277

theorem tailTrace_2884087 : CollatzResearch.WordTrace tailWord_2884087 prefixEnd_2884087 493640960127920910016277 := by
  unfold tailWord_2884087
  simp only [CollatzResearch.WordTrace]
  refine ⟨105191294702452836689778515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70127529801635224459852343 105191294702452836689778515)
  ·
    refine ⟨157786942053679255034667773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105191294702452836689778515 157786942053679255034667773)
    ·
      refine ⟨59170103270129720638000415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157786942053679255034667773 59170103270129720638000415)
      ·
        refine ⟨88755154905194580957000623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59170103270129720638000415 88755154905194580957000623)
        ·
          refine ⟨133132732357791871435500935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88755154905194580957000623 133132732357791871435500935)
          ·
            refine ⟨199699098536687807153251403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133132732357791871435500935 199699098536687807153251403)
            ·
              refine ⟨299548647805031710729877105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199699098536687807153251403 299548647805031710729877105)
              ·
                refine ⟨224661485853773783047407829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299548647805031710729877105 224661485853773783047407829)
                ·
                  refine ⟨5265503574697823040173621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 224661485853773783047407829 5265503574697823040173621)
                  ·
                    refine ⟨493640960127920910016277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5265503574697823040173621 493640960127920910016277)
                    ·
                      rfl

theorem cell23_2884087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_2884087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884087 prefixEnd_2884087 := by exact prefixLift 2884087
  have htrace : WordTrace (prefixWord ++ tailWord_2884087) baseStart_2884087 baseEnd_2884087 := by
    simpa [prefixWord, tailWord_2884087, baseEnd_2884087] using wordTrace_append hprefix tailTrace_2884087
  have hstable : (prefixWord ++ tailWord_2884087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884087).length < 2 ^ (prefixWord ++ tailWord_2884087).sum := by decide
  have hdescent : baseEnd_2884087 < baseStart_2884087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884138 : List Nat := [3, 1, 4, 1, 1, 4, 1, 2, 1, 5]
def baseStart_2884138 : Nat := 118140960795 + 2884138 * 2 ^ 59
def prefixEnd_2884138 : Nat := 4983230072969 + 3 ^ 40 * 2884138 * 2
def baseEnd_2884138 : Nat := 493649689299047343503699

theorem tailTrace_2884138 : CollatzResearch.WordTrace tailWord_2884138 prefixEnd_2884138 493649689299047343503699 := by
  unfold tailWord_2884138
  simp only [CollatzResearch.WordTrace]
  refine ⟨26298288706317018099971267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70128769883512048266590045 26298288706317018099971267)
  ·
    refine ⟨39447433059475527149956901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26298288706317018099971267 39447433059475527149956901)
    ·
      refine ⟨7396393698651661340616919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39447433059475527149956901 7396393698651661340616919)
      ·
        refine ⟨11094590547977492010925379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7396393698651661340616919 11094590547977492010925379)
        ·
          refine ⟨16641885821966238016388069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11094590547977492010925379 16641885821966238016388069)
          ·
            refine ⟨3120353591618669628072763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16641885821966238016388069 3120353591618669628072763)
            ·
              refine ⟨4680530387428004442109145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3120353591618669628072763 4680530387428004442109145)
              ·
                refine ⟨3510397790571003331581859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4680530387428004442109145 3510397790571003331581859)
                ·
                  refine ⟨5265596685856504997372789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3510397790571003331581859 5265596685856504997372789)
                  ·
                    refine ⟨493649689299047343503699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5265596685856504997372789 493649689299047343503699)
                    ·
                      rfl

theorem cell23_2884138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_2884138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884138 prefixEnd_2884138 := by exact prefixLift 2884138
  have htrace : WordTrace (prefixWord ++ tailWord_2884138) baseStart_2884138 baseEnd_2884138 := by
    simpa [prefixWord, tailWord_2884138, baseEnd_2884138] using wordTrace_append hprefix tailTrace_2884138
  have hstable : (prefixWord ++ tailWord_2884138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884138).length < 2 ^ (prefixWord ++ tailWord_2884138).sum := by decide
  have hdescent : baseEnd_2884138 < baseStart_2884138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884147 : List Nat := [1, 1, 1, 2, 4, 2, 1, 11]
def baseStart_2884147 : Nat := 118140960795 + 2884147 * 2 ^ 59
def prefixEnd_2884147 : Nat := 4983230072969 + 3 ^ 40 * 2884147 * 2
def baseEnd_2884147 : Nat := 54850136637890092418465

theorem tailTrace_2884147 : CollatzResearch.WordTrace tailWord_2884147 prefixEnd_2884147 54850136637890092418465 := by
  unfold tailWord_2884147
  simp only [CollatzResearch.WordTrace]
  refine ⟨105193483082235466936962695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70128988721490311291308463 105193483082235466936962695)
  ·
    refine ⟨157790224623353200405444043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105193483082235466936962695 157790224623353200405444043)
    ·
      refine ⟨236685336935029800608166065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157790224623353200405444043 236685336935029800608166065)
      ·
        refine ⟨177514002701272350456124549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236685336935029800608166065 177514002701272350456124549)
        ·
          refine ⟨33283875506488565710523353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177514002701272350456124549 33283875506488565710523353)
          ·
            refine ⟨24962906629866424282892515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33283875506488565710523353 24962906629866424282892515)
            ·
              refine ⟨37444359944799636424338773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24962906629866424282892515 37444359944799636424338773)
              ·
                refine ⟨54850136637890092418465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 37444359944799636424338773 54850136637890092418465)
                ·
                  rfl

theorem cell23_2884147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 11].length) (baseStart_2884147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884147 prefixEnd_2884147 := by exact prefixLift 2884147
  have htrace : WordTrace (prefixWord ++ tailWord_2884147) baseStart_2884147 baseEnd_2884147 := by
    simpa [prefixWord, tailWord_2884147, baseEnd_2884147] using wordTrace_append hprefix tailTrace_2884147
  have hstable : (prefixWord ++ tailWord_2884147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884147).length < 2 ^ (prefixWord ++ tailWord_2884147).sum := by decide
  have hdescent : baseEnd_2884147 < baseStart_2884147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884154 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4]
def baseStart_2884154 : Nat := 118140960795 + 2884154 * 2 ^ 59
def prefixEnd_2884154 : Nat := 4983230072969 + 3 ^ 40 * 2884154 * 2
def baseEnd_2884154 : Nat := 1480957283587613967911023

theorem tailTrace_2884154 : CollatzResearch.WordTrace tailWord_2884154 prefixEnd_2884154 1480957283587613967911023 := by
  unfold tailWord_2884154
  simp only [CollatzResearch.WordTrace]
  refine ⟨26298434598302526783116879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70129158928806738088311677 26298434598302526783116879)
  ·
    refine ⟨39447651897453790174675319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26298434598302526783116879 39447651897453790174675319)
    ·
      refine ⟨59171477846180685262012979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39447651897453790174675319 59171477846180685262012979)
      ·
        refine ⟨88757216769271027893019469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59171477846180685262012979 88757216769271027893019469)
        ·
          refine ⟨33283956288476635459882301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88757216769271027893019469 33283956288476635459882301)
          ·
            refine ⟨12481483608178738297455863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33283956288476635459882301 12481483608178738297455863)
            ·
              refine ⟨18722225412268107446183795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12481483608178738297455863 18722225412268107446183795)
              ·
                refine ⟨28083338118402161169275693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18722225412268107446183795 28083338118402161169275693)
                ·
                  refine ⟨10531251794400810438478385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28083338118402161169275693 10531251794400810438478385)
                  ·
                    refine ⟨7898438845800607828858789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10531251794400810438478385 7898438845800607828858789)
                    ·
                      refine ⟨1480957283587613967911023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7898438845800607828858789 1480957283587613967911023)
                      ·
                        rfl

theorem cell23_2884154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_2884154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884154 prefixEnd_2884154 := by exact prefixLift 2884154
  have htrace : WordTrace (prefixWord ++ tailWord_2884154) baseStart_2884154 baseEnd_2884154 := by
    simpa [prefixWord, tailWord_2884154, baseEnd_2884154] using wordTrace_append hprefix tailTrace_2884154
  have hstable : (prefixWord ++ tailWord_2884154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884154).length < 2 ^ (prefixWord ++ tailWord_2884154).sum := by decide
  have hdescent : baseEnd_2884154 < baseStart_2884154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884161 : List Nat := [1, 2, 5, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_2884161 : Nat := 118140960795 + 2884161 * 2 ^ 59
def prefixEnd_2884161 : Nat := 4983230072969 + 3 ^ 40 * 2884161 * 2
def baseEnd_2884161 : Nat := 1480960877952195440523491

theorem tailTrace_2884161 : CollatzResearch.WordTrace tailWord_2884161 prefixEnd_2884161 1480960877952195440523491 := by
  unfold tailWord_2884161
  simp only [CollatzResearch.WordTrace]
  refine ⟨105193993704184747327972337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70129329136123164885314891 105193993704184747327972337)
  ·
    refine ⟨78895495278138560495979253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105193993704184747327972337 78895495278138560495979253)
    ·
      refine ⟨7396452682325490046498055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78895495278138560495979253 7396452682325490046498055)
      ·
        refine ⟨11094679023488235069747083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7396452682325490046498055 11094679023488235069747083)
        ·
          refine ⟨16642018535232352604620625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11094679023488235069747083 16642018535232352604620625)
          ·
            refine ⟨12481513901424264453465469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16642018535232352604620625 12481513901424264453465469)
            ·
              refine ⟨4680567713034099170049551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12481513901424264453465469 4680567713034099170049551)
              ·
                refine ⟨7020851569551148755074327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4680567713034099170049551 7020851569551148755074327)
                ·
                  refine ⟨10531277354326723132611491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7020851569551148755074327 10531277354326723132611491)
                  ·
                    refine ⟨15796916031490084698917237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10531277354326723132611491 15796916031490084698917237)
                    ·
                      refine ⟨1480960877952195440523491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15796916031490084698917237 1480960877952195440523491)
                      ·
                        rfl

theorem cell23_2884161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_2884161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884161 prefixEnd_2884161 := by exact prefixLift 2884161
  have htrace : WordTrace (prefixWord ++ tailWord_2884161) baseStart_2884161 baseEnd_2884161 := by
    simpa [prefixWord, tailWord_2884161, baseEnd_2884161] using wordTrace_append hprefix tailTrace_2884161
  have hstable : (prefixWord ++ tailWord_2884161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884161).length < 2 ^ (prefixWord ++ tailWord_2884161).sum := by decide
  have hdescent : baseEnd_2884161 < baseStart_2884161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884188 : List Nat := [2, 2, 4, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_2884188 : Nat := 118140960795 + 2884188 * 2 ^ 59
def prefixEnd_2884188 : Nat := 4983230072969 + 3 ^ 40 * 2884188 * 2
def baseEnd_2884188 : Nat := 1480974741929866834885867

theorem tailTrace_2884188 : CollatzResearch.WordTrace tailWord_2884188 prefixEnd_2884188 1480974741929866834885867 := by
  unfold tailWord_2884188
  simp only [CollatzResearch.WordTrace]
  refine ⟨52597489237543465469602609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70129985650057953959470145 52597489237543465469602609)
  ·
    refine ⟨39448116928157599102201957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52597489237543465469602609 39448116928157599102201957)
    ·
      refine ⟨7396521924029549831662867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39448116928157599102201957 7396521924029549831662867)
      ·
        refine ⟨11094782886044324747494301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7396521924029549831662867 11094782886044324747494301)
        ·
          refine ⟨4160543582266621780310363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11094782886044324747494301 4160543582266621780310363)
          ·
            refine ⟨6240815373399932670465545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4160543582266621780310363 6240815373399932670465545)
            ·
              refine ⟨4680611530049949502849159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6240815373399932670465545 4680611530049949502849159)
              ·
                refine ⟨7020917295074924254273739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4680611530049949502849159 7020917295074924254273739)
                ·
                  refine ⟨10531375942612386381410609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7020917295074924254273739 10531375942612386381410609)
                  ·
                    refine ⟨7898531956959289786057957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10531375942612386381410609 7898531956959289786057957)
                    ·
                      refine ⟨1480974741929866834885867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7898531956959289786057957 1480974741929866834885867)
                      ·
                        rfl

theorem cell23_2884188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_2884188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884188 prefixEnd_2884188 := by exact prefixLift 2884188
  have htrace : WordTrace (prefixWord ++ tailWord_2884188) baseStart_2884188 baseEnd_2884188 := by
    simpa [prefixWord, tailWord_2884188, baseEnd_2884188] using wordTrace_append hprefix tailTrace_2884188
  have hstable : (prefixWord ++ tailWord_2884188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884188).length < 2 ^ (prefixWord ++ tailWord_2884188).sum := by decide
  have hdescent : baseEnd_2884188 < baseStart_2884188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884224 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 2, 6]
def baseStart_2884224 : Nat := 118140960795 + 2884224 * 2 ^ 59
def prefixEnd_2884224 : Nat := 4983230072969 + 3 ^ 40 * 2884224 * 2
def baseEnd_2884224 : Nat := 493664409077809564678567

theorem tailTrace_2884224 : CollatzResearch.WordTrace tailWord_2884224 prefixEnd_2884224 493664409077809564678567 := by
  unfold tailWord_2884224
  simp only [CollatzResearch.WordTrace]
  refine ⟨52598145751478254543757863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70130861001971006058343817 52598145751478254543757863)
  ·
    refine ⟨78897218627217381815636795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52598145751478254543757863 78897218627217381815636795)
    ·
      refine ⟨118345827940826072723455193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78897218627217381815636795 118345827940826072723455193)
      ·
        refine ⟨88759370955619554542591395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118345827940826072723455193 88759370955619554542591395)
        ·
          refine ⟨133139056433429331813887093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88759370955619554542591395 133139056433429331813887093)
          ·
            refine ⟨12481786540633999857551915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133139056433429331813887093 12481786540633999857551915)
            ·
              refine ⟨18722679810950999786327873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12481786540633999857551915 18722679810950999786327873)
              ·
                refine ⟨14042009858213249839745905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18722679810950999786327873 14042009858213249839745905)
                ·
                  refine ⟨10531507393659937379809429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14042009858213249839745905 10531507393659937379809429)
                  ·
                    refine ⟨493664409077809564678567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10531507393659937379809429 493664409077809564678567)
                    ·
                      rfl

theorem cell23_2884224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 2, 6].length) (baseStart_2884224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884224 prefixEnd_2884224 := by exact prefixLift 2884224
  have htrace : WordTrace (prefixWord ++ tailWord_2884224) baseStart_2884224 baseEnd_2884224 := by
    simpa [prefixWord, tailWord_2884224, baseEnd_2884224] using wordTrace_append hprefix tailTrace_2884224
  have hstable : (prefixWord ++ tailWord_2884224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884224).length < 2 ^ (prefixWord ++ tailWord_2884224).sum := by decide
  have hdescent : baseEnd_2884224 < baseStart_2884224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884226 : List Nat := [3, 4, 3, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_2884226 : Nat := 118140960795 + 2884226 * 2 ^ 59
def prefixEnd_2884226 : Nat := 4983230072969 + 3 ^ 40 * 2884226 * 2
def baseEnd_2884226 : Nat := 1480994254194737686210693

theorem tailTrace_2884226 : CollatzResearch.WordTrace tailWord_2884226 prefixEnd_2884226 1480994254194737686210693 := by
  unfold tailWord_2884226
  simp only [CollatzResearch.WordTrace]
  refine ⟨26299091112237315857272133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70130909632632842286059021 26299091112237315857272133)
  ·
    refine ⟨4931079583544496723238525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26299091112237315857272133 4931079583544496723238525)
    ·
      refine ⟨1849154843829186271214447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4931079583544496723238525 1849154843829186271214447)
      ·
        refine ⟨2773732265743779406821671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1849154843829186271214447 2773732265743779406821671)
        ·
          refine ⟨4160598398615669110232507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2773732265743779406821671 4160598398615669110232507)
          ·
            refine ⟨6240897597923503665348761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4160598398615669110232507 6240897597923503665348761)
            ·
              refine ⟨4680673198442627749011571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6240897597923503665348761 4680673198442627749011571)
              ·
                refine ⟨7021009797663941623517357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4680673198442627749011571 7021009797663941623517357)
                ·
                  refine ⟨2632878674123978108819009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7021009797663941623517357 2632878674123978108819009)
                  ·
                    refine ⟨1974659005592983581614257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2632878674123978108819009 1974659005592983581614257)
                    ·
                      refine ⟨1480994254194737686210693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1974659005592983581614257 1480994254194737686210693)
                      ·
                        rfl

theorem cell23_2884226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_2884226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884226 prefixEnd_2884226 := by exact prefixLift 2884226
  have htrace : WordTrace (prefixWord ++ tailWord_2884226) baseStart_2884226 baseEnd_2884226 := by
    simpa [prefixWord, tailWord_2884226, baseEnd_2884226] using wordTrace_append hprefix tailTrace_2884226
  have hstable : (prefixWord ++ tailWord_2884226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884226).length < 2 ^ (prefixWord ++ tailWord_2884226).sum := by decide
  have hdescent : baseEnd_2884226 < baseStart_2884226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884242 : List Nat := [3, 2, 3, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_2884242 : Nat := 118140960795 + 2884242 * 2 ^ 59
def prefixEnd_2884242 : Nat := 4983230072969 + 3 ^ 40 * 2884242 * 2
def baseEnd_2884242 : Nat := 1481002469885209623610619

theorem tailTrace_2884242 : CollatzResearch.WordTrace tailWord_2884242 prefixEnd_2884242 1481002469885209623610619 := by
  unfold tailWord_2884242
  simp only [CollatzResearch.WordTrace]
  refine ⟨26299237004222824540417745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70131298677927532107780653 26299237004222824540417745)
  ·
    refine ⟨19724427753167118405313309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26299237004222824540417745 19724427753167118405313309)
    ·
      refine ⟨7396660407437669401992491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19724427753167118405313309 7396660407437669401992491)
      ·
        refine ⟨11094990611156504102988737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7396660407437669401992491 11094990611156504102988737)
        ·
          refine ⟨8321242958367378077241553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11094990611156504102988737 8321242958367378077241553)
          ·
            refine ⟨6240932218775533557931165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8321242958367378077241553 6240932218775533557931165)
            ·
              refine ⟨2340349582040825084224187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6240932218775533557931165 2340349582040825084224187)
              ·
                refine ⟨3510524373061237626336281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2340349582040825084224187 3510524373061237626336281)
                ·
                  refine ⟨2632893279795928219752211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3510524373061237626336281 2632893279795928219752211)
                  ·
                    refine ⟨3949339919693892329628317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2632893279795928219752211 3949339919693892329628317)
                    ·
                      refine ⟨1481002469885209623610619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3949339919693892329628317 1481002469885209623610619)
                      ·
                        rfl

theorem cell23_2884242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_2884242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884242 prefixEnd_2884242 := by exact prefixLift 2884242
  have htrace : WordTrace (prefixWord ++ tailWord_2884242) baseStart_2884242 baseEnd_2884242 := by
    simpa [prefixWord, tailWord_2884242, baseEnd_2884242] using wordTrace_append hprefix tailTrace_2884242
  have hstable : (prefixWord ++ tailWord_2884242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884242).length < 2 ^ (prefixWord ++ tailWord_2884242).sum := by decide
  have hdescent : baseEnd_2884242 < baseStart_2884242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884338 : List Nat := [3, 2, 1, 3, 1, 2, 2, 2, 2, 1, 4]
def baseStart_2884338 : Nat := 118140960795 + 2884338 * 2 ^ 59
def prefixEnd_2884338 : Nat := 4983230072969 + 3 ^ 40 * 2884338 * 2
def baseEnd_2884338 : Nat := 1481051764028041248010177

theorem tailTrace_2884338 : CollatzResearch.WordTrace tailWord_2884338 prefixEnd_2884338 1481051764028041248010177 := by
  unfold tailWord_2884338
  simp only [CollatzResearch.WordTrace]
  refine ⟨26300112356135876639291417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70133632949695671038110445 26300112356135876639291417)
  ·
    refine ⟨19725084267101907479468563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26300112356135876639291417 19725084267101907479468563)
    ·
      refine ⟨29587626400652861219202845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19725084267101907479468563 29587626400652861219202845)
      ·
        refine ⟨11095359900244822957201067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29587626400652861219202845 11095359900244822957201067)
        ·
          refine ⟨16643039850367234435801601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11095359900244822957201067 16643039850367234435801601)
          ·
            refine ⟨12482279887775425826851201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16643039850367234435801601 12482279887775425826851201)
            ·
              refine ⟨9361709915831569370138401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12482279887775425826851201 9361709915831569370138401)
              ·
                refine ⟨7021282436873677027603801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9361709915831569370138401 7021282436873677027603801)
                ·
                  refine ⟨5265961827655257770702851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7021282436873677027603801 5265961827655257770702851)
                  ·
                    refine ⟨7898942741482886656054277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5265961827655257770702851 7898942741482886656054277)
                    ·
                      refine ⟨1481051764028041248010177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7898942741482886656054277 1481051764028041248010177)
                      ·
                        rfl

theorem cell23_2884338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_2884338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884338 prefixEnd_2884338 := by exact prefixLift 2884338
  have htrace : WordTrace (prefixWord ++ tailWord_2884338) baseStart_2884338 baseEnd_2884338 := by
    simpa [prefixWord, tailWord_2884338, baseEnd_2884338] using wordTrace_append hprefix tailTrace_2884338
  have hstable : (prefixWord ++ tailWord_2884338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884338).length < 2 ^ (prefixWord ++ tailWord_2884338).sum := by decide
  have hdescent : baseEnd_2884338 < baseStart_2884338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884361 : List Nat := [1, 2, 1, 1, 3, 2, 4, 3, 6]
def baseStart_2884361 : Nat := 118140960795 + 2884361 * 2 ^ 59
def prefixEnd_2884361 : Nat := 4983230072969 + 3 ^ 40 * 2884361 * 2
def baseEnd_2884361 : Nat := 164562619342566073113619

theorem tailTrace_2884361 : CollatzResearch.WordTrace tailWord_2884361 prefixEnd_2884361 164562619342566073113619 := by
  unfold tailWord_2884361
  simp only [CollatzResearch.WordTrace]
  refine ⟨105201288303460181485252937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70134192202306787656835291 105201288303460181485252937)
  ·
    refine ⟨78900966227595136113939703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105201288303460181485252937 78900966227595136113939703)
    ·
      refine ⟨118351449341392704170909555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78900966227595136113939703 118351449341392704170909555)
      ·
        refine ⟨177527174012089056256364333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118351449341392704170909555 177527174012089056256364333)
        ·
          refine ⟨66572690254533396096136625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177527174012089056256364333 66572690254533396096136625)
          ·
            refine ⟨49929517690900047072102469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66572690254533396096136625 49929517690900047072102469)
            ·
              refine ⟨9361784567043758826019213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49929517690900047072102469 9361784567043758826019213)
              ·
                refine ⟨3510669212641409559757205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9361784567043758826019213 3510669212641409559757205)
                ·
                  refine ⟨164562619342566073113619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3510669212641409559757205 164562619342566073113619)
                  ·
                    rfl

theorem cell23_2884361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 6].length) (baseStart_2884361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884361 prefixEnd_2884361 := by exact prefixLift 2884361
  have htrace : WordTrace (prefixWord ++ tailWord_2884361) baseStart_2884361 baseEnd_2884361 := by
    simpa [prefixWord, tailWord_2884361, baseEnd_2884361] using wordTrace_append hprefix tailTrace_2884361
  have hstable : (prefixWord ++ tailWord_2884361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884361).length < 2 ^ (prefixWord ++ tailWord_2884361).sum := by decide
  have hdescent : baseEnd_2884361 < baseStart_2884361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884398 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_2884398 : Nat := 118140960795 + 2884398 * 2 ^ 59
def prefixEnd_2884398 : Nat := 4983230072969 + 3 ^ 40 * 2884398 * 2
def baseEnd_2884398 : Nat := 1481082572867311013259901

theorem tailTrace_2884398 : CollatzResearch.WordTrace tailWord_2884398 prefixEnd_2884398 1481082572867311013259901 := by
  unfold tailWord_2884398
  simp only [CollatzResearch.WordTrace]
  refine ⟨13150329725540767100543731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70135091869550757869566565 13150329725540767100543731)
  ·
    refine ⟨19725494588311150650815597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13150329725540767100543731 19725494588311150650815597)
    ·
      refine ⟨7397060470616681494055849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19725494588311150650815597 7397060470616681494055849)
      ·
        refine ⟨5547795352962511120541887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7397060470616681494055849 5547795352962511120541887)
        ·
          refine ⟨8321693029443766680812831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5547795352962511120541887 8321693029443766680812831)
          ·
            refine ⟨12482539544165650021219247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8321693029443766680812831 12482539544165650021219247)
            ·
              refine ⟨18723809316248475031828871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12482539544165650021219247 18723809316248475031828871)
              ·
                refine ⟨28085713974372712547743307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18723809316248475031828871 28085713974372712547743307)
                ·
                  refine ⟨42128570961559068821614961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28085713974372712547743307 42128570961559068821614961)
                  ·
                    refine ⟨31596428221169301616211221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42128570961559068821614961 31596428221169301616211221)
                    ·
                      refine ⟨1481082572867311013259901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31596428221169301616211221 1481082572867311013259901)
                      ·
                        rfl

theorem cell23_2884398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_2884398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884398 prefixEnd_2884398 := by exact prefixLift 2884398
  have htrace : WordTrace (prefixWord ++ tailWord_2884398) baseStart_2884398 baseEnd_2884398 := by
    simpa [prefixWord, tailWord_2884398, baseEnd_2884398] using wordTrace_append hprefix tailTrace_2884398
  have hstable : (prefixWord ++ tailWord_2884398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884398).length < 2 ^ (prefixWord ++ tailWord_2884398).sum := by decide
  have hdescent : baseEnd_2884398 < baseStart_2884398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884405 : List Nat := [1, 3, 3, 1, 3, 1, 1, 3, 3, 1, 3]
def baseStart_2884405 : Nat := 118140960795 + 2884405 * 2 ^ 59
def prefixEnd_2884405 : Nat := 4983230072969 + 3 ^ 40 * 2884405 * 2
def baseEnd_2884405 : Nat := 1481086167231892485872369

theorem tailTrace_2884405 : CollatzResearch.WordTrace tailWord_2884405 prefixEnd_2884405 1481086167231892485872369 := by
  unfold tailWord_2884405
  simp only [CollatzResearch.WordTrace]
  refine ⟨105202893115300776999854669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70135262076867184666569779 105202893115300776999854669)
  ·
    refine ⟨39451084918237791374945501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105202893115300776999854669 39451084918237791374945501)
    ·
      refine ⟨14794156844339171765604563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39451084918237791374945501 14794156844339171765604563)
      ·
        refine ⟨22191235266508757648406845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14794156844339171765604563 22191235266508757648406845)
        ·
          refine ⟨8321713224940784118152567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22191235266508757648406845 8321713224940784118152567)
          ·
            refine ⟨12482569837411176177228851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8321713224940784118152567 12482569837411176177228851)
            ·
              refine ⟨18723854756116764265843277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12482569837411176177228851 18723854756116764265843277)
              ·
                refine ⟨7021445533543786599691229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18723854756116764265843277 7021445533543786599691229)
                ·
                  refine ⟨2633042075078919974884211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7021445533543786599691229 2633042075078919974884211)
                  ·
                    refine ⟨3949563112618379962326317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2633042075078919974884211 3949563112618379962326317)
                    ·
                      refine ⟨1481086167231892485872369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3949563112618379962326317 1481086167231892485872369)
                      ·
                        rfl

theorem cell23_2884405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_2884405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884405 prefixEnd_2884405 := by exact prefixLift 2884405
  have htrace : WordTrace (prefixWord ++ tailWord_2884405) baseStart_2884405 baseEnd_2884405 := by
    simpa [prefixWord, tailWord_2884405, baseEnd_2884405] using wordTrace_append hprefix tailTrace_2884405
  have hstable : (prefixWord ++ tailWord_2884405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884405).length < 2 ^ (prefixWord ++ tailWord_2884405).sum := by decide
  have hdescent : baseEnd_2884405 < baseStart_2884405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884421 : List Nat := [1, 3, 1, 1, 1, 2, 2, 5, 1, 6]
def baseStart_2884421 : Nat := 118140960795 + 2884421 * 2 ^ 59
def prefixEnd_2884421 : Nat := 4983230072969 + 3 ^ 40 * 2884421 * 2
def baseEnd_2884421 : Nat := 493698127640788141090765

theorem tailTrace_2884421 : CollatzResearch.WordTrace tailWord_2884421 prefixEnd_2884421 493698127640788141090765 := by
  unfold tailWord_2884421
  simp only [CollatzResearch.WordTrace]
  refine ⟨105203476683242811732437117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70135651122161874488291411 105203476683242811732437117)
  ·
    refine ⟨39451303756216054399663919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105203476683242811732437117 39451303756216054399663919)
    ·
      refine ⟨59176955634324081599495879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39451303756216054399663919 59176955634324081599495879)
      ·
        refine ⟨88765433451486122399243819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59176955634324081599495879 88765433451486122399243819)
        ·
          refine ⟨133148150177229183598865729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88765433451486122399243819 133148150177229183598865729)
          ·
            refine ⟨99861112632921887699149297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133148150177229183598865729 99861112632921887699149297)
            ·
              refine ⟨74895834474691415774361973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99861112632921887699149297 74895834474691415774361973)
              ·
                refine ⟨7021484482002320228846435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74895834474691415774361973 7021484482002320228846435)
                ·
                  refine ⟨10532226723003480343269653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7021484482002320228846435 10532226723003480343269653)
                  ·
                    refine ⟨493698127640788141090765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10532226723003480343269653 493698127640788141090765)
                    ·
                      rfl

theorem cell23_2884421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_2884421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884421 prefixEnd_2884421 := by exact prefixLift 2884421
  have htrace : WordTrace (prefixWord ++ tailWord_2884421) baseStart_2884421 baseEnd_2884421 := by
    simpa [prefixWord, tailWord_2884421, baseEnd_2884421] using wordTrace_append hprefix tailTrace_2884421
  have hstable : (prefixWord ++ tailWord_2884421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884421).length < 2 ^ (prefixWord ++ tailWord_2884421).sum := by decide
  have hdescent : baseEnd_2884421 < baseStart_2884421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884431 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 3]
def baseStart_2884431 : Nat := 118140960795 + 2884431 * 2 ^ 59
def prefixEnd_2884431 : Nat := 4983230072969 + 3 ^ 40 * 2884431 * 2
def baseEnd_2884431 : Nat := 1481099517728909384147249

theorem tailTrace_2884431 : CollatzResearch.WordTrace tailWord_2884431 prefixEnd_2884431 1481099517728909384147249 := by
  unfold tailWord_2884431
  simp only [CollatzResearch.WordTrace]
  refine ⟨105203841413206583440301147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70135894275471055626867431 105203841413206583440301147)
  ·
    refine ⟨157805762119809875160451721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105203841413206583440301147 157805762119809875160451721)
    ·
      refine ⟨118354321589857406370338791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157805762119809875160451721 118354321589857406370338791)
      ·
        refine ⟨177531482384786109555508187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118354321589857406370338791 177531482384786109555508187)
        ·
          refine ⟨266297223577179164333262281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177531482384786109555508187 266297223577179164333262281)
          ·
            refine ⟨199722917682884373249946711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266297223577179164333262281 199722917682884373249946711)
            ·
              refine ⟨299584376524326559874920067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199722917682884373249946711 299584376524326559874920067)
              ·
                refine ⟨449376564786489839812380101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299584376524326559874920067 449376564786489839812380101)
                ·
                  refine ⟨84258105897466844964821269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 449376564786489839812380101 84258105897466844964821269)
                  ·
                    refine ⟨3949598713943758357725997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84258105897466844964821269 3949598713943758357725997)
                    ·
                      refine ⟨1481099517728909384147249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3949598713943758357725997 1481099517728909384147249)
                      ·
                        rfl

theorem cell23_2884431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 3].length) (baseStart_2884431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884431 prefixEnd_2884431 := by exact prefixLift 2884431
  have htrace : WordTrace (prefixWord ++ tailWord_2884431) baseStart_2884431 baseEnd_2884431 := by
    simpa [prefixWord, tailWord_2884431, baseEnd_2884431] using wordTrace_append hprefix tailTrace_2884431
  have hstable : (prefixWord ++ tailWord_2884431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884431).length < 2 ^ (prefixWord ++ tailWord_2884431).sum := by decide
  have hdescent : baseEnd_2884431 < baseStart_2884431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884439 : List Nat := [1, 1, 3, 2, 4, 3, 1, 3, 1, 1, 3]
def baseStart_2884439 : Nat := 118140960795 + 2884439 * 2 ^ 59
def prefixEnd_2884439 : Nat := 4983230072969 + 3 ^ 40 * 2884439 * 2
def baseEnd_2884439 : Nat := 1481103625574145352847213

theorem tailTrace_2884439 : CollatzResearch.WordTrace tailWord_2884439 prefixEnd_2884439 1481103625574145352847213 := by
  unfold tailWord_2884439
  simp only [CollatzResearch.WordTrace]
  refine ⟨105204133197177600806592371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70136088798118400537728247 105204133197177600806592371)
  ·
    refine ⟨157806199795766401209888557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105204133197177600806592371 157806199795766401209888557)
    ·
      refine ⟨59177324923412400453708209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157806199795766401209888557 59177324923412400453708209)
      ·
        refine ⟨44382993692559300340281157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59177324923412400453708209 44382993692559300340281157)
        ·
          refine ⟨8321811317354868813802717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44382993692559300340281157 8321811317354868813802717)
          ·
            refine ⟨3120679244008075805176019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8321811317354868813802717 3120679244008075805176019)
            ·
              refine ⟨4681018866012113707764029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3120679244008075805176019 4681018866012113707764029)
              ·
                refine ⟨1755382074754542640411511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4681018866012113707764029 1755382074754542640411511)
                ·
                  refine ⟨2633073112131813960617267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1755382074754542640411511 2633073112131813960617267)
                  ·
                    refine ⟨3949609668197720940925901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2633073112131813960617267 3949609668197720940925901)
                    ·
                      refine ⟨1481103625574145352847213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3949609668197720940925901 1481103625574145352847213)
                      ·
                        rfl

theorem cell23_2884439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 1, 1, 3].length) (baseStart_2884439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884439 prefixEnd_2884439 := by exact prefixLift 2884439
  have htrace : WordTrace (prefixWord ++ tailWord_2884439) baseStart_2884439 baseEnd_2884439 := by
    simpa [prefixWord, tailWord_2884439, baseEnd_2884439] using wordTrace_append hprefix tailTrace_2884439
  have hstable : (prefixWord ++ tailWord_2884439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884439).length < 2 ^ (prefixWord ++ tailWord_2884439).sum := by decide
  have hdescent : baseEnd_2884439 < baseStart_2884439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884448 : List Nat := [2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 5]
def baseStart_2884448 : Nat := 118140960795 + 2884448 * 2 ^ 59
def prefixEnd_2884448 : Nat := 4983230072969 + 3 ^ 40 * 2884448 * 2
def baseEnd_2884448 : Nat := 1481108246900035817634671

theorem tailTrace_2884448 : CollatzResearch.WordTrace tailWord_2884448 prefixEnd_2884448 1481108246900035817634671 := by
  unfold tailWord_2884448
  simp only [CollatzResearch.WordTrace]
  refine ⟨52602230727072497671834999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70136307636096663562446665 52602230727072497671834999)
  ·
    refine ⟨78903346090608746507752499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52602230727072497671834999 78903346090608746507752499)
    ·
      refine ⟨118355019135913119761628749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78903346090608746507752499 118355019135913119761628749)
      ·
        refine ⟨44383132175967419910610781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118355019135913119761628749 44383132175967419910610781)
        ·
          refine ⟨16643674565987782466479043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44383132175967419910610781 16643674565987782466479043)
          ·
            refine ⟨24965511848981673699718565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16643674565987782466479043 24965511848981673699718565)
            ·
              refine ⟨4681033471684063818697231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24965511848981673699718565 4681033471684063818697231)
              ·
                refine ⟨7021550207526095728045847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4681033471684063818697231 7021550207526095728045847)
                ·
                  refine ⟨10532325311289143592068771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7021550207526095728045847 10532325311289143592068771)
                  ·
                    refine ⟨15798487966933715388103157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10532325311289143592068771 15798487966933715388103157)
                    ·
                      refine ⟨1481108246900035817634671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15798487966933715388103157 1481108246900035817634671)
                      ·
                        rfl

theorem cell23_2884448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_2884448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884448 prefixEnd_2884448 := by exact prefixLift 2884448
  have htrace : WordTrace (prefixWord ++ tailWord_2884448) baseStart_2884448 baseEnd_2884448 := by
    simpa [prefixWord, tailWord_2884448, baseEnd_2884448] using wordTrace_append hprefix tailTrace_2884448
  have hstable : (prefixWord ++ tailWord_2884448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884448).length < 2 ^ (prefixWord ++ tailWord_2884448).sum := by decide
  have hdescent : baseEnd_2884448 < baseStart_2884448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884451 : List Nat := [1, 1, 1, 5, 3, 1, 11]
def baseStart_2884451 : Nat := 118140960795 + 2884451 * 2 ^ 59
def prefixEnd_2884451 : Nat := 4983230072969 + 3 ^ 40 * 2884451 * 2
def baseEnd_2884451 : Nat := 18285306016567892665397

theorem tailTrace_2884451 : CollatzResearch.WordTrace tailWord_2884451 prefixEnd_2884451 18285306016567892665397 := by
  unfold tailWord_2884451
  simp only [CollatzResearch.WordTrace]
  refine ⟨105204570873134126856029207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70136380582089417904019471 105204570873134126856029207)
  ·
    refine ⟨157806856309701190284043811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105204570873134126856029207 157806856309701190284043811)
    ·
      refine ⟨236710284464551785426065717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157806856309701190284043811 236710284464551785426065717)
      ·
        refine ⟨22191589168551729883693661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 236710284464551785426065717 22191589168551729883693661)
        ·
          refine ⟨8321845938206898706385123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22191589168551729883693661 8321845938206898706385123)
          ·
            refine ⟨12482768907310348059577685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8321845938206898706385123 12482768907310348059577685)
            ·
              refine ⟨18285306016567892665397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12482768907310348059577685 18285306016567892665397)
              ·
                rfl

theorem cell23_2884451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 11].length) (baseStart_2884451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884451 prefixEnd_2884451 := by exact prefixLift 2884451
  have htrace : WordTrace (prefixWord ++ tailWord_2884451) baseStart_2884451 baseEnd_2884451 := by
    simpa [prefixWord, tailWord_2884451, baseEnd_2884451] using wordTrace_append hprefix tailTrace_2884451
  have hstable : (prefixWord ++ tailWord_2884451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884451).length < 2 ^ (prefixWord ++ tailWord_2884451).sum := by decide
  have hdescent : baseEnd_2884451 < baseStart_2884451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884491 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 5]
def baseStart_2884491 : Nat := 118140960795 + 2884491 * 2 ^ 59
def prefixEnd_2884491 : Nat := 4983230072969 + 3 ^ 40 * 2884491 * 2
def baseEnd_2884491 : Nat := 1481130326568179149396973

theorem tailTrace_2884491 : CollatzResearch.WordTrace tailWord_2884491 prefixEnd_2884491 1481130326568179149396973 := by
  unfold tailWord_2884491
  simp only [CollatzResearch.WordTrace]
  refine ⟨105206029792989213687485327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70137353195326142458323551 105206029792989213687485327)
  ·
    refine ⟨157809044689483820531227991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105206029792989213687485327 157809044689483820531227991)
    ·
      refine ⟨236713567034225730796841987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157809044689483820531227991 236713567034225730796841987)
      ·
        refine ⟨355070350551338596195262981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236713567034225730796841987 355070350551338596195262981)
        ·
          refine ⟨66575690728375986786611809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 355070350551338596195262981 66575690728375986786611809)
          ·
            refine ⟨49931768046281990089958857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66575690728375986786611809 49931768046281990089958857)
            ·
              refine ⟨37448826034711492567469143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49931768046281990089958857 37448826034711492567469143)
              ·
                refine ⟨56173239052067238851203715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37448826034711492567469143 56173239052067238851203715)
                ·
                  refine ⟨84259858578100858276805573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56173239052067238851203715 84259858578100858276805573)
                  ·
                    refine ⟨15798723483393910926901045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84259858578100858276805573 15798723483393910926901045)
                    ·
                      refine ⟨1481130326568179149396973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15798723483393910926901045 1481130326568179149396973)
                      ·
                        rfl

theorem cell23_2884491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 5].length) (baseStart_2884491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884491 prefixEnd_2884491 := by exact prefixLift 2884491
  have htrace : WordTrace (prefixWord ++ tailWord_2884491) baseStart_2884491 baseEnd_2884491 := by
    simpa [prefixWord, tailWord_2884491, baseEnd_2884491] using wordTrace_append hprefix tailTrace_2884491
  have hstable : (prefixWord ++ tailWord_2884491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884491).length < 2 ^ (prefixWord ++ tailWord_2884491).sum := by decide
  have hdescent : baseEnd_2884491 < baseStart_2884491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884513 : List Nat := [1, 2, 3, 4, 1, 3, 2, 2, 1, 2, 2]
def baseStart_2884513 : Nat := 118140960795 + 2884513 * 2 ^ 59
def prefixEnd_2884513 : Nat := 4983230072969 + 3 ^ 40 * 2884513 * 2
def baseEnd_2884513 : Nat := 1481141623142578063321873

theorem tailTrace_2884513 : CollatzResearch.WordTrace tailWord_2884513 prefixEnd_2884513 1481141623142578063321873 := by
  unfold tailWord_2884513
  simp only [CollatzResearch.WordTrace]
  refine ⟨105206832198909511444786193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70137888132606340963190795 105206832198909511444786193)
  ·
    refine ⟨78905124149182133583589645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105206832198909511444786193 78905124149182133583589645)
    ·
      refine ⟨29589421555943300093846117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78905124149182133583589645 29589421555943300093846117)
      ·
        refine ⟨5548016541739368767596147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29589421555943300093846117 5548016541739368767596147)
        ·
          refine ⟨8322024812609053151394221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5548016541739368767596147 8322024812609053151394221)
          ·
            refine ⟨3120759304728394931772833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8322024812609053151394221 3120759304728394931772833)
            ·
              refine ⟨2340569478546296198829625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3120759304728394931772833 2340569478546296198829625)
              ·
                refine ⟨1755427108909722149122219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2340569478546296198829625 1755427108909722149122219)
                ·
                  refine ⟨2633140663364583223683329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1755427108909722149122219 2633140663364583223683329)
                  ·
                    refine ⟨1974855497523437417762497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2633140663364583223683329 1974855497523437417762497)
                    ·
                      refine ⟨1481141623142578063321873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1974855497523437417762497 1481141623142578063321873)
                      ·
                        rfl

theorem cell23_2884513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_2884513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884513 prefixEnd_2884513 := by exact prefixLift 2884513
  have htrace : WordTrace (prefixWord ++ tailWord_2884513) baseStart_2884513 baseEnd_2884513 := by
    simpa [prefixWord, tailWord_2884513, baseEnd_2884513] using wordTrace_append hprefix tailTrace_2884513
  have hstable : (prefixWord ++ tailWord_2884513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884513).length < 2 ^ (prefixWord ++ tailWord_2884513).sum := by decide
  have hdescent : baseEnd_2884513 < baseStart_2884513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884535 : List Nat := [1, 1, 3, 1, 3, 1, 3, 3, 1, 4, 2]
def baseStart_2884535 : Nat := 118140960795 + 2884535 * 2 ^ 59
def prefixEnd_2884535 : Nat := 4983230072969 + 3 ^ 40 * 2884535 * 2
def baseEnd_2884535 : Nat := 1481152919716976977246771

theorem tailTrace_2884535 : CollatzResearch.WordTrace tailWord_2884535 prefixEnd_2884535 1481152919716976977246771 := by
  unfold tailWord_2884535
  simp only [CollatzResearch.WordTrace]
  refine ⟨105207634604829809202087059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70138423069886539468058039 105207634604829809202087059)
  ·
    refine ⟨157811451907244713803130589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105207634604829809202087059 157811451907244713803130589)
    ·
      refine ⟨59179294465216767676173971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157811451907244713803130589 59179294465216767676173971)
      ·
        refine ⟨88768941697825151514260957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59179294465216767676173971 88768941697825151514260957)
        ·
          refine ⟨33288353136684431817847859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88768941697825151514260957 33288353136684431817847859)
          ·
            refine ⟨49932529705026647726771789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33288353136684431817847859 49932529705026647726771789)
            ·
              refine ⟨18724698639384992897539421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49932529705026647726771789 18724698639384992897539421)
              ·
                refine ⟨7021761989769372336577283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18724698639384992897539421 7021761989769372336577283)
                ·
                  refine ⟨10532642984654058504865925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7021761989769372336577283 10532642984654058504865925)
                  ·
                    refine ⟨1974870559622635969662361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10532642984654058504865925 1974870559622635969662361)
                    ·
                      refine ⟨1481152919716976977246771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1974870559622635969662361 1481152919716976977246771)
                      ·
                        rfl

theorem cell23_2884535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 4, 2].length) (baseStart_2884535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884535 prefixEnd_2884535 := by exact prefixLift 2884535
  have htrace : WordTrace (prefixWord ++ tailWord_2884535) baseStart_2884535 baseEnd_2884535 := by
    simpa [prefixWord, tailWord_2884535, baseEnd_2884535] using wordTrace_append hprefix tailTrace_2884535
  have hstable : (prefixWord ++ tailWord_2884535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884535).length < 2 ^ (prefixWord ++ tailWord_2884535).sum := by decide
  have hdescent : baseEnd_2884535 < baseStart_2884535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884538 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3]
def baseStart_2884538 : Nat := 118140960795 + 2884538 * 2 ^ 59
def prefixEnd_2884538 : Nat := 4983230072969 + 3 ^ 40 * 2884538 * 2
def baseEnd_2884538 : Nat := 1481154460158940465509257

theorem tailTrace_2884538 : CollatzResearch.WordTrace tailWord_2884538 prefixEnd_2884538 1481154460158940465509257 := by
  unfold tailWord_2884538
  simp only [CollatzResearch.WordTrace]
  refine ⟨26301936005954735178611567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70138496015879293809630845 26301936005954735178611567)
  ·
    refine ⟨39452904008932102767917351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26301936005954735178611567 39452904008932102767917351)
    ·
      refine ⟨59179356013398154151876027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39452904008932102767917351 59179356013398154151876027)
      ·
        refine ⟨88769034020097231227814041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59179356013398154151876027 88769034020097231227814041)
        ·
          refine ⟨66576775515072923420860531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88769034020097231227814041 66576775515072923420860531)
          ·
            refine ⟨99865163272609385131290797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66576775515072923420860531 99865163272609385131290797)
            ·
              refine ⟨37449436227228519424234049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99865163272609385131290797 37449436227228519424234049)
              ·
                refine ⟨28087077170421389568175537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37449436227228519424234049 28087077170421389568175537)
                ·
                  refine ⟨21065307877816042176131653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28087077170421389568175537 21065307877816042176131653)
                  ·
                    refine ⟨3949745227090507908024685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21065307877816042176131653 3949745227090507908024685)
                    ·
                      refine ⟨1481154460158940465509257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3949745227090507908024685 1481154460158940465509257)
                      ·
                        rfl

theorem cell23_2884538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_2884538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884538 prefixEnd_2884538 := by exact prefixLift 2884538
  have htrace : WordTrace (prefixWord ++ tailWord_2884538) baseStart_2884538 baseEnd_2884538 := by
    simpa [prefixWord, tailWord_2884538, baseEnd_2884538] using wordTrace_append hprefix tailTrace_2884538
  have hstable : (prefixWord ++ tailWord_2884538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884538).length < 2 ^ (prefixWord ++ tailWord_2884538).sum := by decide
  have hdescent : baseEnd_2884538 < baseStart_2884538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884569 : List Nat := [1, 2, 1, 2, 5, 1, 3, 2, 2, 2, 2]
def baseStart_2884569 : Nat := 118140960795 + 2884569 * 2 ^ 59
def prefixEnd_2884569 : Nat := 4983230072969 + 3 ^ 40 * 2884569 * 2
def baseEnd_2884569 : Nat := 1481170378059229844221615

theorem tailTrace_2884569 : CollatzResearch.WordTrace tailWord_2884569 prefixEnd_2884569 1481170378059229844221615 := by
  unfold tailWord_2884569
  simp only [CollatzResearch.WordTrace]
  refine ⟨105208874686706633008824761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70139249791137755339216507 105208874686706633008824761)
  ·
    refine ⟨78906656015029974756618571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105208874686706633008824761 78906656015029974756618571)
    ·
      refine ⟨118359984022544962134927857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78906656015029974756618571 118359984022544962134927857)
      ·
        refine ⟨88769988016908721601195893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118359984022544962134927857 88769988016908721601195893)
        ·
          refine ⟨8322186376585192650112115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88769988016908721601195893 8322186376585192650112115)
          ·
            refine ⟨12483279564877788975168173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8322186376585192650112115 12483279564877788975168173)
            ·
              refine ⟨4681229836829170865688065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12483279564877788975168173 4681229836829170865688065)
              ·
                refine ⟨3510922377621878149266049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4681229836829170865688065 3510922377621878149266049)
                ·
                  refine ⟨2633191783216408611949537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3510922377621878149266049 2633191783216408611949537)
                  ·
                    refine ⟨1974893837412306458962153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2633191783216408611949537 1974893837412306458962153)
                    ·
                      refine ⟨1481170378059229844221615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1974893837412306458962153 1481170378059229844221615)
                      ·
                        rfl

theorem cell23_2884569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 2, 2].length) (baseStart_2884569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884569 prefixEnd_2884569 := by exact prefixLift 2884569
  have htrace : WordTrace (prefixWord ++ tailWord_2884569) baseStart_2884569 baseEnd_2884569 := by
    simpa [prefixWord, tailWord_2884569, baseEnd_2884569] using wordTrace_append hprefix tailTrace_2884569
  have hstable : (prefixWord ++ tailWord_2884569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884569).length < 2 ^ (prefixWord ++ tailWord_2884569).sum := by decide
  have hdescent : baseEnd_2884569 < baseStart_2884569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884575 : List Nat := [1, 1, 2, 3, 5, 1, 2, 1, 7]
def baseStart_2884575 : Nat := 118140960795 + 2884575 * 2 ^ 59
def prefixEnd_2884575 : Nat := 4983230072969 + 3 ^ 40 * 2884575 * 2
def baseEnd_2884575 : Nat := 164574828771461868971843

theorem tailTrace_2884575 : CollatzResearch.WordTrace tailWord_2884575 prefixEnd_2884575 164574828771461868971843 := by
  unfold tailWord_2884575
  simp only [CollatzResearch.WordTrace]
  refine ⟨105209093524684896033543179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70139395683123264022362119 105209093524684896033543179)
  ·
    refine ⟨157813640287027344050314769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105209093524684896033543179 157813640287027344050314769)
    ·
      refine ⟨118360230215270508037736077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157813640287027344050314769 118360230215270508037736077)
      ·
        refine ⟨44385086330726440514151029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118360230215270508037736077 44385086330726440514151029)
        ·
          refine ⟨4161101843505603798201659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44385086330726440514151029 4161101843505603798201659)
          ·
            refine ⟨6241652765258405697302489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4161101843505603798201659 6241652765258405697302489)
            ·
              refine ⟨4681239573943804272976867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6241652765258405697302489 4681239573943804272976867)
              ·
                refine ⟨7021859360915706409465301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4681239573943804272976867 7021859360915706409465301)
                ·
                  refine ⟨164574828771461868971843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7021859360915706409465301 164574828771461868971843)
                  ·
                    rfl

theorem cell23_2884575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 7].length) (baseStart_2884575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884575 prefixEnd_2884575 := by exact prefixLift 2884575
  have htrace : WordTrace (prefixWord ++ tailWord_2884575) baseStart_2884575 baseEnd_2884575 := by
    simpa [prefixWord, tailWord_2884575, baseEnd_2884575] using wordTrace_append hprefix tailTrace_2884575
  have hstable : (prefixWord ++ tailWord_2884575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884575).length < 2 ^ (prefixWord ++ tailWord_2884575).sum := by decide
  have hdescent : baseEnd_2884575 < baseStart_2884575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884586 : List Nat := [3, 1, 3, 1, 2, 3, 3, 1, 2, 2, 2]
def baseStart_2884586 : Nat := 118140960795 + 2884586 * 2 ^ 59
def prefixEnd_2884586 : Nat := 4983230072969 + 3 ^ 40 * 2884586 * 2
def baseEnd_2884586 : Nat := 1481179107230356277709037

theorem tailTrace_2884586 : CollatzResearch.WordTrace tailWord_2884586 prefixEnd_2884586 1481179107230356277709037 := by
  unfold tailWord_2884586
  simp only [CollatzResearch.WordTrace]
  refine ⟨26302373681911261228048403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70139663151763363274795741 26302373681911261228048403)
  ·
    refine ⟨39453560522866891842072605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26302373681911261228048403 39453560522866891842072605)
    ·
      refine ⟨14795085196075084440777227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39453560522866891842072605 14795085196075084440777227)
      ·
        refine ⟨22192627794112626661165841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14795085196075084440777227 22192627794112626661165841)
        ·
          refine ⟨16644470845584469995874381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22192627794112626661165841 16644470845584469995874381)
          ·
            refine ⟨6241676567094176248452893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16644470845584469995874381 6241676567094176248452893)
            ·
              refine ⟨2340628712660316093169835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6241676567094176248452893 2340628712660316093169835)
              ·
                refine ⟨3510943068990474139754753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2340628712660316093169835 3510943068990474139754753)
                ·
                  refine ⟨2633207301742855604816065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3510943068990474139754753 2633207301742855604816065)
                  ·
                    refine ⟨1974905476307141703612049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2633207301742855604816065 1974905476307141703612049)
                    ·
                      refine ⟨1481179107230356277709037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1974905476307141703612049 1481179107230356277709037)
                      ·
                        rfl

theorem cell23_2884586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_2884586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884586 prefixEnd_2884586 := by exact prefixLift 2884586
  have htrace : WordTrace (prefixWord ++ tailWord_2884586) baseStart_2884586 baseEnd_2884586 := by
    simpa [prefixWord, tailWord_2884586, baseEnd_2884586] using wordTrace_append hprefix tailTrace_2884586
  have hstable : (prefixWord ++ tailWord_2884586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884586).length < 2 ^ (prefixWord ++ tailWord_2884586).sum := by decide
  have hdescent : baseEnd_2884586 < baseStart_2884586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884625 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 4, 4, 2]
def baseStart_2884625 : Nat := 118140960795 + 2884625 * 2 ^ 59
def prefixEnd_2884625 : Nat := 4983230072969 + 3 ^ 40 * 2884625 * 2
def baseEnd_2884625 : Nat := 1481199132975881625121357

theorem tailTrace_2884625 : CollatzResearch.WordTrace tailWord_2884625 prefixEnd_2884625 1481199132975881625121357 := by
  unfold tailWord_2884625
  simp only [CollatzResearch.WordTrace]
  refine ⟨105210917174503754572863329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70140611449669169715242219 105210917174503754572863329)
  ·
    refine ⟨78908187880877815929647497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105210917174503754572863329 78908187880877815929647497)
    ·
      refine ⟨59181140910658361947235623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78908187880877815929647497 59181140910658361947235623)
      ·
        refine ⟨88771711365987542920853435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59181140910658361947235623 88771711365987542920853435)
        ·
          refine ⟨133157567048981314381280153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88771711365987542920853435 133157567048981314381280153)
          ·
            refine ⟨99868175286735985785960115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133157567048981314381280153 99868175286735985785960115)
            ·
              refine ⟨149802262930103978678940173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99868175286735985785960115 149802262930103978678940173)
              ·
                refine ⟨56175848598788992004602565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149802262930103978678940173 56175848598788992004602565)
                ·
                  refine ⟨10532971612272936000862981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56175848598788992004602565 10532971612272936000862981)
                  ·
                    refine ⟨1974932177301175500161809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10532971612272936000862981 1974932177301175500161809)
                    ·
                      refine ⟨1481199132975881625121357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1974932177301175500161809 1481199132975881625121357)
                      ·
                        rfl

theorem cell23_2884625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 4, 2].length) (baseStart_2884625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884625 prefixEnd_2884625 := by exact prefixLift 2884625
  have htrace : WordTrace (prefixWord ++ tailWord_2884625) baseStart_2884625 baseEnd_2884625 := by
    simpa [prefixWord, tailWord_2884625, baseEnd_2884625] using wordTrace_append hprefix tailTrace_2884625
  have hstable : (prefixWord ++ tailWord_2884625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884625).length < 2 ^ (prefixWord ++ tailWord_2884625).sum := by decide
  have hdescent : baseEnd_2884625 < baseStart_2884625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884626 : List Nat := [3, 2, 5, 1, 1, 2, 1, 1, 7]
def baseStart_2884626 : Nat := 118140960795 + 2884626 * 2 ^ 59
def prefixEnd_2884626 : Nat := 4983230072969 + 3 ^ 40 * 2884626 * 2
def baseEnd_2884626 : Nat := 164577738495170680134317

theorem tailTrace_2884626 : CollatzResearch.WordTrace tailWord_2884626 prefixEnd_2884626 164577738495170680134317 := by
  unfold tailWord_2884626
  simp only [CollatzResearch.WordTrace]
  refine ⟨26302738411875032935912433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70140635765000087829099821 26302738411875032935912433)
  ·
    refine ⟨19727053808906274701934325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26302738411875032935912433 19727053808906274701934325)
    ·
      refine ⟨1849411294584963253306343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19727053808906274701934325 1849411294584963253306343)
      ·
        refine ⟨2774116941877444879959515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1849411294584963253306343 2774116941877444879959515)
        ·
          refine ⟨4161175412816167319939273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2774116941877444879959515 4161175412816167319939273)
          ·
            refine ⟨3120881559612125489954455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4161175412816167319939273 3120881559612125489954455)
            ·
              refine ⟨4681322339418188234931683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3120881559612125489954455 4681322339418188234931683)
              ·
                refine ⟨7021983509127282352397525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4681322339418188234931683 7021983509127282352397525)
                ·
                  refine ⟨164577738495170680134317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7021983509127282352397525 164577738495170680134317)
                  ·
                    rfl

theorem cell23_2884626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_2884626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884626 prefixEnd_2884626 := by exact prefixLift 2884626
  have htrace : WordTrace (prefixWord ++ tailWord_2884626) baseStart_2884626 baseEnd_2884626 := by
    simpa [prefixWord, tailWord_2884626, baseEnd_2884626] using wordTrace_append hprefix tailTrace_2884626
  have hstable : (prefixWord ++ tailWord_2884626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884626).length < 2 ^ (prefixWord ++ tailWord_2884626).sum := by decide
  have hdescent : baseEnd_2884626 < baseStart_2884626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884645 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 4, 2, 3]
def baseStart_2884645 : Nat := 118140960795 + 2884645 * 2 ^ 59
def prefixEnd_2884645 : Nat := 4983230072969 + 3 ^ 40 * 2884645 * 2
def baseEnd_2884645 : Nat := 1481209402588971546871265

theorem tailTrace_2884645 : CollatzResearch.WordTrace tailWord_2884645 prefixEnd_2884645 1481209402588971546871265 := by
  unfold tailWord_2884645
  simp only [CollatzResearch.WordTrace]
  refine ⟨105211646634431297988591389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70141097756287531992394259 105211646634431297988591389)
  ·
    refine ⟨39454367487911736745721771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105211646634431297988591389 39454367487911736745721771)
    ·
      refine ⟨59181551231867605118582657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39454367487911736745721771 59181551231867605118582657)
      ·
        refine ⟨44386163423900703838936993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59181551231867605118582657 44386163423900703838936993)
        ·
          refine ⟨33289622567925527879202745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44386163423900703838936993 33289622567925527879202745)
          ·
            refine ⟨24967216925944145909402059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33289622567925527879202745 24967216925944145909402059)
            ·
              refine ⟨37450825388916218864103089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24967216925944145909402059 37450825388916218864103089)
              ·
                refine ⟨28088119041687164148077317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37450825388916218864103089 28088119041687164148077317)
                ·
                  refine ⟨5266522320316343277764497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28088119041687164148077317 5266522320316343277764497)
                  ·
                    refine ⟨3949891740237257458323373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5266522320316343277764497 3949891740237257458323373)
                    ·
                      refine ⟨1481209402588971546871265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3949891740237257458323373 1481209402588971546871265)
                      ·
                        rfl

theorem cell23_2884645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_2884645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884645 prefixEnd_2884645 := by exact prefixLift 2884645
  have htrace : WordTrace (prefixWord ++ tailWord_2884645) baseStart_2884645 baseEnd_2884645 := by
    simpa [prefixWord, tailWord_2884645, baseEnd_2884645] using wordTrace_append hprefix tailTrace_2884645
  have hstable : (prefixWord ++ tailWord_2884645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884645).length < 2 ^ (prefixWord ++ tailWord_2884645).sum := by decide
  have hdescent : baseEnd_2884645 < baseStart_2884645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884688 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 5]
def baseStart_2884688 : Nat := 118140960795 + 2884688 * 2 ^ 59
def prefixEnd_2884688 : Nat := 4983230072969 + 3 ^ 40 * 2884688 * 2
def baseEnd_2884688 : Nat := 1481231482257114878633567

theorem tailTrace_2884688 : CollatzResearch.WordTrace tailWord_2884688 prefixEnd_2884688 1481231482257114878633567 := by
  unfold tailWord_2884688
  simp only [CollatzResearch.WordTrace]
  refine ⟨52606607486637758166203359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70142143315517010888271145 52606607486637758166203359)
  ·
    refine ⟨78909911229956637249305039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52606607486637758166203359 78909911229956637249305039)
    ·
      refine ⟨118364866844934955873957559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78909911229956637249305039 118364866844934955873957559)
      ·
        refine ⟨177547300267402433810936339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118364866844934955873957559 177547300267402433810936339)
        ·
          refine ⟨266320950401103650716404509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177547300267402433810936339 266320950401103650716404509)
          ·
            refine ⟨99870356400413869018651691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266320950401103650716404509 99870356400413869018651691)
            ·
              refine ⟨149805534600620803527977537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99870356400413869018651691 149805534600620803527977537)
              ·
                refine ⟨112354150950465602645983153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149805534600620803527977537 112354150950465602645983153)
                ·
                  refine ⟨84265613212849201984487365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112354150950465602645983153 84265613212849201984487365)
                  ·
                    refine ⟨15799802477409225372091381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84265613212849201984487365 15799802477409225372091381)
                    ·
                      refine ⟨1481231482257114878633567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15799802477409225372091381 1481231482257114878633567)
                      ·
                        rfl

theorem cell23_2884688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_2884688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884688 prefixEnd_2884688 := by exact prefixLift 2884688
  have htrace : WordTrace (prefixWord ++ tailWord_2884688) baseStart_2884688 baseEnd_2884688 := by
    simpa [prefixWord, tailWord_2884688, baseEnd_2884688] using wordTrace_append hprefix tailTrace_2884688
  have hstable : (prefixWord ++ tailWord_2884688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884688).length < 2 ^ (prefixWord ++ tailWord_2884688).sum := by decide
  have hdescent : baseEnd_2884688 < baseStart_2884688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884732 : List Nat := [2, 2, 2, 1, 1, 3, 3, 3, 1, 1, 4]
def baseStart_2884732 : Nat := 118140960795 + 2884732 * 2 ^ 59
def prefixEnd_2884732 : Nat := 4983230072969 + 3 ^ 40 * 2884732 * 2
def baseEnd_2884732 : Nat := 1481254075405912706483365

theorem tailTrace_2884732 : CollatzResearch.WordTrace tailWord_2884732 prefixEnd_2884732 1481254075405912706483365 := by
  unfold tailWord_2884732
  simp only [CollatzResearch.WordTrace]
  refine ⟨52607409892558055923504225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70143213190077407898005633 52607409892558055923504225)
  ·
    refine ⟨39455557419418541942628169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52607409892558055923504225 39455557419418541942628169)
    ·
      refine ⟨29591668064563906456971127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39455557419418541942628169 29591668064563906456971127)
      ·
        refine ⟨44387502096845859685456691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29591668064563906456971127 44387502096845859685456691)
        ·
          refine ⟨66581253145268789528185037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44387502096845859685456691 66581253145268789528185037)
          ·
            refine ⟨24967969929475796073069389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66581253145268789528185037 24967969929475796073069389)
            ·
              refine ⟨9362988723553423527401021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24967969929475796073069389 9362988723553423527401021)
              ·
                refine ⟨3511120771332533822775383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9362988723553423527401021 3511120771332533822775383)
                ·
                  refine ⟨5266681156998800734163075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3511120771332533822775383 5266681156998800734163075)
                  ·
                    refine ⟨7900021735498201101244613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5266681156998800734163075 7900021735498201101244613)
                    ·
                      refine ⟨1481254075405912706483365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7900021735498201101244613 1481254075405912706483365)
                      ·
                        rfl

theorem cell23_2884732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_2884732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884732 prefixEnd_2884732 := by exact prefixLift 2884732
  have htrace : WordTrace (prefixWord ++ tailWord_2884732) baseStart_2884732 baseEnd_2884732 := by
    simpa [prefixWord, tailWord_2884732, baseEnd_2884732] using wordTrace_append hprefix tailTrace_2884732
  have hstable : (prefixWord ++ tailWord_2884732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884732).length < 2 ^ (prefixWord ++ tailWord_2884732).sum := by decide
  have hdescent : baseEnd_2884732 < baseStart_2884732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884762 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6]
def baseStart_2884762 : Nat := 118140960795 + 2884762 * 2 ^ 59
def prefixEnd_2884762 : Nat := 4983230072969 + 3 ^ 40 * 2884762 * 2
def baseEnd_2884762 : Nat := 1481269479825547589108227

theorem tailTrace_2884762 : CollatzResearch.WordTrace tailWord_2884762 prefixEnd_2884762 1481269479825547589108227 := by
  unfold tailWord_2884762
  simp only [CollatzResearch.WordTrace]
  refine ⟨26303978493751856742650135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70143942650004951313733693 26303978493751856742650135)
  ·
    refine ⟨39455967740627785113975203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26303978493751856742650135 39455967740627785113975203)
    ·
      refine ⟨59183951610941677670962805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39455967740627785113975203 59183951610941677670962805)
      ·
        refine ⟨5548495463525782281652763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59183951610941677670962805 5548495463525782281652763)
        ·
          refine ⟨8322743195288673422479145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5548495463525782281652763 8322743195288673422479145)
          ·
            refine ⟨6242057396466505066859359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8322743195288673422479145 6242057396466505066859359)
            ·
              refine ⟨9363086094699757600289039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6242057396466505066859359 9363086094699757600289039)
              ·
                refine ⟨14044629142049636400433559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9363086094699757600289039 14044629142049636400433559)
                ·
                  refine ⟨21066943713074454600650339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14044629142049636400433559 21066943713074454600650339)
                  ·
                    refine ⟨31600415569611681900975509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21066943713074454600650339 31600415569611681900975509)
                    ·
                      refine ⟨1481269479825547589108227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31600415569611681900975509 1481269479825547589108227)
                      ·
                        rfl

theorem cell23_2884762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_2884762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884762 prefixEnd_2884762 := by exact prefixLift 2884762
  have htrace : WordTrace (prefixWord ++ tailWord_2884762) baseStart_2884762 baseEnd_2884762 := by
    simpa [prefixWord, tailWord_2884762, baseEnd_2884762] using wordTrace_append hprefix tailTrace_2884762
  have hstable : (prefixWord ++ tailWord_2884762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884762).length < 2 ^ (prefixWord ++ tailWord_2884762).sum := by decide
  have hdescent : baseEnd_2884762 < baseStart_2884762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884766 : List Nat := [4, 3, 1, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_2884766 : Nat := 118140960795 + 2884766 * 2 ^ 59
def prefixEnd_2884766 : Nat := 4983230072969 + 3 ^ 40 * 2884766 * 2
def baseEnd_2884766 : Nat := 1481271533748165573458209

theorem tailTrace_2884766 : CollatzResearch.WordTrace tailWord_2884766 prefixEnd_2884766 1481271533748165573458209 := by
  unfold tailWord_2884766
  simp only [CollatzResearch.WordTrace]
  refine ⟨13152007483374116956718269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70144039911328623769164101 13152007483374116956718269)
  ·
    refine ⟨4932002806265293858769351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13152007483374116956718269 4932002806265293858769351)
    ·
      refine ⟨7398004209397940788154027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4932002806265293858769351 7398004209397940788154027)
      ·
        refine ⟨11097006314096911182231041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7398004209397940788154027 11097006314096911182231041)
        ·
          refine ⟨8322754735572683386673281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11097006314096911182231041 8322754735572683386673281)
          ·
            refine ⟨6242066051679512540004961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8322754735572683386673281 6242066051679512540004961)
            ·
              refine ⟨4681549538759634405003721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6242066051679512540004961 4681549538759634405003721)
              ·
                refine ⟨3511162154069725803752791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4681549538759634405003721 3511162154069725803752791)
                ·
                  refine ⟨5266743231104588705629187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3511162154069725803752791 5266743231104588705629187)
                  ·
                    refine ⟨7900114846656883058443781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5266743231104588705629187 7900114846656883058443781)
                    ·
                      refine ⟨1481271533748165573458209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7900114846656883058443781 1481271533748165573458209)
                      ·
                        rfl

theorem cell23_2884766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_2884766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884766 prefixEnd_2884766 := by exact prefixLift 2884766
  have htrace : WordTrace (prefixWord ++ tailWord_2884766) baseStart_2884766 baseEnd_2884766 := by
    simpa [prefixWord, tailWord_2884766, baseEnd_2884766] using wordTrace_append hprefix tailTrace_2884766
  have hstable : (prefixWord ++ tailWord_2884766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884766).length < 2 ^ (prefixWord ++ tailWord_2884766).sum := by decide
  have hdescent : baseEnd_2884766 < baseStart_2884766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884769 : List Nat := [1, 2, 3, 3, 1, 1, 4, 2, 1, 2, 3]
def baseStart_2884769 : Nat := 118140960795 + 2884769 * 2 ^ 59
def prefixEnd_2884769 : Nat := 4983230072969 + 3 ^ 40 * 2884769 * 2
def baseEnd_2884769 : Nat := 1481273074190129061720695

theorem tailTrace_2884769 : CollatzResearch.WordTrace tailWord_2884769 prefixEnd_2884769 1481273074190129061720695 := by
  unfold tailWord_2884769
  simp only [CollatzResearch.WordTrace]
  refine ⟨105216169285982067166105361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70144112857321378110736907 105216169285982067166105361)
  ·
    refine ⟨78912126964486550374579021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105216169285982067166105361 78912126964486550374579021)
    ·
      refine ⟨29592047611682456390467133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78912126964486550374579021 29592047611682456390467133)
      ·
        refine ⟨11097017854380921146425175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29592047611682456390467133 11097017854380921146425175)
        ·
          refine ⟨16645526781571381719637763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11097017854380921146425175 16645526781571381719637763)
          ·
            refine ⟨24968290172357072579456645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16645526781571381719637763 24968290172357072579456645)
            ·
              refine ⟨4681554407316951108648121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24968290172357072579456645 4681554407316951108648121)
              ·
                refine ⟨3511165805487713331486091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4681554407316951108648121 3511165805487713331486091)
                ·
                  refine ⟨5266748708231569997229137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3511165805487713331486091 5266748708231569997229137)
                  ·
                    refine ⟨3950061531173677497921853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5266748708231569997229137 3950061531173677497921853)
                    ·
                      refine ⟨1481273074190129061720695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3950061531173677497921853 1481273074190129061720695)
                      ·
                        rfl

theorem cell23_2884769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_2884769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884769 prefixEnd_2884769 := by exact prefixLift 2884769
  have htrace : WordTrace (prefixWord ++ tailWord_2884769) baseStart_2884769 baseEnd_2884769 := by
    simpa [prefixWord, tailWord_2884769, baseEnd_2884769] using wordTrace_append hprefix tailTrace_2884769
  have hstable : (prefixWord ++ tailWord_2884769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884769).length < 2 ^ (prefixWord ++ tailWord_2884769).sum := by decide
  have hdescent : baseEnd_2884769 < baseStart_2884769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884772 : List Nat := [2, 3, 1, 2, 3, 1, 4, 7]
def baseStart_2884772 : Nat := 118140960795 + 2884772 * 2 ^ 59
def prefixEnd_2884772 : Nat := 4983230072969 + 3 ^ 40 * 2884772 * 2
def baseEnd_2884772 : Nat := 54862022764151575925303

theorem tailTrace_2884772 : CollatzResearch.WordTrace tailWord_2884772 prefixEnd_2884772 54862022764151575925303 := by
  unfold tailWord_2884772
  simp only [CollatzResearch.WordTrace]
  refine ⟨52608139352485599339232285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70144185803314132452309713 52608139352485599339232285)
  ·
    refine ⟨19728052257182099752212107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52608139352485599339232285 19728052257182099752212107)
    ·
      refine ⟨29592078385773149628318161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19728052257182099752212107 29592078385773149628318161)
      ·
        refine ⟨22194058789329862221238621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29592078385773149628318161 22194058789329862221238621)
        ·
          refine ⟨8322772045998698332964483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22194058789329862221238621 8322772045998698332964483)
          ·
            refine ⟨12484158068998047499446725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8322772045998698332964483 12484158068998047499446725)
            ·
              refine ⟨2340779637937133906146261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12484158068998047499446725 2340779637937133906146261)
              ·
                refine ⟨54862022764151575925303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2340779637937133906146261 54862022764151575925303)
                ·
                  rfl

theorem cell23_2884772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 7].length) (baseStart_2884772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884772 prefixEnd_2884772 := by exact prefixLift 2884772
  have htrace : WordTrace (prefixWord ++ tailWord_2884772) baseStart_2884772 baseEnd_2884772 := by
    simpa [prefixWord, tailWord_2884772, baseEnd_2884772] using wordTrace_append hprefix tailTrace_2884772
  have hstable : (prefixWord ++ tailWord_2884772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884772).length < 2 ^ (prefixWord ++ tailWord_2884772).sum := by decide
  have hdescent : baseEnd_2884772 < baseStart_2884772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884800 : List Nat := [2, 1, 1, 2, 6, 1, 3, 2, 1, 2, 2]
def baseStart_2884800 : Nat := 118140960795 + 2884800 * 2 ^ 59
def prefixEnd_2884800 : Nat := 4983230072969 + 3 ^ 40 * 2884800 * 2
def baseEnd_2884800 : Nat := 1481288992090418440433053

theorem tailTrace_2884800 : CollatzResearch.WordTrace tailWord_2884800 prefixEnd_2884800 1481288992090418440433053 := by
  unfold tailWord_2884800
  simp only [CollatzResearch.WordTrace]
  refine ⟨52608649974434879730241927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70144866632579839640322569 52608649974434879730241927)
  ·
    refine ⟨78912974961652319595362891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52608649974434879730241927 78912974961652319595362891)
    ·
      refine ⟨118369462442478479393044337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78912974961652319595362891 118369462442478479393044337)
      ·
        refine ⟨88777096831858859544783253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118369462442478479393044337 88777096831858859544783253)
        ·
          refine ⟨4161426413993384041161715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88777096831858859544783253 4161426413993384041161715)
          ·
            refine ⟨6242139620990076061742573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4161426413993384041161715 6242139620990076061742573)
            ·
              refine ⟨2340802357871278523153465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6242139620990076061742573 2340802357871278523153465)
              ·
                refine ⟨1755601768403458892365099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2340802357871278523153465 1755601768403458892365099)
                ·
                  refine ⟨2633402652605188338547649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1755601768403458892365099 2633402652605188338547649)
                  ·
                    refine ⟨1975051989453891253910737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2633402652605188338547649 1975051989453891253910737)
                    ·
                      refine ⟨1481288992090418440433053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1975051989453891253910737 1481288992090418440433053)
                      ·
                        rfl

theorem cell23_2884800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 1, 2, 2].length) (baseStart_2884800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884800 prefixEnd_2884800 := by exact prefixLift 2884800
  have htrace : WordTrace (prefixWord ++ tailWord_2884800) baseStart_2884800 baseEnd_2884800 := by
    simpa [prefixWord, tailWord_2884800, baseEnd_2884800] using wordTrace_append hprefix tailTrace_2884800
  have hstable : (prefixWord ++ tailWord_2884800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884800).length < 2 ^ (prefixWord ++ tailWord_2884800).sum := by decide
  have hdescent : baseEnd_2884800 < baseStart_2884800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884805 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 2, 3, 4]
def baseStart_2884805 : Nat := 118140960795 + 2884805 * 2 ^ 59
def prefixEnd_2884805 : Nat := 4983230072969 + 3 ^ 40 * 2884805 * 2
def baseEnd_2884805 : Nat := 1481291559493690920870529

theorem tailTrace_2884805 : CollatzResearch.WordTrace tailWord_2884805 prefixEnd_2884805 1481291559493690920870529 := by
  unfold tailWord_2884805
  simp only [CollatzResearch.WordTrace]
  refine ⟨105217482313851645314415869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70144988209234430209610579 105217482313851645314415869)
  ·
    refine ⟨39456555867694366992905951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105217482313851645314415869 39456555867694366992905951)
    ·
      refine ⟨59184833801541550489358927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39456555867694366992905951 59184833801541550489358927)
      ·
        refine ⟨88777250702312325734038391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59184833801541550489358927 88777250702312325734038391)
        ·
          refine ⟨133165876053468488601057587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88777250702312325734038391 133165876053468488601057587)
          ·
            refine ⟨199748814080202732901586381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133165876053468488601057587 199748814080202732901586381)
            ·
              refine ⟨74905805280076024838094893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199748814080202732901586381 74905805280076024838094893)
              ·
                refine ⟨28089676980028509314285585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74905805280076024838094893 28089676980028509314285585)
                ·
                  refine ⟨21067257735021381985714189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28089676980028509314285585 21067257735021381985714189)
                  ·
                    refine ⟨7900221650633018244642821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21067257735021381985714189 7900221650633018244642821)
                    ·
                      refine ⟨1481291559493690920870529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7900221650633018244642821 1481291559493690920870529)
                      ·
                        rfl

theorem cell23_2884805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_2884805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884805 prefixEnd_2884805 := by exact prefixLift 2884805
  have htrace : WordTrace (prefixWord ++ tailWord_2884805) baseStart_2884805 baseEnd_2884805 := by
    simpa [prefixWord, tailWord_2884805, baseEnd_2884805] using wordTrace_append hprefix tailTrace_2884805
  have hstable : (prefixWord ++ tailWord_2884805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884805).length < 2 ^ (prefixWord ++ tailWord_2884805).sum := by decide
  have hdescent : baseEnd_2884805 < baseStart_2884805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884820 : List Nat := [2, 4, 1, 4, 2, 1, 1, 2, 1, 2, 3]
def baseStart_2884820 : Nat := 118140960795 + 2884820 * 2 ^ 59
def prefixEnd_2884820 : Nat := 4983230072969 + 3 ^ 40 * 2884820 * 2
def baseEnd_2884820 : Nat := 1481299261703508362182961

theorem tailTrace_2884820 : CollatzResearch.WordTrace tailWord_2884820 prefixEnd_2884820 1481299261703508362182961 := by
  unfold tailWord_2884820
  simp only [CollatzResearch.WordTrace]
  refine ⟨52609014704398651438105957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70145352939198201917474609 52609014704398651438105957)
  ·
    refine ⟨9864190257074747144644867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52609014704398651438105957 9864190257074747144644867)
    ·
      refine ⟨14796285385612120716967301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9864190257074747144644867 14796285385612120716967301)
      ·
        refine ⟨2774303509802272634431369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14796285385612120716967301 2774303509802272634431369)
        ·
          refine ⟨2080727632351704475823527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2774303509802272634431369 2080727632351704475823527)
          ·
            refine ⟨3121091448527556713735291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080727632351704475823527 3121091448527556713735291)
            ·
              refine ⟨4681637172791335070602937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3121091448527556713735291 4681637172791335070602937)
              ·
                refine ⟨3511227879593501302952203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4681637172791335070602937 3511227879593501302952203)
                ·
                  refine ⟨5266841819390251954428305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3511227879593501302952203 5266841819390251954428305)
                  ·
                    refine ⟨3950131364542688965821229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5266841819390251954428305 3950131364542688965821229)
                    ·
                      refine ⟨1481299261703508362182961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3950131364542688965821229 1481299261703508362182961)
                      ·
                        rfl

theorem cell23_2884820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_2884820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884820 prefixEnd_2884820 := by exact prefixLift 2884820
  have htrace : WordTrace (prefixWord ++ tailWord_2884820) baseStart_2884820 baseEnd_2884820 := by
    simpa [prefixWord, tailWord_2884820, baseEnd_2884820] using wordTrace_append hprefix tailTrace_2884820
  have hstable : (prefixWord ++ tailWord_2884820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884820).length < 2 ^ (prefixWord ++ tailWord_2884820).sum := by decide
  have hdescent : baseEnd_2884820 < baseStart_2884820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884842 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_2884842 : Nat := 118140960795 + 2884842 * 2 ^ 59
def prefixEnd_2884842 : Nat := 4983230072969 + 3 ^ 40 * 2884842 * 2
def baseEnd_2884842 : Nat := 1481310558277907276107859

theorem tailTrace_2884842 : CollatzResearch.WordTrace tailWord_2884842 prefixEnd_2884842 1481310558277907276107859 := by
  unfold tailWord_2884842
  simp only [CollatzResearch.WordTrace]
  refine ⟨26304707953679400158378195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70145887876478400422341853 26304707953679400158378195)
  ·
    refine ⟨39457061930519100237567293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26304707953679400158378195 39457061930519100237567293)
    ·
      refine ⟨14796398223944662589087735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39457061930519100237567293 14796398223944662589087735)
      ·
        refine ⟨22194597335916993883631603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14796398223944662589087735 22194597335916993883631603)
        ·
          refine ⟨33291896003875490825447405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22194597335916993883631603 33291896003875490825447405)
          ·
            refine ⟨12484461001453309059542777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33291896003875490825447405 12484461001453309059542777)
            ·
              refine ⟨9363345751089981794657083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12484461001453309059542777 9363345751089981794657083)
              ·
                refine ⟨14045018626634972691985625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9363345751089981794657083 14045018626634972691985625)
                ·
                  refine ⟨10533763969976229518989219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14045018626634972691985625 10533763969976229518989219)
                  ·
                    refine ⟨15800645954964344278483829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10533763969976229518989219 15800645954964344278483829)
                    ·
                      refine ⟨1481310558277907276107859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15800645954964344278483829 1481310558277907276107859)
                      ·
                        rfl

theorem cell23_2884842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_2884842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884842 prefixEnd_2884842 := by exact prefixLift 2884842
  have htrace : WordTrace (prefixWord ++ tailWord_2884842) baseStart_2884842 baseEnd_2884842 := by
    simpa [prefixWord, tailWord_2884842, baseEnd_2884842] using wordTrace_append hprefix tailTrace_2884842
  have hstable : (prefixWord ++ tailWord_2884842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884842).length < 2 ^ (prefixWord ++ tailWord_2884842).sum := by decide
  have hdescent : baseEnd_2884842 < baseStart_2884842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884894 : List Nat := [4, 3, 2, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_2884894 : Nat := 118140960795 + 2884894 * 2 ^ 59
def prefixEnd_2884894 : Nat := 4983230072969 + 3 ^ 40 * 2884894 * 2
def baseEnd_2884894 : Nat := 1481337259271941072657621

theorem tailTrace_2884894 : CollatzResearch.WordTrace tailWord_2884894 prefixEnd_2884894 1481337259271941072657621 := by
  unfold tailWord_2884894
  simp only [CollatzResearch.WordTrace]
  refine ⟨13152591051316151689300717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70147152273686142342937157 13152591051316151689300717)
  ·
    refine ⟨4932221644243556883487769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13152591051316151689300717 4932221644243556883487769)
    ·
      refine ⟨3699166233182667662615827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4932221644243556883487769 3699166233182667662615827)
      ·
        refine ⟨5548749349774001493923741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3699166233182667662615827 5548749349774001493923741)
        ·
          refine ⟨2080781006165250560221403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5548749349774001493923741 2080781006165250560221403)
          ·
            refine ⟨3121171509247875840332105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080781006165250560221403 3121171509247875840332105)
            ·
              refine ⟨2340878631935906880249079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3121171509247875840332105 2340878631935906880249079)
              ·
                refine ⟨3511317947903860320373619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2340878631935906880249079 3511317947903860320373619)
                ·
                  refine ⟨5266976921855790480560429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3511317947903860320373619 5266976921855790480560429)
                  ·
                    refine ⟨1975116345695921430210161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5266976921855790480560429 1975116345695921430210161)
                    ·
                      refine ⟨1481337259271941072657621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1975116345695921430210161 1481337259271941072657621)
                      ·
                        rfl

theorem cell23_2884894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_2884894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884894 prefixEnd_2884894 := by exact prefixLift 2884894
  have htrace : WordTrace (prefixWord ++ tailWord_2884894) baseStart_2884894 baseEnd_2884894 := by
    simpa [prefixWord, tailWord_2884894, baseEnd_2884894] using wordTrace_append hprefix tailTrace_2884894
  have hstable : (prefixWord ++ tailWord_2884894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884894).length < 2 ^ (prefixWord ++ tailWord_2884894).sum := by decide
  have hdescent : baseEnd_2884894 < baseStart_2884894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884896 : List Nat := [2, 1, 1, 5, 3, 1, 2, 3, 5]
def baseStart_2884896 : Nat := 118140960795 + 2884896 * 2 ^ 59
def prefixEnd_2884896 : Nat := 4983230072969 + 3 ^ 40 * 2884896 * 2
def baseEnd_2884896 : Nat := 164593142914805562759179

theorem tailTrace_2884896 : CollatzResearch.WordTrace tailWord_2884896 prefixEnd_2884896 164593142914805562759179 := by
  unfold tailWord_2884896
  simp only [CollatzResearch.WordTrace]
  refine ⟨52610400678260983927989271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70147200904347978570652361 52610400678260983927989271)
  ·
    refine ⟨78915601017391475891983907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52610400678260983927989271 78915601017391475891983907)
    ·
      refine ⟨118373401526087213837975861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78915601017391475891983907 118373401526087213837975861)
      ·
        refine ⟨11097506393070676297310237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118373401526087213837975861 11097506393070676297310237)
        ·
          refine ⟨4161564897401503611491339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11097506393070676297310237 4161564897401503611491339)
          ·
            refine ⟨6242347346102255417237009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4161564897401503611491339 6242347346102255417237009)
            ·
              refine ⟨4681760509576691562927757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6242347346102255417237009 4681760509576691562927757)
              ·
                refine ⟨1755660191091259336097909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4681760509576691562927757 1755660191091259336097909)
                ·
                  refine ⟨164593142914805562759179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1755660191091259336097909 164593142914805562759179)
                  ·
                    rfl

theorem cell23_2884896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 5].length) (baseStart_2884896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884896 prefixEnd_2884896 := by exact prefixLift 2884896
  have htrace : WordTrace (prefixWord ++ tailWord_2884896) baseStart_2884896 baseEnd_2884896 := by
    simpa [prefixWord, tailWord_2884896, baseEnd_2884896] using wordTrace_append hprefix tailTrace_2884896
  have hstable : (prefixWord ++ tailWord_2884896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884896).length < 2 ^ (prefixWord ++ tailWord_2884896).sum := by decide
  have hdescent : baseEnd_2884896 < baseStart_2884896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884912 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 4]
def baseStart_2884912 : Nat := 118140960795 + 2884912 * 2 ^ 59
def prefixEnd_2884912 : Nat := 4983230072969 + 3 ^ 40 * 2884912 * 2
def baseEnd_2884912 : Nat := 1481346501923722002232537

theorem tailTrace_2884912 : CollatzResearch.WordTrace tailWord_2884912 prefixEnd_2884912 1481346501923722002232537 := by
  unfold tailWord_2884912
  simp only [CollatzResearch.WordTrace]
  refine ⟨52610692462232001294280495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70147589949642668392373993 52610692462232001294280495)
  ·
    refine ⟨78916038693348001941420743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52610692462232001294280495 78916038693348001941420743)
    ·
      refine ⟨118374058040022002912131115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78916038693348001941420743 118374058040022002912131115)
      ·
        refine ⟨177561087060033004368196673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118374058040022002912131115 177561087060033004368196673)
        ·
          refine ⟨133170815295024753276147505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177561087060033004368196673 133170815295024753276147505)
          ·
            refine ⟨99878111471268564957110629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133170815295024753276147505 99878111471268564957110629)
            ·
              refine ⟨18727145900862855929458243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99878111471268564957110629 18727145900862855929458243)
              ·
                refine ⟨28090718851294283894187365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18727145900862855929458243 28090718851294283894187365)
                ·
                  refine ⟨5267009784617678230160131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28090718851294283894187365 5267009784617678230160131)
                  ·
                    refine ⟨7900514676926517345240197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5267009784617678230160131 7900514676926517345240197)
                    ·
                      refine ⟨1481346501923722002232537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7900514676926517345240197 1481346501923722002232537)
                      ·
                        rfl

theorem cell23_2884912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 4].length) (baseStart_2884912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884912 prefixEnd_2884912 := by exact prefixLift 2884912
  have htrace : WordTrace (prefixWord ++ tailWord_2884912) baseStart_2884912 baseEnd_2884912 := by
    simpa [prefixWord, tailWord_2884912, baseEnd_2884912] using wordTrace_append hprefix tailTrace_2884912
  have hstable : (prefixWord ++ tailWord_2884912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884912).length < 2 ^ (prefixWord ++ tailWord_2884912).sum := by decide
  have hdescent : baseEnd_2884912 < baseStart_2884912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884929 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_2884929 : Nat := 118140960795 + 2884929 * 2 ^ 59
def prefixEnd_2884929 : Nat := 4983230072969 + 3 ^ 40 * 2884929 * 2
def baseEnd_2884929 : Nat := 1481355231094848435719959

theorem tailTrace_2884929 : CollatzResearch.WordTrace tailWord_2884929 prefixEnd_2884929 1481355231094848435719959 := by
  unfold tailWord_2884929
  simp only [CollatzResearch.WordTrace]
  refine ⟨105222004965402414491929841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70148003310268276327953227 105222004965402414491929841)
  ·
    refine ⟨78916503724051810868947381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105222004965402414491929841 78916503724051810868947381)
    ·
      refine ⟨7398422224129857268963817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78916503724051810868947381 7398422224129857268963817)
      ·
        refine ⟨5548816668097392951722863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7398422224129857268963817 5548816668097392951722863)
        ·
          refine ⟨8323225002146089427584295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5548816668097392951722863 8323225002146089427584295)
          ·
            refine ⟨12484837503219134141376443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8323225002146089427584295 12484837503219134141376443)
            ·
              refine ⟨18727256254828701212064665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12484837503219134141376443 18727256254828701212064665)
              ·
                refine ⟨14045442191121525909048499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18727256254828701212064665 14045442191121525909048499)
                ·
                  refine ⟨21068163286682288863572749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14045442191121525909048499 21068163286682288863572749)
                  ·
                    refine ⟨7900561232505858323839781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21068163286682288863572749 7900561232505858323839781)
                    ·
                      refine ⟨1481355231094848435719959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7900561232505858323839781 1481355231094848435719959)
                      ·
                        rfl

theorem cell23_2884929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_2884929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884929 prefixEnd_2884929 := by exact prefixLift 2884929
  have htrace : WordTrace (prefixWord ++ tailWord_2884929) baseStart_2884929 baseEnd_2884929 := by
    simpa [prefixWord, tailWord_2884929, baseEnd_2884929] using wordTrace_append hprefix tailTrace_2884929
  have hstable : (prefixWord ++ tailWord_2884929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884929).length < 2 ^ (prefixWord ++ tailWord_2884929).sum := by decide
  have hdescent : baseEnd_2884929 < baseStart_2884929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884942 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_2884942 : Nat := 118140960795 + 2884942 * 2 ^ 59
def prefixEnd_2884942 : Nat := 4983230072969 + 3 ^ 40 * 2884942 * 2
def baseEnd_2884942 : Nat := 1481361906343356884857399

theorem tailTrace_2884942 : CollatzResearch.WordTrace tailWord_2884942 prefixEnd_2884942 1481361906343356884857399 := by
  unfold tailWord_2884942
  simp only [CollatzResearch.WordTrace]
  refine ⟨13152809889294414714019135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70148319409570211808102053 13152809889294414714019135)
  ·
    refine ⟨19729214833941622071028703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13152809889294414714019135 19729214833941622071028703)
    ·
      refine ⟨29593822250912433106543055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19729214833941622071028703 29593822250912433106543055)
      ·
        refine ⟨44390733376368649659814583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29593822250912433106543055 44390733376368649659814583)
        ·
          refine ⟨66586100064552974489721875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44390733376368649659814583 66586100064552974489721875)
          ·
            refine ⟨99879150096829461734582813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66586100064552974489721875 99879150096829461734582813)
            ·
              refine ⟨37454681286311048150468555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99879150096829461734582813 37454681286311048150468555)
              ·
                refine ⟨56182021929466572225702833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37454681286311048150468555 56182021929466572225702833)
                ·
                  refine ⟨42136516447099929169277125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56182021929466572225702833 42136516447099929169277125)
                  ·
                    refine ⟨7900596833831236719239461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42136516447099929169277125 7900596833831236719239461)
                    ·
                      refine ⟨1481361906343356884857399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7900596833831236719239461 1481361906343356884857399)
                      ·
                        rfl

theorem cell23_2884942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_2884942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884942 prefixEnd_2884942 := by exact prefixLift 2884942
  have htrace : WordTrace (prefixWord ++ tailWord_2884942) baseStart_2884942 baseEnd_2884942 := by
    simpa [prefixWord, tailWord_2884942, baseEnd_2884942] using wordTrace_append hprefix tailTrace_2884942
  have hstable : (prefixWord ++ tailWord_2884942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884942).length < 2 ^ (prefixWord ++ tailWord_2884942).sum := by decide
  have hdescent : baseEnd_2884942 < baseStart_2884942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884949 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 1, 4, 3]
def baseStart_2884949 : Nat := 118140960795 + 2884949 * 2 ^ 59
def prefixEnd_2884949 : Nat := 4983230072969 + 3 ^ 40 * 2884949 * 2
def baseEnd_2884949 : Nat := 1481365500707938357469867

theorem tailTrace_2884949 : CollatzResearch.WordTrace tailWord_2884949 prefixEnd_2884949 1481365500707938357469867 := by
  unfold tailWord_2884949
  simp only [CollatzResearch.WordTrace]
  refine ⟨105222734425329957907657901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70148489616886638605105267 105222734425329957907657901)
  ·
    refine ⟨39458525409498734215371713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105222734425329957907657901 39458525409498734215371713)
    ·
      refine ⟨29593894057124050661528785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39458525409498734215371713 29593894057124050661528785)
      ·
        refine ⟨22195420542843037996146589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29593894057124050661528785 22195420542843037996146589)
        ·
          refine ⟨8323282703566139248554971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22195420542843037996146589 8323282703566139248554971)
          ·
            refine ⟨12484924055349208872832457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8323282703566139248554971 12484924055349208872832457)
            ·
              refine ⟨9363693041511906654624343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12484924055349208872832457 9363693041511906654624343)
              ·
                refine ⟨14045539562267859981936515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9363693041511906654624343 14045539562267859981936515)
                ·
                  refine ⟨21068309343401789972904773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14045539562267859981936515 21068309343401789972904773)
                  ·
                    refine ⟨3950308001887835619919645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21068309343401789972904773 3950308001887835619919645)
                    ·
                      refine ⟨1481365500707938357469867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3950308001887835619919645 1481365500707938357469867)
                      ·
                        rfl

theorem cell23_2884949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_2884949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884949 prefixEnd_2884949 := by exact prefixLift 2884949
  have htrace : WordTrace (prefixWord ++ tailWord_2884949) baseStart_2884949 baseEnd_2884949 := by
    simpa [prefixWord, tailWord_2884949, baseEnd_2884949] using wordTrace_append hprefix tailTrace_2884949
  have hstable : (prefixWord ++ tailWord_2884949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884949).length < 2 ^ (prefixWord ++ tailWord_2884949).sum := by decide
  have hdescent : baseEnd_2884949 < baseStart_2884949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884999 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 3, 5]
def baseStart_2884999 : Nat := 118140960795 + 2884999 * 2 ^ 59
def prefixEnd_2884999 : Nat := 4983230072969 + 3 ^ 40 * 2884999 * 2
def baseEnd_2884999 : Nat := 493797058246887720614879

theorem tailTrace_2884999 : CollatzResearch.WordTrace tailWord_2884999 prefixEnd_2884999 493797058246887720614879 := by
  unfold tailWord_2884999
  simp only [CollatzResearch.WordTrace]
  refine ⟨105224558075148816446978051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70149705383432544297985367 105224558075148816446978051)
  ·
    refine ⟨157836837112723224670467077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105224558075148816446978051 157836837112723224670467077)
    ·
      refine ⟨29594406958635604625712577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157836837112723224670467077 29594406958635604625712577)
      ·
        refine ⟨22195805218976703469284433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29594406958635604625712577 22195805218976703469284433)
        ·
          refine ⟨16646853914232527601963325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22195805218976703469284433 16646853914232527601963325)
          ·
            refine ⟨6242570217837197850736247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16646853914232527601963325 6242570217837197850736247)
            ·
              refine ⟨9363855326755796776104371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6242570217837197850736247 9363855326755796776104371)
              ·
                refine ⟨14045782990133695164156557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9363855326755796776104371 14045782990133695164156557)
                ·
                  refine ⟨5267168621300135686558709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14045782990133695164156557 5267168621300135686558709)
                  ·
                    refine ⟨493797058246887720614879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5267168621300135686558709 493797058246887720614879)
                    ·
                      rfl

theorem cell23_2884999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_2884999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2884999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2884999 prefixEnd_2884999 := by exact prefixLift 2884999
  have htrace : WordTrace (prefixWord ++ tailWord_2884999) baseStart_2884999 baseEnd_2884999 := by
    simpa [prefixWord, tailWord_2884999, baseEnd_2884999] using wordTrace_append hprefix tailTrace_2884999
  have hstable : (prefixWord ++ tailWord_2884999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884999).length < 2 ^ (prefixWord ++ tailWord_2884999).sum := by decide
  have hdescent : baseEnd_2884999 < baseStart_2884999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885042 : List Nat := [3, 2, 1, 1, 1, 1, 2, 12]
def baseStart_2885042 : Nat := 118140960795 + 2885042 * 2 ^ 59
def prefixEnd_2885042 : Nat := 4983230072969 + 3 ^ 40 * 2885042 * 2
def baseEnd_2885042 : Nat := 54867157570696536800257

theorem tailTrace_2885042 : CollatzResearch.WordTrace tailWord_2885042 prefixEnd_2885042 54867157570696536800257 := by
  unfold tailWord_2885042
  simp only [CollatzResearch.WordTrace]
  refine ⟨26306531603498258697698345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70150750942662023193862253 26306531603498258697698345)
  ·
    refine ⟨19729898702623694023273759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26306531603498258697698345 19729898702623694023273759)
    ·
      refine ⟨29594848053935541034910639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19729898702623694023273759 29594848053935541034910639)
      ·
        refine ⟨44392272080903311552365959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29594848053935541034910639 44392272080903311552365959)
        ·
          refine ⟨66588408121354967328548939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44392272080903311552365959 66588408121354967328548939)
          ·
            refine ⟨99882612182032450992823409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66588408121354967328548939 99882612182032450992823409)
            ·
              refine ⟨74911959136524338244617557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99882612182032450992823409 74911959136524338244617557)
              ·
                refine ⟨54867157570696536800257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 74911959136524338244617557 54867157570696536800257)
                ·
                  rfl

theorem cell23_2885042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 12].length) (baseStart_2885042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885042 prefixEnd_2885042 := by exact prefixLift 2885042
  have htrace : WordTrace (prefixWord ++ tailWord_2885042) baseStart_2885042 baseEnd_2885042 := by
    simpa [prefixWord, tailWord_2885042, baseEnd_2885042] using wordTrace_append hprefix tailTrace_2885042
  have hstable : (prefixWord ++ tailWord_2885042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885042).length < 2 ^ (prefixWord ++ tailWord_2885042).sum := by decide
  have hdescent : baseEnd_2885042 < baseStart_2885042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885053 : List Nat := [1, 4, 1, 2, 2, 1, 3, 2, 3, 2, 2]
def baseStart_2885053 : Nat := 118140960795 + 2885053 * 2 ^ 59
def prefixEnd_2885053 : Nat := 4983230072969 + 3 ^ 40 * 2885053 * 2
def baseEnd_2885053 : Nat := 1481418902696005950569389

theorem tailTrace_2885053 : CollatzResearch.WordTrace tailWord_2885053 prefixEnd_2885053 1481418902696005950569389 := by
  unfold tailWord_2885053
  simp only [CollatzResearch.WordTrace]
  refine ⟨105226527616953183669443813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70151018411302122446295875 105226527616953183669443813)
  ·
    refine ⟨19729973928178721938020715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105226527616953183669443813 19729973928178721938020715)
    ·
      refine ⟨29594960892268082907031073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19729973928178721938020715 29594960892268082907031073)
      ·
        refine ⟨22196220669201062180273305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29594960892268082907031073 22196220669201062180273305)
        ·
          refine ⟨16647165501900796635204979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22196220669201062180273305 16647165501900796635204979)
          ·
            refine ⟨24970748252851194952807469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16647165501900796635204979 24970748252851194952807469)
            ·
              refine ⟨9364030594819198107302801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24970748252851194952807469 9364030594819198107302801)
              ·
                refine ⟨7023022946114398580477101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9364030594819198107302801 7023022946114398580477101)
                ·
                  refine ⟨2633633604792899467678913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7023022946114398580477101 2633633604792899467678913)
                  ·
                    refine ⟨1975225203594674600759185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2633633604792899467678913 1975225203594674600759185)
                    ·
                      refine ⟨1481418902696005950569389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1975225203594674600759185 1481418902696005950569389)
                      ·
                        rfl

theorem cell23_2885053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_2885053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885053 prefixEnd_2885053 := by exact prefixLift 2885053
  have htrace : WordTrace (prefixWord ++ tailWord_2885053) baseStart_2885053 baseEnd_2885053 := by
    simpa [prefixWord, tailWord_2885053, baseEnd_2885053] using wordTrace_append hprefix tailTrace_2885053
  have hstable : (prefixWord ++ tailWord_2885053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885053).length < 2 ^ (prefixWord ++ tailWord_2885053).sum := by decide
  have hdescent : baseEnd_2885053 < baseStart_2885053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885070 : List Nat := [4, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2]
def baseStart_2885070 : Nat := 118140960795 + 2885070 * 2 ^ 59
def prefixEnd_2885070 : Nat := 4983230072969 + 3 ^ 40 * 2885070 * 2
def baseEnd_2885070 : Nat := 1481427631867132384056811

theorem tailTrace_2885070 : CollatzResearch.WordTrace tailWord_2885070 prefixEnd_2885070 1481427631867132384056811 := by
  unfold tailWord_2885070
  simp only [CollatzResearch.WordTrace]
  refine ⟨13153393457236449446601583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70151431771927730381875109 13153393457236449446601583)
  ·
    refine ⟨19730090185854674169902375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13153393457236449446601583 19730090185854674169902375)
    ·
      refine ⟨29595135278782011254853563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19730090185854674169902375 29595135278782011254853563)
      ·
        refine ⟨44392702918173016882280345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29595135278782011254853563 44392702918173016882280345)
        ·
          refine ⟨33294527188629762661710259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44392702918173016882280345 33294527188629762661710259)
          ·
            refine ⟨49941790782944643992565389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33294527188629762661710259 49941790782944643992565389)
            ·
              refine ⟨18728171543604241497212021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49941790782944643992565389 18728171543604241497212021)
              ·
                refine ⟨1755766082212897640363627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18728171543604241497212021 1755766082212897640363627)
                ·
                  refine ⟨2633649123319346460545441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1755766082212897640363627 2633649123319346460545441)
                  ·
                    refine ⟨1975236842489509845409081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2633649123319346460545441 1975236842489509845409081)
                    ·
                      refine ⟨1481427631867132384056811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1975236842489509845409081 1481427631867132384056811)
                      ·
                        rfl

theorem cell23_2885070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2].length) (baseStart_2885070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885070 prefixEnd_2885070 := by exact prefixLift 2885070
  have htrace : WordTrace (prefixWord ++ tailWord_2885070) baseStart_2885070 baseEnd_2885070 := by
    simpa [prefixWord, tailWord_2885070, baseEnd_2885070] using wordTrace_append hprefix tailTrace_2885070
  have hstable : (prefixWord ++ tailWord_2885070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885070).length < 2 ^ (prefixWord ++ tailWord_2885070).sum := by decide
  have hdescent : baseEnd_2885070 < baseStart_2885070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885072 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 4, 7]
def baseStart_2885072 : Nat := 118140960795 + 2885072 * 2 ^ 59
def prefixEnd_2885072 : Nat := 4983230072969 + 3 ^ 40 * 2885072 * 2
def baseEnd_2885072 : Nat := 493809552942813792077267

theorem tailTrace_2885072 : CollatzResearch.WordTrace tailWord_2885072 prefixEnd_2885072 493809552942813792077267 := by
  unfold tailWord_2885072
  simp only [CollatzResearch.WordTrace]
  refine ⟨52613610301942174957192735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70151480402589566609590313 52613610301942174957192735)
  ·
    refine ⟨78920415452913262435789103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52613610301942174957192735 78920415452913262435789103)
    ·
      refine ⟨118380623179369893653683655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78920415452913262435789103 118380623179369893653683655)
      ·
        refine ⟨177570934769054840480525483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118380623179369893653683655 177570934769054840480525483)
        ·
          refine ⟨266356402153582260720788225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177570934769054840480525483 266356402153582260720788225)
          ·
            refine ⟨199767301615186695540591169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266356402153582260720788225 199767301615186695540591169)
            ·
              refine ⟨149825476211390021655443377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199767301615186695540591169 149825476211390021655443377)
              ·
                refine ⟨112369107158542516241582533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149825476211390021655443377 112369107158542516241582533)
                ·
                  refine ⟨21069207592226721795296725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112369107158542516241582533 21069207592226721795296725)
                  ·
                    refine ⟨493809552942813792077267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21069207592226721795296725 493809552942813792077267)
                    ·
                      rfl

theorem cell23_2885072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 4, 7].length) (baseStart_2885072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885072 prefixEnd_2885072 := by exact prefixLift 2885072
  have htrace : WordTrace (prefixWord ++ tailWord_2885072) baseStart_2885072 baseEnd_2885072 := by
    simpa [prefixWord, tailWord_2885072, baseEnd_2885072] using wordTrace_append hprefix tailTrace_2885072
  have hstable : (prefixWord ++ tailWord_2885072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885072).length < 2 ^ (prefixWord ++ tailWord_2885072).sum := by decide
  have hdescent : baseEnd_2885072 < baseStart_2885072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885129 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 2, 1, 5]
def baseStart_2885129 : Nat := 118140960795 + 2885129 * 2 ^ 59
def prefixEnd_2885129 : Nat := 4983230072969 + 3 ^ 40 * 2885129 * 2
def baseEnd_2885129 : Nat := 1481457927225747653219039

theorem tailTrace_2885129 : CollatzResearch.WordTrace tailWord_2885129 prefixEnd_2885129 1481457927225747653219039 := by
  unfold tailWord_2885129
  simp only [CollatzResearch.WordTrace]
  refine ⟨105229299564677848649210441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70152866376451899099473627 105229299564677848649210441)
  ·
    refine ⟨78921974673508386486907831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105229299564677848649210441 78921974673508386486907831)
    ·
      refine ⟨118382962010262579730361747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78921974673508386486907831 118382962010262579730361747)
      ·
        refine ⟨177574443015393869595542621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118382962010262579730361747 177574443015393869595542621)
        ·
          refine ⟨66590416130772701098328483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177574443015393869595542621 66590416130772701098328483)
          ·
            refine ⟨99885624196159051647492725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66590416130772701098328483 99885624196159051647492725)
            ·
              refine ⟨9364277268389911091952443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99885624196159051647492725 9364277268389911091952443)
              ·
                refine ⟨14046415902584866637928665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9364277268389911091952443 14046415902584866637928665)
                ·
                  refine ⟨10534811926938649978446499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14046415902584866637928665 10534811926938649978446499)
                  ·
                    refine ⟨15802217890407974967669749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10534811926938649978446499 15802217890407974967669749)
                    ·
                      refine ⟨1481457927225747653219039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15802217890407974967669749 1481457927225747653219039)
                      ·
                        rfl

theorem cell23_2885129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 1, 5].length) (baseStart_2885129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885129 prefixEnd_2885129 := by exact prefixLift 2885129
  have htrace : WordTrace (prefixWord ++ tailWord_2885129) baseStart_2885129 baseEnd_2885129 := by
    simpa [prefixWord, tailWord_2885129, baseEnd_2885129] using wordTrace_append hprefix tailTrace_2885129
  have hstable : (prefixWord ++ tailWord_2885129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885129).length < 2 ^ (prefixWord ++ tailWord_2885129).sum := by decide
  have hdescent : baseEnd_2885129 < baseStart_2885129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885189 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 3, 2, 5]
def baseStart_2885189 : Nat := 118140960795 + 2885189 * 2 ^ 59
def prefixEnd_2885189 : Nat := 4983230072969 + 3 ^ 40 * 2885189 * 2
def baseEnd_2885189 : Nat := 1481488736065017418468763

theorem tailTrace_2885189 : CollatzResearch.WordTrace tailWord_2885189 prefixEnd_2885189 1481488736065017418468763 := by
  unfold tailWord_2885189
  simp only [CollatzResearch.WordTrace]
  refine ⟨105231487944460478896394621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70154325296306985930929747 105231487944460478896394621)
  ·
    refine ⟨39461807979172679586147983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105231487944460478896394621 39461807979172679586147983)
    ·
      refine ⟨59192711968759019379221975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39461807979172679586147983 59192711968759019379221975)
      ·
        refine ⟨88789067953138529068832963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59192711968759019379221975 88789067953138529068832963)
        ·
          refine ⟨133183601929707793603249445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88789067953138529068832963 133183601929707793603249445)
          ·
            refine ⟨24971925361820211300609271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133183601929707793603249445 24971925361820211300609271)
            ·
              refine ⟨37457888042730316950913907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24971925361820211300609271 37457888042730316950913907)
              ·
                refine ⟨56186832064095475426370861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37457888042730316950913907 56186832064095475426370861)
                ·
                  refine ⟨21070062024035803284889073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56186832064095475426370861 21070062024035803284889073)
                  ·
                    refine ⟨15802546518026852463666805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21070062024035803284889073 15802546518026852463666805)
                    ·
                      refine ⟨1481488736065017418468763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15802546518026852463666805 1481488736065017418468763)
                      ·
                        rfl

theorem cell23_2885189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_2885189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885189 prefixEnd_2885189 := by exact prefixLift 2885189
  have htrace : WordTrace (prefixWord ++ tailWord_2885189) baseStart_2885189 baseEnd_2885189 := by
    simpa [prefixWord, tailWord_2885189, baseEnd_2885189] using wordTrace_append hprefix tailTrace_2885189
  have hstable : (prefixWord ++ tailWord_2885189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885189).length < 2 ^ (prefixWord ++ tailWord_2885189).sum := by decide
  have hdescent : baseEnd_2885189 < baseStart_2885189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885196 : List Nat := [2, 2, 1, 3, 1, 3, 2, 2, 2, 5]
def baseStart_2885196 : Nat := 118140960795 + 2885196 * 2 ^ 59
def prefixEnd_2885196 : Nat := 4983230072969 + 3 ^ 40 * 2885196 * 2
def baseEnd_2885196 : Nat := 493830776809866297027077

theorem tailTrace_2885196 : CollatzResearch.WordTrace tailWord_2885196 prefixEnd_2885196 493830776809866297027077 := by
  unfold tailWord_2885196
  simp only [CollatzResearch.WordTrace]
  refine ⟨52615871627717559545949721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70154495503623412727932961 52615871627717559545949721)
  ·
    refine ⟨39461903720788169659462291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52615871627717559545949721 39461903720788169659462291)
    ·
      refine ⟨59192855581182254489193437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39461903720788169659462291 59192855581182254489193437)
      ·
        refine ⟨22197320842943345433447539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59192855581182254489193437 22197320842943345433447539)
        ·
          refine ⟨33295981264415018150171309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22197320842943345433447539 33295981264415018150171309)
          ·
            refine ⟨12485992974155631806314241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33295981264415018150171309 12485992974155631806314241)
            ·
              refine ⟨9364494730616723854735681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12485992974155631806314241 9364494730616723854735681)
              ·
                refine ⟨7023371047962542891051761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9364494730616723854735681 7023371047962542891051761)
                ·
                  refine ⟨5267528285971907168288821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7023371047962542891051761 5267528285971907168288821)
                  ·
                    refine ⟨493830776809866297027077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5267528285971907168288821 493830776809866297027077)
                    ·
                      rfl

theorem cell23_2885196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_2885196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885196 prefixEnd_2885196 := by exact prefixLift 2885196
  have htrace : WordTrace (prefixWord ++ tailWord_2885196) baseStart_2885196 baseEnd_2885196 := by
    simpa [prefixWord, tailWord_2885196, baseEnd_2885196] using wordTrace_append hprefix tailTrace_2885196
  have hstable : (prefixWord ++ tailWord_2885196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885196).length < 2 ^ (prefixWord ++ tailWord_2885196).sum := by decide
  have hdescent : baseEnd_2885196 < baseStart_2885196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885199 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 4]
def baseStart_2885199 : Nat := 118140960795 + 2885199 * 2 ^ 59
def prefixEnd_2885199 : Nat := 4983230072969 + 3 ^ 40 * 2885199 * 2
def baseEnd_2885199 : Nat := 1481493870871562379343717

theorem tailTrace_2885199 : CollatzResearch.WordTrace tailWord_2885199 prefixEnd_2885199 1481493870871562379343717 := by
  unfold tailWord_2885199
  simp only [CollatzResearch.WordTrace]
  refine ⟨105231852674424250604258651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70154568449616167069505767 105231852674424250604258651)
  ·
    refine ⟨157847779011636375906387977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105231852674424250604258651 157847779011636375906387977)
    ·
      refine ⟨118385834258727281929790983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157847779011636375906387977 118385834258727281929790983)
      ·
        refine ⟨177578751388090922894686475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118385834258727281929790983 177578751388090922894686475)
        ·
          refine ⟨266368127082136384342029713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177578751388090922894686475 266368127082136384342029713)
          ·
            refine ⟨199776095311602288256522285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266368127082136384342029713 199776095311602288256522285)
            ·
              refine ⟨74916035741850858096195857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199776095311602288256522285 74916035741850858096195857)
              ·
                refine ⟨56187026806388143572146893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74916035741850858096195857 56187026806388143572146893)
                ·
                  refine ⟨21070135052395553839555085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56187026806388143572146893 21070135052395553839555085)
                  ·
                    refine ⟨7901300644648332689833157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21070135052395553839555085 7901300644648332689833157)
                    ·
                      refine ⟨1481493870871562379343717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7901300644648332689833157 1481493870871562379343717)
                      ·
                        rfl

theorem cell23_2885199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 4].length) (baseStart_2885199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885199 prefixEnd_2885199 := by exact prefixLift 2885199
  have htrace : WordTrace (prefixWord ++ tailWord_2885199) baseStart_2885199 baseEnd_2885199 := by
    simpa [prefixWord, tailWord_2885199, baseEnd_2885199] using wordTrace_append hprefix tailTrace_2885199
  have hstable : (prefixWord ++ tailWord_2885199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885199).length < 2 ^ (prefixWord ++ tailWord_2885199).sum := by decide
  have hdescent : baseEnd_2885199 < baseStart_2885199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885230 : List Nat := [4, 1, 2, 2, 3, 2, 1, 1, 2, 5]
def baseStart_2885230 : Nat := 118140960795 + 2885230 * 2 ^ 59
def prefixEnd_2885230 : Nat := 4983230072969 + 3 ^ 40 * 2885230 * 2
def baseEnd_2885230 : Nat := 493836596257283919352025

theorem tailTrace_2885230 : CollatzResearch.WordTrace tailWord_2885230 prefixEnd_2885230 493836596257283919352025 := by
  unfold tailWord_2885230
  simp only [CollatzResearch.WordTrace]
  refine ⟨13154122917163992862329643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70155322224874628599091429 13154122917163992862329643)
  ·
    refine ⟨19731184375745989293494465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13154122917163992862329643 19731184375745989293494465)
    ·
      refine ⟨14798388281809491970120849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19731184375745989293494465 14798388281809491970120849)
      ·
        refine ⟨11098791211357118977590637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14798388281809491970120849 11098791211357118977590637)
        ·
          refine ⟨4162046704258919616596489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11098791211357118977590637 4162046704258919616596489)
          ·
            refine ⟨3121535028194189712447367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4162046704258919616596489 3121535028194189712447367)
            ·
              refine ⟨4682302542291284568671051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3121535028194189712447367 4682302542291284568671051)
              ·
                refine ⟨7023453813436926853006577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4682302542291284568671051 7023453813436926853006577)
                ·
                  refine ⟨5267590360077695139754933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7023453813436926853006577 5267590360077695139754933)
                  ·
                    refine ⟨493836596257283919352025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5267590360077695139754933 493836596257283919352025)
                    ·
                      rfl

theorem cell23_2885230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_2885230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885230 prefixEnd_2885230 := by exact prefixLift 2885230
  have htrace : WordTrace (prefixWord ++ tailWord_2885230) baseStart_2885230 baseEnd_2885230 := by
    simpa [prefixWord, tailWord_2885230, baseEnd_2885230] using wordTrace_append hprefix tailTrace_2885230
  have hstable : (prefixWord ++ tailWord_2885230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885230).length < 2 ^ (prefixWord ++ tailWord_2885230).sum := by decide
  have hdescent : baseEnd_2885230 < baseStart_2885230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885239 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 8]
def baseStart_2885239 : Nat := 118140960795 + 2885239 * 2 ^ 59
def prefixEnd_2885239 : Nat := 4983230072969 + 3 ^ 40 * 2885239 * 2
def baseEnd_2885239 : Nat := 164612712233082469204837

theorem tailTrace_2885239 : CollatzResearch.WordTrace tailWord_2885239 prefixEnd_2885239 164612712233082469204837 := by
  unfold tailWord_2885239
  simp only [CollatzResearch.WordTrace]
  refine ⟨105233311594279337435714771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70155541062852891623809847 105233311594279337435714771)
  ·
    refine ⟨157849967391419006153572157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105233311594279337435714771 157849967391419006153572157)
    ·
      refine ⟨59193737771782127307589559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157849967391419006153572157 59193737771782127307589559)
      ·
        refine ⟨88790606657673190961384339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59193737771782127307589559 88790606657673190961384339)
        ·
          refine ⟨133185909986509786442076509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88790606657673190961384339 133185909986509786442076509)
          ·
            refine ⟨49944716244941169915778691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133185909986509786442076509 49944716244941169915778691)
            ·
              refine ⟨74917074367411754873668037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49944716244941169915778691 74917074367411754873668037)
              ·
                refine ⟨14046951443889704038812757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74917074367411754873668037 14046951443889704038812757)
                ·
                  refine ⟨164612712233082469204837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14046951443889704038812757 164612712233082469204837)
                  ·
                    rfl

theorem cell23_2885239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 8].length) (baseStart_2885239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885239 prefixEnd_2885239 := by exact prefixLift 2885239
  have htrace : WordTrace (prefixWord ++ tailWord_2885239) baseStart_2885239 baseEnd_2885239 := by
    simpa [prefixWord, tailWord_2885239, baseEnd_2885239] using wordTrace_append hprefix tailTrace_2885239
  have hstable : (prefixWord ++ tailWord_2885239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885239).length < 2 ^ (prefixWord ++ tailWord_2885239).sum := by decide
  have hdescent : baseEnd_2885239 < baseStart_2885239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885259 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 8]
def baseStart_2885259 : Nat := 118140960795 + 2885259 * 2 ^ 59
def prefixEnd_2885259 : Nat := 4983230072969 + 3 ^ 40 * 2885259 * 2
def baseEnd_2885259 : Nat := 1481524679710832144593441

theorem tailTrace_2885259 : CollatzResearch.WordTrace tailWord_2885259 prefixEnd_2885259 1481524679710832144593441 := by
  unfold tailWord_2885259
  simp only [CollatzResearch.WordTrace]
  refine ⟨105234041054206880851442831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70156027369471253900961887 105234041054206880851442831)
  ·
    refine ⟨157851061581310321277164247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105234041054206880851442831 157851061581310321277164247)
    ·
      refine ⟨236776592371965481915746371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157851061581310321277164247 236776592371965481915746371)
      ·
        refine ⟨355164888557948222873619557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236776592371965481915746371 355164888557948222873619557)
        ·
          refine ⟨66593416604615291788803667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 355164888557948222873619557 66593416604615291788803667)
          ·
            refine ⟨99890124906922937683205501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66593416604615291788803667 99890124906922937683205501)
            ·
              refine ⟨37458796840096101631202063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99890124906922937683205501 37458796840096101631202063)
              ·
                refine ⟨56188195260144152446803095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37458796840096101631202063 56188195260144152446803095)
                ·
                  refine ⟨84282292890216228670204643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56188195260144152446803095 84282292890216228670204643)
                  ·
                    refine ⟨126423439335324343005306965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84282292890216228670204643 126423439335324343005306965)
                    ·
                      refine ⟨1481524679710832144593441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 126423439335324343005306965 1481524679710832144593441)
                      ·
                        rfl

theorem cell23_2885259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 8].length) (baseStart_2885259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885259 prefixEnd_2885259 := by exact prefixLift 2885259
  have htrace : WordTrace (prefixWord ++ tailWord_2885259) baseStart_2885259 baseEnd_2885259 := by
    simpa [prefixWord, tailWord_2885259, baseEnd_2885259] using wordTrace_append hprefix tailTrace_2885259
  have hstable : (prefixWord ++ tailWord_2885259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885259).length < 2 ^ (prefixWord ++ tailWord_2885259).sum := by decide
  have hdescent : baseEnd_2885259 < baseStart_2885259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885283 : List Nat := [1, 1, 1, 4, 1, 1, 3, 4, 3, 1, 3]
def baseStart_2885283 : Nat := 118140960795 + 2885283 * 2 ^ 59
def prefixEnd_2885283 : Nat := 4983230072969 + 3 ^ 40 * 2885283 * 2
def baseEnd_2885283 : Nat := 1481537003246540050693331

theorem tailTrace_2885283 : CollatzResearch.WordTrace tailWord_2885283 prefixEnd_2885283 1481537003246540050693331 := by
  unfold tailWord_2885283
  simp only [CollatzResearch.WordTrace]
  refine ⟨105234916406119932950316503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70156610937413288633544335 105234916406119932950316503)
  ·
    refine ⟨157852374609179899425474755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105234916406119932950316503 157852374609179899425474755)
    ·
      refine ⟨236778561913769849138212133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157852374609179899425474755 236778561913769849138212133)
      ·
        refine ⟨44395980358831846713414775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236778561913769849138212133 44395980358831846713414775)
        ·
          refine ⟨66593970538247770070122163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44395980358831846713414775 66593970538247770070122163)
          ·
            refine ⟨99890955807371655105183245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66593970538247770070122163 99890955807371655105183245)
            ·
              refine ⟨37459108427764370664443717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99890955807371655105183245 37459108427764370664443717)
              ·
                refine ⟨7023582830205819499583197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37459108427764370664443717 7023582830205819499583197)
                ·
                  refine ⟨2633843561327182312343699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7023582830205819499583197 2633843561327182312343699)
                  ·
                    refine ⟨3950765341990773468515549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2633843561327182312343699 3950765341990773468515549)
                    ·
                      refine ⟨1481537003246540050693331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3950765341990773468515549 1481537003246540050693331)
                      ·
                        rfl

theorem cell23_2885283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_2885283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885283 prefixEnd_2885283 := by exact prefixLift 2885283
  have htrace : WordTrace (prefixWord ++ tailWord_2885283) baseStart_2885283 baseEnd_2885283 := by
    simpa [prefixWord, tailWord_2885283, baseEnd_2885283] using wordTrace_append hprefix tailTrace_2885283
  have hstable : (prefixWord ++ tailWord_2885283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885283).length < 2 ^ (prefixWord ++ tailWord_2885283).sum := by decide
  have hdescent : baseEnd_2885283 < baseStart_2885283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885303 : List Nat := [1, 1, 3, 1, 5, 1, 2, 3, 1, 5]
def baseStart_2885303 : Nat := 118140960795 + 2885303 * 2 ^ 59
def prefixEnd_2885303 : Nat := 4983230072969 + 3 ^ 40 * 2885303 * 2
def baseEnd_2885303 : Nat := 493849090953209990814413

theorem tailTrace_2885303 : CollatzResearch.WordTrace tailWord_2885303 prefixEnd_2885303 493849090953209990814413 := by
  unfold tailWord_2885303
  simp only [CollatzResearch.WordTrace]
  refine ⟨105235645866047476366044563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70157097244031650910696375 105235645866047476366044563)
  ·
    refine ⟨157853468799071214549066845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105235645866047476366044563 157853468799071214549066845)
    ·
      refine ⟨59195050799651705455900067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157853468799071214549066845 59195050799651705455900067)
      ·
        refine ⟨88792576199477558183850101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59195050799651705455900067 88792576199477558183850101)
        ·
          refine ⟨8324304018701021079735947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88792576199477558183850101 8324304018701021079735947)
          ·
            refine ⟨12486456028051531619603921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8324304018701021079735947 12486456028051531619603921)
            ·
              refine ⟨9364842021038648714702941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12486456028051531619603921 9364842021038648714702941)
              ·
                refine ⟨3511815757889493268013603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9364842021038648714702941 3511815757889493268013603)
                ·
                  refine ⟨5267723636834239902020405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3511815757889493268013603 5267723636834239902020405)
                  ·
                    refine ⟨493849090953209990814413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5267723636834239902020405 493849090953209990814413)
                    ·
                      rfl

theorem cell23_2885303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 5].length) (baseStart_2885303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885303 prefixEnd_2885303 := by exact prefixLift 2885303
  have htrace : WordTrace (prefixWord ++ tailWord_2885303) baseStart_2885303 baseEnd_2885303 := by
    simpa [prefixWord, tailWord_2885303, baseEnd_2885303] using wordTrace_append hprefix tailTrace_2885303
  have hstable : (prefixWord ++ tailWord_2885303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885303).length < 2 ^ (prefixWord ++ tailWord_2885303).sum := by decide
  have hdescent : baseEnd_2885303 < baseStart_2885303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885310 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2]
def baseStart_2885310 : Nat := 118140960795 + 2885310 * 2 ^ 59
def prefixEnd_2885310 : Nat := 4983230072969 + 3 ^ 40 * 2885310 * 2
def baseEnd_2885310 : Nat := 1481550867224211445055707

theorem tailTrace_2885310 : CollatzResearch.WordTrace tailWord_2885310 prefixEnd_2885310 1481550867224211445055707 := by
  unfold tailWord_2885310
  simp only [CollatzResearch.WordTrace]
  refine ⟨13154487647127764570193673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70157267451348077707699589 13154487647127764570193673)
  ·
    refine ⟨9865865735345823427645255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13154487647127764570193673 9865865735345823427645255)
    ·
      refine ⟨14798798603018735141467883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9865865735345823427645255 14798798603018735141467883)
      ·
        refine ⟨22198197904528102712201825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14798798603018735141467883 22198197904528102712201825)
        ·
          refine ⟨16648648428396077034151369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22198197904528102712201825 16648648428396077034151369)
          ·
            refine ⟨12486486321297057775613527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16648648428396077034151369 12486486321297057775613527)
            ·
              refine ⟨18729729481945586663420291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12486486321297057775613527 18729729481945586663420291)
              ·
                refine ⟨28094594222918379995130437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18729729481945586663420291 28094594222918379995130437)
                ·
                  refine ⟨5267736416797196249086957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28094594222918379995130437 5267736416797196249086957)
                  ·
                    refine ⟨1975401156298948593407609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5267736416797196249086957 1975401156298948593407609)
                    ·
                      refine ⟨1481550867224211445055707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1975401156298948593407609 1481550867224211445055707)
                      ·
                        rfl

theorem cell23_2885310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_2885310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885310 prefixEnd_2885310 := by exact prefixLift 2885310
  have htrace : WordTrace (prefixWord ++ tailWord_2885310) baseStart_2885310 baseEnd_2885310 := by
    simpa [prefixWord, tailWord_2885310, baseEnd_2885310] using wordTrace_append hprefix tailTrace_2885310
  have hstable : (prefixWord ++ tailWord_2885310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885310).length < 2 ^ (prefixWord ++ tailWord_2885310).sum := by decide
  have hdescent : baseEnd_2885310 < baseStart_2885310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885336 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 1, 1, 6]
def baseStart_2885336 : Nat := 118140960795 + 2885336 * 2 ^ 59
def prefixEnd_2885336 : Nat := 4983230072969 + 3 ^ 40 * 2885336 * 2
def baseEnd_2885336 : Nat := 1481564217721228343330587

theorem tailTrace_2885336 : CollatzResearch.WordTrace tailWord_2885336 prefixEnd_2885336 1481564217721228343330587 := by
  unfold tailWord_2885336
  simp only [CollatzResearch.WordTrace]
  refine ⟨52618424737463961500997931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70157899649951948667997241 52618424737463961500997931)
  ·
    refine ⟨78927637106195942251496897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52618424737463961500997931 78927637106195942251496897)
    ·
      refine ⟨59195727829646956688622673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78927637106195942251496897 59195727829646956688622673)
      ·
        refine ⟨44396795872235217516467005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59195727829646956688622673 44396795872235217516467005)
        ·
          refine ⟨16648798452088206568675127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44396795872235217516467005 16648798452088206568675127)
          ·
            refine ⟨24973197678132309853012691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16648798452088206568675127 24973197678132309853012691)
            ·
              refine ⟨37459796517198464779519037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24973197678132309853012691 37459796517198464779519037)
              ·
                refine ⟨14047423693949424292319639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37459796517198464779519037 14047423693949424292319639)
                ·
                  refine ⟨21071135540924136438479459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14047423693949424292319639 21071135540924136438479459)
                  ·
                    refine ⟨31606703311386204657719189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21071135540924136438479459 31606703311386204657719189)
                    ·
                      refine ⟨1481564217721228343330587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31606703311386204657719189 1481564217721228343330587)
                      ·
                        rfl

theorem cell23_2885336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_2885336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885336 prefixEnd_2885336 := by exact prefixLift 2885336
  have htrace : WordTrace (prefixWord ++ tailWord_2885336) baseStart_2885336 baseEnd_2885336 := by
    simpa [prefixWord, tailWord_2885336, baseEnd_2885336] using wordTrace_append hprefix tailTrace_2885336
  have hstable : (prefixWord ++ tailWord_2885336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885336).length < 2 ^ (prefixWord ++ tailWord_2885336).sum := by decide
  have hdescent : baseEnd_2885336 < baseStart_2885336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885343 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 3]
def baseStart_2885343 : Nat := 118140960795 + 2885343 * 2 ^ 59
def prefixEnd_2885343 : Nat := 4983230072969 + 3 ^ 40 * 2885343 * 2
def baseEnd_2885343 : Nat := 1481567812085809815943055

theorem tailTrace_2885343 : CollatzResearch.WordTrace tailWord_2885343 prefixEnd_2885343 1481567812085809815943055 := by
  unfold tailWord_2885343
  simp only [CollatzResearch.WordTrace]
  refine ⟨105237104785902563197500683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70158069857268375465000455 105237104785902563197500683)
  ·
    refine ⟨157855657178853844796251025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105237104785902563197500683 157855657178853844796251025)
    ·
      refine ⟨118391742884140383597188269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157855657178853844796251025 118391742884140383597188269)
      ·
        refine ⟨44396903581552643848945601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118391742884140383597188269 44396903581552643848945601)
        ·
          refine ⟨33297677686164482886709201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44396903581552643848945601 33297677686164482886709201)
          ·
            refine ⟨24973258264623362165031901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33297677686164482886709201 24973258264623362165031901)
            ·
              refine ⟨9364971849233760811886963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24973258264623362165031901 9364971849233760811886963)
              ·
                refine ⟨14047457773850641217830445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9364971849233760811886963 14047457773850641217830445)
                ·
                  refine ⟨5267796665193990456686417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14047457773850641217830445 5267796665193990456686417)
                  ·
                    refine ⟨3950847498895492842514813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5267796665193990456686417 3950847498895492842514813)
                    ·
                      refine ⟨1481567812085809815943055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3950847498895492842514813 1481567812085809815943055)
                      ·
                        rfl

theorem cell23_2885343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_2885343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885343 prefixEnd_2885343 := by exact prefixLift 2885343
  have htrace : WordTrace (prefixWord ++ tailWord_2885343) baseStart_2885343 baseEnd_2885343 := by
    simpa [prefixWord, tailWord_2885343, baseEnd_2885343] using wordTrace_append hprefix tailTrace_2885343
  have hstable : (prefixWord ++ tailWord_2885343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885343).length < 2 ^ (prefixWord ++ tailWord_2885343).sum := by decide
  have hdescent : baseEnd_2885343 < baseStart_2885343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885357 : List Nat := [1, 5, 1, 2, 1, 3, 3, 1, 1, 1, 4]
def baseStart_2885357 : Nat := 118140960795 + 2885357 * 2 ^ 59
def prefixEnd_2885357 : Nat := 4983230072969 + 3 ^ 40 * 2885357 * 2
def baseEnd_2885357 : Nat := 1481575000814972761167991

theorem tailTrace_2885357 : CollatzResearch.WordTrace tailWord_2885357 prefixEnd_2885357 1481575000814972761167991 := by
  unfold tailWord_2885357
  simp only [CollatzResearch.WordTrace]
  refine ⟨105237615407851843588510325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70158410271901229059006883 105237615407851843588510325)
  ·
    refine ⟨9866026444486110336422843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105237615407851843588510325 9866026444486110336422843)
    ·
      refine ⟨14799039666729165504634265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9866026444486110336422843 14799039666729165504634265)
      ·
        refine ⟨11099279750046874128475699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14799039666729165504634265 11099279750046874128475699)
        ·
          refine ⟨16648919625070311192713549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11099279750046874128475699 16648919625070311192713549)
          ·
            refine ⟨6243344859401366697267581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16648919625070311192713549 6243344859401366697267581)
            ·
              refine ⟨2341254322275512511475343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6243344859401366697267581 2341254322275512511475343)
              ·
                refine ⟨3511881483413268767213015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2341254322275512511475343 3511881483413268767213015)
                ·
                  refine ⟨5267822225119903150819523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3511881483413268767213015 5267822225119903150819523)
                  ·
                    refine ⟨7901733337679854726229285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5267822225119903150819523 7901733337679854726229285)
                    ·
                      refine ⟨1481575000814972761167991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7901733337679854726229285 1481575000814972761167991)
                      ·
                        rfl

theorem cell23_2885357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_2885357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885357 prefixEnd_2885357 := by exact prefixLift 2885357
  have htrace : WordTrace (prefixWord ++ tailWord_2885357) baseStart_2885357 baseEnd_2885357 := by
    simpa [prefixWord, tailWord_2885357, baseEnd_2885357] using wordTrace_append hprefix tailTrace_2885357
  have hstable : (prefixWord ++ tailWord_2885357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885357).length < 2 ^ (prefixWord ++ tailWord_2885357).sum := by decide
  have hdescent : baseEnd_2885357 < baseStart_2885357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885400 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 3, 3, 2]
def baseStart_2885400 : Nat := 118140960795 + 2885400 * 2 ^ 59
def prefixEnd_2885400 : Nat := 4983230072969 + 3 ^ 40 * 2885400 * 2
def baseEnd_2885400 : Nat := 1481597080483116092930293

theorem tailTrace_2885400 : CollatzResearch.WordTrace tailWord_2885400 prefixEnd_2885400 1481597080483116092930293 := by
  unfold tailWord_2885400
  simp only [CollatzResearch.WordTrace]
  refine ⟨52619591873348030966162827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70159455831130707954883769 52619591873348030966162827)
  ·
    refine ⟨78929387810022046449244241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52619591873348030966162827 78929387810022046449244241)
    ·
      refine ⟨59197040857516534836933181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78929387810022046449244241 59197040857516534836933181)
      ·
        refine ⟨22198890321568700563849943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59197040857516534836933181 22198890321568700563849943)
        ·
          refine ⟨33298335482353050845774915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22198890321568700563849943 33298335482353050845774915)
          ·
            refine ⟨49947503223529576268662373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33298335482353050845774915 49947503223529576268662373)
            ·
              refine ⟨9365156854411795550374195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49947503223529576268662373 9365156854411795550374195)
              ·
                refine ⟨14047735281617693325561293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9365156854411795550374195 14047735281617693325561293)
                ·
                  refine ⟨5267900730606634997085485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14047735281617693325561293 5267900730606634997085485)
                  ·
                    refine ⟨1975462773977488123907057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5267900730606634997085485 1975462773977488123907057)
                    ·
                      refine ⟨1481597080483116092930293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1975462773977488123907057 1481597080483116092930293)
                      ·
                        rfl

theorem cell23_2885400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_2885400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885400 prefixEnd_2885400 := by exact prefixLift 2885400
  have htrace : WordTrace (prefixWord ++ tailWord_2885400) baseStart_2885400 baseEnd_2885400 := by
    simpa [prefixWord, tailWord_2885400, baseEnd_2885400] using wordTrace_append hprefix tailTrace_2885400
  have hstable : (prefixWord ++ tailWord_2885400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885400).length < 2 ^ (prefixWord ++ tailWord_2885400).sum := by decide
  have hdescent : baseEnd_2885400 < baseStart_2885400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885443 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 4]
def baseStart_2885443 : Nat := 118140960795 + 2885443 * 2 ^ 59
def prefixEnd_2885443 : Nat := 4983230072969 + 3 ^ 40 * 2885443 * 2
def baseEnd_2885443 : Nat := 1481619160151259424692595

theorem tailTrace_2885443 : CollatzResearch.WordTrace tailWord_2885443 prefixEnd_2885443 1481619160151259424692595 := by
  unfold tailWord_2885443
  simp only [CollatzResearch.WordTrace]
  refine ⟨105240752085540280276140983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70160501390360186850760655 105240752085540280276140983)
  ·
    refine ⟨157861128128310420414211475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105240752085540280276140983 157861128128310420414211475)
    ·
      refine ⟨236791692192465630621317213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157861128128310420414211475 236791692192465630621317213)
      ·
        refine ⟨88796884572174611482993955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236791692192465630621317213 88796884572174611482993955)
        ·
          refine ⟨133195326858261917224490933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88796884572174611482993955 133195326858261917224490933)
          ·
            refine ⟨12487061892962054739796025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133195326858261917224490933 12487061892962054739796025)
            ·
              refine ⟨9365296419721541054847019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12487061892962054739796025 9365296419721541054847019)
              ·
                refine ⟨14047944629582311582270529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9365296419721541054847019 14047944629582311582270529)
                ·
                  refine ⟨10535958472186733686702897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14047944629582311582270529 10535958472186733686702897)
                  ·
                    refine ⟨7901968854140050265027173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10535958472186733686702897 7901968854140050265027173)
                    ·
                      refine ⟨1481619160151259424692595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7901968854140050265027173 1481619160151259424692595)
                      ·
                        rfl

theorem cell23_2885443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_2885443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885443 prefixEnd_2885443 := by exact prefixLift 2885443
  have htrace : WordTrace (prefixWord ++ tailWord_2885443) baseStart_2885443 baseEnd_2885443 := by
    simpa [prefixWord, tailWord_2885443, baseEnd_2885443] using wordTrace_append hprefix tailTrace_2885443
  have hstable : (prefixWord ++ tailWord_2885443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885443).length < 2 ^ (prefixWord ++ tailWord_2885443).sum := by decide
  have hdescent : baseEnd_2885443 < baseStart_2885443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885447 : List Nat := [1, 1, 4, 1, 2, 1, 2, 5, 2, 2, 2]
def baseStart_2885447 : Nat := 118140960795 + 2885447 * 2 ^ 59
def prefixEnd_2885447 : Nat := 4983230072969 + 3 ^ 40 * 2885447 * 2
def baseEnd_2885447 : Nat := 1481621214073877409042577

theorem tailTrace_2885447 : CollatzResearch.WordTrace tailWord_2885447 prefixEnd_2885447 1481621214073877409042577 := by
  unfold tailWord_2885447
  simp only [CollatzResearch.WordTrace]
  refine ⟨105240897977525788959286595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70160598651683859306191063 105240897977525788959286595)
  ·
    refine ⟨157861346966288683438929893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105240897977525788959286595 157861346966288683438929893)
    ·
      refine ⟨29599002556179128144799355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157861346966288683438929893 29599002556179128144799355)
      ·
        refine ⟨44398503834268692217199033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29599002556179128144799355 44398503834268692217199033)
        ·
          refine ⟨33298877875701519162899275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44398503834268692217199033 33298877875701519162899275)
          ·
            refine ⟨49948316813552278744348913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33298877875701519162899275 49948316813552278744348913)
            ·
              refine ⟨37461237610164209058261685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49948316813552278744348913 37461237610164209058261685)
              ·
                refine ⟨3511991025952894599212033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37461237610164209058261685 3511991025952894599212033)
                ·
                  refine ⟨2633993269464670949409025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3511991025952894599212033 2633993269464670949409025)
                  ·
                    refine ⟨1975494952098503212056769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2633993269464670949409025 1975494952098503212056769)
                    ·
                      refine ⟨1481621214073877409042577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1975494952098503212056769 1481621214073877409042577)
                      ·
                        rfl

theorem cell23_2885447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_2885447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885447 prefixEnd_2885447 := by exact prefixLift 2885447
  have htrace : WordTrace (prefixWord ++ tailWord_2885447) baseStart_2885447 baseEnd_2885447 := by
    simpa [prefixWord, tailWord_2885447, baseEnd_2885447] using wordTrace_append hprefix tailTrace_2885447
  have hstable : (prefixWord ++ tailWord_2885447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885447).length < 2 ^ (prefixWord ++ tailWord_2885447).sum := by decide
  have hdescent : baseEnd_2885447 < baseStart_2885447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885490 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 2, 5, 2]
def baseStart_2885490 : Nat := 118140960795 + 2885490 * 2 ^ 59
def prefixEnd_2885490 : Nat := 4983230072969 + 3 ^ 40 * 2885490 * 2
def baseEnd_2885490 : Nat := 1481643293742020740804879

theorem tailTrace_2885490 : CollatzResearch.WordTrace tailWord_2885490 prefixEnd_2885490 1481643293742020740804879 := by
  unfold tailWord_2885490
  simp only [CollatzResearch.WordTrace]
  refine ⟨26310616579092501825775481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70161644210913338202067949 26310616579092501825775481)
  ·
    refine ⟨19732962434319376369331611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26310616579092501825775481 19732962434319376369331611)
    ·
      refine ⟨29599443651479064553997417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19732962434319376369331611 29599443651479064553997417)
      ·
        refine ⟨22199582738609298415498063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29599443651479064553997417 22199582738609298415498063)
        ·
          refine ⟨33299374107913947623247095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22199582738609298415498063 33299374107913947623247095)
          ·
            refine ⟨49949061161870921434870643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33299374107913947623247095 49949061161870921434870643)
            ·
              refine ⟨74923591742806382152305965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49949061161870921434870643 74923591742806382152305965)
              ·
                refine ⟨28096346903552393307114737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74923591742806382152305965 28096346903552393307114737)
                ·
                  refine ⟨21072260177664294980336053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28096346903552393307114737 21072260177664294980336053)
                  ·
                    refine ⟨1975524391656027654406505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21072260177664294980336053 1975524391656027654406505)
                    ·
                      refine ⟨1481643293742020740804879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1975524391656027654406505 1481643293742020740804879)
                      ·
                        rfl

theorem cell23_2885490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_2885490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885490 prefixEnd_2885490 := by exact prefixLift 2885490
  have htrace : WordTrace (prefixWord ++ tailWord_2885490) baseStart_2885490 baseEnd_2885490 := by
    simpa [prefixWord, tailWord_2885490, baseEnd_2885490] using wordTrace_append hprefix tailTrace_2885490
  have hstable : (prefixWord ++ tailWord_2885490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885490).length < 2 ^ (prefixWord ++ tailWord_2885490).sum := by decide
  have hdescent : baseEnd_2885490 < baseStart_2885490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885503 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 4]
def baseStart_2885503 : Nat := 118140960795 + 2885503 * 2 ^ 59
def prefixEnd_2885503 : Nat := 4983230072969 + 3 ^ 40 * 2885503 * 2
def baseEnd_2885503 : Nat := 1481649968990529189942319

theorem tailTrace_2885503 : CollatzResearch.WordTrace tailWord_2885503 prefixEnd_2885503 1481649968990529189942319 := by
  unfold tailWord_2885503
  simp only [CollatzResearch.WordTrace]
  refine ⟨105242940465322910523325163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70161960310215273682216775 105242940465322910523325163)
  ·
    refine ⟨157864410697984365784987745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105242940465322910523325163 157864410697984365784987745)
    ·
      refine ⟨118398308023488274338740809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157864410697984365784987745 118398308023488274338740809)
      ·
        refine ⟨88798731017616205754055607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118398308023488274338740809 88798731017616205754055607)
        ·
          refine ⟨133198096526424308631083411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88798731017616205754055607 133198096526424308631083411)
          ·
            refine ⟨199797144789636462946625117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133198096526424308631083411 199797144789636462946625117)
            ·
              refine ⟨74923929296113673604984419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199797144789636462946625117 74923929296113673604984419)
              ·
                refine ⟨112385893944170510407476629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74923929296113673604984419 112385893944170510407476629)
                ·
                  refine ⟨5268088778632992675350467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112385893944170510407476629 5268088778632992675350467)
                  ·
                    refine ⟨7902133167949489013025701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5268088778632992675350467 7902133167949489013025701)
                    ·
                      refine ⟨1481649968990529189942319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7902133167949489013025701 1481649968990529189942319)
                      ·
                        rfl

theorem cell23_2885503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_2885503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885503 prefixEnd_2885503 := by exact prefixLift 2885503
  have htrace : WordTrace (prefixWord ++ tailWord_2885503) baseStart_2885503 baseEnd_2885503 := by
    simpa [prefixWord, tailWord_2885503, baseEnd_2885503] using wordTrace_append hprefix tailTrace_2885503
  have hstable : (prefixWord ++ tailWord_2885503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885503).length < 2 ^ (prefixWord ++ tailWord_2885503).sum := by decide
  have hdescent : baseEnd_2885503 < baseStart_2885503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885523 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 3]
def baseStart_2885523 : Nat := 118140960795 + 2885523 * 2 ^ 59
def prefixEnd_2885523 : Nat := 4983230072969 + 3 ^ 40 * 2885523 * 2
def baseEnd_2885523 : Nat := 1481660238603619111692227

theorem tailTrace_2885523 : CollatzResearch.WordTrace tailWord_2885523 prefixEnd_2885523 1481660238603619111692227 := by
  unfold tailWord_2885523
  simp only [CollatzResearch.WordTrace]
  refine ⟨105243669925250453939053223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70162446616833635959368815 105243669925250453939053223)
  ·
    refine ⟨157865504887875680908579835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105243669925250453939053223 157865504887875680908579835)
    ·
      refine ⟨236798257331813521362869753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157865504887875680908579835 236798257331813521362869753)
      ·
        refine ⟨177598692998860141022152315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236798257331813521362869753 177598692998860141022152315)
        ·
          refine ⟨266398039498290211533228473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177598692998860141022152315 266398039498290211533228473)
          ·
            refine ⟨199798529623717658649921355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266398039498290211533228473 199798529623717658649921355)
            ·
              refine ⟨299697794435576487974882033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199798529623717658649921355 299697794435576487974882033)
              ·
                refine ⟨224773345826682365981161525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299697794435576487974882033 224773345826682365981161525)
                ·
                  refine ⟨21072501171251471810733893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 224773345826682365981161525 21072501171251471810733893)
                  ·
                    refine ⟨3951093969609650964512605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21072501171251471810733893 3951093969609650964512605)
                    ·
                      refine ⟨1481660238603619111692227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3951093969609650964512605 1481660238603619111692227)
                      ·
                        rfl

theorem cell23_2885523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 3].length) (baseStart_2885523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885523 prefixEnd_2885523 := by exact prefixLift 2885523
  have htrace : WordTrace (prefixWord ++ tailWord_2885523) baseStart_2885523 baseEnd_2885523 := by
    simpa [prefixWord, tailWord_2885523, baseEnd_2885523] using wordTrace_append hprefix tailTrace_2885523
  have hstable : (prefixWord ++ tailWord_2885523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885523).length < 2 ^ (prefixWord ++ tailWord_2885523).sum := by decide
  have hdescent : baseEnd_2885523 < baseStart_2885523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885564 : List Nat := [2, 2, 2, 5, 1, 1, 1, 2, 3, 4]
def baseStart_2885564 : Nat := 118140960795 + 2885564 * 2 ^ 59
def prefixEnd_2885564 : Nat := 4983230072969 + 3 ^ 40 * 2885564 * 2
def baseEnd_2885564 : Nat := 493893763770151150426513

theorem tailTrace_2885564 : CollatzResearch.WordTrace tailWord_2885564 prefixEnd_2885564 493893763770151150426513 := by
  unfold tailWord_2885564
  simp only [CollatzResearch.WordTrace]
  refine ⟨52622582659050958970647873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70163443545401278627530497 52622582659050958970647873)
  ·
    refine ⟨39466936994288219227985905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52622582659050958970647873 39466936994288219227985905)
    ·
      refine ⟨29600202745716164420989429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39466936994288219227985905 29600202745716164420989429)
      ·
        refine ⟨2775019007410890414467759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29600202745716164420989429 2775019007410890414467759)
        ·
          refine ⟨4162528511116335621701639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2775019007410890414467759 4162528511116335621701639)
          ·
            refine ⟨6243792766674503432552459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4162528511116335621701639 6243792766674503432552459)
            ·
              refine ⟨9365689150011755148828689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6243792766674503432552459 9365689150011755148828689)
              ·
                refine ⟨7024266862508816361621517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9365689150011755148828689 7024266862508816361621517)
                ·
                  refine ⟨2634100073440806135608069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7024266862508816361621517 2634100073440806135608069)
                  ·
                    refine ⟨493893763770151150426513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2634100073440806135608069 493893763770151150426513)
                    ·
                      rfl

theorem cell23_2885564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_2885564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885564 prefixEnd_2885564 := by exact prefixLift 2885564
  have htrace : WordTrace (prefixWord ++ tailWord_2885564) baseStart_2885564 baseEnd_2885564 := by
    simpa [prefixWord, tailWord_2885564, baseEnd_2885564] using wordTrace_append hprefix tailTrace_2885564
  have hstable : (prefixWord ++ tailWord_2885564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885564).length < 2 ^ (prefixWord ++ tailWord_2885564).sum := by decide
  have hdescent : baseEnd_2885564 < baseStart_2885564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885594 : List Nat := [3, 1, 1, 2, 6, 1, 1, 2, 6]
def baseStart_2885594 : Nat := 118140960795 + 2885594 * 2 ^ 59
def prefixEnd_2885594 : Nat := 4983230072969 + 3 ^ 40 * 2885594 * 2
def baseEnd_2885594 : Nat := 164632966192232037100489

theorem tailTrace_2885594 : CollatzResearch.WordTrace tailWord_2885594 prefixEnd_2885594 164632966192232037100489 := by
  unfold tailWord_2885594
  simp only [CollatzResearch.WordTrace]
  refine ⟨26311564876998308266221959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70164173005328822043258557 26311564876998308266221959)
  ·
    refine ⟨39467347315497462399332939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26311564876998308266221959 39467347315497462399332939)
    ·
      refine ⟨59201020973246193598999409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39467347315497462399332939 59201020973246193598999409)
      ·
        refine ⟨44400765729934645199249557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59201020973246193598999409 44400765729934645199249557)
        ·
          refine ⟨2081285893590686493714823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44400765729934645199249557 2081285893590686493714823)
          ·
            refine ⟨3121928840386029740572235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2081285893590686493714823 3121928840386029740572235)
            ·
              refine ⟨4682893260579044610858353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3121928840386029740572235 4682893260579044610858353)
              ·
                refine ⟨3512169945434283458143765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4682893260579044610858353 3512169945434283458143765)
                ·
                  refine ⟨164632966192232037100489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3512169945434283458143765 164632966192232037100489)
                  ·
                    rfl

theorem cell23_2885594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 6].length) (baseStart_2885594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885594 prefixEnd_2885594 := by exact prefixLift 2885594
  have htrace : WordTrace (prefixWord ++ tailWord_2885594) baseStart_2885594 baseEnd_2885594 := by
    simpa [prefixWord, tailWord_2885594, baseEnd_2885594] using wordTrace_append hprefix tailTrace_2885594
  have hstable : (prefixWord ++ tailWord_2885594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885594).length < 2 ^ (prefixWord ++ tailWord_2885594).sum := by decide
  have hdescent : baseEnd_2885594 < baseStart_2885594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885604 : List Nat := [2, 3, 1, 1, 1, 1, 3, 6, 1, 1, 3]
def baseStart_2885604 : Nat := 118140960795 + 2885604 * 2 ^ 59
def prefixEnd_2885604 : Nat := 4983230072969 + 3 ^ 40 * 2885604 * 2
def baseEnd_2885604 : Nat := 1481701830536633294779355

theorem tailTrace_2885604 : CollatzResearch.WordTrace tailWord_2885604 prefixEnd_2885604 1481701830536633294779355 := by
  unfold tailWord_2885604
  simp only [CollatzResearch.WordTrace]
  refine ⟨52623312118978502386375933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70164416158638003181834577 52623312118978502386375933)
  ·
    refine ⟨19733742044616938394890975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52623312118978502386375933 19733742044616938394890975)
    ·
      refine ⟨29600613066925407592336463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19733742044616938394890975 29600613066925407592336463)
      ·
        refine ⟨44400919600388111388504695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29600613066925407592336463 44400919600388111388504695)
        ·
          refine ⟨66601379400582167082757043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44400919600388111388504695 66601379400582167082757043)
          ·
            refine ⟨99902069100873250624135565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66601379400582167082757043 99902069100873250624135565)
            ·
              refine ⟨37463275912827468984050837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99902069100873250624135565 37463275912827468984050837)
              ·
                refine ⟨1756091058413787608627383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37463275912827468984050837 1756091058413787608627383)
                ·
                  refine ⟨2634136587620681412941075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1756091058413787608627383 2634136587620681412941075)
                  ·
                    refine ⟨3951204881431022119411613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2634136587620681412941075 3951204881431022119411613)
                    ·
                      refine ⟨1481701830536633294779355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3951204881431022119411613 1481701830536633294779355)
                      ·
                        rfl

theorem cell23_2885604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 1, 1, 3].length) (baseStart_2885604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885604 prefixEnd_2885604 := by exact prefixLift 2885604
  have htrace : WordTrace (prefixWord ++ tailWord_2885604) baseStart_2885604 baseEnd_2885604 := by
    simpa [prefixWord, tailWord_2885604, baseEnd_2885604] using wordTrace_append hprefix tailTrace_2885604
  have hstable : (prefixWord ++ tailWord_2885604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885604).length < 2 ^ (prefixWord ++ tailWord_2885604).sum := by decide
  have hdescent : baseEnd_2885604 < baseStart_2885604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885640 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_2885640 : Nat := 118140960795 + 2885640 * 2 ^ 59
def prefixEnd_2885640 : Nat := 4983230072969 + 3 ^ 40 * 2885640 * 2
def baseEnd_2885640 : Nat := 1481720315840195153929189

theorem tailTrace_2885640 : CollatzResearch.WordTrace tailWord_2885640 prefixEnd_2885640 1481720315840195153929189 := by
  unfold tailWord_2885640
  simp only [CollatzResearch.WordTrace]
  refine ⟨52623968632913291460531187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70165291510551055280708249 52623968632913291460531187)
  ·
    refine ⟨78935952949369937190796781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52623968632913291460531187 78935952949369937190796781)
    ·
      refine ⟨29600982356013726446548793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78935952949369937190796781 29600982356013726446548793)
      ·
        refine ⟨22200736767010294834911595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29600982356013726446548793 22200736767010294834911595)
        ·
          refine ⟨33301105150515442252367393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22200736767010294834911595 33301105150515442252367393)
          ·
            refine ⟨24975828862886581689275545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33301105150515442252367393 24975828862886581689275545)
            ·
              refine ⟨18731871647164936266956659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24975828862886581689275545 18731871647164936266956659)
              ·
                refine ⟨28097807470747404400434989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18731871647164936266956659 28097807470747404400434989)
                ·
                  refine ⟨10536677801530276650163121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28097807470747404400434989 10536677801530276650163121)
                  ·
                    refine ⟨7902508351147707487622341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10536677801530276650163121 7902508351147707487622341)
                    ·
                      refine ⟨1481720315840195153929189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7902508351147707487622341 1481720315840195153929189)
                      ·
                        rfl

theorem cell23_2885640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_2885640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885640 prefixEnd_2885640 := by exact prefixLift 2885640
  have htrace : WordTrace (prefixWord ++ tailWord_2885640) baseStart_2885640 baseEnd_2885640 := by
    simpa [prefixWord, tailWord_2885640, baseEnd_2885640] using wordTrace_append hprefix tailTrace_2885640
  have hstable : (prefixWord ++ tailWord_2885640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885640).length < 2 ^ (prefixWord ++ tailWord_2885640).sum := by decide
  have hdescent : baseEnd_2885640 < baseStart_2885640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885661 : List Nat := [1, 4, 2, 2, 2, 1, 3, 1, 3, 2, 2]
def baseStart_2885661 : Nat := 118140960795 + 2885661 * 2 ^ 59
def prefixEnd_2885661 : Nat := 4983230072969 + 3 ^ 40 * 2885661 * 2
def baseEnd_2885661 : Nat := 1481731098933939571766593

theorem tailTrace_2885661 : CollatzResearch.WordTrace tailWord_2885661 prefixEnd_2885661 1481731098933939571766593 := by
  unfold tailWord_2885661
  simp only [CollatzResearch.WordTrace]
  refine ⟨105248703198750503507576837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70165802132500335671717891 105248703198750503507576837)
  ·
    refine ⟨19734131849765719407670657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105248703198750503507576837 19734131849765719407670657)
    ·
      refine ⟨14800598887324289555752993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19734131849765719407670657 14800598887324289555752993)
      ·
        refine ⟨11100449165493217166814745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14800598887324289555752993 11100449165493217166814745)
        ·
          refine ⟨8325336874119912875111059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11100449165493217166814745 8325336874119912875111059)
          ·
            refine ⟨12488005311179869312666589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8325336874119912875111059 12488005311179869312666589)
            ·
              refine ⟨4683001991692450992249971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12488005311179869312666589 4683001991692450992249971)
              ·
                refine ⟨7024502987538676488374957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4683001991692450992249971 7024502987538676488374957)
                ·
                  refine ⟨2634188620327003683140609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7024502987538676488374957 2634188620327003683140609)
                  ·
                    refine ⟨1975641465245252762355457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2634188620327003683140609 1975641465245252762355457)
                    ·
                      refine ⟨1481731098933939571766593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1975641465245252762355457 1481731098933939571766593)
                      ·
                        rfl

theorem cell23_2885661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_2885661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885661 prefixEnd_2885661 := by exact prefixLift 2885661
  have htrace : WordTrace (prefixWord ++ tailWord_2885661) baseStart_2885661 baseEnd_2885661 := by
    simpa [prefixWord, tailWord_2885661, baseEnd_2885661] using wordTrace_append hprefix tailTrace_2885661
  have hstable : (prefixWord ++ tailWord_2885661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885661).length < 2 ^ (prefixWord ++ tailWord_2885661).sum := by decide
  have hdescent : baseEnd_2885661 < baseStart_2885661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885671 : List Nat := [1, 1, 7, 1, 2, 1, 1, 3, 2, 4]
def baseStart_2885671 : Nat := 118140960795 + 2885671 * 2 ^ 59
def prefixEnd_2885671 : Nat := 4983230072969 + 3 ^ 40 * 2885671 * 2
def baseEnd_2885671 : Nat := 493912077913494844213849

theorem tailTrace_2885671 : CollatzResearch.WordTrace tailWord_2885671 prefixEnd_2885671 493912077913494844213849 := by
  unfold tailWord_2885671
  simp only [CollatzResearch.WordTrace]
  refine ⟨105249067928714275215440867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70166045285809516810293911 105249067928714275215440867)
  ·
    refine ⟨157873601893071412823161301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105249067928714275215440867 157873601893071412823161301)
    ·
      refine ⟨3700162544368861238042843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 157873601893071412823161301 3700162544368861238042843)
      ·
        refine ⟨5550243816553291857064265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3700162544368861238042843 5550243816553291857064265)
        ·
          refine ⟨4162682862414968892798199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5550243816553291857064265 4162682862414968892798199)
          ·
            refine ⟨6244024293622453339197299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4162682862414968892798199 6244024293622453339197299)
            ·
              refine ⟨9366036440433680008795949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6244024293622453339197299 9366036440433680008795949)
              ·
                refine ⟨3512263665162630003298481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9366036440433680008795949 3512263665162630003298481)
                ·
                  refine ⟨2634197748871972502473861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3512263665162630003298481 2634197748871972502473861)
                  ·
                    refine ⟨493912077913494844213849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2634197748871972502473861 493912077913494844213849)
                    ·
                      rfl

theorem cell23_2885671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_2885671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885671 prefixEnd_2885671 := by exact prefixLift 2885671
  have htrace : WordTrace (prefixWord ++ tailWord_2885671) baseStart_2885671 baseEnd_2885671 := by
    simpa [prefixWord, tailWord_2885671, baseEnd_2885671] using wordTrace_append hprefix tailTrace_2885671
  have hstable : (prefixWord ++ tailWord_2885671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885671).length < 2 ^ (prefixWord ++ tailWord_2885671).sum := by decide
  have hdescent : baseEnd_2885671 < baseStart_2885671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885740 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 9]
def baseStart_2885740 : Nat := 118140960795 + 2885740 * 2 ^ 59
def prefixEnd_2885740 : Nat := 4983230072969 + 3 ^ 40 * 2885740 * 2
def baseEnd_2885740 : Nat := 164641295989516084742081

theorem tailTrace_2885740 : CollatzResearch.WordTrace tailWord_2885740 prefixEnd_2885740 164641295989516084742081 := by
  unfold tailWord_2885740
  simp only [CollatzResearch.WordTrace]
  refine ⟨52625792282732149999851337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70167723043642866666468449 52625792282732149999851337)
  ·
    refine ⟨39469344212049112499888503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52625792282732149999851337 39469344212049112499888503)
    ·
      refine ⟨59204016318073668749832755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39469344212049112499888503 59204016318073668749832755)
      ·
        refine ⟨88806024477110503124749133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59204016318073668749832755 88806024477110503124749133)
        ·
          refine ⟨33302259178916438671780925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88806024477110503124749133 33302259178916438671780925)
          ·
            refine ⟨12488347192093664501917847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33302259178916438671780925 12488347192093664501917847)
            ·
              refine ⟨18732520788140496752876771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12488347192093664501917847 18732520788140496752876771)
              ·
                refine ⟨28098781182210745129315157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18732520788140496752876771 28098781182210745129315157)
                ·
                  refine ⟨164641295989516084742081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28098781182210745129315157 164641295989516084742081)
                  ·
                    rfl

theorem cell23_2885740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 9].length) (baseStart_2885740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885740 prefixEnd_2885740 := by exact prefixLift 2885740
  have htrace : WordTrace (prefixWord ++ tailWord_2885740) baseStart_2885740 baseEnd_2885740 := by
    simpa [prefixWord, tailWord_2885740, baseEnd_2885740] using wordTrace_append hprefix tailTrace_2885740
  have hstable : (prefixWord ++ tailWord_2885740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885740).length < 2 ^ (prefixWord ++ tailWord_2885740).sum := by decide
  have hdescent : baseEnd_2885740 < baseStart_2885740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885767 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 3]
def baseStart_2885767 : Nat := 118140960795 + 2885767 * 2 ^ 59
def prefixEnd_2885767 : Nat := 4983230072969 + 3 ^ 40 * 2885767 * 2
def baseEnd_2885767 : Nat := 1481785527883316157041105

theorem tailTrace_2885767 : CollatzResearch.WordTrace tailWord_2885767 prefixEnd_2885767 1481785527883316157041105 := by
  unfold tailWord_2885767
  simp only [CollatzResearch.WordTrace]
  refine ⟨105252569336366483610935555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70168379557577655740623703 105252569336366483610935555)
  ·
    refine ⟨157878854004549725416403333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105252569336366483610935555 157878854004549725416403333)
    ·
      refine ⟨29602285125853073515575625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157878854004549725416403333 29602285125853073515575625)
      ·
        refine ⟨22201713844389805136681719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29602285125853073515575625 22201713844389805136681719)
        ·
          refine ⟨33302570766584707705022579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22201713844389805136681719 33302570766584707705022579)
          ·
            refine ⟨49953856149877061557533869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33302570766584707705022579 49953856149877061557533869)
            ·
              refine ⟨18732696056203898084075201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49953856149877061557533869 18732696056203898084075201)
              ·
                refine ⟨14049522042152923563056401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18732696056203898084075201 14049522042152923563056401)
                ·
                  refine ⟨10537141531614692672292301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14049522042152923563056401 10537141531614692672292301)
                  ·
                    refine ⟨3951428074355509752109613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10537141531614692672292301 3951428074355509752109613)
                    ·
                      refine ⟨1481785527883316157041105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3951428074355509752109613 1481785527883316157041105)
                      ·
                        rfl

theorem cell23_2885767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_2885767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885767 prefixEnd_2885767 := by exact prefixLift 2885767
  have htrace : WordTrace (prefixWord ++ tailWord_2885767) baseStart_2885767 baseEnd_2885767 := by
    simpa [prefixWord, tailWord_2885767, baseEnd_2885767] using wordTrace_append hprefix tailTrace_2885767
  have hstable : (prefixWord ++ tailWord_2885767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885767).length < 2 ^ (prefixWord ++ tailWord_2885767).sum := by decide
  have hdescent : baseEnd_2885767 < baseStart_2885767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885768 : List Nat := [2, 1, 3, 4, 1, 1, 3, 2, 2, 2, 2]
def baseStart_2885768 : Nat := 118140960795 + 2885768 * 2 ^ 59
def prefixEnd_2885768 : Nat := 4983230072969 + 3 ^ 40 * 2885768 * 2
def baseEnd_2885768 : Nat := 1481786041363970653128601

theorem tailTrace_2885768 : CollatzResearch.WordTrace tailWord_2885768 prefixEnd_2885768 1481786041363970653128601 := by
  unfold tailWord_2885768
  simp only [CollatzResearch.WordTrace]
  refine ⟨52626302904681430390860979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70168403872908573854481305 52626302904681430390860979)
  ·
    refine ⟨78939454357022145586291469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52626302904681430390860979 78939454357022145586291469)
    ·
      refine ⟨29602295383883304594859301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78939454357022145586291469 29602295383883304594859301)
      ·
        refine ⟨5550430384478119611536119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29602295383883304594859301 5550430384478119611536119)
        ·
          refine ⟨8325645576717179417304179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5550430384478119611536119 8325645576717179417304179)
          ·
            refine ⟨12488468365075769125956269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8325645576717179417304179 12488468365075769125956269)
            ·
              refine ⟨4683175636903413422233601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12488468365075769125956269 4683175636903413422233601)
              ·
                refine ⟨3512381727677560066675201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4683175636903413422233601 3512381727677560066675201)
                ·
                  refine ⟨2634286295758170050006401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3512381727677560066675201 2634286295758170050006401)
                  ·
                    refine ⟨1975714721818627537504801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2634286295758170050006401 1975714721818627537504801)
                    ·
                      refine ⟨1481786041363970653128601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1975714721818627537504801 1481786041363970653128601)
                      ·
                        rfl

theorem cell23_2885768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_2885768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885768 prefixEnd_2885768 := by exact prefixLift 2885768
  have htrace : WordTrace (prefixWord ++ tailWord_2885768) baseStart_2885768 baseEnd_2885768 := by
    simpa [prefixWord, tailWord_2885768, baseEnd_2885768] using wordTrace_append hprefix tailTrace_2885768
  have hstable : (prefixWord ++ tailWord_2885768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885768).length < 2 ^ (prefixWord ++ tailWord_2885768).sum := by decide
  have hdescent : baseEnd_2885768 < baseStart_2885768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885774 : List Nat := [4, 1, 1, 3, 3, 1, 2, 1, 7]
def baseStart_2885774 : Nat := 118140960795 + 2885774 * 2 ^ 59
def prefixEnd_2885774 : Nat := 4983230072969 + 3 ^ 40 * 2885774 * 2
def baseEnd_2885774 : Nat := 164643235805321958850397

theorem tailTrace_2885774 : CollatzResearch.WordTrace tailWord_2885774 prefixEnd_2885774 164643235805321958850397 := by
  unfold tailWord_2885774
  simp only [CollatzResearch.WordTrace]
  refine ⟨13156603080917640475805047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70168549764894082537626917 13156603080917640475805047)
  ·
    refine ⟨19734904621376460713707571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13156603080917640475805047 19734904621376460713707571)
    ·
      refine ⟨29602356932064691070561357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19734904621376460713707571 29602356932064691070561357)
      ·
        refine ⟨11100883849524259151460509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29602356932064691070561357 11100883849524259151460509)
        ·
          refine ⟨4162831443571597181797691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11100883849524259151460509 4162831443571597181797691)
          ·
            refine ⟨6244247165357395772696537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4162831443571597181797691 6244247165357395772696537)
            ·
              refine ⟨4683185374018046829522403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6244247165357395772696537 4683185374018046829522403)
              ·
                refine ⟨7024778061027070244283605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4683185374018046829522403 7024778061027070244283605)
                ·
                  refine ⟨164643235805321958850397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7024778061027070244283605 164643235805321958850397)
                  ·
                    rfl

theorem cell23_2885774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_2885774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885774 prefixEnd_2885774 := by exact prefixLift 2885774
  have htrace : WordTrace (prefixWord ++ tailWord_2885774) baseStart_2885774 baseEnd_2885774 := by
    simpa [prefixWord, tailWord_2885774, baseEnd_2885774] using wordTrace_append hprefix tailTrace_2885774
  have hstable : (prefixWord ++ tailWord_2885774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885774).length < 2 ^ (prefixWord ++ tailWord_2885774).sum := by decide
  have hdescent : baseEnd_2885774 < baseStart_2885774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885807 : List Nat := [1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 4]
def baseStart_2885807 : Nat := 118140960795 + 2885807 * 2 ^ 59
def prefixEnd_2885807 : Nat := 4983230072969 + 3 ^ 40 * 2885807 * 2
def baseEnd_2885807 : Nat := 1481806067109496000540921

theorem tailTrace_2885807 : CollatzResearch.WordTrace tailWord_2885807 prefixEnd_2885807 1481806067109496000540921 := by
  unfold tailWord_2885807
  simp only [CollatzResearch.WordTrace]
  refine ⟨105254028256221570442391675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70169352170814380294927783 105254028256221570442391675)
  ·
    refine ⟨157881042384332355663587513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105254028256221570442391675 157881042384332355663587513)
    ·
      refine ⟨118410781788249266747690635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157881042384332355663587513 118410781788249266747690635)
      ·
        refine ⟨177616172682373900121535953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118410781788249266747690635 177616172682373900121535953)
        ·
          refine ⟨133212129511780425091151965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177616172682373900121535953 133212129511780425091151965)
          ·
            refine ⟨49954548566917659409181987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133212129511780425091151965 49954548566917659409181987)
            ·
              refine ⟨74931822850376489113772981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49954548566917659409181987 74931822850376489113772981)
              ·
                refine ⟨7024858392222795854416217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74931822850376489113772981 7024858392222795854416217)
                ·
                  refine ⟨5268643794167096890812163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7024858392222795854416217 5268643794167096890812163)
                  ·
                    refine ⟨7902965691250645336218245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5268643794167096890812163 7902965691250645336218245)
                    ·
                      refine ⟨1481806067109496000540921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7902965691250645336218245 1481806067109496000540921)
                      ·
                        rfl

theorem cell23_2885807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 4].length) (baseStart_2885807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885807 prefixEnd_2885807 := by exact prefixLift 2885807
  have htrace : WordTrace (prefixWord ++ tailWord_2885807) baseStart_2885807 baseEnd_2885807 := by
    simpa [prefixWord, tailWord_2885807, baseEnd_2885807] using wordTrace_append hprefix tailTrace_2885807
  have hstable : (prefixWord ++ tailWord_2885807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885807).length < 2 ^ (prefixWord ++ tailWord_2885807).sum := by decide
  have hdescent : baseEnd_2885807 < baseStart_2885807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885824 : List Nat := [2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 4]
def baseStart_2885824 : Nat := 118140960795 + 2885824 * 2 ^ 59
def prefixEnd_2885824 : Nat := 4983230072969 + 3 ^ 40 * 2885824 * 2
def baseEnd_2885824 : Nat := 1481814796280622434028343

theorem tailTrace_2885824 : CollatzResearch.WordTrace tailWord_2885824 prefixEnd_2885824 1481814796280622434028343 := by
  unfold tailWord_2885824
  simp only [CollatzResearch.WordTrace]
  refine ⟨52627324148579991172880263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70169765531439988230507017 52627324148579991172880263)
  ·
    refine ⟨78940986222869986759320395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52627324148579991172880263 78940986222869986759320395)
    ·
      refine ⟨118411479334304980138980593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78940986222869986759320395 118411479334304980138980593)
      ·
        refine ⟨88808609500728735104235445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118411479334304980138980593 88808609500728735104235445)
        ·
          refine ⟨8325807140693318916022073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88808609500728735104235445 8325807140693318916022073)
          ·
            refine ⟨6244355355519989187016555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8325807140693318916022073 6244355355519989187016555)
            ·
              refine ⟨9366533033279983780524833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6244355355519989187016555 9366533033279983780524833)
              ·
                refine ⟨7024899774959987835393625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9366533033279983780524833 7024899774959987835393625)
                ·
                  refine ⟨5268674831219990876545219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7024899774959987835393625 5268674831219990876545219)
                  ·
                    refine ⟨7903012246829986314817829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5268674831219990876545219 7903012246829986314817829)
                    ·
                      refine ⟨1481814796280622434028343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7903012246829986314817829 1481814796280622434028343)
                      ·
                        rfl

theorem cell23_2885824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_2885824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885824 prefixEnd_2885824 := by exact prefixLift 2885824
  have htrace : WordTrace (prefixWord ++ tailWord_2885824) baseStart_2885824 baseEnd_2885824 := by
    simpa [prefixWord, tailWord_2885824, baseEnd_2885824] using wordTrace_append hprefix tailTrace_2885824
  have hstable : (prefixWord ++ tailWord_2885824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885824).length < 2 ^ (prefixWord ++ tailWord_2885824).sum := by decide
  have hdescent : baseEnd_2885824 < baseStart_2885824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885861 : List Nat := [1, 3, 1, 4, 2, 2, 2, 1, 2, 2, 3]
def baseStart_2885861 : Nat := 118140960795 + 2885861 * 2 ^ 59
def prefixEnd_2885861 : Nat := 4983230072969 + 3 ^ 40 * 2885861 * 2
def baseEnd_2885861 : Nat := 1481833795064838789265673

theorem tailTrace_2885861 : CollatzResearch.WordTrace tailWord_2885861 prefixEnd_2885861 1481833795064838789265673 := by
  unfold tailWord_2885861
  simp only [CollatzResearch.WordTrace]
  refine ⟨105255997798025937664857437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70170665198683958443238291 105255997798025937664857437)
  ·
    refine ⟨39470999174259726624321539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105255997798025937664857437 39470999174259726624321539)
    ·
      refine ⟨59206498761389589936482309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39470999174259726624321539 59206498761389589936482309)
      ·
        refine ⟨11101218517760548113090433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59206498761389589936482309 11101218517760548113090433)
        ·
          refine ⟨8325913888320411084817825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11101218517760548113090433 8325913888320411084817825)
          ·
            refine ⟨6244435416240308313613369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8325913888320411084817825 6244435416240308313613369)
            ·
              refine ⟨4683326562180231235210027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6244435416240308313613369 4683326562180231235210027)
              ·
                refine ⟨7024989843270346852815041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4683326562180231235210027 7024989843270346852815041)
                ·
                  refine ⟨5268742382452760139611281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7024989843270346852815041 5268742382452760139611281)
                  ·
                    refine ⟨3951556786839570104708461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5268742382452760139611281 3951556786839570104708461)
                    ·
                      refine ⟨1481833795064838789265673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3951556786839570104708461 1481833795064838789265673)
                      ·
                        rfl

theorem cell23_2885861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_2885861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885861 prefixEnd_2885861 := by exact prefixLift 2885861
  have htrace : WordTrace (prefixWord ++ tailWord_2885861) baseStart_2885861 baseEnd_2885861 := by
    simpa [prefixWord, tailWord_2885861, baseEnd_2885861] using wordTrace_append hprefix tailTrace_2885861
  have hstable : (prefixWord ++ tailWord_2885861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885861).length < 2 ^ (prefixWord ++ tailWord_2885861).sum := by decide
  have hdescent : baseEnd_2885861 < baseStart_2885861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885924 : List Nat := [2, 3, 1, 3, 1, 2, 2, 2, 1, 6]
def baseStart_2885924 : Nat := 118140960795 + 2885924 * 2 ^ 59
def prefixEnd_2885924 : Nat := 4983230072969 + 3 ^ 40 * 2885924 * 2
def baseEnd_2885924 : Nat := 493955381448690680925961

theorem tailTrace_2885924 : CollatzResearch.WordTrace tailWord_2885924 prefixEnd_2885924 493955381448690680925961 := by
  unfold tailWord_2885924
  simp only [CollatzResearch.WordTrace]
  refine ⟨52629147798398849712200413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70172197064531799616267217 52629147798398849712200413)
  ·
    refine ⟨19735930424399568642075155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52629147798398849712200413 19735930424399568642075155)
    ·
      refine ⟨29603895636599352963112733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19735930424399568642075155 29603895636599352963112733)
      ·
        refine ⟨11101460863724757361167275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29603895636599352963112733 11101460863724757361167275)
        ·
          refine ⟨16652191295587136041750913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11101460863724757361167275 16652191295587136041750913)
          ·
            refine ⟨12489143471690352031313185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16652191295587136041750913 12489143471690352031313185)
            ·
              refine ⟨9366857603767764023484889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12489143471690352031313185 9366857603767764023484889)
              ·
                refine ⟨7025143202825823017613667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9366857603767764023484889 7025143202825823017613667)
                ·
                  refine ⟨10537714804238734526420501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7025143202825823017613667 10537714804238734526420501)
                  ·
                    refine ⟨493955381448690680925961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10537714804238734526420501 493955381448690680925961)
                    ·
                      rfl

theorem cell23_2885924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_2885924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885924 prefixEnd_2885924 := by exact prefixLift 2885924
  have htrace : WordTrace (prefixWord ++ tailWord_2885924) baseStart_2885924 baseEnd_2885924 := by
    simpa [prefixWord, tailWord_2885924, baseEnd_2885924] using wordTrace_append hprefix tailTrace_2885924
  have hstable : (prefixWord ++ tailWord_2885924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885924).length < 2 ^ (prefixWord ++ tailWord_2885924).sum := by decide
  have hdescent : baseEnd_2885924 < baseStart_2885924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885925 : List Nat := [1, 3, 1, 2, 5, 1, 2, 3, 1, 1, 3]
def baseStart_2885925 : Nat := 118140960795 + 2885925 * 2 ^ 59
def prefixEnd_2885925 : Nat := 4983230072969 + 3 ^ 40 * 2885925 * 2
def baseEnd_2885925 : Nat := 1481866657826726538865379

theorem tailTrace_2885925 : CollatzResearch.WordTrace tailWord_2885925 prefixEnd_2885925 1481866657826726538865379 := by
  unfold tailWord_2885925
  simp only [CollatzResearch.WordTrace]
  refine ⟨105258332069794076595187229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70172221379862717730124819 105258332069794076595187229)
  ·
    refine ⟨39471874526172778723195211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105258332069794076595187229 39471874526172778723195211)
    ·
      refine ⟨59207811789259168084792817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39471874526172778723195211 59207811789259168084792817)
      ·
        refine ⟨44405858841944376063594613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59207811789259168084792817 44405858841944376063594613)
        ·
          refine ⟨4163049266432285255961995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44405858841944376063594613 4163049266432285255961995)
          ·
            refine ⟨6244573899648427883942993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4163049266432285255961995 6244573899648427883942993)
            ·
              refine ⟨4683430424736320912957245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6244573899648427883942993 4683430424736320912957245)
              ·
                refine ⟨1756286409276120342358967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4683430424736320912957245 1756286409276120342358967)
                ·
                  refine ⟨2634429613914180513538451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1756286409276120342358967 2634429613914180513538451)
                  ·
                    refine ⟨3951644420871270770307677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2634429613914180513538451 3951644420871270770307677)
                    ·
                      refine ⟨1481866657826726538865379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3951644420871270770307677 1481866657826726538865379)
                      ·
                        rfl

theorem cell23_2885925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 1, 1, 3].length) (baseStart_2885925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885925 prefixEnd_2885925 := by exact prefixLift 2885925
  have htrace : WordTrace (prefixWord ++ tailWord_2885925) baseStart_2885925 baseEnd_2885925 := by
    simpa [prefixWord, tailWord_2885925, baseEnd_2885925] using wordTrace_append hprefix tailTrace_2885925
  have hstable : (prefixWord ++ tailWord_2885925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885925).length < 2 ^ (prefixWord ++ tailWord_2885925).sum := by decide
  have hdescent : baseEnd_2885925 < baseStart_2885925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885948 : List Nat := [2, 2, 2, 2, 1, 2, 4, 1, 3, 2, 2]
def baseStart_2885948 : Nat := 118140960795 + 2885948 * 2 ^ 59
def prefixEnd_2885948 : Nat := 4983230072969 + 3 ^ 40 * 2885948 * 2
def baseEnd_2885948 : Nat := 1481878467881779948877773

theorem tailTrace_2885948 : CollatzResearch.WordTrace tailWord_2885948 prefixEnd_2885948 1481878467881779948877773 := by
  unfold tailWord_2885948
  simp only [CollatzResearch.WordTrace]
  refine ⟨52629585474355375761637249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70172780632473834348849665 52629585474355375761637249)
  ·
    refine ⟨39472189105766531821227937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52629585474355375761637249 39472189105766531821227937)
    ·
      refine ⟨29604141829324898865920953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39472189105766531821227937 29604141829324898865920953)
      ·
        refine ⟨22203106371993674149440715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29604141829324898865920953 22203106371993674149440715)
        ·
          refine ⟨33304659557990511224161073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22203106371993674149440715 33304659557990511224161073)
          ·
            refine ⟨24978494668492883418120805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33304659557990511224161073 24978494668492883418120805)
            ·
              refine ⟨4683467750342415640897651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24978494668492883418120805 4683467750342415640897651)
              ·
                refine ⟨7025201625513623461346477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4683467750342415640897651 7025201625513623461346477)
                ·
                  refine ⟨2634450609567608798004929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7025201625513623461346477 2634450609567608798004929)
                  ·
                    refine ⟨1975837957175706598503697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2634450609567608798004929 1975837957175706598503697)
                    ·
                      refine ⟨1481878467881779948877773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1975837957175706598503697 1481878467881779948877773)
                      ·
                        rfl

theorem cell23_2885948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_2885948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2885948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2885948 prefixEnd_2885948 := by exact prefixLift 2885948
  have htrace : WordTrace (prefixWord ++ tailWord_2885948) baseStart_2885948 baseEnd_2885948 := by
    simpa [prefixWord, tailWord_2885948, baseEnd_2885948] using wordTrace_append hprefix tailTrace_2885948
  have hstable : (prefixWord ++ tailWord_2885948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885948).length < 2 ^ (prefixWord ++ tailWord_2885948).sum := by decide
  have hdescent : baseEnd_2885948 < baseStart_2885948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886021 : List Nat := [1, 3, 1, 1, 3, 1, 1, 5, 1, 4, 2]
def baseStart_2886021 : Nat := 118140960795 + 2886021 * 2 ^ 59
def prefixEnd_2886021 : Nat := 4983230072969 + 3 ^ 40 * 2886021 * 2
def baseEnd_2886021 : Nat := 1481915951969558163264937

theorem tailTrace_2886021 : CollatzResearch.WordTrace tailWord_2886021 prefixEnd_2886021 1481915951969558163264937 := by
  unfold tailWord_2886021
  simp only [CollatzResearch.WordTrace]
  refine ⟨105261833477446284990681917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70174555651630856660454611 105261833477446284990681917)
  ·
    refine ⟨39473187554042356871505719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105261833477446284990681917 39473187554042356871505719)
    ·
      refine ⟨59209781331063535307258579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39473187554042356871505719 59209781331063535307258579)
      ·
        refine ⟨88814671996595302960887869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59209781331063535307258579 88814671996595302960887869)
        ·
          refine ⟨33305501998723238610332951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88814671996595302960887869 33305501998723238610332951)
          ·
            refine ⟨49958252998084857915499427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33305501998723238610332951 49958252998084857915499427)
            ·
              refine ⟨74937379497127286873249141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49958252998084857915499427 74937379497127286873249141)
              ·
                refine ⟨7025379327855683144367107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74937379497127286873249141 7025379327855683144367107)
                ·
                  refine ⟨10538068991783524716550661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7025379327855683144367107 10538068991783524716550661)
                  ·
                    refine ⟨1975887935959410884353249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10538068991783524716550661 1975887935959410884353249)
                    ·
                      refine ⟨1481915951969558163264937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1975887935959410884353249 1481915951969558163264937)
                      ·
                        rfl

theorem cell23_2886021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 4, 2].length) (baseStart_2886021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886021 prefixEnd_2886021 := by exact prefixLift 2886021
  have htrace : WordTrace (prefixWord ++ tailWord_2886021) baseStart_2886021 baseEnd_2886021 := by
    simpa [prefixWord, tailWord_2886021, baseEnd_2886021] using wordTrace_append hprefix tailTrace_2886021
  have hstable : (prefixWord ++ tailWord_2886021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886021).length < 2 ^ (prefixWord ++ tailWord_2886021).sum := by decide
  have hdescent : baseEnd_2886021 < baseStart_2886021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886024 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_2886024 : Nat := 118140960795 + 2886024 * 2 ^ 59
def prefixEnd_2886024 : Nat := 4983230072969 + 3 ^ 40 * 2886024 * 2
def baseEnd_2886024 : Nat := 1481917492411521651527423

theorem tailTrace_2886024 : CollatzResearch.WordTrace tailWord_2886024 prefixEnd_2886024 1481917492411521651527423 := by
  unfold tailWord_2886024
  simp only [CollatzResearch.WordTrace]
  refine ⟨52630971448217708251520563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70174628597623611002027417 52630971448217708251520563)
  ·
    refine ⟨78946457172326562377280845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52630971448217708251520563 78946457172326562377280845)
    ·
      refine ⟨29604921439622460891480317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78946457172326562377280845 29604921439622460891480317)
      ·
        refine ⟨11101845539858422834305119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29604921439622460891480317 11101845539858422834305119)
        ·
          refine ⟨16652768309787634251457679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11101845539858422834305119 16652768309787634251457679)
          ·
            refine ⟨24979152464681451377186519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16652768309787634251457679 24979152464681451377186519)
            ·
              refine ⟨37468728697022177065779779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24979152464681451377186519 37468728697022177065779779)
              ·
                refine ⟨56203093045533265598669669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37468728697022177065779779 56203093045533265598669669)
                ·
                  refine ⟨10538079946037487299750563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56203093045533265598669669 10538079946037487299750563)
                  ·
                    refine ⟨15807119919056230949625845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10538079946037487299750563 15807119919056230949625845)
                    ·
                      refine ⟨1481917492411521651527423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15807119919056230949625845 1481917492411521651527423)
                      ·
                        rfl

theorem cell23_2886024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_2886024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886024 prefixEnd_2886024 := by exact prefixLift 2886024
  have htrace : WordTrace (prefixWord ++ tailWord_2886024) baseStart_2886024 baseEnd_2886024 := by
    simpa [prefixWord, tailWord_2886024, baseEnd_2886024] using wordTrace_append hprefix tailTrace_2886024
  have hstable : (prefixWord ++ tailWord_2886024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886024).length < 2 ^ (prefixWord ++ tailWord_2886024).sum := by decide
  have hdescent : baseEnd_2886024 < baseStart_2886024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886025 : List Nat := [1, 2, 1, 1, 6, 3, 1, 2, 1, 3, 2]
def baseStart_2886025 : Nat := 118140960795 + 2886025 * 2 ^ 59
def prefixEnd_2886025 : Nat := 4983230072969 + 3 ^ 40 * 2886025 * 2
def baseEnd_2886025 : Nat := 1481918005892176147614919

theorem tailTrace_2886025 : CollatzResearch.WordTrace tailWord_2886025 prefixEnd_2886025 1481918005892176147614919 := by
  unfold tailWord_2886025
  simp only [CollatzResearch.WordTrace]
  refine ⟨105261979369431793673827529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70174652912954529115885019 105261979369431793673827529)
  ·
    refine ⟨78946484527073845255370647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105261979369431793673827529 78946484527073845255370647)
    ·
      refine ⟨118419726790610767883055971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78946484527073845255370647 118419726790610767883055971)
      ·
        refine ⟨177629590185916151824583957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118419726790610767883055971 177629590185916151824583957)
        ·
          refine ⟨8326387039964819616777373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 177629590185916151824583957 8326387039964819616777373)
          ·
            refine ⟨3122395139986807356291515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8326387039964819616777373 3122395139986807356291515)
            ·
              refine ⟨4683592709980211034437273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3122395139986807356291515 4683592709980211034437273)
              ·
                refine ⟨3512694532485158275827955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4683592709980211034437273 3512694532485158275827955)
                ·
                  refine ⟨5269041798727737413741933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3512694532485158275827955 5269041798727737413741933)
                  ·
                    refine ⟨1975890674522901530153225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5269041798727737413741933 1975890674522901530153225)
                    ·
                      refine ⟨1481918005892176147614919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1975890674522901530153225 1481918005892176147614919)
                      ·
                        rfl

theorem cell23_2886025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 3, 2].length) (baseStart_2886025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886025 prefixEnd_2886025 := by exact prefixLift 2886025
  have htrace : WordTrace (prefixWord ++ tailWord_2886025) baseStart_2886025 baseEnd_2886025 := by
    simpa [prefixWord, tailWord_2886025, baseEnd_2886025] using wordTrace_append hprefix tailTrace_2886025
  have hstable : (prefixWord ++ tailWord_2886025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886025).length < 2 ^ (prefixWord ++ tailWord_2886025).sum := by decide
  have hdescent : baseEnd_2886025 < baseStart_2886025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886055 : List Nat := [1, 1, 6, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_2886055 : Nat := 118140960795 + 2886055 * 2 ^ 59
def prefixEnd_2886055 : Nat := 4983230072969 + 3 ^ 40 * 2886055 * 2
def baseEnd_2886055 : Nat := 1481933410311811030239781

theorem tailTrace_2886055 : CollatzResearch.WordTrace tailWord_2886055 prefixEnd_2886055 1481933410311811030239781 := by
  unfold tailWord_2886055
  simp only [CollatzResearch.WordTrace]
  refine ⟨105263073559323108797419619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70175382372882072531613079 105263073559323108797419619)
  ·
    refine ⟨157894610338984663196129429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105263073559323108797419619 157894610338984663196129429)
    ·
      refine ⟨7401309859639906087318567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 157894610338984663196129429 7401309859639906087318567)
      ·
        refine ⟨11101964789459859130977851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7401309859639906087318567 11101964789459859130977851)
        ·
          refine ⟨16652947184189788696466777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11101964789459859130977851 16652947184189788696466777)
          ·
            refine ⟨12489710388142341522350083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16652947184189788696466777 12489710388142341522350083)
            ·
              refine ⟨18734565582213512283525125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12489710388142341522350083 18734565582213512283525125)
              ·
                refine ⟨3512731046665033553160961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18734565582213512283525125 3512731046665033553160961)
                ·
                  refine ⟨2634548284998775164870721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3512731046665033553160961 2634548284998775164870721)
                  ·
                    refine ⟨1975911213749081373653041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2634548284998775164870721 1975911213749081373653041)
                    ·
                      refine ⟨1481933410311811030239781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1975911213749081373653041 1481933410311811030239781)
                      ·
                        rfl

theorem cell23_2886055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_2886055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886055 prefixEnd_2886055 := by exact prefixLift 2886055
  have htrace : WordTrace (prefixWord ++ tailWord_2886055) baseStart_2886055 baseEnd_2886055 := by
    simpa [prefixWord, tailWord_2886055, baseEnd_2886055] using wordTrace_append hprefix tailTrace_2886055
  have hstable : (prefixWord ++ tailWord_2886055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886055).length < 2 ^ (prefixWord ++ tailWord_2886055).sum := by decide
  have hdescent : baseEnd_2886055 < baseStart_2886055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886071 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 3]
def baseStart_2886071 : Nat := 118140960795 + 2886071 * 2 ^ 59
def prefixEnd_2886071 : Nat := 4983230072969 + 3 ^ 40 * 2886071 * 2
def baseEnd_2886071 : Nat := 1481941626002282967639707

theorem tailTrace_2886071 : CollatzResearch.WordTrace tailWord_2886071 prefixEnd_2886071 1481941626002282967639707 := by
  unfold tailWord_2886071
  simp only [CollatzResearch.WordTrace]
  refine ⟨105263657127265143530002067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70175771418176762353334711 105263657127265143530002067)
  ·
    refine ⟨157895485690897715295003101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105263657127265143530002067 157895485690897715295003101)
    ·
      refine ⟨59210807134086643235626163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157895485690897715295003101 59210807134086643235626163)
      ·
        refine ⟨88816210701129964853439245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59210807134086643235626163 88816210701129964853439245)
        ·
          refine ⟨33306079012923736820039717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88816210701129964853439245 33306079012923736820039717)
          ·
            refine ⟨6244889814923200653757447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33306079012923736820039717 6244889814923200653757447)
            ·
              refine ⟨9367334722384800980636171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6244889814923200653757447 9367334722384800980636171)
              ·
                refine ⟨14051002083577201470954257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9367334722384800980636171 14051002083577201470954257)
                ·
                  refine ⟨10538251562682901103215693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14051002083577201470954257 10538251562682901103215693)
                  ·
                    refine ⟨3951844336006087913705885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10538251562682901103215693 3951844336006087913705885)
                    ·
                      refine ⟨1481941626002282967639707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3951844336006087913705885 1481941626002282967639707)
                      ·
                        rfl

theorem cell23_2886071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_2886071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886071 prefixEnd_2886071 := by exact prefixLift 2886071
  have htrace : WordTrace (prefixWord ++ tailWord_2886071) baseStart_2886071 baseEnd_2886071 := by
    simpa [prefixWord, tailWord_2886071, baseEnd_2886071] using wordTrace_append hprefix tailTrace_2886071
  have hstable : (prefixWord ++ tailWord_2886071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886071).length < 2 ^ (prefixWord ++ tailWord_2886071).sum := by decide
  have hdescent : baseEnd_2886071 < baseStart_2886071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886074 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 4, 5]
def baseStart_2886074 : Nat := 118140960795 + 2886074 * 2 ^ 59
def prefixEnd_2886074 : Nat := 4983230072969 + 3 ^ 40 * 2886074 * 2
def baseEnd_2886074 : Nat := 493981055481415485300731

theorem tailTrace_2886074 : CollatzResearch.WordTrace tailWord_2886074 prefixEnd_2886074 493981055481415485300731 := by
  unfold tailWord_2886074
  simp only [CollatzResearch.WordTrace]
  refine ⟨26315941636563568760590319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70175844364169516694907517 26315941636563568760590319)
  ·
    refine ⟨39473912454845353140885479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26315941636563568760590319 39473912454845353140885479)
    ·
      refine ⟨59210868682268029711328219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39473912454845353140885479 59210868682268029711328219)
      ·
        refine ⟨88816303023402044566992329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59210868682268029711328219 88816303023402044566992329)
        ·
          refine ⟨66612227267551533425244247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88816303023402044566992329 66612227267551533425244247)
          ·
            refine ⟨99918340901327300137866371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66612227267551533425244247 99918340901327300137866371)
            ·
              refine ⟨149877511351990950206799557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99918340901327300137866371 149877511351990950206799557)
              ·
                refine ⟨28102033378498303163774917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149877511351990950206799557 28102033378498303163774917)
                ·
                  refine ⟨5269131258468431843207797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28102033378498303163774917 5269131258468431843207797)
                  ·
                    refine ⟨493981055481415485300731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5269131258468431843207797 493981055481415485300731)
                    ·
                      rfl

theorem cell23_2886074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_2886074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886074 prefixEnd_2886074 := by exact prefixLift 2886074
  have htrace : WordTrace (prefixWord ++ tailWord_2886074) baseStart_2886074 baseEnd_2886074 := by
    simpa [prefixWord, tailWord_2886074, baseEnd_2886074] using wordTrace_append hprefix tailTrace_2886074
  have hstable : (prefixWord ++ tailWord_2886074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886074).length < 2 ^ (prefixWord ++ tailWord_2886074).sum := by decide
  have hdescent : baseEnd_2886074 < baseStart_2886074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886124 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 6]
def baseStart_2886124 : Nat := 118140960795 + 2886124 * 2 ^ 59
def prefixEnd_2886124 : Nat := 4983230072969 + 3 ^ 40 * 2886124 * 2
def baseEnd_2886124 : Nat := 1481968840476971260276963

theorem tailTrace_2886124 : CollatzResearch.WordTrace tailWord_2886124 prefixEnd_2886124 1481968840476971260276963 := by
  unfold tailWord_2886124
  simp only [CollatzResearch.WordTrace]
  refine ⟨52632795098036566790840713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70177060130715422387787617 52632795098036566790840713)
  ·
    refine ⟨39474596323527425093130535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52632795098036566790840713 39474596323527425093130535)
    ·
      refine ⟨59211894485291137639695803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39474596323527425093130535 59211894485291137639695803)
      ·
        refine ⟨88817841727936706459543705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59211894485291137639695803 88817841727936706459543705)
        ·
          refine ⟨66613381295952529844657779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88817841727936706459543705 66613381295952529844657779)
          ·
            refine ⟨99920071943928794766986669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66613381295952529844657779 99920071943928794766986669)
            ·
              refine ⟨37470026978973298037620001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99920071943928794766986669 37470026978973298037620001)
              ·
                refine ⟨28102520234229973528215001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37470026978973298037620001 28102520234229973528215001)
                ·
                  refine ⟨21076890175672480146161251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28102520234229973528215001 21076890175672480146161251)
                  ·
                    refine ⟨31615335263508720219241877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21076890175672480146161251 31615335263508720219241877)
                    ·
                      refine ⟨1481968840476971260276963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31615335263508720219241877 1481968840476971260276963)
                      ·
                        rfl

theorem cell23_2886124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_2886124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886124 prefixEnd_2886124 := by exact prefixLift 2886124
  have htrace : WordTrace (prefixWord ++ tailWord_2886124) baseStart_2886124 baseEnd_2886124 := by
    simpa [prefixWord, tailWord_2886124, baseEnd_2886124] using wordTrace_append hprefix tailTrace_2886124
  have hstable : (prefixWord ++ tailWord_2886124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886124).length < 2 ^ (prefixWord ++ tailWord_2886124).sum := by decide
  have hdescent : baseEnd_2886124 < baseStart_2886124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886148 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_2886148 : Nat := 118140960795 + 2886148 * 2 ^ 59
def prefixEnd_2886148 : Nat := 4983230072969 + 3 ^ 40 * 2886148 * 2
def baseEnd_2886148 : Nat := 1481981164012679166376853

theorem tailTrace_2886148 : CollatzResearch.WordTrace tailWord_2886148 prefixEnd_2886148 1481981164012679166376853 := by
  unfold tailWord_2886148
  simp only [CollatzResearch.WordTrace]
  refine ⟨52633232773993092840277549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70177643698657457120370065 52633232773993092840277549)
  ·
    refine ⟨19737462290247409815104081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52633232773993092840277549 19737462290247409815104081)
    ·
      refine ⟨14803096717685557361328061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19737462290247409815104081 14803096717685557361328061)
      ·
        refine ⟨5551161269132084010498023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14803096717685557361328061 5551161269132084010498023)
        ·
          refine ⟨8326741903698126015747035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5551161269132084010498023 8326741903698126015747035)
          ·
            refine ⟨12490112855547189023620553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8326741903698126015747035 12490112855547189023620553)
            ·
              refine ⟨9367584641660391767715415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12490112855547189023620553 9367584641660391767715415)
              ·
                refine ⟨14051376962490587651573123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9367584641660391767715415 14051376962490587651573123)
                ·
                  refine ⟨21077065443735881477359685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14051376962490587651573123 21077065443735881477359685)
                  ·
                    refine ⟨3951949770700477777004941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21077065443735881477359685 3951949770700477777004941)
                    ·
                      refine ⟨1481981164012679166376853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3951949770700477777004941 1481981164012679166376853)
                      ·
                        rfl

theorem cell23_2886148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_2886148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886148 prefixEnd_2886148 := by exact prefixLift 2886148
  have htrace : WordTrace (prefixWord ++ tailWord_2886148) baseStart_2886148 baseEnd_2886148 := by
    simpa [prefixWord, tailWord_2886148, baseEnd_2886148] using wordTrace_append hprefix tailTrace_2886148
  have hstable : (prefixWord ++ tailWord_2886148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886148).length < 2 ^ (prefixWord ++ tailWord_2886148).sum := by decide
  have hdescent : baseEnd_2886148 < baseStart_2886148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886155 : List Nat := [1, 1, 1, 1, 7, 1, 3, 3, 1, 4]
def baseStart_2886155 : Nat := 118140960795 + 2886155 * 2 ^ 59
def prefixEnd_2886155 : Nat := 4983230072969 + 3 ^ 40 * 2886155 * 2
def baseEnd_2886155 : Nat := 493994919459086879663107

theorem tailTrace_2886155 : CollatzResearch.WordTrace tailWord_2886155 prefixEnd_2886155 493994919459086879663107 := by
  unfold tailWord_2886155
  simp only [CollatzResearch.WordTrace]
  refine ⟨105266720858960825876059919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70177813905973883917373279 105266720858960825876059919)
  ·
    refine ⟨157900081288441238814089879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105266720858960825876059919 157900081288441238814089879)
    ·
      refine ⟨236850121932661858221134819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157900081288441238814089879 236850121932661858221134819)
      ·
        refine ⟨355275182898992787331702229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236850121932661858221134819 355275182898992787331702229)
        ·
          refine ⟨8326762099195143453086771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 355275182898992787331702229 8326762099195143453086771)
          ·
            refine ⟨12490143148792715179630157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8326762099195143453086771 12490143148792715179630157)
            ·
              refine ⟨4683803680797268192361309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12490143148792715179630157 4683803680797268192361309)
              ·
                refine ⟨1756426380298975572135491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4683803680797268192361309 1756426380298975572135491)
                ·
                  refine ⟨2634639570448463358203237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1756426380298975572135491 2634639570448463358203237)
                  ·
                    refine ⟨493994919459086879663107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2634639570448463358203237 493994919459086879663107)
                    ·
                      rfl

theorem cell23_2886155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 1, 4].length) (baseStart_2886155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886155 prefixEnd_2886155 := by exact prefixLift 2886155
  have htrace : WordTrace (prefixWord ++ tailWord_2886155) baseStart_2886155 baseEnd_2886155 := by
    simpa [prefixWord, tailWord_2886155, baseEnd_2886155] using wordTrace_append hprefix tailTrace_2886155
  have hstable : (prefixWord ++ tailWord_2886155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886155).length < 2 ^ (prefixWord ++ tailWord_2886155).sum := by decide
  have hdescent : baseEnd_2886155 < baseStart_2886155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886171 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 2, 9, 2]
def baseStart_2886171 : Nat := 118140960795 + 2886171 * 2 ^ 59
def prefixEnd_2886171 : Nat := 4983230072969 + 3 ^ 40 * 2886171 * 2
def baseEnd_2886171 : Nat := 1481992974067732576389247

theorem tailTrace_2886171 : CollatzResearch.WordTrace tailWord_2886171 prefixEnd_2886171 1481992974067732576389247 := by
  unfold tailWord_2886171
  simp only [CollatzResearch.WordTrace]
  refine ⟨105267304426902860608642367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70178202951268573739094911 105267304426902860608642367)
  ·
    refine ⟨157900956640354290912963551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105267304426902860608642367 157900956640354290912963551)
    ·
      refine ⟨236851434960531436369445327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157900956640354290912963551 236851434960531436369445327)
      ·
        refine ⟨355277152440797154554167991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236851434960531436369445327 355277152440797154554167991)
        ·
          refine ⟨532915728661195731831251987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355277152440797154554167991 532915728661195731831251987)
          ·
            refine ⟨799373592991793597746877981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532915728661195731831251987 799373592991793597746877981)
            ·
              refine ⟨299765097371922599155079243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 799373592991793597746877981 299765097371922599155079243)
              ·
                refine ⟨449647646057883898732618865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299765097371922599155079243 449647646057883898732618865)
                ·
                  refine ⟨337235734543412924049464149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449647646057883898732618865 337235734543412924049464149)
                  ·
                    refine ⟨1975990632090310101852329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 337235734543412924049464149 1975990632090310101852329)
                    ·
                      refine ⟨1481992974067732576389247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1975990632090310101852329 1481992974067732576389247)
                      ·
                        rfl

theorem cell23_2886171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 9, 2].length) (baseStart_2886171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886171 prefixEnd_2886171 := by exact prefixLift 2886171
  have htrace : WordTrace (prefixWord ++ tailWord_2886171) baseStart_2886171 baseEnd_2886171 := by
    simpa [prefixWord, tailWord_2886171, baseEnd_2886171] using wordTrace_append hprefix tailTrace_2886171
  have hstable : (prefixWord ++ tailWord_2886171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886171).length < 2 ^ (prefixWord ++ tailWord_2886171).sum := by decide
  have hdescent : baseEnd_2886171 < baseStart_2886171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886172 : List Nat := [2, 2, 3, 1, 2, 3, 3, 2, 1, 4]
def baseStart_2886172 : Nat := 118140960795 + 2886172 * 2 ^ 59
def prefixEnd_2886172 : Nat := 4983230072969 + 3 ^ 40 * 2886172 * 2
def baseEnd_2886172 : Nat := 493997829182795690825581

theorem tailTrace_2886172 : CollatzResearch.WordTrace tailWord_2886172 prefixEnd_2886172 493997829182795690825581 := by
  unfold tailWord_2886172
  simp only [CollatzResearch.WordTrace]
  refine ⟨52633670449949618889714385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70178227266599491852952513 52633670449949618889714385)
  ·
    refine ⟨39475252837462214167285789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52633670449949618889714385 39475252837462214167285789)
    ·
      refine ⟨14803219814048330312732171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39475252837462214167285789 14803219814048330312732171)
      ·
        refine ⟨22204829721072495469098257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14803219814048330312732171 22204829721072495469098257)
        ·
          refine ⟨16653622290804371601823693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22204829721072495469098257 16653622290804371601823693)
          ·
            refine ⟨6245108359051639350683885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16653622290804371601823693 6245108359051639350683885)
            ·
              refine ⟨2341915634644364756506457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6245108359051639350683885 2341915634644364756506457)
              ·
                refine ⟨1756436725983273567379843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2341915634644364756506457 1756436725983273567379843)
                ·
                  refine ⟨2634655088974910351069765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1756436725983273567379843 2634655088974910351069765)
                  ·
                    refine ⟨493997829182795690825581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2634655088974910351069765 493997829182795690825581)
                    ·
                      rfl

theorem cell23_2886172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_2886172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886172 prefixEnd_2886172 := by exact prefixLift 2886172
  have htrace : WordTrace (prefixWord ++ tailWord_2886172) baseStart_2886172 baseEnd_2886172 := by
    simpa [prefixWord, tailWord_2886172, baseEnd_2886172] using wordTrace_append hprefix tailTrace_2886172
  have hstable : (prefixWord ++ tailWord_2886172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886172).length < 2 ^ (prefixWord ++ tailWord_2886172).sum := by decide
  have hdescent : baseEnd_2886172 < baseStart_2886172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886205 : List Nat := [1, 4, 1, 3, 2, 1, 1, 3, 2, 3, 2]
def baseStart_2886205 : Nat := 118140960795 + 2886205 * 2 ^ 59
def prefixEnd_2886205 : Nat := 4983230072969 + 3 ^ 40 * 2886205 * 2
def baseEnd_2886205 : Nat := 1482010432409985443364091

theorem tailTrace_2886205 : CollatzResearch.WordTrace tailWord_2886205 prefixEnd_2886205 1482010432409985443364091 := by
  unfold tailWord_2886205
  simp only [CollatzResearch.WordTrace]
  refine ⟨105268544508779684415380069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70179029672519789610253379 105268544508779684415380069)
  ·
    refine ⟨19737852095396190827883763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105268544508779684415380069 19737852095396190827883763)
    ·
      refine ⟨29606778143094286241825645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19737852095396190827883763 29606778143094286241825645)
      ·
        refine ⟨11102541803660357340684617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29606778143094286241825645 11102541803660357340684617)
        ·
          refine ⟨8326906352745268005513463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11102541803660357340684617 8326906352745268005513463)
          ·
            refine ⟨12490359529117902008270195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8326906352745268005513463 12490359529117902008270195)
            ·
              refine ⟨18735539293676853012405293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12490359529117902008270195 18735539293676853012405293)
              ·
                refine ⟨7025827235128819879651985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18735539293676853012405293 7025827235128819879651985)
                ·
                  refine ⟨5269370426346614909738989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7025827235128819879651985 5269370426346614909738989)
                  ·
                    refine ⟨1976013909879980591152121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5269370426346614909738989 1976013909879980591152121)
                    ·
                      refine ⟨1482010432409985443364091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1976013909879980591152121 1482010432409985443364091)
                      ·
                        rfl

theorem cell23_2886205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_2886205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886205 prefixEnd_2886205 := by exact prefixLift 2886205
  have htrace : WordTrace (prefixWord ++ tailWord_2886205) baseStart_2886205 baseEnd_2886205 := by
    simpa [prefixWord, tailWord_2886205, baseEnd_2886205] using wordTrace_append hprefix tailTrace_2886205
  have hstable : (prefixWord ++ tailWord_2886205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886205).length < 2 ^ (prefixWord ++ tailWord_2886205).sum := by decide
  have hdescent : baseEnd_2886205 < baseStart_2886205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886211 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 6, 4]
def baseStart_2886211 : Nat := 118140960795 + 2886211 * 2 ^ 59
def prefixEnd_2886211 : Nat := 4983230072969 + 3 ^ 40 * 2886211 * 2
def baseEnd_2886211 : Nat := 494004504431304139963021

theorem tailTrace_2886211 : CollatzResearch.WordTrace tailWord_2886211 prefixEnd_2886211 494004504431304139963021 := by
  unfold tailWord_2886211
  simp only [CollatzResearch.WordTrace]
  refine ⟨105268763346757947440098487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70179175564505298293398991 105268763346757947440098487)
  ·
    refine ⟨157903145020136921160147731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105268763346757947440098487 157903145020136921160147731)
    ·
      refine ⟨236854717530205381740221597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157903145020136921160147731 236854717530205381740221597)
      ·
        refine ⟨88820519073827018152583099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236854717530205381740221597 88820519073827018152583099)
        ·
          refine ⟨133230778610740527228874649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88820519073827018152583099 133230778610740527228874649)
          ·
            refine ⟨99923083958055395421655987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133230778610740527228874649 99923083958055395421655987)
            ·
              refine ⟨149884625937083093132483981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99923083958055395421655987 149884625937083093132483981)
              ·
                refine ⟨56206734726406159924681493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149884625937083093132483981 56206734726406159924681493)
                ·
                  refine ⟨2634690690300288746469445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56206734726406159924681493 2634690690300288746469445)
                  ·
                    refine ⟨494004504431304139963021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2634690690300288746469445 494004504431304139963021)
                    ·
                      rfl

theorem cell23_2886211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 4].length) (baseStart_2886211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886211 prefixEnd_2886211 := by exact prefixLift 2886211
  have htrace : WordTrace (prefixWord ++ tailWord_2886211) baseStart_2886211 baseEnd_2886211 := by
    simpa [prefixWord, tailWord_2886211, baseEnd_2886211] using wordTrace_append hprefix tailTrace_2886211
  have hstable : (prefixWord ++ tailWord_2886211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886211).length < 2 ^ (prefixWord ++ tailWord_2886211).sum := by decide
  have hdescent : baseEnd_2886211 < baseStart_2886211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886215 : List Nat := [1, 1, 4, 1, 4, 2, 3, 1, 1, 5]
def baseStart_2886215 : Nat := 118140960795 + 2886215 * 2 ^ 59
def prefixEnd_2886215 : Nat := 4983230072969 + 3 ^ 40 * 2886215 * 2
def baseEnd_2886215 : Nat := 494005189072176801413015

theorem tailTrace_2886215 : CollatzResearch.WordTrace tailWord_2886215 prefixEnd_2886215 494005189072176801413015 := by
  unfold tailWord_2886215
  simp only [CollatzResearch.WordTrace]
  refine ⟨105268909238743456123244099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70179272825828970748829399 105268909238743456123244099)
  ·
    refine ⟨157903363858115184184866149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105268909238743456123244099 157903363858115184184866149)
    ·
      refine ⟨29606880723396597034662403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157903363858115184184866149 29606880723396597034662403)
      ·
        refine ⟨44410321085094895551993605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29606880723396597034662403 44410321085094895551993605)
        ·
          refine ⟨8326935203455292915998801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44410321085094895551993605 8326935203455292915998801)
          ·
            refine ⟨6245201402591469686999101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8326935203455292915998801 6245201402591469686999101)
            ·
              refine ⟨2341950525971801132624663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6245201402591469686999101 2341950525971801132624663)
              ·
                refine ⟨3512925788957701698936995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2341950525971801132624663 3512925788957701698936995)
                ·
                  refine ⟨5269388683436552548405493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3512925788957701698936995 5269388683436552548405493)
                  ·
                    refine ⟨494005189072176801413015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5269388683436552548405493 494005189072176801413015)
                    ·
                      rfl

theorem cell23_2886215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_2886215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886215 prefixEnd_2886215 := by exact prefixLift 2886215
  have htrace : WordTrace (prefixWord ++ tailWord_2886215) baseStart_2886215 baseEnd_2886215 := by
    simpa [prefixWord, tailWord_2886215, baseEnd_2886215] using wordTrace_append hprefix tailTrace_2886215
  have hstable : (prefixWord ++ tailWord_2886215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886215).length < 2 ^ (prefixWord ++ tailWord_2886215).sum := by decide
  have hdescent : baseEnd_2886215 < baseStart_2886215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886231 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 4]
def baseStart_2886231 : Nat := 118140960795 + 2886231 * 2 ^ 59
def prefixEnd_2886231 : Nat := 4983230072969 + 3 ^ 40 * 2886231 * 2
def baseEnd_2886231 : Nat := 1482023782907002341638971

theorem tailTrace_2886231 : CollatzResearch.WordTrace tailWord_2886231 prefixEnd_2886231 1482023782907002341638971 := by
  unfold tailWord_2886231
  simp only [CollatzResearch.WordTrace]
  refine ⟨105269492806685490855826547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70179661871123660570551031 105269492806685490855826547)
  ·
    refine ⟨157904239210028236283739821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105269492806685490855826547 157904239210028236283739821)
    ·
      refine ⟨59214089703760588606402433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157904239210028236283739821 59214089703760588606402433)
      ·
        refine ⟨44410567277820441454801825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59214089703760588606402433 44410567277820441454801825)
        ·
          refine ⟨33307925458365331091101369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44410567277820441454801825 33307925458365331091101369)
          ·
            refine ⟨24980944093773998318326027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33307925458365331091101369 24980944093773998318326027)
            ·
              refine ⟨37471416140660997477489041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24980944093773998318326027 37471416140660997477489041)
              ·
                refine ⟨28103562105495748108116781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37471416140660997477489041 28103562105495748108116781)
                ·
                  refine ⟨10538835789560905540543793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28103562105495748108116781 10538835789560905540543793)
                  ·
                    refine ⟨7904126842170679155407845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10538835789560905540543793 7904126842170679155407845)
                    ·
                      refine ⟨1482023782907002341638971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7904126842170679155407845 1482023782907002341638971)
                      ·
                        rfl

theorem cell23_2886231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_2886231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886231 prefixEnd_2886231 := by exact prefixLift 2886231
  have htrace : WordTrace (prefixWord ++ tailWord_2886231) baseStart_2886231 baseEnd_2886231 := by
    simpa [prefixWord, tailWord_2886231, baseEnd_2886231] using wordTrace_append hprefix tailTrace_2886231
  have hstable : (prefixWord ++ tailWord_2886231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886231).length < 2 ^ (prefixWord ++ tailWord_2886231).sum := by decide
  have hdescent : baseEnd_2886231 < baseStart_2886231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886241 : List Nat := [1, 2, 3, 1, 1, 4, 3, 8]
def baseStart_2886241 : Nat := 118140960795 + 2886241 * 2 ^ 59
def prefixEnd_2886241 : Nat := 4983230072969 + 3 ^ 40 * 2886241 * 2
def baseEnd_2886241 : Nat := 54889959915316566759775

theorem tailTrace_2886241 : CollatzResearch.WordTrace tailWord_2886241 prefixEnd_2886241 54889959915316566759775 := by
  unfold tailWord_2886241
  simp only [CollatzResearch.WordTrace]
  refine ⟨105269857536649262563690577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70179905024432841709127051 105269857536649262563690577)
  ·
    refine ⟨78952393152486946922767933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105269857536649262563690577 78952393152486946922767933)
    ·
      refine ⟨29607147432182605096037975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78952393152486946922767933 29607147432182605096037975)
      ·
        refine ⟨44410721148273907644056963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29607147432182605096037975 44410721148273907644056963)
        ·
          refine ⟨66616081722410861466085445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44410721148273907644056963 66616081722410861466085445)
          ·
            refine ⟨12490515322952036524891021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66616081722410861466085445 12490515322952036524891021)
            ·
              refine ⟨4683943246107013696834133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12490515322952036524891021 4683943246107013696834133)
              ·
                refine ⟨54889959915316566759775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4683943246107013696834133 54889959915316566759775)
                ·
                  rfl

theorem cell23_2886241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 8].length) (baseStart_2886241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886241 prefixEnd_2886241 := by exact prefixLift 2886241
  have htrace : WordTrace (prefixWord ++ tailWord_2886241) baseStart_2886241 baseEnd_2886241 := by
    simpa [prefixWord, tailWord_2886241, baseEnd_2886241] using wordTrace_append hprefix tailTrace_2886241
  have hstable : (prefixWord ++ tailWord_2886241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886241).length < 2 ^ (prefixWord ++ tailWord_2886241).sum := by decide
  have hdescent : baseEnd_2886241 < baseStart_2886241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886268 : List Nat := [2, 2, 2, 1, 1, 2, 4, 2, 1, 3, 3]
def baseStart_2886268 : Nat := 118140960795 + 2886268 * 2 ^ 59
def prefixEnd_2886268 : Nat := 4983230072969 + 3 ^ 40 * 2886268 * 2
def baseEnd_2886268 : Nat := 1482042781691218696876301

theorem tailTrace_2886268 : CollatzResearch.WordTrace tailWord_2886268 prefixEnd_2886268 1482042781691218696876301 := by
  unfold tailWord_2886268
  simp only [CollatzResearch.WordTrace]
  refine ⟨52635421153775723087461729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70180561538367630783282305 52635421153775723087461729)
  ·
    refine ⟨39476565865331792315596297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52635421153775723087461729 39476565865331792315596297)
    ·
      refine ⟨29607424398998844236697223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39476565865331792315596297 29607424398998844236697223)
      ·
        refine ⟨44411136598498266355045835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29607424398998844236697223 44411136598498266355045835)
        ·
          refine ⟨66616704897747399532568753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44411136598498266355045835 66616704897747399532568753)
          ·
            refine ⟨49962528673310549649426565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66616704897747399532568753 49962528673310549649426565)
            ·
              refine ⟨9367974126245728059267481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49962528673310549649426565 9367974126245728059267481)
              ·
                refine ⟨7025980594684296044450611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9367974126245728059267481 7025980594684296044450611)
                ·
                  refine ⟨10538970892026444066675917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7025980594684296044450611 10538970892026444066675917)
                  ·
                    refine ⟨3952114084509916525003469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10538970892026444066675917 3952114084509916525003469)
                    ·
                      refine ⟨1482042781691218696876301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3952114084509916525003469 1482042781691218696876301)
                      ·
                        rfl

theorem cell23_2886268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_2886268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886268 prefixEnd_2886268 := by exact prefixLift 2886268
  have htrace : WordTrace (prefixWord ++ tailWord_2886268) baseStart_2886268 baseEnd_2886268 := by
    simpa [prefixWord, tailWord_2886268, baseEnd_2886268] using wordTrace_append hprefix tailTrace_2886268
  have hstable : (prefixWord ++ tailWord_2886268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886268).length < 2 ^ (prefixWord ++ tailWord_2886268).sum := by decide
  have hdescent : baseEnd_2886268 < baseStart_2886268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886269 : List Nat := [1, 4, 1, 1, 6, 1, 2, 1, 1, 1, 4]
def baseStart_2886269 : Nat := 118140960795 + 2886269 * 2 ^ 59
def prefixEnd_2886269 : Nat := 4983230072969 + 3 ^ 40 * 2886269 * 2
def baseEnd_2886269 : Nat := 1482043295171873192963797

theorem tailTrace_2886269 : CollatzResearch.WordTrace tailWord_2886269 prefixEnd_2886269 1482043295171873192963797 := by
  unfold tailWord_2886269
  simp only [CollatzResearch.WordTrace]
  refine ⟨105270878780547823345709861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70180585853698548897139907 105270878780547823345709861)
  ·
    refine ⟨19738289771352716877320599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105270878780547823345709861 19738289771352716877320599)
    ·
      refine ⟨29607434657029075315980899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19738289771352716877320599 29607434657029075315980899)
      ·
        refine ⟨44411151985543612973971349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29607434657029075315980899 44411151985543612973971349)
        ·
          refine ⟨2081772749322356858154907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44411151985543612973971349 2081772749322356858154907)
          ·
            refine ⟨3122659123983535287232361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2081772749322356858154907 3122659123983535287232361)
            ·
              refine ⟨2341994342987651465424271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3122659123983535287232361 2341994342987651465424271)
              ·
                refine ⟨3512991514481477198136407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2341994342987651465424271 3512991514481477198136407)
                ·
                  refine ⟨5269487271722215797204611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3512991514481477198136407 5269487271722215797204611)
                  ·
                    refine ⟨7904230907583323695806917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5269487271722215797204611 7904230907583323695806917)
                    ·
                      refine ⟨1482043295171873192963797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7904230907583323695806917 1482043295171873192963797)
                      ·
                        rfl

theorem cell23_2886269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_2886269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886269 prefixEnd_2886269 := by exact prefixLift 2886269
  have htrace : WordTrace (prefixWord ++ tailWord_2886269) baseStart_2886269 baseEnd_2886269 := by
    simpa [prefixWord, tailWord_2886269, baseEnd_2886269] using wordTrace_append hprefix tailTrace_2886269
  have hstable : (prefixWord ++ tailWord_2886269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886269).length < 2 ^ (prefixWord ++ tailWord_2886269).sum := by decide
  have hdescent : baseEnd_2886269 < baseStart_2886269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886272 : List Nat := [2, 1, 1, 2, 1, 7, 2, 1, 1, 2, 3]
def baseStart_2886272 : Nat := 118140960795 + 2886272 * 2 ^ 59
def prefixEnd_2886272 : Nat := 4983230072969 + 3 ^ 40 * 2886272 * 2
def baseEnd_2886272 : Nat := 1482044835613836681226283

theorem tailTrace_2886272 : CollatzResearch.WordTrace tailWord_2886272 prefixEnd_2886272 1482044835613836681226283 := by
  unfold tailWord_2886272
  simp only [CollatzResearch.WordTrace]
  refine ⟨52635494099768477429034535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70180658799691303238712713 52635494099768477429034535)
  ·
    refine ⟨78953241149652716143551803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52635494099768477429034535 78953241149652716143551803)
    ·
      refine ⟨118429861724479074215327705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78953241149652716143551803 118429861724479074215327705)
      ·
        refine ⟨88822396293359305661495779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118429861724479074215327705 88822396293359305661495779)
        ·
          refine ⟨133233594440038958492243669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88822396293359305661495779 133233594440038958492243669)
          ·
            refine ⟨3122662369688413089661961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 133233594440038958492243669 3122662369688413089661961)
            ·
              refine ⟨2341996777266309817246471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3122662369688413089661961 2341996777266309817246471)
              ·
                refine ⟨3512995165899464725869707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2341996777266309817246471 3512995165899464725869707)
                ·
                  refine ⟨5269492748849197088804561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3512995165899464725869707 5269492748849197088804561)
                  ·
                    refine ⟨3952119561636897816603421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5269492748849197088804561 3952119561636897816603421)
                    ·
                      refine ⟨1482044835613836681226283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3952119561636897816603421 1482044835613836681226283)
                      ·
                        rfl

theorem cell23_2886272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 1, 2, 3].length) (baseStart_2886272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886272 prefixEnd_2886272 := by exact prefixLift 2886272
  have htrace : WordTrace (prefixWord ++ tailWord_2886272) baseStart_2886272 baseEnd_2886272 := by
    simpa [prefixWord, tailWord_2886272, baseEnd_2886272] using wordTrace_append hprefix tailTrace_2886272
  have hstable : (prefixWord ++ tailWord_2886272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886272).length < 2 ^ (prefixWord ++ tailWord_2886272).sum := by decide
  have hdescent : baseEnd_2886272 < baseStart_2886272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886359 : List Nat := [1, 1, 3, 2, 1, 4, 4, 1, 2, 2, 2]
def baseStart_2886359 : Nat := 118140960795 + 2886359 * 2 ^ 59
def prefixEnd_2886359 : Nat := 4983230072969 + 3 ^ 40 * 2886359 * 2
def baseEnd_2886359 : Nat := 1482089508430777840838383

theorem tailTrace_2886359 : CollatzResearch.WordTrace tailWord_2886359 prefixEnd_2886359 1482089508430777840838383 := by
  unfold tailWord_2886359
  simp only [CollatzResearch.WordTrace]
  refine ⟨105274161350221768716486131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70182774233481179144324087 105274161350221768716486131)
  ·
    refine ⟨157911242025332653074729197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105274161350221768716486131 157911242025332653074729197)
    ·
      refine ⟨59216715759499744903023449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157911242025332653074729197 59216715759499744903023449)
      ·
        refine ⟨44412536819624808677267587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59216715759499744903023449 44412536819624808677267587)
        ·
          refine ⟨66618805229437213015901381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44412536819624808677267587 66618805229437213015901381)
          ·
            refine ⟨12491025980519477440481509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66618805229437213015901381 12491025980519477440481509)
            ·
              refine ⟨2342067371347402020090283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12491025980519477440481509 2342067371347402020090283)
              ·
                refine ⟨3513101057021103030135425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342067371347402020090283 3513101057021103030135425)
                ·
                  refine ⟨2634825792765827272601569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3513101057021103030135425 2634825792765827272601569)
                  ·
                    refine ⟨1976119344574370454451177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2634825792765827272601569 1976119344574370454451177)
                    ·
                      refine ⟨1482089508430777840838383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1976119344574370454451177 1482089508430777840838383)
                      ·
                        rfl

theorem cell23_2886359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_2886359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886359 prefixEnd_2886359 := by exact prefixLift 2886359
  have htrace : WordTrace (prefixWord ++ tailWord_2886359) baseStart_2886359 baseEnd_2886359 := by
    simpa [prefixWord, tailWord_2886359, baseEnd_2886359] using wordTrace_append hprefix tailTrace_2886359
  have hstable : (prefixWord ++ tailWord_2886359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886359).length < 2 ^ (prefixWord ++ tailWord_2886359).sum := by decide
  have hdescent : baseEnd_2886359 < baseStart_2886359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886402 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_2886402 : Nat := 118140960795 + 2886402 * 2 ^ 59
def prefixEnd_2886402 : Nat := 4983230072969 + 3 ^ 40 * 2886402 * 2
def baseEnd_2886402 : Nat := 1482111588098921172600685

theorem tailTrace_2886402 : CollatzResearch.WordTrace tailWord_2886402 prefixEnd_2886402 1482111588098921172600685 := by
  unfold tailWord_2886402
  simp only [CollatzResearch.WordTrace]
  refine ⟨26318932422266496765075365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70183819792710658040200973 26318932422266496765075365)
  ·
    refine ⟨4934799829174968143451631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26318932422266496765075365 4934799829174968143451631)
    ·
      refine ⟨7402199743762452215177447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4934799829174968143451631 7402199743762452215177447)
      ·
        refine ⟨11103299615643678322766171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7402199743762452215177447 11103299615643678322766171)
        ·
          refine ⟨16654949423465517484149257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11103299615643678322766171 16654949423465517484149257)
          ·
            refine ⟨12491212067599138113111943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16654949423465517484149257 12491212067599138113111943)
            ·
              refine ⟨18736818101398707169667915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12491212067599138113111943 18736818101398707169667915)
              ·
                refine ⟨28105227152098060754501873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18736818101398707169667915 28105227152098060754501873)
                ·
                  refine ⟨21078920364073545565876405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28105227152098060754501873 21078920364073545565876405)
                  ·
                    refine ⟨1976148784131894896800913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21078920364073545565876405 1976148784131894896800913)
                    ·
                      refine ⟨1482111588098921172600685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1976148784131894896800913 1482111588098921172600685)
                      ·
                        rfl

theorem cell23_2886402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_2886402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886402 prefixEnd_2886402 := by exact prefixLift 2886402
  have htrace : WordTrace (prefixWord ++ tailWord_2886402) baseStart_2886402 baseEnd_2886402 := by
    simpa [prefixWord, tailWord_2886402, baseEnd_2886402] using wordTrace_append hprefix tailTrace_2886402
  have hstable : (prefixWord ++ tailWord_2886402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886402).length < 2 ^ (prefixWord ++ tailWord_2886402).sum := by decide
  have hdescent : baseEnd_2886402 < baseStart_2886402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886415 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 2, 4, 2]
def baseStart_2886415 : Nat := 118140960795 + 2886415 * 2 ^ 59
def prefixEnd_2886415 : Nat := 4983230072969 + 3 ^ 40 * 2886415 * 2
def baseEnd_2886415 : Nat := 1482118263347429621738125

theorem tailTrace_2886415 : CollatzResearch.WordTrace tailWord_2886415 prefixEnd_2886415 1482118263347429621738125 := by
  unfold tailWord_2886415
  simp only [CollatzResearch.WordTrace]
  refine ⟨105276203838018890280524699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70184135892012593520349799 105276203838018890280524699)
  ·
    refine ⟨157914305757028335420787049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105276203838018890280524699 157914305757028335420787049)
    ·
      refine ⟨118435729317771251565590287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157914305757028335420787049 118435729317771251565590287)
      ·
        refine ⟨177653593976656877348385431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118435729317771251565590287 177653593976656877348385431)
        ·
          refine ⟨266480390964985316022578147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177653593976656877348385431 266480390964985316022578147)
          ·
            refine ⟨399720586447477974033867221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266480390964985316022578147 399720586447477974033867221)
            ·
              refine ⟨9368451244862765016418763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 399720586447477974033867221 9368451244862765016418763)
              ·
                refine ⟨14052676867294147524628145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9368451244862765016418763 14052676867294147524628145)
                ·
                  refine ⟨10539507650470610643471109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14052676867294147524628145 10539507650470610643471109)
                  ·
                    refine ⟨1976157684463239495650833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10539507650470610643471109 1976157684463239495650833)
                    ·
                      refine ⟨1482118263347429621738125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1976157684463239495650833 1482118263347429621738125)
                      ·
                        rfl

theorem cell23_2886415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 4, 2].length) (baseStart_2886415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886415 prefixEnd_2886415 := by exact prefixLift 2886415
  have htrace : WordTrace (prefixWord ++ tailWord_2886415) baseStart_2886415 baseEnd_2886415 := by
    simpa [prefixWord, tailWord_2886415, baseEnd_2886415] using wordTrace_append hprefix tailTrace_2886415
  have hstable : (prefixWord ++ tailWord_2886415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886415).length < 2 ^ (prefixWord ++ tailWord_2886415).sum := by decide
  have hdescent : baseEnd_2886415 < baseStart_2886415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886429 : List Nat := [1, 4, 2, 4, 1, 2, 1, 1, 2, 5]
def baseStart_2886429 : Nat := 118140960795 + 2886429 * 2 ^ 59
def prefixEnd_2886429 : Nat := 4983230072969 + 3 ^ 40 * 2886429 * 2
def baseEnd_2886429 : Nat := 494041817358864188987687

theorem tailTrace_2886429 : CollatzResearch.WordTrace tailWord_2886429 prefixEnd_2886429 494041817358864188987687 := by
  unfold tailWord_2886429
  simp only [CollatzResearch.WordTrace]
  refine ⟨105276714459968170671534341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70184476306645447114356227 105276714459968170671534341)
  ·
    refine ⟨19739383961244032000912689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105276714459968170671534341 19739383961244032000912689)
    ·
      refine ⟨14804537970933024000684517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19739383961244032000912689 14804537970933024000684517)
      ·
        refine ⟨2775850869549942000128347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14804537970933024000684517 2775850869549942000128347)
        ·
          refine ⟨4163776304324913000192521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2775850869549942000128347 4163776304324913000192521)
          ·
            refine ⟨3122832228243684750144391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4163776304324913000192521 3122832228243684750144391)
            ·
              refine ⟨4684248342365527125216587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3122832228243684750144391 4684248342365527125216587)
              ·
                refine ⟨7026372513548290687824881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4684248342365527125216587 7026372513548290687824881)
                ·
                  refine ⟨5269779385161218015868661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7026372513548290687824881 5269779385161218015868661)
                  ·
                    refine ⟨494041817358864188987687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5269779385161218015868661 494041817358864188987687)
                    ·
                      rfl

theorem cell23_2886429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_2886429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886429 prefixEnd_2886429 := by exact prefixLift 2886429
  have htrace : WordTrace (prefixWord ++ tailWord_2886429) baseStart_2886429 baseEnd_2886429 := by
    simpa [prefixWord, tailWord_2886429, baseEnd_2886429] using wordTrace_append hprefix tailTrace_2886429
  have hstable : (prefixWord ++ tailWord_2886429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886429).length < 2 ^ (prefixWord ++ tailWord_2886429).sum := by decide
  have hdescent : baseEnd_2886429 < baseStart_2886429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886432 : List Nat := [2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 4]
def baseStart_2886432 : Nat := 118140960795 + 2886432 * 2 ^ 59
def prefixEnd_2886432 : Nat := 4983230072969 + 3 ^ 40 * 2886432 * 2
def baseEnd_2886432 : Nat := 1482126992518556055225547

theorem tailTrace_2886432 : CollatzResearch.WordTrace tailWord_2886432 prefixEnd_2886432 1482126992518556055225547 := by
  unfold tailWord_2886432
  simp only [CollatzResearch.WordTrace]
  refine ⟨52638411939478651091946775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70184549252638201455929033 52638411939478651091946775)
  ·
    refine ⟨78957617909217976637920163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52638411939478651091946775 78957617909217976637920163)
    ·
      refine ⟨118436426863826964956880245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78957617909217976637920163 118436426863826964956880245)
      ·
        refine ⟨11103415018483777964707523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118436426863826964956880245 11103415018483777964707523)
        ·
          refine ⟨16655122527725666947061285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11103415018483777964707523 16655122527725666947061285)
          ·
            refine ⟨3122835473948562552573991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16655122527725666947061285 3122835473948562552573991)
            ·
              refine ⟨4684253210922843828860987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3122835473948562552573991 4684253210922843828860987)
              ·
                refine ⟨7026379816384265743291481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4684253210922843828860987 7026379816384265743291481)
                ·
                  refine ⟨5269784862288199307468611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7026379816384265743291481 5269784862288199307468611)
                  ·
                    refine ⟨7904677293432298961202917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5269784862288199307468611 7904677293432298961202917)
                    ·
                      refine ⟨1482126992518556055225547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7904677293432298961202917 1482126992518556055225547)
                      ·
                        rfl

theorem cell23_2886432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_2886432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886432 prefixEnd_2886432 := by exact prefixLift 2886432
  have htrace : WordTrace (prefixWord ++ tailWord_2886432) baseStart_2886432 baseEnd_2886432 := by
    simpa [prefixWord, tailWord_2886432, baseEnd_2886432] using wordTrace_append hprefix tailTrace_2886432
  have hstable : (prefixWord ++ tailWord_2886432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886432).length < 2 ^ (prefixWord ++ tailWord_2886432).sum := by decide
  have hdescent : baseEnd_2886432 < baseStart_2886432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886448 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 3]
def baseStart_2886448 : Nat := 118140960795 + 2886448 * 2 ^ 59
def prefixEnd_2886448 : Nat := 4983230072969 + 3 ^ 40 * 2886448 * 2
def baseEnd_2886448 : Nat := 1482135208209027992625473

theorem tailTrace_2886448 : CollatzResearch.WordTrace tailWord_2886448 prefixEnd_2886448 1482135208209027992625473 := by
  unfold tailWord_2886448
  simp only [CollatzResearch.WordTrace]
  refine ⟨52638703723449668458237999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70184938297932891277650665 52638703723449668458237999)
  ·
    refine ⟨78958055585174502687356999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52638703723449668458237999 78958055585174502687356999)
    ·
      refine ⟨118437083377761754031035499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78958055585174502687356999 118437083377761754031035499)
      ·
        refine ⟨177655625066642631046553249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118437083377761754031035499 177655625066642631046553249)
        ·
          refine ⟨133241718799981973284914937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177655625066642631046553249 133241718799981973284914937)
          ·
            refine ⟨99931289099986479963686203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133241718799981973284914937 99931289099986479963686203)
            ·
              refine ⟨149896933649979719945529305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99931289099986479963686203 149896933649979719945529305)
              ·
                refine ⟨112422700237484789959146979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149896933649979719945529305 112422700237484789959146979)
                ·
                  refine ⟨168634050356227184938720469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112422700237484789959146979 168634050356227184938720469)
                  ·
                    refine ⟨3952360555224074647001261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 168634050356227184938720469 3952360555224074647001261)
                    ·
                      refine ⟨1482135208209027992625473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3952360555224074647001261 1482135208209027992625473)
                      ·
                        rfl

theorem cell23_2886448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 3].length) (baseStart_2886448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886448 prefixEnd_2886448 := by exact prefixLift 2886448
  have htrace : WordTrace (prefixWord ++ tailWord_2886448) baseStart_2886448 baseEnd_2886448 := by
    simpa [prefixWord, tailWord_2886448, baseEnd_2886448] using wordTrace_append hprefix tailTrace_2886448
  have hstable : (prefixWord ++ tailWord_2886448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886448).length < 2 ^ (prefixWord ++ tailWord_2886448).sum := by decide
  have hdescent : baseEnd_2886448 < baseStart_2886448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886478 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_2886478 : Nat := 118140960795 + 2886478 * 2 ^ 59
def prefixEnd_2886478 : Nat := 4983230072969 + 3 ^ 40 * 2886478 * 2
def baseEnd_2886478 : Nat := 1482150612628662875250335

theorem tailTrace_2886478 : CollatzResearch.WordTrace tailWord_2886478 prefixEnd_2886478 1482150612628662875250335 := by
  unfold tailWord_2886478
  simp only [CollatzResearch.WordTrace]
  refine ⟨13159812704598831505008511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70185667757860434693378725 13159812704598831505008511)
  ·
    refine ⟨19739719056898247257512767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13159812704598831505008511 19739719056898247257512767)
    ·
      refine ⟨29609578585347370886269151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19739719056898247257512767 29609578585347370886269151)
      ·
        refine ⟨44414367878021056329403727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29609578585347370886269151 44414367878021056329403727)
        ·
          refine ⟨66621551817031584494105591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44414367878021056329403727 66621551817031584494105591)
          ·
            refine ⟨99932327725547376741158387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66621551817031584494105591 99932327725547376741158387)
            ·
              refine ⟨149898491588321065111737581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99932327725547376741158387 149898491588321065111737581)
              ·
                refine ⟨56211934345620399416901593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149898491588321065111737581 56211934345620399416901593)
                ·
                  refine ⟨42158950759215299562676195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56211934345620399416901593 42158950759215299562676195)
                  ·
                    refine ⟨63238426138822949344014293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42158950759215299562676195 63238426138822949344014293)
                    ·
                      refine ⟨1482150612628662875250335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63238426138822949344014293 1482150612628662875250335)
                      ·
                        rfl

theorem cell23_2886478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_2886478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886478 prefixEnd_2886478 := by exact prefixLift 2886478
  have htrace : WordTrace (prefixWord ++ tailWord_2886478) baseStart_2886478 baseEnd_2886478 := by
    simpa [prefixWord, tailWord_2886478, baseEnd_2886478] using wordTrace_append hprefix tailTrace_2886478
  have hstable : (prefixWord ++ tailWord_2886478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886478).length < 2 ^ (prefixWord ++ tailWord_2886478).sum := by decide
  have hdescent : baseEnd_2886478 < baseStart_2886478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886482 : List Nat := [3, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3]
def baseStart_2886482 : Nat := 118140960795 + 2886482 * 2 ^ 59
def prefixEnd_2886482 : Nat := 4983230072969 + 3 ^ 40 * 2886482 * 2
def baseEnd_2886482 : Nat := 1482152666551280859600317

theorem tailTrace_2886482 : CollatzResearch.WordTrace tailWord_2886482 prefixEnd_2886482 1482152666551280859600317 := by
  unfold tailWord_2886482
  simp only [CollatzResearch.WordTrace]
  refine ⟨26319661882194040180803425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70185765019184107148809133 26319661882194040180803425)
  ·
    refine ⟨19739746411645530135602569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26319661882194040180803425 19739746411645530135602569)
    ·
      refine ⟨14804809808734147601701927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19739746411645530135602569 14804809808734147601701927)
      ·
        refine ⟨22207214713101221402552891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14804809808734147601701927 22207214713101221402552891)
        ·
          refine ⟨33310822069651832103829337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22207214713101221402552891 33310822069651832103829337)
          ·
            refine ⟨24983116552238874077872003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33310822069651832103829337 24983116552238874077872003)
            ·
              refine ⟨37474674828358311116808005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24983116552238874077872003 37474674828358311116808005)
              ·
                refine ⟨7026501530317183334401501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37474674828358311116808005 7026501530317183334401501)
                ·
                  refine ⟨2634938073868943750400563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7026501530317183334401501 2634938073868943750400563)
                  ·
                    refine ⟨3952407110803415625600845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2634938073868943750400563 3952407110803415625600845)
                    ·
                      refine ⟨1482152666551280859600317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3952407110803415625600845 1482152666551280859600317)
                      ·
                        rfl

theorem cell23_2886482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_2886482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886482 prefixEnd_2886482 := by exact prefixLift 2886482
  have htrace : WordTrace (prefixWord ++ tailWord_2886482) baseStart_2886482 baseEnd_2886482 := by
    simpa [prefixWord, tailWord_2886482, baseEnd_2886482] using wordTrace_append hprefix tailTrace_2886482
  have hstable : (prefixWord ++ tailWord_2886482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886482).length < 2 ^ (prefixWord ++ tailWord_2886482).sum := by decide
  have hdescent : baseEnd_2886482 < baseStart_2886482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886488 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 2, 5, 4]
def baseStart_2886488 : Nat := 118140960795 + 2886488 * 2 ^ 59
def prefixEnd_2886488 : Nat := 4983230072969 + 3 ^ 40 * 2886488 * 2
def baseEnd_2886488 : Nat := 1482155747435207836125289

theorem tailTrace_2886488 : CollatzResearch.WordTrace tailWord_2886488 prefixEnd_2886488 1482155747435207836125289 := by
  unfold tailWord_2886488
  simp only [CollatzResearch.WordTrace]
  refine ⟨52639433183377211873966059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70185910911169615831954745 52639433183377211873966059)
  ·
    refine ⟨78959149775065817810949089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52639433183377211873966059 78959149775065817810949089)
    ·
      refine ⟨59219362331299363358211817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78959149775065817810949089 59219362331299363358211817)
      ·
        refine ⟨44414521748474522518658863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59219362331299363358211817 44414521748474522518658863)
        ·
          refine ⟨66621782622711783777988295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44414521748474522518658863 66621782622711783777988295)
          ·
            refine ⟨99932673934067675666982443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66621782622711783777988295 99932673934067675666982443)
            ·
              refine ⟨149899010901101513500473665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99932673934067675666982443 149899010901101513500473665)
              ·
                refine ⟨112424258175826135125355249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149899010901101513500473665 112424258175826135125355249)
                ·
                  refine ⟨84318193631869601344016437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112424258175826135125355249 84318193631869601344016437)
                  ·
                    refine ⟨7904830652987775126001541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84318193631869601344016437 7904830652987775126001541)
                    ·
                      refine ⟨1482155747435207836125289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7904830652987775126001541 1482155747435207836125289)
                      ·
                        rfl

theorem cell23_2886488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_2886488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886488 prefixEnd_2886488 := by exact prefixLift 2886488
  have htrace : WordTrace (prefixWord ++ tailWord_2886488) baseStart_2886488 baseEnd_2886488 := by
    simpa [prefixWord, tailWord_2886488, baseEnd_2886488] using wordTrace_append hprefix tailTrace_2886488
  have hstable : (prefixWord ++ tailWord_2886488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886488).length < 2 ^ (prefixWord ++ tailWord_2886488).sum := by decide
  have hdescent : baseEnd_2886488 < baseStart_2886488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886515 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 4, 4]
def baseStart_2886515 : Nat := 118140960795 + 2886515 * 2 ^ 59
def prefixEnd_2886515 : Nat := 4983230072969 + 3 ^ 40 * 2886515 * 2
def baseEnd_2886515 : Nat := 494056537137626410162555

theorem tailTrace_2886515 : CollatzResearch.WordTrace tailWord_2886515 prefixEnd_2886515 494056537137626410162555 := by
  unfold tailWord_2886515
  simp only [CollatzResearch.WordTrace]
  refine ⟨105279851137656607359164999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70186567425104404906109999 105279851137656607359164999)
  ·
    refine ⟨157919776706484911038747499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105279851137656607359164999 157919776706484911038747499)
    ·
      refine ⟨236879665059727366558121249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157919776706484911038747499 236879665059727366558121249)
      ·
        refine ⟨177659748794795524918590937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236879665059727366558121249 177659748794795524918590937)
        ·
          refine ⟨133244811596096643688943203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177659748794795524918590937 133244811596096643688943203)
          ·
            refine ⟨199867217394144965533414805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133244811596096643688943203 199867217394144965533414805)
            ·
              refine ⟨9368775815350545259378819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 199867217394144965533414805 9368775815350545259378819)
              ·
                refine ⟨14053163723025817889068229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9368775815350545259378819 14053163723025817889068229)
                ·
                  refine ⟨2634968198067340854200293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14053163723025817889068229 2634968198067340854200293)
                  ·
                    refine ⟨494056537137626410162555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2634968198067340854200293 494056537137626410162555)
                    ·
                      rfl

theorem cell23_2886515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 4].length) (baseStart_2886515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886515 prefixEnd_2886515 := by exact prefixLift 2886515
  have htrace : WordTrace (prefixWord ++ tailWord_2886515) baseStart_2886515 baseEnd_2886515 := by
    simpa [prefixWord, tailWord_2886515, baseEnd_2886515] using wordTrace_append hprefix tailTrace_2886515
  have hstable : (prefixWord ++ tailWord_2886515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886515).length < 2 ^ (prefixWord ++ tailWord_2886515).sum := by decide
  have hdescent : baseEnd_2886515 < baseStart_2886515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886525 : List Nat := [1, 4, 1, 1, 2, 1, 4, 2, 1, 1, 5]
def baseStart_2886525 : Nat := 118140960795 + 2886525 * 2 ^ 59
def prefixEnd_2886525 : Nat := 4983230072969 + 3 ^ 40 * 2886525 * 2
def baseEnd_2886525 : Nat := 1482174746219424191362619

theorem tailTrace_2886525 : CollatzResearch.WordTrace tailWord_2886525 prefixEnd_2886525 1482174746219424191362619 := by
  unfold tailWord_2886525
  simp only [CollatzResearch.WordTrace]
  refine ⟨105280215867620379067029029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70186810578413586044686019 105280215867620379067029029)
  ·
    refine ⟨19740040475178821075067943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105280215867620379067029029 19740040475178821075067943)
    ·
      refine ⟨29610060712768231612601915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19740040475178821075067943 29610060712768231612601915)
      ·
        refine ⟨44415091069152347418902873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29610060712768231612601915 44415091069152347418902873)
        ·
          refine ⟨33311318301864260564177155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44415091069152347418902873 33311318301864260564177155)
          ·
            refine ⟨49966977452796390846265733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33311318301864260564177155 49966977452796390846265733)
            ·
              refine ⟨9368808272399323283674825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49966977452796390846265733 9368808272399323283674825)
              ·
                refine ⟨7026606204299492462756119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9368808272399323283674825 7026606204299492462756119)
                ·
                  refine ⟨10539909306449238694134179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7026606204299492462756119 10539909306449238694134179)
                  ·
                    refine ⟨15809863959673858041201269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10539909306449238694134179 15809863959673858041201269)
                    ·
                      refine ⟨1482174746219424191362619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15809863959673858041201269 1482174746219424191362619)
                      ·
                        rfl

theorem cell23_2886525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_2886525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886525 prefixEnd_2886525 := by exact prefixLift 2886525
  have htrace : WordTrace (prefixWord ++ tailWord_2886525) baseStart_2886525 baseEnd_2886525 := by
    simpa [prefixWord, tailWord_2886525, baseEnd_2886525] using wordTrace_append hprefix tailTrace_2886525
  have hstable : (prefixWord ++ tailWord_2886525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886525).length < 2 ^ (prefixWord ++ tailWord_2886525).sum := by decide
  have hdescent : baseEnd_2886525 < baseStart_2886525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886535 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_2886535 : Nat := 118140960795 + 2886535 * 2 ^ 59
def prefixEnd_2886535 : Nat := 4983230072969 + 3 ^ 40 * 2886535 * 2
def baseEnd_2886535 : Nat := 1482179881025969152237573

theorem tailTrace_2886535 : CollatzResearch.WordTrace tailWord_2886535 prefixEnd_2886535 1482179881025969152237573 := by
  unfold tailWord_2886535
  simp only [CollatzResearch.WordTrace]
  refine ⟨105280580597584150774893059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70187053731722767183262039 105280580597584150774893059)
  ·
    refine ⟨157920870896376226162339589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105280580597584150774893059 157920870896376226162339589)
    ·
      refine ⟨29610163293070542405438673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157920870896376226162339589 29610163293070542405438673)
      ·
        refine ⟨22207622469802906804079005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29610163293070542405438673 22207622469802906804079005)
        ·
          refine ⟨8327858426176090051529627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22207622469802906804079005 8327858426176090051529627)
          ·
            refine ⟨12491787639264135077294441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8327858426176090051529627 12491787639264135077294441)
            ·
              refine ⟨9368840729448101307970831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12491787639264135077294441 9368840729448101307970831)
              ·
                refine ⟨14053261094172151961956247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9368840729448101307970831 14053261094172151961956247)
                ·
                  refine ⟨21079891641258227942934371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14053261094172151961956247 21079891641258227942934371)
                  ·
                    refine ⟨31619837461887341914401557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21079891641258227942934371 31619837461887341914401557)
                    ·
                      refine ⟨1482179881025969152237573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31619837461887341914401557 1482179881025969152237573)
                      ·
                        rfl

theorem cell23_2886535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_2886535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886535 prefixEnd_2886535 := by exact prefixLift 2886535
  have htrace : WordTrace (prefixWord ++ tailWord_2886535) baseStart_2886535 baseEnd_2886535 := by
    simpa [prefixWord, tailWord_2886535, baseEnd_2886535] using wordTrace_append hprefix tailTrace_2886535
  have hstable : (prefixWord ++ tailWord_2886535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886535).length < 2 ^ (prefixWord ++ tailWord_2886535).sum := by decide
  have hdescent : baseEnd_2886535 < baseStart_2886535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886556 : List Nat := [2, 2, 3, 3, 2, 1, 3, 1, 1, 1, 4]
def baseStart_2886556 : Nat := 118140960795 + 2886556 * 2 ^ 59
def prefixEnd_2886556 : Nat := 4983230072969 + 3 ^ 40 * 2886556 * 2
def baseEnd_2886556 : Nat := 1482190664119713570074977

theorem tailTrace_2886556 : CollatzResearch.WordTrace tailWord_2886556 prefixEnd_2886556 1482190664119713570074977 := by
  unfold tailWord_2886556
  simp only [CollatzResearch.WordTrace]
  refine ⟨52640673265254035680703761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70187564353672047574271681 52640673265254035680703761)
  ·
    refine ⟨39480504948940526760527821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52640673265254035680703761 39480504948940526760527821)
    ·
      refine ⟨14805189355852697535197933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39480504948940526760527821 14805189355852697535197933)
      ·
        refine ⟨5551946008444761575699225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14805189355852697535197933 5551946008444761575699225)
        ·
          refine ⟨4163959506333571181774419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5551946008444761575699225 4163959506333571181774419)
          ·
            refine ⟨6245939259500356772661629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4163959506333571181774419 6245939259500356772661629)
            ·
              refine ⟨2342227222312633789748111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6245939259500356772661629 2342227222312633789748111)
              ·
                refine ⟨3513340833468950684622167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342227222312633789748111 3513340833468950684622167)
                ·
                  refine ⟨5270011250203426026933251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3513340833468950684622167 5270011250203426026933251)
                  ·
                    refine ⟨7905016875305139040399877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5270011250203426026933251 7905016875305139040399877)
                    ·
                      refine ⟨1482190664119713570074977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7905016875305139040399877 1482190664119713570074977)
                      ·
                        rfl

theorem cell23_2886556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_2886556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886556 prefixEnd_2886556 := by exact prefixLift 2886556
  have htrace : WordTrace (prefixWord ++ tailWord_2886556) baseStart_2886556 baseEnd_2886556 := by
    simpa [prefixWord, tailWord_2886556, baseEnd_2886556] using wordTrace_append hprefix tailTrace_2886556
  have hstable : (prefixWord ++ tailWord_2886556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886556).length < 2 ^ (prefixWord ++ tailWord_2886556).sum := by decide
  have hdescent : baseEnd_2886556 < baseStart_2886556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
