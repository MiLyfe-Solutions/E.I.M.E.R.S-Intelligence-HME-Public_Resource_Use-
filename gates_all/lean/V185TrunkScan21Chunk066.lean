import V185TrunkScan21Chunk065

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_798038 : List Nat := [5, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_798038 : Nat := 118140960795 + 798038 * 2 ^ 59
def prefixEnd_798038 : Nat := 4983230072969 + 3 ^ 40 * 798038 * 2
def baseEnd_798038 : Nat := 182123144245712847268843

theorem tailTrace_798038 : CollatzResearch.WordTrace tailWord_798038 prefixEnd_798038 182123144245712847268843 := by
  unfold tailWord_798038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1819177317678255930286673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19404558055234729923057845 1819177317678255930286673)
  ·
    refine ⟨1364382988258691947715005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1819177317678255930286673 1364382988258691947715005)
    ·
      refine ⟨511643620597009480393127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1364382988258691947715005 511643620597009480393127)
      ·
        refine ⟨767465430895514220589691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511643620597009480393127 767465430895514220589691)
        ·
          refine ⟨1151198146343271330884537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 767465430895514220589691 1151198146343271330884537)
          ·
            refine ⟨863398609757453498163403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1151198146343271330884537 863398609757453498163403)
            ·
              refine ⟨1295097914636180247245105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863398609757453498163403 1295097914636180247245105)
              ·
                refine ⟨971323435977135185433829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1295097914636180247245105 971323435977135185433829)
                ·
                  refine ⟨182123144245712847268843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 971323435977135185433829 182123144245712847268843)
                  ·
                    rfl

theorem cell21_798038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_798038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_798038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_798038 prefixEnd_798038 := by exact prefixLift 798038
  have htrace : WordTrace (prefixWord ++ tailWord_798038) baseStart_798038 baseEnd_798038 := by
    simpa [prefixWord, tailWord_798038, baseEnd_798038] using wordTrace_append hprefix tailTrace_798038
  have hstable : (prefixWord ++ tailWord_798038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798038).length < 2 ^ (prefixWord ++ tailWord_798038).sum := by decide
  have hdescent : baseEnd_798038 < baseStart_798038 := by decide
  rcases family_descends (prefixWord ++ tailWord_798038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798212 : List Nat := [2, 3, 2, 3, 2, 1, 8]
def baseStart_798212 : Nat := 118140960795 + 798212 * 2 ^ 59
def prefixEnd_798212 : Nat := 4983230072969 + 3 ^ 40 * 798212 * 2
def baseEnd_798212 : Nat := 20240317046258579040943

theorem tailTrace_798212 : CollatzResearch.WordTrace tailWord_798212 prefixEnd_798212 20240317046258579040943 := by
  unfold tailWord_798212
  simp only [CollatzResearch.WordTrace]
  refine ⟨14556591692110861300710445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19408788922814481734280593 14556591692110861300710445)
  ·
    refine ⟨5458721884541572987766417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14556591692110861300710445 5458721884541572987766417)
    ·
      refine ⟨4094041413406179740824813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5458721884541572987766417 4094041413406179740824813)
      ·
        refine ⟨1535265530027317402809305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4094041413406179740824813 1535265530027317402809305)
        ·
          refine ⟨1151449147520488052106979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1535265530027317402809305 1151449147520488052106979)
          ·
            refine ⟨1727173721280732078160469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151449147520488052106979 1727173721280732078160469)
            ·
              refine ⟨20240317046258579040943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1727173721280732078160469 20240317046258579040943)
              ·
                rfl

theorem cell21_798212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 8].length) (baseStart_798212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_798212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_798212 prefixEnd_798212 := by exact prefixLift 798212
  have htrace : WordTrace (prefixWord ++ tailWord_798212) baseStart_798212 baseEnd_798212 := by
    simpa [prefixWord, tailWord_798212, baseEnd_798212] using wordTrace_append hprefix tailTrace_798212
  have hstable : (prefixWord ++ tailWord_798212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798212).length < 2 ^ (prefixWord ++ tailWord_798212).sum := by decide
  have hdescent : baseEnd_798212 < baseStart_798212 := by decide
  rcases family_descends (prefixWord ++ tailWord_798212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798271 : List Nat := [1, 1, 2, 2, 3, 5, 7]
def baseStart_798271 : Nat := 118140960795 + 798271 * 2 ^ 59
def prefixEnd_798271 : Nat := 4983230072969 + 3 ^ 40 * 798271 * 2
def baseEnd_798271 : Nat := 20241813113350691098337

theorem tailTrace_798271 : CollatzResearch.WordTrace tailWord_798271 prefixEnd_798271 20241813113350691098337 := by
  unfold tailWord_798271
  simp only [CollatzResearch.WordTrace]
  refine ⟨29115335291007975677818667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19410223527338650451879111 29115335291007975677818667)
  ·
    refine ⟨43673002936511963516728001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29115335291007975677818667 43673002936511963516728001)
    ·
      refine ⟨32754752202383972637546001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43673002936511963516728001 32754752202383972637546001)
      ·
        refine ⟨24566064151787979478159501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32754752202383972637546001 24566064151787979478159501)
        ·
          refine ⟨9212274056920492304309813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24566064151787979478159501 9212274056920492304309813)
          ·
            refine ⟨863650692836296153529045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9212274056920492304309813 863650692836296153529045)
            ·
              refine ⟨20241813113350691098337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 863650692836296153529045 20241813113350691098337)
              ·
                rfl

theorem cell21_798271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 7].length) (baseStart_798271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_798271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_798271 prefixEnd_798271 := by exact prefixLift 798271
  have htrace : WordTrace (prefixWord ++ tailWord_798271) baseStart_798271 baseEnd_798271 := by
    simpa [prefixWord, tailWord_798271, baseEnd_798271] using wordTrace_append hprefix tailTrace_798271
  have hstable : (prefixWord ++ tailWord_798271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798271).length < 2 ^ (prefixWord ++ tailWord_798271).sum := by decide
  have hdescent : baseEnd_798271 < baseStart_798271 := by decide
  rcases family_descends (prefixWord ++ tailWord_798271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798333 : List Nat := [1, 4, 1, 1, 4, 1, 1, 4, 4]
def baseStart_798333 : Nat := 118140960795 + 798333 * 2 ^ 59
def prefixEnd_798333 : Nat := 4983230072969 + 3 ^ 40 * 798333 * 2
def baseEnd_798333 : Nat := 182190467264857889851573

theorem tailTrace_798333 : CollatzResearch.WordTrace tailWord_798333 prefixEnd_798333 182190467264857889851573 := by
  unfold tailWord_798333
  simp only [CollatzResearch.WordTrace]
  refine ⟨29117596616783360266575653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19411731077855573511050435 29117596616783360266575653)
  ·
    refine ⟨5459549365646880049982935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29117596616783360266575653 5459549365646880049982935)
    ·
      refine ⟨8189324048470320074974403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5459549365646880049982935 8189324048470320074974403)
      ·
        refine ⟨12283986072705480112461605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8189324048470320074974403 12283986072705480112461605)
        ·
          refine ⟨2303247388632277521086551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12283986072705480112461605 2303247388632277521086551)
          ·
            refine ⟨3454871082948416281629827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2303247388632277521086551 3454871082948416281629827)
            ·
              refine ⟨5182306624422624422444741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3454871082948416281629827 5182306624422624422444741)
              ·
                refine ⟨971682492079242079208389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5182306624422624422444741 971682492079242079208389)
                ·
                  refine ⟨182190467264857889851573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 971682492079242079208389 182190467264857889851573)
                  ·
                    rfl

theorem cell21_798333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_798333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_798333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_798333 prefixEnd_798333 := by exact prefixLift 798333
  have htrace : WordTrace (prefixWord ++ tailWord_798333) baseStart_798333 baseEnd_798333 := by
    simpa [prefixWord, tailWord_798333, baseEnd_798333] using wordTrace_append hprefix tailTrace_798333
  have hstable : (prefixWord ++ tailWord_798333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798333).length < 2 ^ (prefixWord ++ tailWord_798333).sum := by decide
  have hdescent : baseEnd_798333 < baseStart_798333 := by decide
  rcases family_descends (prefixWord ++ tailWord_798333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798516 : List Nat := [2, 5, 1, 1, 2, 1, 3, 6]
def baseStart_798516 : Nat := 118140960795 + 798516 * 2 ^ 59
def prefixEnd_798516 : Nat := 4983230072969 + 3 ^ 40 * 798516 * 2
def baseEnd_798516 : Nat := 60744076786030079433733

theorem tailTrace_798516 : CollatzResearch.WordTrace tailWord_798516 prefixEnd_798516 60744076786030079433733 := by
  unfold tailWord_798516
  simp only [CollatzResearch.WordTrace]
  refine ⟨14562135587560191260243701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19416180783413588346991601 14562135587560191260243701)
  ·
    refine ⟨1365200211333767930647847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14562135587560191260243701 1365200211333767930647847)
    ·
      refine ⟨2047800317000651895971771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1365200211333767930647847 2047800317000651895971771)
      ·
        refine ⟨3071700475500977843957657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2047800317000651895971771 3071700475500977843957657)
        ·
          refine ⟨2303775356625733382968243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3071700475500977843957657 2303775356625733382968243)
          ·
            refine ⟨3455663034938600074452365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2303775356625733382968243 3455663034938600074452365)
            ·
              refine ⟨1295873638101975027919637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3455663034938600074452365 1295873638101975027919637)
              ·
                refine ⟨60744076786030079433733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1295873638101975027919637 60744076786030079433733)
                ·
                  rfl

theorem cell21_798516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 6].length) (baseStart_798516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_798516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_798516 prefixEnd_798516 := by exact prefixLift 798516
  have htrace : WordTrace (prefixWord ++ tailWord_798516) baseStart_798516 baseEnd_798516 := by
    simpa [prefixWord, tailWord_798516, baseEnd_798516] using wordTrace_append hprefix tailTrace_798516
  have hstable : (prefixWord ++ tailWord_798516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798516).length < 2 ^ (prefixWord ++ tailWord_798516).sum := by decide
  have hdescent : baseEnd_798516 < baseStart_798516 := by decide
  rcases family_descends (prefixWord ++ tailWord_798516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798623 : List Nat := [1, 1, 2, 5, 3, 2, 1, 1, 5]
def baseStart_798623 : Nat := 118140960795 + 798623 * 2 ^ 59
def prefixEnd_798623 : Nat := 4983230072969 + 3 ^ 40 * 798623 * 2
def baseEnd_798623 : Nat := 182256649215881830017647

theorem tailTrace_798623 : CollatzResearch.WordTrace tailWord_798623 prefixEnd_798623 182256649215881830017647 := by
  unfold tailWord_798623
  simp only [CollatzResearch.WordTrace]
  refine ⟨29128173785732739794632523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19418782523821826529755015 29128173785732739794632523)
  ·
    refine ⟨43692260678599109691948785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29128173785732739794632523 43692260678599109691948785)
    ·
      refine ⟨32769195508949332268961589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43692260678599109691948785 32769195508949332268961589)
      ·
        refine ⟨3072112078963999900215149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32769195508949332268961589 3072112078963999900215149)
        ·
          refine ⟨1152042029611499962580681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3072112078963999900215149 1152042029611499962580681)
          ·
            refine ⟨864031522208624971935511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1152042029611499962580681 864031522208624971935511)
            ·
              refine ⟨1296047283312937457903267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864031522208624971935511 1296047283312937457903267)
              ·
                refine ⟨1944070924969406186854901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1296047283312937457903267 1944070924969406186854901)
                ·
                  refine ⟨182256649215881830017647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1944070924969406186854901 182256649215881830017647)
                  ·
                    rfl

theorem cell21_798623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 5].length) (baseStart_798623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_798623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_798623 prefixEnd_798623 := by exact prefixLift 798623
  have htrace : WordTrace (prefixWord ++ tailWord_798623) baseStart_798623 baseEnd_798623 := by
    simpa [prefixWord, tailWord_798623, baseEnd_798623] using wordTrace_append hprefix tailTrace_798623
  have hstable : (prefixWord ++ tailWord_798623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798623).length < 2 ^ (prefixWord ++ tailWord_798623).sum := by decide
  have hdescent : baseEnd_798623 < baseStart_798623 := by decide
  rcases family_descends (prefixWord ++ tailWord_798623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798674 : List Nat := [3, 2, 2, 3, 3, 1, 2, 2, 3]
def baseStart_798674 : Nat := 118140960795 + 798674 * 2 ^ 59
def prefixEnd_798674 : Nat := 4983230072969 + 3 ^ 40 * 798674 * 2
def baseEnd_798674 : Nat := 182268288110717074667543

theorem tailTrace_798674 : CollatzResearch.WordTrace tailWord_798674 prefixEnd_798674 182268288110717074667543 := by
  unfold tailWord_798674
  simp only [CollatzResearch.WordTrace]
  refine ⟨7282508477136993876184769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19420022605698650336492717 7282508477136993876184769)
  ·
    refine ⟨5461881357852745407138577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7282508477136993876184769 5461881357852745407138577)
    ·
      refine ⟨4096411018389559055353933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5461881357852745407138577 4096411018389559055353933)
      ·
        refine ⟨1536154131896084645757725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4096411018389559055353933 1536154131896084645757725)
        ·
          refine ⟨576057799461031742159147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1536154131896084645757725 576057799461031742159147)
          ·
            refine ⟨864086699191547613238721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576057799461031742159147 864086699191547613238721)
            ·
              refine ⟨648065024393660709929041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 864086699191547613238721 648065024393660709929041)
              ·
                refine ⟨486048768295245532446781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 648065024393660709929041 486048768295245532446781)
                ·
                  refine ⟨182268288110717074667543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 486048768295245532446781 182268288110717074667543)
                  ·
                    rfl

theorem cell21_798674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_798674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_798674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_798674 prefixEnd_798674 := by exact prefixLift 798674
  have htrace : WordTrace (prefixWord ++ tailWord_798674) baseStart_798674 baseEnd_798674 := by
    simpa [prefixWord, tailWord_798674, baseEnd_798674] using wordTrace_append hprefix tailTrace_798674
  have hstable : (prefixWord ++ tailWord_798674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798674).length < 2 ^ (prefixWord ++ tailWord_798674).sum := by decide
  have hdescent : baseEnd_798674 < baseStart_798674 := by decide
  rcases family_descends (prefixWord ++ tailWord_798674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798685 : List Nat := [1, 4, 3, 1, 4, 1, 1, 6]
def baseStart_798685 : Nat := 118140960795 + 798685 * 2 ^ 59
def prefixEnd_798685 : Nat := 4983230072969 + 3 ^ 40 * 798685 * 2
def baseEnd_798685 : Nat := 60756932820194499994729

theorem tailTrace_798685 : CollatzResearch.WordTrace tailWord_798685 prefixEnd_798685 60756932820194499994729 := by
  unfold tailWord_798685
  simp only [CollatzResearch.WordTrace]
  refine ⟨29130435111508124383389509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19420290074338749588926339 29130435111508124383389509)
  ·
    refine ⟨5461956583407773321885533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29130435111508124383389509 5461956583407773321885533)
    ·
      refine ⟨2048233718777914995707075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5461956583407773321885533 2048233718777914995707075)
      ·
        refine ⟨3072350578166872493560613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2048233718777914995707075 3072350578166872493560613)
        ·
          refine ⟨576065733406288592542615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3072350578166872493560613 576065733406288592542615)
          ·
            refine ⟨864098600109432888813923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576065733406288592542615 864098600109432888813923)
            ·
              refine ⟨1296147900164149333220885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864098600109432888813923 1296147900164149333220885)
              ·
                refine ⟨60756932820194499994729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1296147900164149333220885 60756932820194499994729)
                ·
                  rfl

theorem cell21_798685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 6].length) (baseStart_798685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_798685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_798685 prefixEnd_798685 := by exact prefixLift 798685
  have htrace : WordTrace (prefixWord ++ tailWord_798685) baseStart_798685 baseEnd_798685 := by
    simpa [prefixWord, tailWord_798685, baseEnd_798685] using wordTrace_append hprefix tailTrace_798685
  have hstable : (prefixWord ++ tailWord_798685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798685).length < 2 ^ (prefixWord ++ tailWord_798685).sum := by decide
  have hdescent : baseEnd_798685 < baseStart_798685 := by decide
  rcases family_descends (prefixWord ++ tailWord_798685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798730 : List Nat := [3, 1, 2, 2, 4, 2, 1, 2, 4]
def baseStart_798730 : Nat := 118140960795 + 798730 * 2 ^ 59
def prefixEnd_798730 : Nat := 4983230072969 + 3 ^ 40 * 798730 * 2
def baseEnd_798730 : Nat := 182281068073673421734095

theorem tailTrace_798730 : CollatzResearch.WordTrace tailWord_798730 prefixEnd_798730 182281068073673421734095 := by
  unfold tailWord_798730
  simp only [CollatzResearch.WordTrace]
  refine ⟨7283019099086274267194411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19421384264230064712518429 7283019099086274267194411)
  ·
    refine ⟨10924528648629411400791617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7283019099086274267194411 10924528648629411400791617)
    ·
      refine ⟨8193396486472058550593713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10924528648629411400791617 8193396486472058550593713)
      ·
        refine ⟨6145047364854043912945285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8193396486472058550593713 6145047364854043912945285)
        ·
          refine ⟨1152196380910133233677241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6145047364854043912945285 1152196380910133233677241)
          ·
            refine ⟨864147285682599925257931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1152196380910133233677241 864147285682599925257931)
            ·
              refine ⟨1296220928523899887886897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864147285682599925257931 1296220928523899887886897)
              ·
                refine ⟨972165696392924915915173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1296220928523899887886897 972165696392924915915173)
                ·
                  refine ⟨182281068073673421734095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 972165696392924915915173 182281068073673421734095)
                  ·
                    rfl

theorem cell21_798730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_798730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_798730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_798730 prefixEnd_798730 := by exact prefixLift 798730
  have htrace : WordTrace (prefixWord ++ tailWord_798730) baseStart_798730 baseEnd_798730 := by
    simpa [prefixWord, tailWord_798730, baseEnd_798730] using wordTrace_append hprefix tailTrace_798730
  have hstable : (prefixWord ++ tailWord_798730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798730).length < 2 ^ (prefixWord ++ tailWord_798730).sum := by decide
  have hdescent : baseEnd_798730 < baseStart_798730 := by decide
  rcases family_descends (prefixWord ++ tailWord_798730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798733 : List Nat := [1, 7, 1, 2, 1, 1, 2, 1, 5]
def baseStart_798733 : Nat := 118140960795 + 798733 * 2 ^ 59
def prefixEnd_798733 : Nat := 4983230072969 + 3 ^ 40 * 798733 * 2
def baseEnd_798733 : Nat := 182281752714546083184089

theorem tailTrace_798733 : CollatzResearch.WordTrace tailWord_798733 prefixEnd_798733 182281752714546083184089 := by
  unfold tailWord_798733
  simp only [CollatzResearch.WordTrace]
  refine ⟨29132185815334228581136853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19421457210222819054091235 29132185815334228581136853)
  ·
    refine ⟨682785605046895982370395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 29132185815334228581136853 682785605046895982370395)
    ·
      refine ⟨1024178407570343973555593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 682785605046895982370395 1024178407570343973555593)
      ·
        refine ⟨768133805677757980166695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1024178407570343973555593 768133805677757980166695)
        ·
          refine ⟨1152200708516636970250043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768133805677757980166695 1152200708516636970250043)
          ·
            refine ⟨1728301062774955455375065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1152200708516636970250043 1728301062774955455375065)
            ·
              refine ⟨1296225797081216591531299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1728301062774955455375065 1296225797081216591531299)
              ·
                refine ⟨1944338695621824887296949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1296225797081216591531299 1944338695621824887296949)
                ·
                  refine ⟨182281752714546083184089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1944338695621824887296949 182281752714546083184089)
                  ·
                    rfl

theorem cell21_798733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_798733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_798733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_798733 prefixEnd_798733 := by exact prefixLift 798733
  have htrace : WordTrace (prefixWord ++ tailWord_798733) baseStart_798733 baseEnd_798733 := by
    simpa [prefixWord, tailWord_798733, baseEnd_798733] using wordTrace_append hprefix tailTrace_798733
  have hstable : (prefixWord ++ tailWord_798733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798733).length < 2 ^ (prefixWord ++ tailWord_798733).sum := by decide
  have hdescent : baseEnd_798733 < baseStart_798733 := by decide
  rcases family_descends (prefixWord ++ tailWord_798733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798851 : List Nat := [1, 1, 1, 3, 3, 3, 4, 2, 3]
def baseStart_798851 : Nat := 118140960795 + 798851 * 2 ^ 59
def prefixEnd_798851 : Nat := 4983230072969 + 3 ^ 40 * 798851 * 2
def baseEnd_798851 : Nat := 182308681922204100217181

theorem tailTrace_798851 : CollatzResearch.WordTrace tailWord_798851 prefixEnd_798851 182308681922204100217181 := by
  unfold tailWord_798851
  simp only [CollatzResearch.WordTrace]
  refine ⟨29136489628906734733932407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19424326419271156489288271 29136489628906734733932407)
  ·
    refine ⟨43704734443360102100898611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29136489628906734733932407 43704734443360102100898611)
    ·
      refine ⟨65557101665040153151347917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43704734443360102100898611 65557101665040153151347917)
      ·
        refine ⟨24583913124390057431755469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65557101665040153151347917 24583913124390057431755469)
        ·
          refine ⟨9218967421646271536908301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24583913124390057431755469 9218967421646271536908301)
          ·
            refine ⟨3457112783117351826340613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9218967421646271536908301 3457112783117351826340613)
            ·
              refine ⟨648208646834503467438865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3457112783117351826340613 648208646834503467438865)
              ·
                refine ⟨486156485125877600579149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 648208646834503467438865 486156485125877600579149)
                ·
                  refine ⟨182308681922204100217181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 486156485125877600579149 182308681922204100217181)
                  ·
                    rfl

theorem cell21_798851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 3].length) (baseStart_798851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_798851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_798851 prefixEnd_798851 := by exact prefixLift 798851
  have htrace : WordTrace (prefixWord ++ tailWord_798851) baseStart_798851 baseEnd_798851 := by
    simpa [prefixWord, tailWord_798851, baseEnd_798851] using wordTrace_append hprefix tailTrace_798851
  have hstable : (prefixWord ++ tailWord_798851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798851).length < 2 ^ (prefixWord ++ tailWord_798851).sum := by decide
  have hdescent : baseEnd_798851 < baseStart_798851 := by decide
  rcases family_descends (prefixWord ++ tailWord_798851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798907 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 6]
def baseStart_798907 : Nat := 118140960795 + 798907 * 2 ^ 59
def prefixEnd_798907 : Nat := 4983230072969 + 3 ^ 40 * 798907 * 2
def baseEnd_798907 : Nat := 182321461885160447283733

theorem tailTrace_798907 : CollatzResearch.WordTrace tailWord_798907 prefixEnd_798907 182321461885160447283733 := by
  unfold tailWord_798907
  simp only [CollatzResearch.WordTrace]
  refine ⟨29138532116703856297970975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19425688077802570865313983 29138532116703856297970975)
  ·
    refine ⟨43707798175055784446956463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29138532116703856297970975 43707798175055784446956463)
    ·
      refine ⟨65561697262583676670434695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43707798175055784446956463 65561697262583676670434695)
      ·
        refine ⟨98342545893875515005652043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65561697262583676670434695 98342545893875515005652043)
        ·
          refine ⟨147513818840813272508478065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98342545893875515005652043 147513818840813272508478065)
          ·
            refine ⟨110635364130609954381358549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147513818840813272508478065 110635364130609954381358549)
            ·
              refine ⟨2593016346811170805813091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 110635364130609954381358549 2593016346811170805813091)
              ·
                refine ⟨3889524520216756208719637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2593016346811170805813091 3889524520216756208719637)
                ·
                  refine ⟨182321461885160447283733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3889524520216756208719637 182321461885160447283733)
                  ·
                    rfl

theorem cell21_798907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 6].length) (baseStart_798907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_798907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_798907 prefixEnd_798907 := by exact prefixLift 798907
  have htrace : WordTrace (prefixWord ++ tailWord_798907) baseStart_798907 baseEnd_798907 := by
    simpa [prefixWord, tailWord_798907, baseEnd_798907] using wordTrace_append hprefix tailTrace_798907
  have hstable : (prefixWord ++ tailWord_798907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798907).length < 2 ^ (prefixWord ++ tailWord_798907).sum := by decide
  have hdescent : baseEnd_798907 < baseStart_798907 := by decide
  rcases family_descends (prefixWord ++ tailWord_798907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799124 : List Nat := [2, 4, 2, 1, 4, 1, 7]
def baseStart_799124 : Nat := 118140960795 + 799124 * 2 ^ 59
def prefixEnd_799124 : Nat := 4983230072969 + 3 ^ 40 * 799124 * 2
def baseEnd_799124 : Nat := 20263442693512921351847

theorem tailTrace_799124 : CollatzResearch.WordTrace tailWord_799124 prefixEnd_799124 20263442693512921351847 := by
  unfold tailWord_799124
  simp only [CollatzResearch.WordTrace]
  refine ⟨14573223378458851179310213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19430964504611801572413617 14573223378458851179310213)
  ·
    refine ⟨2732479383461034596120665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14573223378458851179310213 2732479383461034596120665)
    ·
      refine ⟨2049359537595775947090499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2732479383461034596120665 2049359537595775947090499)
      ·
        refine ⟨3074039306393663920635749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2049359537595775947090499 3074039306393663920635749)
        ·
          refine ⟨576382369948811985119203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3074039306393663920635749 576382369948811985119203)
          ·
            refine ⟨864573554923217977678805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576382369948811985119203 864573554923217977678805)
            ·
              refine ⟨20263442693512921351847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 864573554923217977678805 20263442693512921351847)
              ·
                rfl

theorem cell21_799124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 7].length) (baseStart_799124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799124 prefixEnd_799124 := by exact prefixLift 799124
  have htrace : WordTrace (prefixWord ++ tailWord_799124) baseStart_799124 baseEnd_799124 := by
    simpa [prefixWord, tailWord_799124, baseEnd_799124] using wordTrace_append hprefix tailTrace_799124
  have hstable : (prefixWord ++ tailWord_799124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799124).length < 2 ^ (prefixWord ++ tailWord_799124).sum := by decide
  have hdescent : baseEnd_799124 < baseStart_799124 := by decide
  rcases family_descends (prefixWord ++ tailWord_799124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799135 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 6]
def baseStart_799135 : Nat := 118140960795 + 799135 * 2 ^ 59
def prefixEnd_799135 : Nat := 4983230072969 + 3 ^ 40 * 799135 * 2
def baseEnd_799135 : Nat := 182373494591482717483267

theorem tailTrace_799135 : CollatzResearch.WordTrace tailWord_799135 prefixEnd_799135 182373494591482717483267 := by
  unfold tailWord_799135
  simp only [CollatzResearch.WordTrace]
  refine ⟨29146847959877851237270859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19431231973251900824847239 29146847959877851237270859)
  ·
    refine ⟨43720271939816776855906289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29146847959877851237270859 43720271939816776855906289)
    ·
      refine ⟨32790203954862582641929717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43720271939816776855906289 32790203954862582641929717)
      ·
        refine ⟨3074081620768367122680911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32790203954862582641929717 3074081620768367122680911)
        ·
          refine ⟨4611122431152550684021367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3074081620768367122680911 4611122431152550684021367)
          ·
            refine ⟨6916683646728826026032051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4611122431152550684021367 6916683646728826026032051)
            ·
              refine ⟨10375025470093239039048077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6916683646728826026032051 10375025470093239039048077)
              ·
                refine ⟨3890634551284964639643029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10375025470093239039048077 3890634551284964639643029)
                ·
                  refine ⟨182373494591482717483267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3890634551284964639643029 182373494591482717483267)
                  ·
                    rfl

theorem cell21_799135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 6].length) (baseStart_799135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799135 prefixEnd_799135 := by exact prefixLift 799135
  have htrace : WordTrace (prefixWord ++ tailWord_799135) baseStart_799135 baseEnd_799135 := by
    simpa [prefixWord, tailWord_799135, baseEnd_799135] using wordTrace_append hprefix tailTrace_799135
  have hstable : (prefixWord ++ tailWord_799135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799135).length < 2 ^ (prefixWord ++ tailWord_799135).sum := by decide
  have hdescent : baseEnd_799135 < baseStart_799135 := by decide
  rcases family_descends (prefixWord ++ tailWord_799135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799166 : List Nat := [4, 2, 1, 1, 1, 1, 4, 7]
def baseStart_799166 : Nat := 118140960795 + 799166 * 2 ^ 59
def prefixEnd_799166 : Nat := 4983230072969 + 3 ^ 40 * 799166 * 2
def baseEnd_799166 : Nat := 60793523071277850822179

theorem tailTrace_799166 : CollatzResearch.WordTrace tailWord_799166 prefixEnd_799166 60793523071277850822179 := by
  unfold tailWord_799166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3643497327845692941456169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19431985748510362354432901 3643497327845692941456169)
  ·
    refine ⟨2732622995884269706092127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3643497327845692941456169 2732622995884269706092127)
    ·
      refine ⟨4098934493826404559138191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2732622995884269706092127 4098934493826404559138191)
      ·
        refine ⟨6148401740739606838707287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4098934493826404559138191 6148401740739606838707287)
        ·
          refine ⟨9222602611109410258060931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6148401740739606838707287 9222602611109410258060931)
          ·
            refine ⟨13833903916664115387091397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9222602611109410258060931 13833903916664115387091397)
            ·
              refine ⟨2593856984374521635079637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13833903916664115387091397 2593856984374521635079637)
              ·
                refine ⟨60793523071277850822179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2593856984374521635079637 60793523071277850822179)
                ·
                  rfl

theorem cell21_799166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_799166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799166 prefixEnd_799166 := by exact prefixLift 799166
  have htrace : WordTrace (prefixWord ++ tailWord_799166) baseStart_799166 baseEnd_799166 := by
    simpa [prefixWord, tailWord_799166, baseEnd_799166] using wordTrace_append hprefix tailTrace_799166
  have hstable : (prefixWord ++ tailWord_799166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799166).length < 2 ^ (prefixWord ++ tailWord_799166).sum := by decide
  have hdescent : baseEnd_799166 < baseStart_799166 := by decide
  rcases family_descends (prefixWord ++ tailWord_799166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799186 : List Nat := [3, 2, 2, 4, 1, 1, 2, 2, 4]
def baseStart_799186 : Nat := 118140960795 + 799186 * 2 ^ 59
def prefixEnd_799186 : Nat := 4983230072969 + 3 ^ 40 * 799186 * 2
def baseEnd_799186 : Nat := 182385133486317962133163

theorem tailTrace_799186 : CollatzResearch.WordTrace tailWord_799186 prefixEnd_799186 182385133486317962133163 := by
  unfold tailWord_799186
  simp only [CollatzResearch.WordTrace]
  refine ⟨7287177020673271736844353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19432472055128724631584941 7287177020673271736844353)
  ·
    refine ⟨5465382765504953802633265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7287177020673271736844353 5465382765504953802633265)
    ·
      refine ⟨4099037074128715351974949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5465382765504953802633265 4099037074128715351974949)
      ·
        refine ⟨768569451399134128495303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4099037074128715351974949 768569451399134128495303)
        ·
          refine ⟨1152854177098701192742955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768569451399134128495303 1152854177098701192742955)
          ·
            refine ⟨1729281265648051789114433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1152854177098701192742955 1729281265648051789114433)
            ·
              refine ⟨1296960949236038841835825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1729281265648051789114433 1296960949236038841835825)
              ·
                refine ⟨972720711927029131376869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1296960949236038841835825 972720711927029131376869)
                ·
                  refine ⟨182385133486317962133163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 972720711927029131376869 182385133486317962133163)
                  ·
                    rfl

theorem cell21_799186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_799186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799186 prefixEnd_799186 := by exact prefixLift 799186
  have htrace : WordTrace (prefixWord ++ tailWord_799186) baseStart_799186 baseEnd_799186 := by
    simpa [prefixWord, tailWord_799186, baseEnd_799186] using wordTrace_append hprefix tailTrace_799186
  have hstable : (prefixWord ++ tailWord_799186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799186).length < 2 ^ (prefixWord ++ tailWord_799186).sum := by decide
  have hdescent : baseEnd_799186 < baseStart_799186 := by decide
  rcases family_descends (prefixWord ++ tailWord_799186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799197 : List Nat := [1, 4, 3, 1, 1, 1, 2, 3, 5]
def baseStart_799197 : Nat := 118140960795 + 799197 * 2 ^ 59
def prefixEnd_799197 : Nat := 4983230072969 + 3 ^ 40 * 799197 * 2
def baseEnd_799197 : Nat := 182387643836184387449807

theorem tailTrace_799197 : CollatzResearch.WordTrace tailWord_799197 prefixEnd_799197 182387643836184387449807 := by
  unfold tailWord_799197
  simp only [CollatzResearch.WordTrace]
  refine ⟨29149109285653235826027845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19432739523768823884018563 29149109285653235826027845)
  ·
    refine ⟨5465457991059981717380221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29149109285653235826027845 5465457991059981717380221)
    ·
      refine ⟨2049546746647493144017583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5465457991059981717380221 2049546746647493144017583)
      ·
        refine ⟨3074320119971239716026375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2049546746647493144017583 3074320119971239716026375)
        ·
          refine ⟨4611480179956859574039563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3074320119971239716026375 4611480179956859574039563)
          ·
            refine ⟨6917220269935289361059345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4611480179956859574039563 6917220269935289361059345)
            ·
              refine ⟨5187915202451467020794509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6917220269935289361059345 5187915202451467020794509)
              ·
                refine ⟨1945468200919300132797941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5187915202451467020794509 1945468200919300132797941)
                ·
                  refine ⟨182387643836184387449807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1945468200919300132797941 182387643836184387449807)
                  ·
                    rfl

theorem cell21_799197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_799197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799197 prefixEnd_799197 := by exact prefixLift 799197
  have htrace : WordTrace (prefixWord ++ tailWord_799197) baseStart_799197 baseEnd_799197 := by
    simpa [prefixWord, tailWord_799197, baseEnd_799197] using wordTrace_append hprefix tailTrace_799197
  have hstable : (prefixWord ++ tailWord_799197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799197).length < 2 ^ (prefixWord ++ tailWord_799197).sum := by decide
  have hdescent : baseEnd_799197 < baseStart_799197 := by decide
  rcases family_descends (prefixWord ++ tailWord_799197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799211 : List Nat := [1, 1, 1, 1, 2, 3, 3, 5, 4]
def baseStart_799211 : Nat := 118140960795 + 799211 * 2 ^ 59
def prefixEnd_799211 : Nat := 4983230072969 + 3 ^ 40 * 799211 * 2
def baseEnd_799211 : Nat := 182390838826923474216445

theorem tailTrace_799211 : CollatzResearch.WordTrace tailWord_799211 prefixEnd_799211 182390838826923474216445 := by
  unfold tailWord_799211
  simp only [CollatzResearch.WordTrace]
  refine ⟨29149619907602516217037487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19433079938401677478024991 29149619907602516217037487)
  ·
    refine ⟨43724429861403774325556231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29149619907602516217037487 43724429861403774325556231)
    ·
      refine ⟨65586644792105661488334347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43724429861403774325556231 65586644792105661488334347)
      ·
        refine ⟨98379967188158492232501521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65586644792105661488334347 98379967188158492232501521)
        ·
          refine ⟨73784975391118869174376141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98379967188158492232501521 73784975391118869174376141)
          ·
            refine ⟨27669365771669575940391053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73784975391118869174376141 27669365771669575940391053)
            ·
              refine ⟨10376012164376090977646645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27669365771669575940391053 10376012164376090977646645)
              ·
                refine ⟨972751140410258529154373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10376012164376090977646645 972751140410258529154373)
                ·
                  refine ⟨182390838826923474216445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 972751140410258529154373 182390838826923474216445)
                  ·
                    rfl

theorem cell21_799211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 4].length) (baseStart_799211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799211 prefixEnd_799211 := by exact prefixLift 799211
  have htrace : WordTrace (prefixWord ++ tailWord_799211) baseStart_799211 baseEnd_799211 := by
    simpa [prefixWord, tailWord_799211, baseEnd_799211] using wordTrace_append hprefix tailTrace_799211
  have hstable : (prefixWord ++ tailWord_799211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799211).length < 2 ^ (prefixWord ++ tailWord_799211).sum := by decide
  have hdescent : baseEnd_799211 < baseStart_799211 := by decide
  rcases family_descends (prefixWord ++ tailWord_799211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799225 : List Nat := [1, 2, 1, 3, 1, 2, 2, 9]
def baseStart_799225 : Nat := 118140960795 + 799225 * 2 ^ 59
def prefixEnd_799225 : Nat := 4983230072969 + 3 ^ 40 * 799225 * 2
def baseEnd_799225 : Nat := 60798011272554186994361

theorem tailTrace_799225 : CollatzResearch.WordTrace tailWord_799225 prefixEnd_799225 60798011272554186994361 := by
  unfold tailWord_799225
  simp only [CollatzResearch.WordTrace]
  refine ⟨29150130529551796608047129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19433420353034531072031419 29150130529551796608047129)
  ·
    refine ⟨21862597897163847456035347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29150130529551796608047129 21862597897163847456035347)
    ·
      refine ⟨32793896845745771184053021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21862597897163847456035347 32793896845745771184053021)
      ·
        refine ⟨12297711317154664194019883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32793896845745771184053021 12297711317154664194019883)
        ·
          refine ⟨18446566975731996291029825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12297711317154664194019883 18446566975731996291029825)
          ·
            refine ⟨13834925231798997218272369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18446566975731996291029825 13834925231798997218272369)
            ·
              refine ⟨10376193923849247913704277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13834925231798997218272369 10376193923849247913704277)
              ·
                refine ⟨60798011272554186994361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10376193923849247913704277 60798011272554186994361)
                ·
                  rfl

theorem cell21_799225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 9].length) (baseStart_799225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799225 prefixEnd_799225 := by exact prefixLift 799225
  have htrace : WordTrace (prefixWord ++ tailWord_799225) baseStart_799225 baseEnd_799225 := by
    simpa [prefixWord, tailWord_799225, baseEnd_799225] using wordTrace_append hprefix tailTrace_799225
  have hstable : (prefixWord ++ tailWord_799225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799225).length < 2 ^ (prefixWord ++ tailWord_799225).sum := by decide
  have hdescent : baseEnd_799225 < baseStart_799225 := by decide
  rcases family_descends (prefixWord ++ tailWord_799225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799290 : List Nat := [3, 1, 1, 1, 3, 3, 3, 3, 3]
def baseStart_799290 : Nat := 118140960795 + 799290 * 2 ^ 59
def prefixEnd_799290 : Nat := 4983230072969 + 3 ^ 40 * 799290 * 2
def baseEnd_799290 : Nat := 182408867703236892399617

theorem tailTrace_799290 : CollatzResearch.WordTrace tailWord_799290 prefixEnd_799290 182408867703236892399617 := by
  unfold tailWord_799290
  simp only [CollatzResearch.WordTrace]
  refine ⟨7288125318579078177290831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19435000849544208472775549 7288125318579078177290831)
  ·
    refine ⟨10932187977868617265936247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7288125318579078177290831 10932187977868617265936247)
    ·
      refine ⟨16398281966802925898904371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10932187977868617265936247 16398281966802925898904371)
      ·
        refine ⟨24597422950204388848356557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16398281966802925898904371 24597422950204388848356557)
        ·
          refine ⟨9224033606326645818133709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24597422950204388848356557 9224033606326645818133709)
          ·
            refine ⟨3459012602372492181800141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9224033606326645818133709 3459012602372492181800141)
            ·
              refine ⟨1297129725889684568175053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3459012602372492181800141 1297129725889684568175053)
              ·
                refine ⟨486423647208631713065645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1297129725889684568175053 486423647208631713065645)
                ·
                  refine ⟨182408867703236892399617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 486423647208631713065645 182408867703236892399617)
                  ·
                    rfl

theorem cell21_799290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_799290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799290 prefixEnd_799290 := by exact prefixLift 799290
  have htrace : WordTrace (prefixWord ++ tailWord_799290) baseStart_799290 baseEnd_799290 := by
    simpa [prefixWord, tailWord_799290, baseEnd_799290] using wordTrace_append hprefix tailTrace_799290
  have hstable : (prefixWord ++ tailWord_799290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799290).length < 2 ^ (prefixWord ++ tailWord_799290).sum := by decide
  have hdescent : baseEnd_799290 < baseStart_799290 := by decide
  rcases family_descends (prefixWord ++ tailWord_799290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799301 : List Nat := [1, 3, 1, 1, 1, 5, 9]
def baseStart_799301 : Nat := 118140960795 + 799301 * 2 ^ 59
def prefixEnd_799301 : Nat := 4983230072969 + 3 ^ 40 * 799301 * 2
def baseEnd_799301 : Nat := 20267930894789257524029

theorem tailTrace_799301 : CollatzResearch.WordTrace tailWord_799301 prefixEnd_799301 20267930894789257524029 := by
  unfold tailWord_799301
  simp only [CollatzResearch.WordTrace]
  refine ⟨29152902477276461587813757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19435268318184307725209171 29152902477276461587813757)
  ·
    refine ⟨10932338428978673095430159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29152902477276461587813757 10932338428978673095430159)
    ·
      refine ⟨16398507643468009643145239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10932338428978673095430159 16398507643468009643145239)
      ·
        refine ⟨24597761465202014464717859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16398507643468009643145239 24597761465202014464717859)
        ·
          refine ⟨36896642197803021697076789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24597761465202014464717859 36896642197803021697076789)
          ·
            refine ⟨3459060206044033284100949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36896642197803021697076789 3459060206044033284100949)
            ·
              refine ⟨20267930894789257524029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3459060206044033284100949 20267930894789257524029)
              ·
                rfl

theorem cell21_799301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 9].length) (baseStart_799301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799301 prefixEnd_799301 := by exact prefixLift 799301
  have htrace : WordTrace (prefixWord ++ tailWord_799301) baseStart_799301 baseEnd_799301 := by
    simpa [prefixWord, tailWord_799301, baseEnd_799301] using wordTrace_append hprefix tailTrace_799301
  have hstable : (prefixWord ++ tailWord_799301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799301).length < 2 ^ (prefixWord ++ tailWord_799301).sum := by decide
  have hdescent : baseEnd_799301 < baseStart_799301 := by decide
  rcases family_descends (prefixWord ++ tailWord_799301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799332 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 7]
def baseStart_799332 : Nat := 118140960795 + 799332 * 2 ^ 59
def prefixEnd_799332 : Nat := 4983230072969 + 3 ^ 40 * 799332 * 2
def baseEnd_799332 : Nat := 182418452675454152699531

theorem tailTrace_799332 : CollatzResearch.WordTrace tailWord_799332 prefixEnd_799332 182418452675454152699531 := by
  unfold tailWord_799332
  simp only [CollatzResearch.WordTrace]
  refine ⟨14577016570082076941096125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19436022093442769254794833 14577016570082076941096125)
  ·
    refine ⟨5466381213780778852911047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14577016570082076941096125 5466381213780778852911047)
    ·
      refine ⟨8199571820671168279366571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5466381213780778852911047 8199571820671168279366571)
      ·
        refine ⟨12299357731006752419049857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8199571820671168279366571 12299357731006752419049857)
        ·
          refine ⟨9224518298255064314287393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12299357731006752419049857 9224518298255064314287393)
          ·
            refine ⟨6918388723691298235715545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9224518298255064314287393 6918388723691298235715545)
            ·
              refine ⟨5188791542768473676786659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6918388723691298235715545 5188791542768473676786659)
              ·
                refine ⟨7783187314152710515179989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5188791542768473676786659 7783187314152710515179989)
                ·
                  refine ⟨182418452675454152699531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7783187314152710515179989 182418452675454152699531)
                  ·
                    rfl

theorem cell21_799332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_799332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799332 prefixEnd_799332 := by exact prefixLift 799332
  have htrace : WordTrace (prefixWord ++ tailWord_799332) baseStart_799332 baseEnd_799332 := by
    simpa [prefixWord, tailWord_799332, baseEnd_799332] using wordTrace_append hprefix tailTrace_799332
  have hstable : (prefixWord ++ tailWord_799332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799332).length < 2 ^ (prefixWord ++ tailWord_799332).sum := by decide
  have hdescent : baseEnd_799332 < baseStart_799332 := by decide
  rcases family_descends (prefixWord ++ tailWord_799332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799363 : List Nat := [1, 1, 1, 3, 3, 1, 3, 4, 4]
def baseStart_799363 : Nat := 118140960795 + 799363 * 2 ^ 59
def prefixEnd_799363 : Nat := 4983230072969 + 3 ^ 40 * 799363 * 2
def baseEnd_799363 : Nat := 182425527297804987682801

theorem tailTrace_799363 : CollatzResearch.WordTrace tailWord_799363 prefixEnd_799363 182425527297804987682801 := by
  unfold tailWord_799363
  simp only [CollatzResearch.WordTrace]
  refine ⟨29155163803051846176570743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19436775868701230784380495 29155163803051846176570743)
  ·
    refine ⟨43732745704577769264856115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29155163803051846176570743 43732745704577769264856115)
    ·
      refine ⟨65599118556866653897284173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43732745704577769264856115 65599118556866653897284173)
      ·
        refine ⟨24599669458824995211481565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65599118556866653897284173 24599669458824995211481565)
        ·
          refine ⟨9224876047059373204305587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24599669458824995211481565 9224876047059373204305587)
          ·
            refine ⟨13837314070589059806458381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9224876047059373204305587 13837314070589059806458381)
            ·
              refine ⟨5188992776470897427421893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13837314070589059806458381 5188992776470897427421893)
              ·
                refine ⟨972936145588293267641605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5188992776470897427421893 972936145588293267641605)
                ·
                  refine ⟨182425527297804987682801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 972936145588293267641605 182425527297804987682801)
                  ·
                    rfl

theorem cell21_799363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 4].length) (baseStart_799363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799363 prefixEnd_799363 := by exact prefixLift 799363
  have htrace : WordTrace (prefixWord ++ tailWord_799363) baseStart_799363 baseEnd_799363 := by
    simpa [prefixWord, tailWord_799363, baseEnd_799363] using wordTrace_append hprefix tailTrace_799363
  have hstable : (prefixWord ++ tailWord_799363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799363).length < 2 ^ (prefixWord ++ tailWord_799363).sum := by decide
  have hdescent : baseEnd_799363 < baseStart_799363 := by decide
  rcases family_descends (prefixWord ++ tailWord_799363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799445 : List Nat := [1, 3, 2, 5, 2, 1, 2, 5]
def baseStart_799445 : Nat := 118140960795 + 799445 * 2 ^ 59
def prefixEnd_799445 : Nat := 4983230072969 + 3 ^ 40 * 799445 * 2
def baseEnd_799445 : Nat := 60814746938330355771989

theorem tailTrace_799445 : CollatzResearch.WordTrace tailWord_799445 prefixEnd_799445 60814746938330355771989 := by
  unfold tailWord_799445
  simp only [CollatzResearch.WordTrace]
  refine ⟨29158154588754774181055789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19438769725836516120703859 29158154588754774181055789)
  ·
    refine ⟨10934307970783040317895921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29158154588754774181055789 10934307970783040317895921)
    ·
      refine ⟨8200730978087280238421941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10934307970783040317895921 8200730978087280238421941)
      ·
        refine ⟨768818529195682522352057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8200730978087280238421941 768818529195682522352057)
        ·
          refine ⟨576613896896761891764043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 768818529195682522352057 576613896896761891764043)
          ·
            refine ⟨864920845345142837646065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576613896896761891764043 864920845345142837646065)
            ·
              refine ⟨648690634008857128234549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 864920845345142837646065 648690634008857128234549)
              ·
                refine ⟨60814746938330355771989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 648690634008857128234549 60814746938330355771989)
                ·
                  rfl

theorem cell21_799445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 5].length) (baseStart_799445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799445 prefixEnd_799445 := by exact prefixLift 799445
  have htrace : WordTrace (prefixWord ++ tailWord_799445) baseStart_799445 baseEnd_799445 := by
    simpa [prefixWord, tailWord_799445, baseEnd_799445] using wordTrace_append hprefix tailTrace_799445
  have hstable : (prefixWord ++ tailWord_799445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799445).length < 2 ^ (prefixWord ++ tailWord_799445).sum := by decide
  have hdescent : baseEnd_799445 < baseStart_799445 := by decide
  rcases family_descends (prefixWord ++ tailWord_799445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799459 : List Nat := [1, 1, 1, 7, 1, 3, 1, 3, 3]
def baseStart_799459 : Nat := 118140960795 + 799459 * 2 ^ 59
def prefixEnd_799459 : Nat := 4983230072969 + 3 ^ 40 * 799459 * 2
def baseEnd_799459 : Nat := 182447435805730154082605

theorem tailTrace_799459 : CollatzResearch.WordTrace tailWord_799459 prefixEnd_799459 182447435805730154082605 := by
  unfold tailWord_799459
  simp only [CollatzResearch.WordTrace]
  refine ⟨29158665210704054572065431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19439110140469369714710287 29158665210704054572065431)
  ·
    refine ⟨43737997816056081858098147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29158665210704054572065431 43737997816056081858098147)
    ·
      refine ⟨65606996724084122787147221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43737997816056081858098147 65606996724084122787147221)
      ·
        refine ⟨1537663985720721627823763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 65606996724084122787147221 1537663985720721627823763)
        ·
          refine ⟨2306495978581082441735645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1537663985720721627823763 2306495978581082441735645)
          ·
            refine ⟨864935991967905915650867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2306495978581082441735645 864935991967905915650867)
            ·
              refine ⟨1297403987951858873476301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864935991967905915650867 1297403987951858873476301)
              ·
                refine ⟨486526495481947077553613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1297403987951858873476301 486526495481947077553613)
                ·
                  refine ⟨182447435805730154082605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 486526495481947077553613 182447435805730154082605)
                  ·
                    rfl

theorem cell21_799459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 3].length) (baseStart_799459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799459 prefixEnd_799459 := by exact prefixLift 799459
  have htrace : WordTrace (prefixWord ++ tailWord_799459) baseStart_799459 baseEnd_799459 := by
    simpa [prefixWord, tailWord_799459, baseEnd_799459] using wordTrace_append hprefix tailTrace_799459
  have hstable : (prefixWord ++ tailWord_799459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799459).length < 2 ^ (prefixWord ++ tailWord_799459).sum := by decide
  have hdescent : baseEnd_799459 < baseStart_799459 := by decide
  rcases family_descends (prefixWord ++ tailWord_799459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799470 : List Nat := [4, 1, 2, 1, 1, 5, 7]
def baseStart_799470 : Nat := 118140960795 + 799470 * 2 ^ 59
def prefixEnd_799470 : Nat := 4983230072969 + 3 ^ 40 * 799470 * 2
def baseEnd_799470 : Nat := 20272216239510731044361

theorem tailTrace_799470 : CollatzResearch.WordTrace tailWord_799470 prefixEnd_799470 20272216239510731044361 := by
  unfold tailWord_799470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3644883301708025431339483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19439377609109468967143909 3644883301708025431339483)
  ·
    refine ⟨5467324952562038147009225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3644883301708025431339483 5467324952562038147009225)
    ·
      refine ⟨4100493714421528610256919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5467324952562038147009225 4100493714421528610256919)
      ·
        refine ⟨6150740571632292915385379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4100493714421528610256919 6150740571632292915385379)
        ·
          refine ⟨9226110857448439373078069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6150740571632292915385379 9226110857448439373078069)
          ·
            refine ⟨864947892885791191226069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9226110857448439373078069 864947892885791191226069)
            ·
              refine ⟨20272216239510731044361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 864947892885791191226069 20272216239510731044361)
              ·
                rfl

theorem cell21_799470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 7].length) (baseStart_799470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799470 prefixEnd_799470 := by exact prefixLift 799470
  have htrace : WordTrace (prefixWord ++ tailWord_799470) baseStart_799470 baseEnd_799470 := by
    simpa [prefixWord, tailWord_799470, baseEnd_799470] using wordTrace_append hprefix tailTrace_799470
  have hstable : (prefixWord ++ tailWord_799470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799470).length < 2 ^ (prefixWord ++ tailWord_799470).sum := by decide
  have hdescent : baseEnd_799470 < baseStart_799470 := by decide
  rcases family_descends (prefixWord ++ tailWord_799470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799476 : List Nat := [2, 6, 1, 1, 2, 2, 1, 1, 5]
def baseStart_799476 : Nat := 118140960795 + 799476 * 2 ^ 59
def prefixEnd_799476 : Nat := 4983230072969 + 3 ^ 40 * 799476 * 2
def baseEnd_799476 : Nat := 182451315437341902299237

theorem tailTrace_799476 : CollatzResearch.WordTrace tailWord_799476 prefixEnd_799476 182451315437341902299237 := by
  unfold tailWord_799476
  simp only [CollatzResearch.WordTrace]
  refine ⟨14579642625821233237717141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19439523501094977650289521 14579642625821233237717141)
  ·
    refine ⟨683420748085370308017991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14579642625821233237717141 683420748085370308017991)
    ·
      refine ⟨1025131122128055462026987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 683420748085370308017991 1025131122128055462026987)
      ·
        refine ⟨1537696683192083193040481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1025131122128055462026987 1537696683192083193040481)
        ·
          refine ⟨1153272512394062394780361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1537696683192083193040481 1153272512394062394780361)
          ·
            refine ⟨864954384295546796085271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1153272512394062394780361 864954384295546796085271)
            ·
              refine ⟨1297431576443320194127907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864954384295546796085271 1297431576443320194127907)
              ·
                refine ⟨1946147364664980291191861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1297431576443320194127907 1946147364664980291191861)
                ·
                  refine ⟨182451315437341902299237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1946147364664980291191861 182451315437341902299237)
                  ·
                    rfl

theorem cell21_799476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_799476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799476 prefixEnd_799476 := by exact prefixLift 799476
  have htrace : WordTrace (prefixWord ++ tailWord_799476) baseStart_799476 baseEnd_799476 := by
    simpa [prefixWord, tailWord_799476, baseEnd_799476] using wordTrace_append hprefix tailTrace_799476
  have hstable : (prefixWord ++ tailWord_799476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799476).length < 2 ^ (prefixWord ++ tailWord_799476).sum := by decide
  have hdescent : baseEnd_799476 < baseStart_799476 := by decide
  rcases family_descends (prefixWord ++ tailWord_799476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799490 : List Nat := [3, 4, 1, 1, 1, 4, 2, 1, 4]
def baseStart_799490 : Nat := 118140960795 + 799490 * 2 ^ 59
def prefixEnd_799490 : Nat := 4983230072969 + 3 ^ 40 * 799490 * 2
def baseEnd_799490 : Nat := 182454510428080989065875

theorem tailTrace_799490 : CollatzResearch.WordTrace tailWord_799490 prefixEnd_799490 182454510428080989065875 := by
  unfold tailWord_799490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7289948968397936716610981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19439863915727831244295949 7289948968397936716610981)
  ·
    refine ⟨1366865431574613134364559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7289948968397936716610981 1366865431574613134364559)
    ·
      refine ⟨2050298147361919701546839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1366865431574613134364559 2050298147361919701546839)
      ·
        refine ⟨3075447221042879552320259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2050298147361919701546839 3075447221042879552320259)
        ·
          refine ⟨4613170831564319328480389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3075447221042879552320259 4613170831564319328480389)
          ·
            refine ⟨864969530918309874090073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4613170831564319328480389 864969530918309874090073)
            ·
              refine ⟨648727148188732405567555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 864969530918309874090073 648727148188732405567555)
              ·
                refine ⟨973090722283098608351333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 648727148188732405567555 973090722283098608351333)
                ·
                  refine ⟨182454510428080989065875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 973090722283098608351333 182454510428080989065875)
                  ·
                    rfl

theorem cell21_799490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_799490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799490 prefixEnd_799490 := by exact prefixLift 799490
  have htrace : WordTrace (prefixWord ++ tailWord_799490) baseStart_799490 baseEnd_799490 := by
    simpa [prefixWord, tailWord_799490, baseEnd_799490] using wordTrace_append hprefix tailTrace_799490
  have hstable : (prefixWord ++ tailWord_799490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799490).length < 2 ^ (prefixWord ++ tailWord_799490).sum := by decide
  have hdescent : baseEnd_799490 < baseStart_799490 := by decide
  rcases family_descends (prefixWord ++ tailWord_799490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799560 : List Nat := [2, 1, 3, 1, 1, 3, 3, 2, 5]
def baseStart_799560 : Nat := 118140960795 + 799560 * 2 ^ 59
def prefixEnd_799560 : Nat := 4983230072969 + 3 ^ 40 * 799560 * 2
def baseEnd_799560 : Nat := 182470485381776422899065

theorem tailTrace_799560 : CollatzResearch.WordTrace tailWord_799560 prefixEnd_799560 182470485381776422899065 := by
  unfold tailWord_799560
  simp only [CollatzResearch.WordTrace]
  refine ⟨14581174491669074410746067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19441565988892099214328089 14581174491669074410746067)
  ·
    refine ⟨21871761737503611616119101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14581174491669074410746067 21871761737503611616119101)
    ·
      refine ⟨8201910651563854356044663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21871761737503611616119101 8201910651563854356044663)
      ·
        refine ⟨12302865977345781534066995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8201910651563854356044663 12302865977345781534066995)
        ·
          refine ⟨18454298966018672301100493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12302865977345781534066995 18454298966018672301100493)
          ·
            refine ⟨6920362112257002112912685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18454298966018672301100493 6920362112257002112912685)
            ·
              refine ⟨2595135792096375792342257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6920362112257002112912685 2595135792096375792342257)
              ·
                refine ⟨1946351844072281844256693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2595135792096375792342257 1946351844072281844256693)
                ·
                  refine ⟨182470485381776422899065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1946351844072281844256693 182470485381776422899065)
                  ·
                    rfl

theorem cell21_799560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_799560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799560 prefixEnd_799560 := by exact prefixLift 799560
  have htrace : WordTrace (prefixWord ++ tailWord_799560) baseStart_799560 baseEnd_799560 := by
    simpa [prefixWord, tailWord_799560, baseEnd_799560] using wordTrace_append hprefix tailTrace_799560
  have hstable : (prefixWord ++ tailWord_799560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799560).length < 2 ^ (prefixWord ++ tailWord_799560).sum := by decide
  have hdescent : baseEnd_799560 < baseStart_799560 := by decide
  rcases family_descends (prefixWord ++ tailWord_799560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799577 : List Nat := [1, 2, 1, 2, 2, 4, 1, 5, 3]
def baseStart_799577 : Nat := 118140960795 + 799577 * 2 ^ 59
def prefixEnd_799577 : Nat := 4983230072969 + 3 ^ 40 * 799577 * 2
def baseEnd_799577 : Nat := 182474365013388171115697

theorem tailTrace_799577 : CollatzResearch.WordTrace tailWord_799577 prefixEnd_799577 182474365013388171115697 := by
  unfold tailWord_799577
  simp only [CollatzResearch.WordTrace]
  refine ⟨29162969024276560724860985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19441979349517707149907323 29162969024276560724860985)
  ·
    refine ⟨21872226768207420543645739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29162969024276560724860985 21872226768207420543645739)
    ·
      refine ⟨32808340152311130815468609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21872226768207420543645739 32808340152311130815468609)
      ·
        refine ⟨24606255114233348111601457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32808340152311130815468609 24606255114233348111601457)
        ·
          refine ⟨18454691335675011083701093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24606255114233348111601457 18454691335675011083701093)
          ·
            refine ⟨3460254625439064578193955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18454691335675011083701093 3460254625439064578193955)
            ·
              refine ⟨5190381938158596867290933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3460254625439064578193955 5190381938158596867290933)
              ·
                refine ⟨486598306702368456308525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5190381938158596867290933 486598306702368456308525)
                ·
                  refine ⟨182474365013388171115697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 486598306702368456308525 182474365013388171115697)
                  ·
                    rfl

theorem cell21_799577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 3].length) (baseStart_799577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799577 prefixEnd_799577 := by exact prefixLift 799577
  have htrace : WordTrace (prefixWord ++ tailWord_799577) baseStart_799577 baseEnd_799577 := by
    simpa [prefixWord, tailWord_799577, baseEnd_799577] using wordTrace_append hprefix tailTrace_799577
  have hstable : (prefixWord ++ tailWord_799577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799577).length < 2 ^ (prefixWord ++ tailWord_799577).sum := by decide
  have hdescent : baseEnd_799577 < baseStart_799577 := by decide
  rcases family_descends (prefixWord ++ tailWord_799577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799591 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 6]
def baseStart_799591 : Nat := 118140960795 + 799591 * 2 ^ 59
def prefixEnd_799591 : Nat := 4983230072969 + 3 ^ 40 * 799591 * 2
def baseEnd_799591 : Nat := 182477560004127257882335

theorem tailTrace_799591 : CollatzResearch.WordTrace tailWord_799591 prefixEnd_799591 182477560004127257882335 := by
  unfold tailWord_799591
  simp only [CollatzResearch.WordTrace]
  refine ⟨29163479646225841115870627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19442319764150560743913751 29163479646225841115870627)
  ·
    refine ⟨43745219469338761673805941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29163479646225841115870627 43745219469338761673805941)
    ·
      refine ⟨4101114325250508906919307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43745219469338761673805941 4101114325250508906919307)
      ·
        refine ⟨6151671487875763360378961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4101114325250508906919307 6151671487875763360378961)
        ·
          refine ⟨4613753615906822520284221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6151671487875763360378961 4613753615906822520284221)
          ·
            refine ⟨1730157605965058445106583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4613753615906822520284221 1730157605965058445106583)
            ·
              refine ⟨2595236408947587667659875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1730157605965058445106583 2595236408947587667659875)
              ·
                refine ⟨3892854613421381501489813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2595236408947587667659875 3892854613421381501489813)
                ·
                  refine ⟨182477560004127257882335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3892854613421381501489813 182477560004127257882335)
                  ·
                    rfl

theorem cell21_799591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 6].length) (baseStart_799591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799591 prefixEnd_799591 := by exact prefixLift 799591
  have htrace : WordTrace (prefixWord ++ tailWord_799591) baseStart_799591 baseEnd_799591 := by
    simpa [prefixWord, tailWord_799591, baseEnd_799591] using wordTrace_append hprefix tailTrace_799591
  have hstable : (prefixWord ++ tailWord_799591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799591).length < 2 ^ (prefixWord ++ tailWord_799591).sum := by decide
  have hdescent : baseEnd_799591 < baseStart_799591 := by decide
  rcases family_descends (prefixWord ++ tailWord_799591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799802 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 6]
def baseStart_799802 : Nat := 118140960795 + 799802 * 2 ^ 59
def prefixEnd_799802 : Nat := 4983230072969 + 3 ^ 40 * 799802 * 2
def baseEnd_799802 : Nat := 182525713078837779865237

theorem tailTrace_799802 : CollatzResearch.WordTrace tailWord_799802 prefixEnd_799802 182525713078837779865237 := by
  unfold tailWord_799802
  simp only [CollatzResearch.WordTrace]
  refine ⟨7292793862115356037950415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19447450298974282767867773 7292793862115356037950415)
  ·
    refine ⟨10939190793173034056925623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7292793862115356037950415 10939190793173034056925623)
    ·
      refine ⟨16408786189759551085388435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10939190793173034056925623 16408786189759551085388435)
      ·
        refine ⟨24613179284639326628082653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16408786189759551085388435 24613179284639326628082653)
        ·
          refine ⟨9229942231739747485530995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24613179284639326628082653 9229942231739747485530995)
          ·
            refine ⟨13844913347609621228296493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9229942231739747485530995 13844913347609621228296493)
            ·
              refine ⟨5191842505353607960611185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13844913347609621228296493 5191842505353607960611185)
              ·
                refine ⟨3893881879015205970458389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5191842505353607960611185 3893881879015205970458389)
                ·
                  refine ⟨182525713078837779865237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3893881879015205970458389 182525713078837779865237)
                  ·
                    rfl

theorem cell21_799802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_799802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799802 prefixEnd_799802 := by exact prefixLift 799802
  have htrace : WordTrace (prefixWord ++ tailWord_799802) baseStart_799802 baseEnd_799802 := by
    simpa [prefixWord, tailWord_799802, baseEnd_799802] using wordTrace_append hprefix tailTrace_799802
  have hstable : (prefixWord ++ tailWord_799802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799802).length < 2 ^ (prefixWord ++ tailWord_799802).sum := by decide
  have hdescent : baseEnd_799802 < baseStart_799802 := by decide
  rcases family_descends (prefixWord ++ tailWord_799802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799822 : List Nat := [4, 1, 1, 1, 1, 3, 5, 2, 3]
def baseStart_799822 : Nat := 118140960795 + 799822 * 2 ^ 59
def prefixEnd_799822 : Nat := 4983230072969 + 3 ^ 40 * 799822 * 2
def baseEnd_799822 : Nat := 182530277351322189531863

theorem tailTrace_799822 : CollatzResearch.WordTrace tailWord_799822 prefixEnd_799822 182530277351322189531863 := by
  unfold tailWord_799822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3646488113548620945941215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19447936605592645045019813 3646488113548620945941215)
  ·
    refine ⟨5469732170322931418911823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3646488113548620945941215 5469732170322931418911823)
    ·
      refine ⟨8204598255484397128367735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5469732170322931418911823 8204598255484397128367735)
      ·
        refine ⟨12306897383226595692551603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8204598255484397128367735 12306897383226595692551603)
        ·
          refine ⟨18460346074839893538827405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12306897383226595692551603 18460346074839893538827405)
          ·
            refine ⟨6922629778064960077060277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18460346074839893538827405 6922629778064960077060277)
            ·
              refine ⟨648996541693590007224401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6922629778064960077060277 648996541693590007224401)
              ·
                refine ⟨486747406270192505418301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 648996541693590007224401 486747406270192505418301)
                ·
                  refine ⟨182530277351322189531863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 486747406270192505418301 182530277351322189531863)
                  ·
                    rfl

theorem cell21_799822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_799822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799822 prefixEnd_799822 := by exact prefixLift 799822
  have htrace : WordTrace (prefixWord ++ tailWord_799822) baseStart_799822 baseEnd_799822 := by
    simpa [prefixWord, tailWord_799822, baseEnd_799822] using wordTrace_append hprefix tailTrace_799822
  have hstable : (prefixWord ++ tailWord_799822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799822).length < 2 ^ (prefixWord ++ tailWord_799822).sum := by decide
  have hdescent : baseEnd_799822 < baseStart_799822 := by decide
  rcases family_descends (prefixWord ++ tailWord_799822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799881 : List Nat := [1, 2, 1, 1, 4, 4, 1, 4, 3]
def baseStart_799881 : Nat := 118140960795 + 799881 * 2 ^ 59
def prefixEnd_799881 : Nat := 4983230072969 + 3 ^ 40 * 799881 * 2
def baseEnd_799881 : Nat := 182543741955151198048409

theorem tailTrace_799881 : CollatzResearch.WordTrace tailWord_799881 prefixEnd_799881 182543741955151198048409 := by
  unfold tailWord_799881
  simp only [CollatzResearch.WordTrace]
  refine ⟨29174056815175220643927497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19449371210116813762618331 29174056815175220643927497)
  ·
    refine ⟨21880542611381415482945623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29174056815175220643927497 21880542611381415482945623)
    ·
      refine ⟨32820813917072123224418435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21880542611381415482945623 32820813917072123224418435)
      ·
        refine ⟨49231220875608184836627653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32820813917072123224418435 49231220875608184836627653)
        ·
          refine ⟨9230853914176534656867685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49231220875608184836627653 9230853914176534656867685)
          ·
            refine ⟨1730785108908100248162691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9230853914176534656867685 1730785108908100248162691)
            ·
              refine ⟨2596177663362150372244037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1730785108908100248162691 2596177663362150372244037)
              ·
                refine ⟨486783311880403194795757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2596177663362150372244037 486783311880403194795757)
                ·
                  refine ⟨182543741955151198048409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 486783311880403194795757 182543741955151198048409)
                  ·
                    rfl

theorem cell21_799881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 3].length) (baseStart_799881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799881 prefixEnd_799881 := by exact prefixLift 799881
  have htrace : WordTrace (prefixWord ++ tailWord_799881) baseStart_799881 baseEnd_799881 := by
    simpa [prefixWord, tailWord_799881, baseEnd_799881] using wordTrace_append hprefix tailTrace_799881
  have hstable : (prefixWord ++ tailWord_799881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799881).length < 2 ^ (prefixWord ++ tailWord_799881).sum := by decide
  have hdescent : baseEnd_799881 < baseStart_799881 := by decide
  rcases family_descends (prefixWord ++ tailWord_799881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799895 : List Nat := [1, 1, 3, 3, 3, 1, 2, 3, 4]
def baseStart_799895 : Nat := 118140960795 + 799895 * 2 ^ 59
def prefixEnd_799895 : Nat := 4983230072969 + 3 ^ 40 * 799895 * 2
def baseEnd_799895 : Nat := 182546936945890284815047

theorem tailTrace_799895 : CollatzResearch.WordTrace tailWord_799895 prefixEnd_799895 182546936945890284815047 := by
  unfold tailWord_799895
  simp only [CollatzResearch.WordTrace]
  refine ⟨29174567437124501034937139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19449711624749667356624759 29174567437124501034937139)
  ·
    refine ⟨43761851155686751552405709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29174567437124501034937139 43761851155686751552405709)
    ·
      refine ⟨16410694183382531832152141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43761851155686751552405709 16410694183382531832152141)
      ·
        refine ⟨6154010318768449437057053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16410694183382531832152141 6154010318768449437057053)
        ·
          refine ⟨2307753869538168538896395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6154010318768449437057053 2307753869538168538896395)
          ·
            refine ⟨3461630804307252808344593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2307753869538168538896395 3461630804307252808344593)
            ·
              refine ⟨2596223103230439606258445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3461630804307252808344593 2596223103230439606258445)
              ·
                refine ⟨973583663711414852346917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2596223103230439606258445 973583663711414852346917)
                ·
                  refine ⟨182546936945890284815047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 973583663711414852346917 182546936945890284815047)
                  ·
                    rfl

theorem cell21_799895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 4].length) (baseStart_799895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_799895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_799895 prefixEnd_799895 := by exact prefixLift 799895
  have htrace : WordTrace (prefixWord ++ tailWord_799895) baseStart_799895 baseEnd_799895 := by
    simpa [prefixWord, tailWord_799895, baseEnd_799895] using wordTrace_append hprefix tailTrace_799895
  have hstable : (prefixWord ++ tailWord_799895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799895).length < 2 ^ (prefixWord ++ tailWord_799895).sum := by decide
  have hdescent : baseEnd_799895 < baseStart_799895 := by decide
  rcases family_descends (prefixWord ++ tailWord_799895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800050 : List Nat := [3, 2, 1, 1, 4, 1, 4, 2, 3]
def baseStart_800050 : Nat := 118140960795 + 800050 * 2 ^ 59
def prefixEnd_800050 : Nat := 4983230072969 + 3 ^ 40 * 800050 * 2
def baseEnd_800050 : Nat := 182582310057644459731397

theorem tailTrace_800050 : CollatzResearch.WordTrace tailWord_800050 prefixEnd_800050 182582310057644459731397 := by
  unfold tailWord_800050
  simp only [CollatzResearch.WordTrace]
  refine ⟨7295055187890740626707401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19453480501041975004553069 7295055187890740626707401)
  ·
    refine ⟨5471291390918055470030551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7295055187890740626707401 5471291390918055470030551)
    ·
      refine ⟨8206937086377083205045827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5471291390918055470030551 8206937086377083205045827)
      ·
        refine ⟨12310405629565624807568741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8206937086377083205045827 12310405629565624807568741)
        ·
          refine ⟨2308201055543554651419139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12310405629565624807568741 2308201055543554651419139)
          ·
            refine ⟨3462301583315331977128709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2308201055543554651419139 3462301583315331977128709)
            ·
              refine ⟨649181546871624745711633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3462301583315331977128709 649181546871624745711633)
              ·
                refine ⟨486886160153718559283725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 649181546871624745711633 486886160153718559283725)
                ·
                  refine ⟨182582310057644459731397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 486886160153718559283725 182582310057644459731397)
                  ·
                    rfl

theorem cell21_800050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_800050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800050 prefixEnd_800050 := by exact prefixLift 800050
  have htrace : WordTrace (prefixWord ++ tailWord_800050) baseStart_800050 baseEnd_800050 := by
    simpa [prefixWord, tailWord_800050, baseEnd_800050] using wordTrace_append hprefix tailTrace_800050
  have hstable : (prefixWord ++ tailWord_800050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800050).length < 2 ^ (prefixWord ++ tailWord_800050).sum := by decide
  have hdescent : baseEnd_800050 < baseStart_800050 := by decide
  rcases family_descends (prefixWord ++ tailWord_800050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800109 : List Nat := [1, 5, 1, 1, 1, 3, 2, 4, 3]
def baseStart_800109 : Nat := 118140960795 + 800109 * 2 ^ 59
def prefixEnd_800109 : Nat := 4983230072969 + 3 ^ 40 * 800109 * 2
def baseEnd_800109 : Nat := 182595774661473468247943

theorem tailTrace_800109 : CollatzResearch.WordTrace tailWord_800109 prefixEnd_800109 182595774661473468247943 := by
  unfold tailWord_800109
  simp only [CollatzResearch.WordTrace]
  refine ⟨29182372658349215583227381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19454915105566143722151587 29182372658349215583227381)
  ·
    refine ⟨2735847436720238960927567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29182372658349215583227381 2735847436720238960927567)
    ·
      refine ⟨4103771155080358441391351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2735847436720238960927567 4103771155080358441391351)
      ·
        refine ⟨6155656732620537662087027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4103771155080358441391351 6155656732620537662087027)
        ·
          refine ⟨9233485098930806493130541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6155656732620537662087027 9233485098930806493130541)
          ·
            refine ⟨3462556912099052434923953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9233485098930806493130541 3462556912099052434923953)
            ·
              refine ⟨2596917684074289326192965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3462556912099052434923953 2596917684074289326192965)
              ·
                refine ⟨486922065763929248661181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2596917684074289326192965 486922065763929248661181)
                ·
                  refine ⟨182595774661473468247943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 486922065763929248661181 182595774661473468247943)
                  ·
                    rfl

theorem cell21_800109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_800109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800109 prefixEnd_800109 := by exact prefixLift 800109
  have htrace : WordTrace (prefixWord ++ tailWord_800109) baseStart_800109 baseEnd_800109 := by
    simpa [prefixWord, tailWord_800109, baseEnd_800109] using wordTrace_append hprefix tailTrace_800109
  have hstable : (prefixWord ++ tailWord_800109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800109).length < 2 ^ (prefixWord ++ tailWord_800109).sum := by decide
  have hdescent : baseEnd_800109 < baseStart_800109 := by decide
  rcases family_descends (prefixWord ++ tailWord_800109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800123 : List Nat := [1, 1, 1, 1, 1, 6, 5, 1, 4]
def baseStart_800123 : Nat := 118140960795 + 800123 * 2 ^ 59
def prefixEnd_800123 : Nat := 4983230072969 + 3 ^ 40 * 800123 * 2
def baseEnd_800123 : Nat := 182598969652212555014581

theorem tailTrace_800123 : CollatzResearch.WordTrace tailWord_800123 prefixEnd_800123 182598969652212555014581 := by
  unfold tailWord_800123
  simp only [CollatzResearch.WordTrace]
  refine ⟨29182883280298495974237023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19455255520198997316158015 29182883280298495974237023)
  ·
    refine ⟨43774324920447743961355535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29182883280298495974237023 43774324920447743961355535)
    ·
      refine ⟨65661487380671615942033303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43774324920447743961355535 65661487380671615942033303)
      ·
        refine ⟨98492231071007423913049955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65661487380671615942033303 98492231071007423913049955)
        ·
          refine ⟨147738346606511135869574933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98492231071007423913049955 147738346606511135869574933)
          ·
            refine ⟨6925234997180209493886325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 147738346606511135869574933 6925234997180209493886325)
            ·
              refine ⟨649240780985644640051843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6925234997180209493886325 649240780985644640051843)
              ·
                refine ⟨973861171478466960077765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649240780985644640051843 973861171478466960077765)
                ·
                  refine ⟨182598969652212555014581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 973861171478466960077765 182598969652212555014581)
                  ·
                    rfl

theorem cell21_800123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 4].length) (baseStart_800123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800123 prefixEnd_800123 := by exact prefixLift 800123
  have htrace : WordTrace (prefixWord ++ tailWord_800123) baseStart_800123 baseEnd_800123 := by
    simpa [prefixWord, tailWord_800123, baseEnd_800123] using wordTrace_append hprefix tailTrace_800123
  have hstable : (prefixWord ++ tailWord_800123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800123).length < 2 ^ (prefixWord ++ tailWord_800123).sum := by decide
  have hdescent : baseEnd_800123 < baseStart_800123 := by decide
  rcases family_descends (prefixWord ++ tailWord_800123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800137 : List Nat := [1, 2, 1, 1, 7, 1, 1, 7]
def baseStart_800137 : Nat := 118140960795 + 800137 * 2 ^ 59
def prefixEnd_800137 : Nat := 4983230072969 + 3 ^ 40 * 800137 * 2
def baseEnd_800137 : Nat := 60867388214317213927073

theorem tailTrace_800137 : CollatzResearch.WordTrace tailWord_800137 prefixEnd_800137 60867388214317213927073 := by
  unfold tailWord_800137
  simp only [CollatzResearch.WordTrace]
  refine ⟨29183393902247776365246665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19455595934831850910164443 29183393902247776365246665)
  ·
    refine ⟨21887545426685832273934999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29183393902247776365246665 21887545426685832273934999)
    ·
      refine ⟨32831318140028748410902499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21887545426685832273934999 32831318140028748410902499)
      ·
        refine ⟨49246977210043122616353749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32831318140028748410902499 49246977210043122616353749)
        ·
          refine ⟨1154226028360385686320791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 49246977210043122616353749 1154226028360385686320791)
          ·
            refine ⟨1731339042540578529481187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154226028360385686320791 1731339042540578529481187)
            ·
              refine ⟨2597008563810867794221781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1731339042540578529481187 2597008563810867794221781)
              ·
                refine ⟨60867388214317213927073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2597008563810867794221781 60867388214317213927073)
                ·
                  rfl

theorem cell21_800137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 7].length) (baseStart_800137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800137 prefixEnd_800137 := by exact prefixLift 800137
  have htrace : WordTrace (prefixWord ++ tailWord_800137) baseStart_800137 baseEnd_800137 := by
    simpa [prefixWord, tailWord_800137, baseEnd_800137] using wordTrace_append hprefix tailTrace_800137
  have hstable : (prefixWord ++ tailWord_800137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800137).length < 2 ^ (prefixWord ++ tailWord_800137).sum := by decide
  have hdescent : baseEnd_800137 < baseStart_800137 := by decide
  rcases family_descends (prefixWord ++ tailWord_800137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800275 : List Nat := [1, 1, 1, 2, 1, 8, 1, 2, 4]
def baseStart_800275 : Nat := 118140960795 + 800275 * 2 ^ 59
def prefixEnd_800275 : Nat := 4983230072969 + 3 ^ 40 * 800275 * 2
def baseEnd_800275 : Nat := 182633658123094068480937

theorem tailTrace_800275 : CollatzResearch.WordTrace tailWord_800275 prefixEnd_800275 182633658123094068480937 := by
  unfold tailWord_800275
  simp only [CollatzResearch.WordTrace]
  refine ⟨29188427175747825933770279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19458951450498550622513519 29188427175747825933770279)
  ·
    refine ⟨43782640763621738900655419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29188427175747825933770279 43782640763621738900655419)
    ·
      refine ⟨65673961145432608350983129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43782640763621738900655419 65673961145432608350983129)
      ·
        refine ⟨49255470859074456263237347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65673961145432608350983129 49255470859074456263237347)
        ·
          refine ⟨73883206288611684394856021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49255470859074456263237347 73883206288611684394856021)
          ·
            refine ⟨865818823694668176502219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 73883206288611684394856021 865818823694668176502219)
            ·
              refine ⟨1298728235542002264753329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865818823694668176502219 1298728235542002264753329)
              ·
                refine ⟨974046176656501698564997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1298728235542002264753329 974046176656501698564997)
                ·
                  refine ⟨182633658123094068480937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 974046176656501698564997 182633658123094068480937)
                  ·
                    rfl

theorem cell21_800275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 4].length) (baseStart_800275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800275 prefixEnd_800275 := by exact prefixLift 800275
  have htrace : WordTrace (prefixWord ++ tailWord_800275) baseStart_800275 baseEnd_800275 := by
    simpa [prefixWord, tailWord_800275, baseEnd_800275] using wordTrace_append hprefix tailTrace_800275
  have hstable : (prefixWord ++ tailWord_800275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800275).length < 2 ^ (prefixWord ++ tailWord_800275).sum := by decide
  have hdescent : baseEnd_800275 < baseStart_800275 := by decide
  rcases family_descends (prefixWord ++ tailWord_800275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800334 : List Nat := [4, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_800334 : Nat := 118140960795 + 800334 * 2 ^ 59
def prefixEnd_800334 : Nat := 4983230072969 + 3 ^ 40 * 800334 * 2
def baseEnd_800334 : Nat := 182647122726923076997483

theorem tailTrace_800334 : CollatzResearch.WordTrace tailWord_800334 prefixEnd_800334 182647122726923076997483 := by
  unfold tailWord_800334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3648822385316759876271007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19460386055022719340112037 3648822385316759876271007)
  ·
    refine ⟨5473233577975139814406511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3648822385316759876271007 5473233577975139814406511)
    ·
      refine ⟨8209850366962709721609767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5473233577975139814406511 8209850366962709721609767)
      ·
        refine ⟨12314775550444064582414651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8209850366962709721609767 12314775550444064582414651)
        ·
          refine ⟨18472163325666096873621977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12314775550444064582414651 18472163325666096873621977)
          ·
            refine ⟨13854122494249572655216483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18472163325666096873621977 13854122494249572655216483)
            ·
              refine ⟨20781183741374358982824725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13854122494249572655216483 20781183741374358982824725)
              ·
                refine ⟨974117987876923077319909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20781183741374358982824725 974117987876923077319909)
                ·
                  refine ⟨182647122726923076997483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 974117987876923077319909 182647122726923076997483)
                  ·
                    rfl

theorem cell21_800334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_800334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800334 prefixEnd_800334 := by exact prefixLift 800334
  have htrace : WordTrace (prefixWord ++ tailWord_800334) baseStart_800334 baseEnd_800334 := by
    simpa [prefixWord, tailWord_800334, baseEnd_800334] using wordTrace_append hprefix tailTrace_800334
  have hstable : (prefixWord ++ tailWord_800334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800334).length < 2 ^ (prefixWord ++ tailWord_800334).sum := by decide
  have hdescent : baseEnd_800334 < baseStart_800334 := by decide
  rcases family_descends (prefixWord ++ tailWord_800334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800337 : List Nat := [1, 2, 2, 1, 3, 2, 5, 2, 3]
def baseStart_800337 : Nat := 118140960795 + 800337 * 2 ^ 59
def prefixEnd_800337 : Nat := 4983230072969 + 3 ^ 40 * 800337 * 2
def baseEnd_800337 : Nat := 182647807367795738447477

theorem tailTrace_800337 : CollatzResearch.WordTrace tailWord_800337 prefixEnd_800337 182647807367795738447477 := by
  unfold tailWord_800337
  simp only [CollatzResearch.WordTrace]
  refine ⟨29190688501523210522527265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19460459001015473681684843 29190688501523210522527265)
  ·
    refine ⟨21893016376142407891895449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29190688501523210522527265 21893016376142407891895449)
    ·
      refine ⟨16419762282106805918921587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21893016376142407891895449 16419762282106805918921587)
      ·
        refine ⟨24629643423160208878382381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16419762282106805918921587 24629643423160208878382381)
        ·
          refine ⟨9236116283685078329393393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24629643423160208878382381 9236116283685078329393393)
          ·
            refine ⟨6927087212763808747045045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9236116283685078329393393 6927087212763808747045045)
            ·
              refine ⟨649414426196607070035473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6927087212763808747045045 649414426196607070035473)
              ·
                refine ⟨487060819647455302526605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 649414426196607070035473 487060819647455302526605)
                ·
                  refine ⟨182647807367795738447477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487060819647455302526605 182647807367795738447477)
                  ·
                    rfl

theorem cell21_800337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 3].length) (baseStart_800337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800337 prefixEnd_800337 := by exact prefixLift 800337
  have htrace : WordTrace (prefixWord ++ tailWord_800337) baseStart_800337 baseEnd_800337 := by
    simpa [prefixWord, tailWord_800337, baseEnd_800337] using wordTrace_append hprefix tailTrace_800337
  have hstable : (prefixWord ++ tailWord_800337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800337).length < 2 ^ (prefixWord ++ tailWord_800337).sum := by decide
  have hdescent : baseEnd_800337 < baseStart_800337 := by decide
  rcases family_descends (prefixWord ++ tailWord_800337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800393 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 6]
def baseStart_800393 : Nat := 118140960795 + 800393 * 2 ^ 59
def prefixEnd_800393 : Nat := 4983230072969 + 3 ^ 40 * 800393 * 2
def baseEnd_800393 : Nat := 182660587330752085514029

theorem tailTrace_800393 : CollatzResearch.WordTrace tailWord_800393 prefixEnd_800393 182660587330752085514029 := by
  unfold tailWord_800393
  simp only [CollatzResearch.WordTrace]
  refine ⟨29192730989320332086565833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19461820659546888057710555 29192730989320332086565833)
  ·
    refine ⟨21894548241990249064924375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29192730989320332086565833 21894548241990249064924375)
    ·
      refine ⟨32841822362985373597386563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21894548241990249064924375 32841822362985373597386563)
      ·
        refine ⟨49262733544478060396079845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32841822362985373597386563 49262733544478060396079845)
        ·
          refine ⟨9236762539589636324264971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49262733544478060396079845 9236762539589636324264971)
          ·
            refine ⟨13855143809384454486397457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9236762539589636324264971 13855143809384454486397457)
            ·
              refine ⟨10391357857038340864798093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13855143809384454486397457 10391357857038340864798093)
              ·
                refine ⟨3896759196389377824299285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10391357857038340864798093 3896759196389377824299285)
                ·
                  refine ⟨182660587330752085514029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3896759196389377824299285 182660587330752085514029)
                  ·
                    rfl

theorem cell21_800393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_800393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800393 prefixEnd_800393 := by exact prefixLift 800393
  have htrace : WordTrace (prefixWord ++ tailWord_800393) baseStart_800393 baseEnd_800393 := by
    simpa [prefixWord, tailWord_800393, baseEnd_800393] using wordTrace_append hprefix tailTrace_800393
  have hstable : (prefixWord ++ tailWord_800393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800393).length < 2 ^ (prefixWord ++ tailWord_800393).sum := by decide
  have hdescent : baseEnd_800393 < baseStart_800393 := by decide
  rcases family_descends (prefixWord ++ tailWord_800393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800396 : List Nat := [2, 2, 1, 2, 1, 1, 5, 4, 3]
def baseStart_800396 : Nat := 118140960795 + 800396 * 2 ^ 59
def prefixEnd_800396 : Nat := 4983230072969 + 3 ^ 40 * 800396 * 2
def baseEnd_800396 : Nat := 182661271971624746964023

theorem tailTrace_800396 : CollatzResearch.WordTrace tailWord_800396 prefixEnd_800396 182661271971624746964023 := by
  unfold tailWord_800396
  simp only [CollatzResearch.WordTrace]
  refine ⟨14596420204154731799462521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19461893605539642399283361 14596420204154731799462521)
  ·
    refine ⟨10947315153116048849596891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14596420204154731799462521 10947315153116048849596891)
    ·
      refine ⟨16420972729674073274395337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10947315153116048849596891 16420972729674073274395337)
      ·
        refine ⟨12315729547255554955796503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16420972729674073274395337 12315729547255554955796503)
        ·
          refine ⟨18473594320883332433694755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12315729547255554955796503 18473594320883332433694755)
          ·
            refine ⟨27710391481324998650542133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18473594320883332433694755 27710391481324998650542133)
            ·
              refine ⟨2597849201374218623488325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27710391481324998650542133 2597849201374218623488325)
              ·
                refine ⟨487096725257665991904061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2597849201374218623488325 487096725257665991904061)
                ·
                  refine ⟨182661271971624746964023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487096725257665991904061 182661271971624746964023)
                  ·
                    rfl

theorem cell21_800396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_800396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800396 prefixEnd_800396 := by exact prefixLift 800396
  have htrace : WordTrace (prefixWord ++ tailWord_800396) baseStart_800396 baseEnd_800396 := by
    simpa [prefixWord, tailWord_800396, baseEnd_800396] using wordTrace_append hprefix tailTrace_800396
  have hstable : (prefixWord ++ tailWord_800396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800396).length < 2 ^ (prefixWord ++ tailWord_800396).sum := by decide
  have hdescent : baseEnd_800396 < baseStart_800396 := by decide
  rcases family_descends (prefixWord ++ tailWord_800396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800455 : List Nat := [1, 1, 4, 1, 1, 1, 6, 1, 5]
def baseStart_800455 : Nat := 118140960795 + 800455 * 2 ^ 59
def prefixEnd_800455 : Nat := 4983230072969 + 3 ^ 40 * 800455 * 2
def baseEnd_800455 : Nat := 182674736575453755480569

theorem tailTrace_800455 : CollatzResearch.WordTrace tailWord_800455 prefixEnd_800455 182674736575453755480569 := by
  unfold tailWord_800455
  simp only [CollatzResearch.WordTrace]
  refine ⟨29194992315095716675322819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19463328210063811116881879 29194992315095716675322819)
  ·
    refine ⟨43792488472643575012984229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29194992315095716675322819 43792488472643575012984229)
    ·
      refine ⟨8211091588620670314934543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43792488472643575012984229 8211091588620670314934543)
      ·
        refine ⟨12316637382931005472401815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8211091588620670314934543 12316637382931005472401815)
        ·
          refine ⟨18474956074396508208602723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12316637382931005472401815 18474956074396508208602723)
          ·
            refine ⟨27712434111594762312904085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18474956074396508208602723 27712434111594762312904085)
            ·
              refine ⟨1299020348981004483417379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27712434111594762312904085 1299020348981004483417379)
              ·
                refine ⟨1948530523471506725126069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1299020348981004483417379 1948530523471506725126069)
                ·
                  refine ⟨182674736575453755480569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1948530523471506725126069 182674736575453755480569)
                  ·
                    rfl

theorem cell21_800455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 5].length) (baseStart_800455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800455 prefixEnd_800455 := by exact prefixLift 800455
  have htrace : WordTrace (prefixWord ++ tailWord_800455) baseStart_800455 baseEnd_800455 := by
    simpa [prefixWord, tailWord_800455, baseEnd_800455] using wordTrace_append hprefix tailTrace_800455
  have hstable : (prefixWord ++ tailWord_800455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800455).length < 2 ^ (prefixWord ++ tailWord_800455).sum := by decide
  have hdescent : baseEnd_800455 < baseStart_800455 := by decide
  rcases family_descends (prefixWord ++ tailWord_800455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800461 : List Nat := [1, 6, 2, 1, 1, 2, 3, 1, 4]
def baseStart_800461 : Nat := 118140960795 + 800461 * 2 ^ 59
def prefixEnd_800461 : Nat := 4983230072969 + 3 ^ 40 * 800461 * 2
def baseEnd_800461 : Nat := 182676105857199078380557

theorem tailTrace_800461 : CollatzResearch.WordTrace tailWord_800461 prefixEnd_800461 182676105857199078380557 := by
  unfold tailWord_800461
  simp only [CollatzResearch.WordTrace]
  refine ⟨29195211153073979700041237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19463474102049319800027491 29195211153073979700041237)
  ·
    refine ⟨1368525522800342798439433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29195211153073979700041237 1368525522800342798439433)
    ·
      refine ⟨1026394142100257098829575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1368525522800342798439433 1026394142100257098829575)
      ·
        refine ⟨1539591213150385648244363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1026394142100257098829575 1539591213150385648244363)
        ·
          refine ⟨2309386819725578472366545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1539591213150385648244363 2309386819725578472366545)
          ·
            refine ⟨1732040114794183854274909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2309386819725578472366545 1732040114794183854274909)
            ·
              refine ⟨649515043047818945353091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1732040114794183854274909 649515043047818945353091)
              ·
                refine ⟨974272564571728418029637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649515043047818945353091 974272564571728418029637)
                ·
                  refine ⟨182676105857199078380557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 974272564571728418029637 182676105857199078380557)
                  ·
                    rfl

theorem cell21_800461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_800461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800461 prefixEnd_800461 := by exact prefixLift 800461
  have htrace : WordTrace (prefixWord ++ tailWord_800461) baseStart_800461 baseEnd_800461 := by
    simpa [prefixWord, tailWord_800461, baseEnd_800461] using wordTrace_append hprefix tailTrace_800461
  have hstable : (prefixWord ++ tailWord_800461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800461).length < 2 ^ (prefixWord ++ tailWord_800461).sum := by decide
  have hdescent : baseEnd_800461 < baseStart_800461 := by decide
  rcases family_descends (prefixWord ++ tailWord_800461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800562 : List Nat := [3, 2, 1, 1, 3, 2, 1, 4, 4]
def baseStart_800562 : Nat := 118140960795 + 800562 * 2 ^ 59
def prefixEnd_800562 : Nat := 4983230072969 + 3 ^ 40 * 800562 * 2
def baseEnd_800562 : Nat := 182699155433245347197017

theorem tailTrace_800562 : CollatzResearch.WordTrace tailWord_800562 prefixEnd_800562 182699155433245347197017 := by
  unfold tailWord_800562
  simp only [CollatzResearch.WordTrace]
  refine ⟨7299723731427018487366985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19465929950472049299645293 7299723731427018487366985)
  ·
    refine ⟨5474792798570263865525239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7299723731427018487366985 5474792798570263865525239)
    ·
      refine ⟨8212189197855395798287859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5474792798570263865525239 8212189197855395798287859)
      ·
        refine ⟨12318283796783093697431789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8212189197855395798287859 12318283796783093697431789)
        ·
          refine ⟨4619356423793660136536921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12318283796783093697431789 4619356423793660136536921)
          ·
            refine ⟨3464517317845245102402691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4619356423793660136536921 3464517317845245102402691)
            ·
              refine ⟨5196775976767867653604037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3464517317845245102402691 5196775976767867653604037)
              ·
                refine ⟨974395495643975185050757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5196775976767867653604037 974395495643975185050757)
                ·
                  refine ⟨182699155433245347197017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 974395495643975185050757 182699155433245347197017)
                  ·
                    rfl

theorem cell21_800562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_800562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800562 prefixEnd_800562 := by exact prefixLift 800562
  have htrace : WordTrace (prefixWord ++ tailWord_800562) baseStart_800562 baseEnd_800562 := by
    simpa [prefixWord, tailWord_800562, baseEnd_800562] using wordTrace_append hprefix tailTrace_800562
  have hstable : (prefixWord ++ tailWord_800562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800562).length < 2 ^ (prefixWord ++ tailWord_800562).sum := by decide
  have hdescent : baseEnd_800562 < baseStart_800562 := by decide
  rcases family_descends (prefixWord ++ tailWord_800562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800565 : List Nat := [1, 3, 3, 1, 4, 1, 1, 4, 3]
def baseStart_800565 : Nat := 118140960795 + 800565 * 2 ^ 59
def prefixEnd_800565 : Nat := 4983230072969 + 3 ^ 40 * 800565 * 2
def baseEnd_800565 : Nat := 182699840074118008647011

theorem tailTrace_800565 : CollatzResearch.WordTrace tailWord_800565 prefixEnd_800565 182699840074118008647011 := by
  unfold tailWord_800565
  simp only [CollatzResearch.WordTrace]
  refine ⟨29199004344697205461827149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19466002896464803641218099 29199004344697205461827149)
  ·
    refine ⟨10949626629261452048185181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29199004344697205461827149 10949626629261452048185181)
    ·
      refine ⟨4106109985973044518069443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10949626629261452048185181 4106109985973044518069443)
      ·
        refine ⟨6159164978959566777104165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4106109985973044518069443 6159164978959566777104165)
        ·
          refine ⟨1154843433554918770707031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6159164978959566777104165 1154843433554918770707031)
          ·
            refine ⟨1732265150332378156060547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154843433554918770707031 1732265150332378156060547)
            ·
              refine ⟨2598397725498567234090821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1732265150332378156060547 2598397725498567234090821)
              ·
                refine ⟨487199573530981356392029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2598397725498567234090821 487199573530981356392029)
                ·
                  refine ⟨182699840074118008647011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487199573530981356392029 182699840074118008647011)
                  ·
                    rfl

theorem cell21_800565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_800565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800565 prefixEnd_800565 := by exact prefixLift 800565
  have htrace : WordTrace (prefixWord ++ tailWord_800565) baseStart_800565 baseEnd_800565 := by
    simpa [prefixWord, tailWord_800565, baseEnd_800565] using wordTrace_append hprefix tailTrace_800565
  have hstable : (prefixWord ++ tailWord_800565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800565).length < 2 ^ (prefixWord ++ tailWord_800565).sum := by decide
  have hdescent : baseEnd_800565 < baseStart_800565 := by decide
  rcases family_descends (prefixWord ++ tailWord_800565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800593 : List Nat := [1, 2, 2, 1, 5, 2, 3, 5]
def baseStart_800593 : Nat := 118140960795 + 800593 * 2 ^ 59
def prefixEnd_800593 : Nat := 4983230072969 + 3 ^ 40 * 800593 * 2
def baseEnd_800593 : Nat := 60902076685198727393429

theorem tailTrace_800593 : CollatzResearch.WordTrace tailWord_800593 prefixEnd_800593 60902076685198727393429 := by
  unfold tailWord_800593
  simp only [CollatzResearch.WordTrace]
  refine ⟨29200025588595766243846433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19466683725730510829230955 29200025588595766243846433)
  ·
    refine ⟨21900019191446824682884825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29200025588595766243846433 21900019191446824682884825)
    ·
      refine ⟨16425014393585118512163619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21900019191446824682884825 16425014393585118512163619)
      ·
        refine ⟨24637521590377677768245429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16425014393585118512163619 24637521590377677768245429)
        ·
          refine ⟨2309767649097907290773009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24637521590377677768245429 2309767649097907290773009)
          ·
            refine ⟨1732325736823430468079757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2309767649097907290773009 1732325736823430468079757)
            ·
              refine ⟨649622151308786425529909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1732325736823430468079757 649622151308786425529909)
              ·
                refine ⟨60902076685198727393429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 649622151308786425529909 60902076685198727393429)
                ·
                  rfl

theorem cell21_800593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 5].length) (baseStart_800593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800593 prefixEnd_800593 := by exact prefixLift 800593
  have htrace : WordTrace (prefixWord ++ tailWord_800593) baseStart_800593 baseEnd_800593 := by
    simpa [prefixWord, tailWord_800593, baseEnd_800593] using wordTrace_append hprefix tailTrace_800593
  have hstable : (prefixWord ++ tailWord_800593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800593).length < 2 ^ (prefixWord ++ tailWord_800593).sum := by decide
  have hdescent : baseEnd_800593 < baseStart_800593 := by decide
  rcases family_descends (prefixWord ++ tailWord_800593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800635 : List Nat := [1, 1, 1, 1, 1, 5, 1, 10]
def baseStart_800635 : Nat := 118140960795 + 800635 * 2 ^ 59
def prefixEnd_800635 : Nat := 4983230072969 + 3 ^ 40 * 800635 * 2
def baseEnd_800635 : Nat := 60905271675937814160067

theorem tailTrace_800635 : CollatzResearch.WordTrace tailWord_800635 prefixEnd_800635 60905271675937814160067 := by
  unfold tailWord_800635
  simp only [CollatzResearch.WordTrace]
  refine ⟨29201557454443607416875359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19467704969629071611250239 29201557454443607416875359)
  ·
    refine ⟨43802336181665411125313039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29201557454443607416875359 43802336181665411125313039)
    ·
      refine ⟨65703504272498116687969559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43802336181665411125313039 65703504272498116687969559)
      ·
        refine ⟨98555256408747175031954339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65703504272498116687969559 98555256408747175031954339)
        ·
          refine ⟨147832884613120762547931509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98555256408747175031954339 147832884613120762547931509)
          ·
            refine ⟨13859332932480071488868579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147832884613120762547931509 13859332932480071488868579)
            ·
              refine ⟨20788999398720107233302869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13859332932480071488868579 20788999398720107233302869)
              ·
                refine ⟨60905271675937814160067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20788999398720107233302869 60905271675937814160067)
                ·
                  rfl

theorem cell21_800635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 10].length) (baseStart_800635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800635 prefixEnd_800635 := by exact prefixLift 800635
  have htrace : WordTrace (prefixWord ++ tailWord_800635) baseStart_800635 baseEnd_800635 := by
    simpa [prefixWord, tailWord_800635, baseEnd_800635] using wordTrace_append hprefix tailTrace_800635
  have hstable : (prefixWord ++ tailWord_800635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800635).length < 2 ^ (prefixWord ++ tailWord_800635).sum := by decide
  have hdescent : baseEnd_800635 < baseStart_800635 := by decide
  rcases family_descends (prefixWord ++ tailWord_800635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800658 : List Nat := [3, 2, 3, 2, 1, 3, 1, 3, 3]
def baseStart_800658 : Nat := 118140960795 + 800658 * 2 ^ 59
def prefixEnd_800658 : Nat := 4983230072969 + 3 ^ 40 * 800658 * 2
def baseEnd_800658 : Nat := 182721063941170513596821

theorem tailTrace_800658 : CollatzResearch.WordTrace tailWord_800658 prefixEnd_800658 182721063941170513596821 := by
  unfold tailWord_800658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7300599083340070586240657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19468264222240188229975085 7300599083340070586240657)
  ·
    refine ⟨5475449312505052939680493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7300599083340070586240657 5475449312505052939680493)
    ·
      refine ⟨2053293492189394852380185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5475449312505052939680493 2053293492189394852380185)
      ·
        refine ⟨1539970119142046139285139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2053293492189394852380185 1539970119142046139285139)
        ·
          refine ⟨2309955178713069208927709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1539970119142046139285139 2309955178713069208927709)
          ·
            refine ⟨866233192017400953347891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2309955178713069208927709 866233192017400953347891)
            ·
              refine ⟨1299349788026101430021837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 866233192017400953347891 1299349788026101430021837)
              ·
                refine ⟨487256170509788036258189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1299349788026101430021837 487256170509788036258189)
                ·
                  refine ⟨182721063941170513596821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487256170509788036258189 182721063941170513596821)
                  ·
                    rfl

theorem cell21_800658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_800658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800658 prefixEnd_800658 := by exact prefixLift 800658
  have htrace : WordTrace (prefixWord ++ tailWord_800658) baseStart_800658 baseEnd_800658 := by
    simpa [prefixWord, tailWord_800658, baseEnd_800658] using wordTrace_append hprefix tailTrace_800658
  have hstable : (prefixWord ++ tailWord_800658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800658).length < 2 ^ (prefixWord ++ tailWord_800658).sum := by decide
  have hdescent : baseEnd_800658 < baseStart_800658 := by decide
  rcases family_descends (prefixWord ++ tailWord_800658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800776 : List Nat := [2, 1, 3, 2, 1, 2, 4, 3, 3]
def baseStart_800776 : Nat := 118140960795 + 800776 * 2 ^ 59
def prefixEnd_800776 : Nat := 4983230072969 + 3 ^ 40 * 800776 * 2
def baseEnd_800776 : Nat := 182747993148828530629913

theorem tailTrace_800776 : CollatzResearch.WordTrace tailWord_800776 prefixEnd_800776 182747993148828530629913 := by
  unfold tailWord_800776
  simp only [CollatzResearch.WordTrace]
  refine ⟨14603350073466394248879091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19471133431288525665172121 14603350073466394248879091)
  ·
    refine ⟨21905025110199591373318637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14603350073466394248879091 21905025110199591373318637)
    ·
      refine ⟨8214384416324846764994489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21905025110199591373318637 8214384416324846764994489)
      ·
        refine ⟨6160788312243635073745867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8214384416324846764994489 6160788312243635073745867)
        ·
          refine ⟨9241182468365452610618801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6160788312243635073745867 9241182468365452610618801)
          ·
            refine ⟨6930886851274089457964101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9241182468365452610618801 6930886851274089457964101)
            ·
              refine ⟨1299541284613891773368269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6930886851274089457964101 1299541284613891773368269)
              ·
                refine ⟨487327981730209415013101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1299541284613891773368269 487327981730209415013101)
                ·
                  refine ⟨182747993148828530629913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487327981730209415013101 182747993148828530629913)
                  ·
                    rfl

theorem cell21_800776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 3].length) (baseStart_800776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800776 prefixEnd_800776 := by exact prefixLift 800776
  have htrace : WordTrace (prefixWord ++ tailWord_800776) baseStart_800776 baseEnd_800776 := by
    simpa [prefixWord, tailWord_800776, baseEnd_800776] using wordTrace_append hprefix tailTrace_800776
  have hstable : (prefixWord ++ tailWord_800776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800776).length < 2 ^ (prefixWord ++ tailWord_800776).sum := by decide
  have hdescent : baseEnd_800776 < baseStart_800776 := by decide
  rcases family_descends (prefixWord ++ tailWord_800776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800835 : List Nat := [1, 1, 1, 3, 1, 2, 2, 7, 3]
def baseStart_800835 : Nat := 118140960795 + 800835 * 2 ^ 59
def prefixEnd_800835 : Nat := 4983230072969 + 3 ^ 40 * 800835 * 2
def baseEnd_800835 : Nat := 182761457752657539146459

theorem tailTrace_800835 : CollatzResearch.WordTrace tailWord_800835 prefixEnd_800835 182761457752657539146459 := by
  unfold tailWord_800835
  simp only [CollatzResearch.WordTrace]
  refine ⟨29208852053719041574155959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19472568035812694382770639 29208852053719041574155959)
  ·
    refine ⟨43813278080578562361233939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29208852053719041574155959 43813278080578562361233939)
    ·
      refine ⟨65719917120867843541850909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43813278080578562361233939 65719917120867843541850909)
      ·
        refine ⟨24644968920325441328194091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65719917120867843541850909 24644968920325441328194091)
        ·
          refine ⟨36967453380488161992291137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24644968920325441328194091 36967453380488161992291137)
          ·
            refine ⟨27725590035366121494218353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36967453380488161992291137 27725590035366121494218353)
            ·
              refine ⟨20794192526524591120663765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27725590035366121494218353 20794192526524591120663765)
              ·
                refine ⟨487363887340420104390557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20794192526524591120663765 487363887340420104390557)
                ·
                  refine ⟨182761457752657539146459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487363887340420104390557 182761457752657539146459)
                  ·
                    rfl

theorem cell21_800835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 3].length) (baseStart_800835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800835 prefixEnd_800835 := by exact prefixLift 800835
  have htrace : WordTrace (prefixWord ++ tailWord_800835) baseStart_800835 baseEnd_800835 := by
    simpa [prefixWord, tailWord_800835, baseEnd_800835] using wordTrace_append hprefix tailTrace_800835
  have hstable : (prefixWord ++ tailWord_800835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800835).length < 2 ^ (prefixWord ++ tailWord_800835).sum := by decide
  have hdescent : baseEnd_800835 < baseStart_800835 := by decide
  rcases family_descends (prefixWord ++ tailWord_800835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800849 : List Nat := [1, 2, 2, 1, 3, 1, 1, 6, 4]
def baseStart_800849 : Nat := 118140960795 + 800849 * 2 ^ 59
def prefixEnd_800849 : Nat := 4983230072969 + 3 ^ 40 * 800849 * 2
def baseEnd_800849 : Nat := 182764652743396625913097

theorem tailTrace_800849 : CollatzResearch.WordTrace tailWord_800849 prefixEnd_800849 182764652743396625913097 := by
  unfold tailWord_800849
  simp only [CollatzResearch.WordTrace]
  refine ⟨29209362675668321965165601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19472908450445547976777067 29209362675668321965165601)
  ·
    refine ⟨21907022006751241473874201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29209362675668321965165601 21907022006751241473874201)
    ·
      refine ⟨16430266505063431105405651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21907022006751241473874201 16430266505063431105405651)
      ·
        refine ⟨24645399757595146658108477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16430266505063431105405651 24645399757595146658108477)
        ·
          refine ⟨9242024909098179996790679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24645399757595146658108477 9242024909098179996790679)
          ·
            refine ⟨13863037363647269995186019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9242024909098179996790679 13863037363647269995186019)
            ·
              refine ⟨20794556045470904992779029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13863037363647269995186019 20794556045470904992779029)
              ·
                refine ⟨974744814631448671536517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20794556045470904992779029 974744814631448671536517)
                ·
                  refine ⟨182764652743396625913097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 974744814631448671536517 182764652743396625913097)
                  ·
                    rfl

theorem cell21_800849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 4].length) (baseStart_800849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800849 prefixEnd_800849 := by exact prefixLift 800849
  have htrace : WordTrace (prefixWord ++ tailWord_800849) baseStart_800849 baseEnd_800849 := by
    simpa [prefixWord, tailWord_800849, baseEnd_800849] using wordTrace_append hprefix tailTrace_800849
  have hstable : (prefixWord ++ tailWord_800849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800849).length < 2 ^ (prefixWord ++ tailWord_800849).sum := by decide
  have hdescent : baseEnd_800849 < baseStart_800849 := by decide
  rcases family_descends (prefixWord ++ tailWord_800849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800945 : List Nat := [1, 2, 2, 5, 2, 1, 2, 3, 3]
def baseStart_800945 : Nat := 118140960795 + 800945 * 2 ^ 59
def prefixEnd_800945 : Nat := 4983230072969 + 3 ^ 40 * 800945 * 2
def baseEnd_800945 : Nat := 182786561251321792312901

theorem tailTrace_800945 : CollatzResearch.WordTrace tailWord_800945 prefixEnd_800945 182786561251321792312901 := by
  unfold tailWord_800945
  simp only [CollatzResearch.WordTrace]
  refine ⟨29212864083320530360660289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19475242722213686907106859 29212864083320530360660289)
  ·
    refine ⟨21909648062490397770495217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29212864083320530360660289 21909648062490397770495217)
    ·
      refine ⟨16432236046867798327871413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21909648062490397770495217 16432236046867798327871413)
      ·
        refine ⟨1540522129393856093237945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16432236046867798327871413 1540522129393856093237945)
        ·
          refine ⟨1155391597045392069928459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1540522129393856093237945 1155391597045392069928459)
          ·
            refine ⟨1733087395568088104892689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155391597045392069928459 1733087395568088104892689)
            ·
              refine ⟨1299815546676066078669517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1733087395568088104892689 1299815546676066078669517)
              ·
                refine ⟨487430830003524779501069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1299815546676066078669517 487430830003524779501069)
                ·
                  refine ⟨182786561251321792312901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487430830003524779501069 182786561251321792312901)
                  ·
                    rfl

theorem cell21_800945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 3].length) (baseStart_800945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800945 prefixEnd_800945 := by exact prefixLift 800945
  have htrace : WordTrace (prefixWord ++ tailWord_800945) baseStart_800945 baseEnd_800945 := by
    simpa [prefixWord, tailWord_800945, baseEnd_800945] using wordTrace_append hprefix tailTrace_800945
  have hstable : (prefixWord ++ tailWord_800945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800945).length < 2 ^ (prefixWord ++ tailWord_800945).sum := by decide
  have hdescent : baseEnd_800945 < baseStart_800945 := by decide
  rcases family_descends (prefixWord ++ tailWord_800945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800956 : List Nat := [2, 2, 2, 3, 3, 1, 8]
def baseStart_800956 : Nat := 118140960795 + 800956 * 2 ^ 59
def prefixEnd_800956 : Nat := 4983230072969 + 3 ^ 40 * 800956 * 2
def baseEnd_800956 : Nat := 20309896844576468625505

theorem tailTrace_800956 : CollatzResearch.WordTrace tailWord_800956 prefixEnd_800956 20309896844576468625505 := by
  unfold tailWord_800956
  simp only [CollatzResearch.WordTrace]
  refine ⟨14606632643140339619655361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19475510190853786159540481 14606632643140339619655361)
  ·
    refine ⟨10954974482355254714741521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14606632643140339619655361 10954974482355254714741521)
    ·
      refine ⟨8216230861766441036056141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10954974482355254714741521 8216230861766441036056141)
      ·
        refine ⟨3081086573162415388521053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8216230861766441036056141 3081086573162415388521053)
        ·
          refine ⟨1155407464935905770695395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3081086573162415388521053 1155407464935905770695395)
          ·
            refine ⟨1733111197403858656043093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155407464935905770695395 1733111197403858656043093)
            ·
              refine ⟨20309896844576468625505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1733111197403858656043093 20309896844576468625505)
              ·
                rfl

theorem cell21_800956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 8].length) (baseStart_800956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800956 prefixEnd_800956 := by exact prefixLift 800956
  have htrace : WordTrace (prefixWord ++ tailWord_800956) baseStart_800956 baseEnd_800956 := by
    simpa [prefixWord, tailWord_800956, baseEnd_800956] using wordTrace_append hprefix tailTrace_800956
  have hstable : (prefixWord ++ tailWord_800956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800956).length < 2 ^ (prefixWord ++ tailWord_800956).sum := by decide
  have hdescent : baseEnd_800956 < baseStart_800956 := by decide
  rcases family_descends (prefixWord ++ tailWord_800956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800962 : List Nat := [3, 5, 1, 1, 1, 1, 2, 4, 3]
def baseStart_800962 : Nat := 118140960795 + 800962 * 2 ^ 59
def prefixEnd_800962 : Nat := 4983230072969 + 3 ^ 40 * 800962 * 2
def baseEnd_800962 : Nat := 182790440882933540529533

theorem tailTrace_800962 : CollatzResearch.WordTrace tailWord_800962 prefixEnd_800962 182790440882933540529533 := by
  unfold tailWord_800962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7303371031064735566007285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19475656082839294842686093 7303371031064735566007285)
  ·
    refine ⟨684691034162318959313183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7303371031064735566007285 684691034162318959313183)
    ·
      refine ⟨1027036551243478438969775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 684691034162318959313183 1027036551243478438969775)
      ·
        refine ⟨1540554826865217658454663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1027036551243478438969775 1540554826865217658454663)
        ·
          refine ⟨2310832240297826487681995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1540554826865217658454663 2310832240297826487681995)
          ·
            refine ⟨3466248360446739731522993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2310832240297826487681995 3466248360446739731522993)
            ·
              refine ⟨2599686270335054798642245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3466248360446739731522993 2599686270335054798642245)
              ·
                refine ⟨487441175687822774745421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2599686270335054798642245 487441175687822774745421)
                ·
                  refine ⟨182790440882933540529533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487441175687822774745421 182790440882933540529533)
                  ·
                    rfl

theorem cell21_800962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_800962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_800962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_800962 prefixEnd_800962 := by exact prefixLift 800962
  have htrace : WordTrace (prefixWord ++ tailWord_800962) baseStart_800962 baseEnd_800962 := by
    simpa [prefixWord, tailWord_800962, baseEnd_800962] using wordTrace_append hprefix tailTrace_800962
  have hstable : (prefixWord ++ tailWord_800962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800962).length < 2 ^ (prefixWord ++ tailWord_800962).sum := by decide
  have hdescent : baseEnd_800962 < baseStart_800962 := by decide
  rcases family_descends (prefixWord ++ tailWord_800962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801032 : List Nat := [2, 1, 3, 2, 3, 2, 2, 6]
def baseStart_801032 : Nat := 118140960795 + 801032 * 2 ^ 59
def prefixEnd_801032 : Nat := 4983230072969 + 3 ^ 40 * 801032 * 2
def baseEnd_801032 : Nat := 60935471945542991454241

theorem tailTrace_801032 : CollatzResearch.WordTrace tailWord_801032 prefixEnd_801032 60935471945542991454241 := by
  unfold tailWord_801032
  simp only [CollatzResearch.WordTrace]
  refine ⟨14608018617002672109538675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19477358156003562812718233 14608018617002672109538675)
  ·
    refine ⟨21912027925504008164308013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14608018617002672109538675 21912027925504008164308013)
    ·
      refine ⟨8217010472064003061615505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21912027925504008164308013 8217010472064003061615505)
      ·
        refine ⟨6162757854048002296211629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8217010472064003061615505 6162757854048002296211629)
        ·
          refine ⟨2311034195268000861079361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6162757854048002296211629 2311034195268000861079361)
          ·
            refine ⟨1733275646451000645809521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2311034195268000861079361 1733275646451000645809521)
            ·
              refine ⟨1299956734838250484357141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1733275646451000645809521 1299956734838250484357141)
              ·
                refine ⟨60935471945542991454241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1299956734838250484357141 60935471945542991454241)
                ·
                  rfl

theorem cell21_801032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 6].length) (baseStart_801032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_801032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_801032 prefixEnd_801032 := by exact prefixLift 801032
  have htrace : WordTrace (prefixWord ++ tailWord_801032) baseStart_801032 baseEnd_801032 := by
    simpa [prefixWord, tailWord_801032, baseEnd_801032] using wordTrace_append hprefix tailTrace_801032
  have hstable : (prefixWord ++ tailWord_801032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801032).length < 2 ^ (prefixWord ++ tailWord_801032).sum := by decide
  have hdescent : baseEnd_801032 < baseStart_801032 := by decide
  rcases family_descends (prefixWord ++ tailWord_801032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801080 : List Nat := [2, 1, 2, 1, 3, 1, 6, 2, 3]
def baseStart_801080 : Nat := 118140960795 + 801080 * 2 ^ 59
def prefixEnd_801080 : Nat := 4983230072969 + 3 ^ 40 * 801080 * 2
def baseEnd_801080 : Nat := 182817370090591557562625

theorem tailTrace_801080 : CollatzResearch.WordTrace tailWord_801080 prefixEnd_801080 182817370090591557562625 := by
  unfold tailWord_801080
  simp only [CollatzResearch.WordTrace]
  refine ⟨14608893968915724208412347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19478525291887632277883129 14608893968915724208412347)
  ·
    refine ⟨21913340953373586312618521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14608893968915724208412347 21913340953373586312618521)
    ·
      refine ⟨16435005715030189734463891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21913340953373586312618521 16435005715030189734463891)
      ·
        refine ⟨24652508572545284601695837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16435005715030189734463891 24652508572545284601695837)
        ·
          refine ⟨9244690714704481725635939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24652508572545284601695837 9244690714704481725635939)
          ·
            refine ⟨13867036072056722588453909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9244690714704481725635939 13867036072056722588453909)
            ·
              refine ⟨650017315877658871333777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13867036072056722588453909 650017315877658871333777)
              ·
                refine ⟨487512986908244153500333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650017315877658871333777 487512986908244153500333)
                ·
                  refine ⟨182817370090591557562625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487512986908244153500333 182817370090591557562625)
                  ·
                    rfl

theorem cell21_801080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 3].length) (baseStart_801080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_801080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_801080 prefixEnd_801080 := by exact prefixLift 801080
  have htrace : WordTrace (prefixWord ++ tailWord_801080) baseStart_801080 baseEnd_801080 := by
    simpa [prefixWord, tailWord_801080, baseEnd_801080] using wordTrace_append hprefix tailTrace_801080
  have hstable : (prefixWord ++ tailWord_801080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801080).length < 2 ^ (prefixWord ++ tailWord_801080).sum := by decide
  have hdescent : baseEnd_801080 < baseStart_801080 := by decide
  rcases family_descends (prefixWord ++ tailWord_801080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801091 : List Nat := [1, 1, 1, 3, 1, 3, 5, 6]
def baseStart_801091 : Nat := 118140960795 + 801091 * 2 ^ 59
def prefixEnd_801091 : Nat := 4983230072969 + 3 ^ 40 * 801091 * 2
def baseEnd_801091 : Nat := 60939960146819327626423

theorem tailTrace_801091 : CollatzResearch.WordTrace tailWord_801091 prefixEnd_801091 60939960146819327626423 := by
  unfold tailWord_801091
  simp only [CollatzResearch.WordTrace]
  refine ⟨29218189140791597295475127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19478792760527731530316751 29218189140791597295475127)
  ·
    refine ⟨43827283711187395943212691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29218189140791597295475127 43827283711187395943212691)
    ·
      refine ⟨65740925566781093914819037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43827283711187395943212691 65740925566781093914819037)
      ·
        refine ⟨24652847087542910218057139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65740925566781093914819037 24652847087542910218057139)
        ·
          refine ⟨36979270631314365327085709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24652847087542910218057139 36979270631314365327085709)
          ·
            refine ⟨13867226486742886997657141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36979270631314365327085709 13867226486742886997657141)
            ·
              refine ⟨1300052483132145656030357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13867226486742886997657141 1300052483132145656030357)
              ·
                refine ⟨60939960146819327626423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1300052483132145656030357 60939960146819327626423)
                ·
                  rfl

theorem cell21_801091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 6].length) (baseStart_801091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_801091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_801091 prefixEnd_801091 := by exact prefixLift 801091
  have htrace : WordTrace (prefixWord ++ tailWord_801091) baseStart_801091 baseEnd_801091 := by
    simpa [prefixWord, tailWord_801091, baseEnd_801091] using wordTrace_append hprefix tailTrace_801091
  have hstable : (prefixWord ++ tailWord_801091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801091).length < 2 ^ (prefixWord ++ tailWord_801091).sum := by decide
  have hdescent : baseEnd_801091 < baseStart_801091 := by decide
  rcases family_descends (prefixWord ++ tailWord_801091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801204 : List Nat := [2, 5, 2, 2, 1, 1, 1, 3, 4]
def baseStart_801204 : Nat := 118140960795 + 801204 * 2 ^ 59
def prefixEnd_801204 : Nat := 4983230072969 + 3 ^ 40 * 801204 * 2
def baseEnd_801204 : Nat := 182845668579994897495705

theorem tailTrace_801204 : CollatzResearch.WordTrace tailWord_801204 prefixEnd_801204 182845668579994897495705 := by
  unfold tailWord_801204
  simp only [CollatzResearch.WordTrace]
  refine ⟨14611155294691108797169333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19481540392921478396225777 14611155294691108797169333)
  ·
    refine ⟨1369795808877291449734625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14611155294691108797169333 1369795808877291449734625)
    ·
      refine ⟨1027346856657968587300969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1369795808877291449734625 1027346856657968587300969)
      ·
        refine ⟨770510142493476440475727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1027346856657968587300969 770510142493476440475727)
        ·
          refine ⟨1155765213740214660713591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770510142493476440475727 1155765213740214660713591)
          ·
            refine ⟨1733647820610321991070387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155765213740214660713591 1733647820610321991070387)
            ·
              refine ⟨2600471730915482986605581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733647820610321991070387 2600471730915482986605581)
              ·
                refine ⟨975176899093306119977093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2600471730915482986605581 975176899093306119977093)
                ·
                  refine ⟨182845668579994897495705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 975176899093306119977093 182845668579994897495705)
                  ·
                    rfl

theorem cell21_801204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_801204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_801204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_801204 prefixEnd_801204 := by exact prefixLift 801204
  have htrace : WordTrace (prefixWord ++ tailWord_801204) baseStart_801204 baseEnd_801204 := by
    simpa [prefixWord, tailWord_801204, baseEnd_801204] using wordTrace_append hprefix tailTrace_801204
  have hstable : (prefixWord ++ tailWord_801204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801204).length < 2 ^ (prefixWord ++ tailWord_801204).sum := by decide
  have hdescent : baseEnd_801204 < baseStart_801204 := by decide
  rcases family_descends (prefixWord ++ tailWord_801204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801288 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 6]
def baseStart_801288 : Nat := 118140960795 + 801288 * 2 ^ 59
def prefixEnd_801288 : Nat := 4983230072969 + 3 ^ 40 * 801288 * 2
def baseEnd_801288 : Nat := 182864838524429418095533

theorem tailTrace_801288 : CollatzResearch.WordTrace tailWord_801288 prefixEnd_801288 182864838524429418095533 := by
  unfold tailWord_801288
  simp only [CollatzResearch.WordTrace]
  refine ⟨14612687160538949970198259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19483582880718599960264345 14612687160538949970198259)
  ·
    refine ⟨21919030740808424955297389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14612687160538949970198259 21919030740808424955297389)
    ·
      refine ⟨8219636527803159358236521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21919030740808424955297389 8219636527803159358236521)
      ·
        refine ⟨6164727395852369518677391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8219636527803159358236521 6164727395852369518677391)
        ·
          refine ⟨9247091093778554278016087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6164727395852369518677391 9247091093778554278016087)
          ·
            refine ⟨13870636640667831417024131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9247091093778554278016087 13870636640667831417024131)
            ·
              refine ⟨20805954961001747125536197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13870636640667831417024131 20805954961001747125536197)
              ·
                refine ⟨3901116555187827586038037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20805954961001747125536197 3901116555187827586038037)
                ·
                  refine ⟨182864838524429418095533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3901116555187827586038037 182864838524429418095533)
                  ·
                    rfl

theorem cell21_801288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_801288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_801288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_801288 prefixEnd_801288 := by exact prefixLift 801288
  have htrace : WordTrace (prefixWord ++ tailWord_801288) baseStart_801288 baseEnd_801288 := by
    simpa [prefixWord, tailWord_801288, baseEnd_801288] using wordTrace_append hprefix tailTrace_801288
  have hstable : (prefixWord ++ tailWord_801288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801288).length < 2 ^ (prefixWord ++ tailWord_801288).sum := by decide
  have hdescent : baseEnd_801288 < baseStart_801288 := by decide
  rcases family_descends (prefixWord ++ tailWord_801288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801291 : List Nat := [1, 1, 1, 1, 7, 1, 1, 5, 3]
def baseStart_801291 : Nat := 118140960795 + 801291 * 2 ^ 59
def prefixEnd_801291 : Nat := 4983230072969 + 3 ^ 40 * 801291 * 2
def baseEnd_801291 : Nat := 182865523165302079545527

theorem tailTrace_801291 : CollatzResearch.WordTrace tailWord_801291 prefixEnd_801291 182865523165302079545527 := by
  unfold tailWord_801291
  simp only [CollatzResearch.WordTrace]
  refine ⟨29225483740067031452755727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19483655826711354301837151 29225483740067031452755727)
  ·
    refine ⟨43838225610100547179133591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29225483740067031452755727 43838225610100547179133591)
    ·
      refine ⟨65757338415150820768700387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43838225610100547179133591 65757338415150820768700387)
      ·
        refine ⟨98636007622726231153050581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65757338415150820768700387 98636007622726231153050581)
        ·
          refine ⟨2311781428657646042649623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 98636007622726231153050581 2311781428657646042649623)
          ·
            refine ⟨3467672142986469063974435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2311781428657646042649623 3467672142986469063974435)
            ·
              refine ⟨5201508214479703595961653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3467672142986469063974435 5201508214479703595961653)
              ·
                refine ⟨487641395107472212121405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5201508214479703595961653 487641395107472212121405)
                ·
                  refine ⟨182865523165302079545527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487641395107472212121405 182865523165302079545527)
                  ·
                    rfl

theorem cell21_801291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 3].length) (baseStart_801291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_801291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_801291 prefixEnd_801291 := by exact prefixLift 801291
  have htrace : WordTrace (prefixWord ++ tailWord_801291) baseStart_801291 baseEnd_801291 := by
    simpa [prefixWord, tailWord_801291, baseEnd_801291] using wordTrace_append hprefix tailTrace_801291
  have hstable : (prefixWord ++ tailWord_801291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801291).length < 2 ^ (prefixWord ++ tailWord_801291).sum := by decide
  have hdescent : baseEnd_801291 < baseStart_801291 := by decide
  rcases family_descends (prefixWord ++ tailWord_801291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801342 : List Nat := [4, 2, 1, 4, 1, 2, 1, 3, 3]
def baseStart_801342 : Nat := 118140960795 + 801342 * 2 ^ 59
def prefixEnd_801342 : Nat := 4983230072969 + 3 ^ 40 * 801342 * 2
def baseEnd_801342 : Nat := 182877162060137324195423

theorem tailTrace_801342 : CollatzResearch.WordTrace tailWord_801342 prefixEnd_801342 182877162060137324195423 := by
  unfold tailWord_801342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3653417982860283395357785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19484895908588178108574853 3653417982860283395357785)
  ·
    refine ⟨2740063487145212546518339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3653417982860283395357785 2740063487145212546518339)
    ·
      refine ⟨4110095230717818819777509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2740063487145212546518339 4110095230717818819777509)
      ·
        refine ⟨770642855759591028708283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4110095230717818819777509 770642855759591028708283)
        ·
          refine ⟨1155964283639386543062425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770642855759591028708283 1155964283639386543062425)
          ·
            refine ⟨866973212729539907296819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1155964283639386543062425 866973212729539907296819)
            ·
              refine ⟨1300459819094309860945229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 866973212729539907296819 1300459819094309860945229)
              ·
                refine ⟨487672432160366197854461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1300459819094309860945229 487672432160366197854461)
                ·
                  refine ⟨182877162060137324195423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487672432160366197854461 182877162060137324195423)
                  ·
                    rfl

theorem cell21_801342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_801342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_801342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_801342 prefixEnd_801342 := by exact prefixLift 801342
  have htrace : WordTrace (prefixWord ++ tailWord_801342) baseStart_801342 baseEnd_801342 := by
    simpa [prefixWord, tailWord_801342, baseEnd_801342] using wordTrace_append hprefix tailTrace_801342
  have hstable : (prefixWord ++ tailWord_801342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801342).length < 2 ^ (prefixWord ++ tailWord_801342).sum := by decide
  have hdescent : baseEnd_801342 < baseStart_801342 := by decide
  rcases family_descends (prefixWord ++ tailWord_801342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801418 : List Nat := [3, 1, 2, 3, 4, 1, 2, 2, 3]
def baseStart_801418 : Nat := 118140960795 + 801418 * 2 ^ 59
def prefixEnd_801418 : Nat := 4983230072969 + 3 ^ 40 * 801418 * 2
def baseEnd_801418 : Nat := 182894506295578080928601

theorem tailTrace_801418 : CollatzResearch.WordTrace tailWord_801418 prefixEnd_801418 182894506295578080928601 := by
  unfold tailWord_801418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7307528952651733035657227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19486743873737954761752605 7307528952651733035657227)
  ·
    refine ⟨10961293428977599553485841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7307528952651733035657227 10961293428977599553485841)
    ·
      refine ⟨8220970071733199665114381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10961293428977599553485841 8220970071733199665114381)
      ·
        refine ⟨3082863776899949874417893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8220970071733199665114381 3082863776899949874417893)
        ·
          refine ⟨578036958168740601453355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3082863776899949874417893 578036958168740601453355)
          ·
            refine ⟨867055437253110902180033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578036958168740601453355 867055437253110902180033)
            ·
              refine ⟨650291577939833176635025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 867055437253110902180033 650291577939833176635025)
              ·
                refine ⟨487718683454874882476269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650291577939833176635025 487718683454874882476269)
                ·
                  refine ⟨182894506295578080928601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487718683454874882476269 182894506295578080928601)
                  ·
                    rfl

theorem cell21_801418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_801418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_801418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_801418 prefixEnd_801418 := by exact prefixLift 801418
  have htrace : WordTrace (prefixWord ++ tailWord_801418) baseStart_801418 baseEnd_801418 := by
    simpa [prefixWord, tailWord_801418, baseEnd_801418] using wordTrace_append hprefix tailTrace_801418
  have hstable : (prefixWord ++ tailWord_801418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801418).length < 2 ^ (prefixWord ++ tailWord_801418).sum := by decide
  have hdescent : baseEnd_801418 < baseStart_801418 := by decide
  rcases family_descends (prefixWord ++ tailWord_801418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801519 : List Nat := [1, 1, 2, 1, 5, 2, 3, 3, 3]
def baseStart_801519 : Nat := 118140960795 + 801519 * 2 ^ 59
def prefixEnd_801519 : Nat := 4983230072969 + 3 ^ 40 * 801519 * 2
def baseEnd_801519 : Nat := 182917555871624349745061

theorem tailTrace_801519 : CollatzResearch.WordTrace tailWord_801519 prefixEnd_801519 182917555871624349745061 := by
  unfold tailWord_801519
  simp only [CollatzResearch.WordTrace]
  refine ⟨29233799583241026392055611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19489199722160684261370407 29233799583241026392055611)
  ·
    refine ⟨43850699374861539588083417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29233799583241026392055611 43850699374861539588083417)
    ·
      refine ⟨32888024531146154691062563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43850699374861539588083417 32888024531146154691062563)
      ·
        refine ⟨49332036796719232036593845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32888024531146154691062563 49332036796719232036593845)
        ·
          refine ⟨4624878449692428003430673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49332036796719232036593845 4624878449692428003430673)
          ·
            refine ⟨3468658837269321002573005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4624878449692428003430673 3468658837269321002573005)
            ·
              refine ⟨1300747063975995375964877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3468658837269321002573005 1300747063975995375964877)
              ·
                refine ⟨487780148990998265986829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1300747063975995375964877 487780148990998265986829)
                ·
                  refine ⟨182917555871624349745061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487780148990998265986829 182917555871624349745061)
                  ·
                    rfl

theorem cell21_801519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 3].length) (baseStart_801519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_801519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_801519 prefixEnd_801519 := by exact prefixLift 801519
  have htrace : WordTrace (prefixWord ++ tailWord_801519) baseStart_801519 baseEnd_801519 := by
    simpa [prefixWord, tailWord_801519, baseEnd_801519] using wordTrace_append hprefix tailTrace_801519
  have hstable : (prefixWord ++ tailWord_801519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801519).length < 2 ^ (prefixWord ++ tailWord_801519).sum := by decide
  have hdescent : baseEnd_801519 < baseStart_801519 := by decide
  rcases family_descends (prefixWord ++ tailWord_801519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801530 : List Nat := [3, 1, 1, 1, 1, 3, 11]
def baseStart_801530 : Nat := 118140960795 + 801530 * 2 ^ 59
def prefixEnd_801530 : Nat := 4983230072969 + 3 ^ 40 * 801530 * 2
def baseEnd_801530 : Nat := 20324451802387863895745

theorem tailTrace_801530 : CollatzResearch.WordTrace tailWord_801530 prefixEnd_801530 20324451802387863895745 := by
  unfold tailWord_801530
  simp only [CollatzResearch.WordTrace]
  refine ⟨7308550196550293817676511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19489467190800783513804029 7308550196550293817676511)
  ·
    refine ⟨10962825294825440726514767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7308550196550293817676511 10962825294825440726514767)
    ·
      refine ⟨16444237942238161089772151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10962825294825440726514767 16444237942238161089772151)
      ·
        refine ⟨24666356913357241634658227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16444237942238161089772151 24666356913357241634658227)
        ·
          refine ⟨36999535370035862451987341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24666356913357241634658227 36999535370035862451987341)
          ·
            refine ⟨13874825763763448419495253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36999535370035862451987341 13874825763763448419495253)
            ·
              refine ⟨20324451802387863895745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13874825763763448419495253 20324451802387863895745)
              ·
                rfl

theorem cell21_801530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 11].length) (baseStart_801530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_801530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_801530 prefixEnd_801530 := by exact prefixLift 801530
  have htrace : WordTrace (prefixWord ++ tailWord_801530) baseStart_801530 baseEnd_801530 := by
    simpa [prefixWord, tailWord_801530, baseEnd_801530] using wordTrace_append hprefix tailTrace_801530
  have hstable : (prefixWord ++ tailWord_801530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801530).length < 2 ^ (prefixWord ++ tailWord_801530).sum := by decide
  have hdescent : baseEnd_801530 < baseStart_801530 := by decide
  rcases family_descends (prefixWord ++ tailWord_801530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801581 : List Nat := [1, 5, 3, 2, 2, 8]
def baseStart_801581 : Nat := 118140960795 + 801581 * 2 ^ 59
def prefixEnd_801581 : Nat := 4983230072969 + 3 ^ 40 * 801581 * 2
def baseEnd_801581 : Nat := 6775248337641704433763

theorem tailTrace_801581 : CollatzResearch.WordTrace tailWord_801581 prefixEnd_801581 6775248337641704433763 := by
  unfold tailWord_801581
  simp only [CollatzResearch.WordTrace]
  refine ⟨29236060909016410980812597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19490707272677607320541731 29236060909016410980812597)
  ·
    refine ⟨2740880710220288529451181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29236060909016410980812597 2740880710220288529451181)
    ·
      refine ⟨1027830266332608198544193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2740880710220288529451181 1027830266332608198544193)
      ·
        refine ⟨770872699749456148908145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1027830266332608198544193 770872699749456148908145)
        ·
          refine ⟨578154524812092111681109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 770872699749456148908145 578154524812092111681109)
          ·
            refine ⟨6775248337641704433763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 578154524812092111681109 6775248337641704433763)
            ·
              rfl

theorem cell21_801581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 8].length) (baseStart_801581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_801581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_801581 prefixEnd_801581 := by exact prefixLift 801581
  have htrace : WordTrace (prefixWord ++ tailWord_801581) baseStart_801581 baseEnd_801581 := by
    simpa [prefixWord, tailWord_801581, baseEnd_801581] using wordTrace_append hprefix tailTrace_801581
  have hstable : (prefixWord ++ tailWord_801581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801581).length < 2 ^ (prefixWord ++ tailWord_801581).sum := by decide
  have hdescent : baseEnd_801581 < baseStart_801581 := by decide
  rcases family_descends (prefixWord ++ tailWord_801581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801716 : List Nat := [2, 5, 2, 1, 1, 1, 1, 8]
def baseStart_801716 : Nat := 118140960795 + 801716 * 2 ^ 59
def prefixEnd_801716 : Nat := 4983230072969 + 3 ^ 40 * 801716 * 2
def baseEnd_801716 : Nat := 60987504651865261653775

theorem tailTrace_801716 : CollatzResearch.WordTrace tailWord_801716 prefixEnd_801716 60987504651865261653775 := by
  unfold tailWord_801716
  simp only [CollatzResearch.WordTrace]
  refine ⟨14620492381763664518488501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19493989842351552691318001 14620492381763664518488501)
  ·
    refine ⟨1370671160790343548608297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14620492381763664518488501 1370671160790343548608297)
    ·
      refine ⟨1028003370592757661456223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1370671160790343548608297 1028003370592757661456223)
      ·
        refine ⟨1542005055889136492184335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1028003370592757661456223 1542005055889136492184335)
        ·
          refine ⟨2313007583833704738276503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1542005055889136492184335 2313007583833704738276503)
          ·
            refine ⟨3469511375750557107414755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2313007583833704738276503 3469511375750557107414755)
            ·
              refine ⟨5204267063625835661122133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3469511375750557107414755 5204267063625835661122133)
              ·
                refine ⟨60987504651865261653775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5204267063625835661122133 60987504651865261653775)
                ·
                  rfl

theorem cell21_801716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 8].length) (baseStart_801716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_801716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_801716 prefixEnd_801716 := by exact prefixLift 801716
  have htrace : WordTrace (prefixWord ++ tailWord_801716) baseStart_801716 baseEnd_801716 := by
    simpa [prefixWord, tailWord_801716, baseEnd_801716] using wordTrace_append hprefix tailTrace_801716
  have hstable : (prefixWord ++ tailWord_801716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801716).length < 2 ^ (prefixWord ++ tailWord_801716).sum := by decide
  have hdescent : baseEnd_801716 < baseStart_801716 := by decide
  rcases family_descends (prefixWord ++ tailWord_801716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801727 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 8]
def baseStart_801727 : Nat := 118140960795 + 801727 * 2 ^ 59
def prefixEnd_801727 : Nat := 4983230072969 + 3 ^ 40 * 801727 * 2
def baseEnd_801727 : Nat := 182965024305462210277969

theorem tailTrace_801727 : CollatzResearch.WordTrace tailWord_801727 prefixEnd_801727 182965024305462210277969 := by
  unfold tailWord_801727
  simp only [CollatzResearch.WordTrace]
  refine ⟨29241385966487477915627435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19494257310991651943751623 29241385966487477915627435)
  ·
    refine ⟨43862078949731216873441153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29241385966487477915627435 43862078949731216873441153)
    ·
      refine ⟨32896559212298412655080865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43862078949731216873441153 32896559212298412655080865)
      ·
        refine ⟨24672419409223809491310649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32896559212298412655080865 24672419409223809491310649)
        ·
          refine ⟨18504314556917857118482987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24672419409223809491310649 18504314556917857118482987)
          ·
            refine ⟨27756471835376785677724481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18504314556917857118482987 27756471835376785677724481)
            ·
              refine ⟨20817353876532589258293361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27756471835376785677724481 20817353876532589258293361)
              ·
                refine ⟨15613015407399441943720021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20817353876532589258293361 15613015407399441943720021)
                ·
                  refine ⟨182965024305462210277969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15613015407399441943720021 182965024305462210277969)
                  ·
                    rfl

theorem cell21_801727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 8].length) (baseStart_801727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_801727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_801727 prefixEnd_801727 := by exact prefixLift 801727
  have htrace : WordTrace (prefixWord ++ tailWord_801727) baseStart_801727 baseEnd_801727 := by
    simpa [prefixWord, tailWord_801727, baseEnd_801727] using wordTrace_append hprefix tailTrace_801727
  have hstable : (prefixWord ++ tailWord_801727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801727).length < 2 ^ (prefixWord ++ tailWord_801727).sum := by decide
  have hdescent : baseEnd_801727 < baseStart_801727 := by decide
  rcases family_descends (prefixWord ++ tailWord_801727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801775 : List Nat := [1, 1, 2, 1, 4, 5, 1, 6]
def baseStart_801775 : Nat := 118140960795 + 801775 * 2 ^ 59
def prefixEnd_801775 : Nat := 4983230072969 + 3 ^ 40 * 801775 * 2
def baseEnd_801775 : Nat := 60991992853141597825957

theorem tailTrace_801775 : CollatzResearch.WordTrace tailWord_801775 prefixEnd_801775 60991992853141597825957 := by
  unfold tailWord_801775
  simp only [CollatzResearch.WordTrace]
  refine ⟨29243136670313582113374779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19495424446875721408916519 29243136670313582113374779)
  ·
    refine ⟨43864705005470373170062169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29243136670313582113374779 43864705005470373170062169)
    ·
      refine ⟨32898528754102779877546627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43864705005470373170062169 32898528754102779877546627)
      ·
        refine ⟨49347793131154169816319941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32898528754102779877546627 49347793131154169816319941)
        ·
          refine ⟨9252711212091406840559989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49347793131154169816319941 9252711212091406840559989)
          ·
            refine ⟨867441676133569391302499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9252711212091406840559989 867441676133569391302499)
            ·
              refine ⟨1301162514200354086953749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 867441676133569391302499 1301162514200354086953749)
              ·
                refine ⟨60991992853141597825957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1301162514200354086953749 60991992853141597825957)
                ·
                  rfl

theorem cell21_801775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 6].length) (baseStart_801775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_801775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_801775 prefixEnd_801775 := by exact prefixLift 801775
  have htrace : WordTrace (prefixWord ++ tailWord_801775) baseStart_801775 baseEnd_801775 := by
    simpa [prefixWord, tailWord_801775, baseEnd_801775] using wordTrace_append hprefix tailTrace_801775
  have hstable : (prefixWord ++ tailWord_801775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801775).length < 2 ^ (prefixWord ++ tailWord_801775).sum := by decide
  have hdescent : baseEnd_801775 < baseStart_801775 := by decide
  rcases family_descends (prefixWord ++ tailWord_801775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801857 : List Nat := [1, 2, 5, 1, 4, 1, 1, 3, 3]
def baseStart_801857 : Nat := 118140960795 + 801857 * 2 ^ 59
def prefixEnd_801857 : Nat := 4983230072969 + 3 ^ 40 * 801857 * 2
def baseEnd_801857 : Nat := 182994692076610873111037

theorem tailTrace_801857 : CollatzResearch.WordTrace tailWord_801857 prefixEnd_801857 182994692076610873111037 := by
  unfold tailWord_801857
  simp only [CollatzResearch.WordTrace]
  refine ⟨29246127456016510117859825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19497418304011006745239883 29246127456016510117859825)
  ·
    refine ⟨21934595592012382588394869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29246127456016510117859825 21934595592012382588394869)
    ·
      refine ⟨2056368336751160867662019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21934595592012382588394869 2056368336751160867662019)
      ·
        refine ⟨3084552505126741301493029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2056368336751160867662019 3084552505126741301493029)
        ·
          refine ⟨578353594711263994029943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3084552505126741301493029 578353594711263994029943)
          ·
            refine ⟨867530392066895991044915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578353594711263994029943 867530392066895991044915)
            ·
              refine ⟨1301295588100343986567373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 867530392066895991044915 1301295588100343986567373)
              ·
                refine ⟨487985845537628994962765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1301295588100343986567373 487985845537628994962765)
                ·
                  refine ⟨182994692076610873111037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487985845537628994962765 182994692076610873111037)
                  ·
                    rfl

theorem cell21_801857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 3].length) (baseStart_801857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_801857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_801857 prefixEnd_801857 := by exact prefixLift 801857
  have htrace : WordTrace (prefixWord ++ tailWord_801857) baseStart_801857 baseEnd_801857 := by
    simpa [prefixWord, tailWord_801857, baseEnd_801857] using wordTrace_append hprefix tailTrace_801857
  have hstable : (prefixWord ++ tailWord_801857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801857).length < 2 ^ (prefixWord ++ tailWord_801857).sum := by decide
  have hdescent : baseEnd_801857 < baseStart_801857 := by decide
  rcases family_descends (prefixWord ++ tailWord_801857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802017 : List Nat := [1, 2, 3, 1, 3, 2, 2, 2, 5]
def baseStart_802017 : Nat := 118140960795 + 802017 * 2 ^ 59
def prefixEnd_802017 : Nat := 4983230072969 + 3 ^ 40 * 802017 * 2
def baseEnd_802017 : Nat := 183031206256486150444043

theorem tailTrace_802017 : CollatzResearch.WordTrace tailWord_802017 prefixEnd_802017 183031206256486150444043 := by
  unfold tailWord_802017
  simp only [CollatzResearch.WordTrace]
  refine ⟨29251963135436857443684305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19501308756957904962456203 29251963135436857443684305)
  ·
    refine ⟨21938972351577643082763229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29251963135436857443684305 21938972351577643082763229)
    ·
      refine ⟨8227114631841616156036211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21938972351577643082763229 8227114631841616156036211)
      ·
        refine ⟨12340671947762424234054317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8227114631841616156036211 12340671947762424234054317)
        ·
          refine ⟨4627751980410909087770369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12340671947762424234054317 4627751980410909087770369)
          ·
            refine ⟨3470813985308181815827777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4627751980410909087770369 3470813985308181815827777)
            ·
              refine ⟨2603110488981136361870833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3470813985308181815827777 2603110488981136361870833)
              ·
                refine ⟨1952332866735852271403125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2603110488981136361870833 1952332866735852271403125)
                ·
                  refine ⟨183031206256486150444043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1952332866735852271403125 183031206256486150444043)
                  ·
                    rfl

theorem cell21_802017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_802017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802017 prefixEnd_802017 := by exact prefixLift 802017
  have htrace : WordTrace (prefixWord ++ tailWord_802017) baseStart_802017 baseEnd_802017 := by
    simpa [prefixWord, tailWord_802017, baseEnd_802017] using wordTrace_append hprefix tailTrace_802017
  have hstable : (prefixWord ++ tailWord_802017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802017).length < 2 ^ (prefixWord ++ tailWord_802017).sum := by decide
  have hdescent : baseEnd_802017 < baseStart_802017 := by decide
  rcases family_descends (prefixWord ++ tailWord_802017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802051 : List Nat := [1, 1, 1, 3, 2, 5, 3, 2, 3]
def baseStart_802051 : Nat := 118140960795 + 802051 * 2 ^ 59
def prefixEnd_802051 : Nat := 4983230072969 + 3 ^ 40 * 802051 * 2
def baseEnd_802051 : Nat := 183038965519709646877307

theorem tailTrace_802051 : CollatzResearch.WordTrace tailWord_802051 prefixEnd_802051 183038965519709646877307 := by
  unfold tailWord_802051
  simp only [CollatzResearch.WordTrace]
  refine ⟨29253203217313681250422007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19502135478209120833614671 29253203217313681250422007)
  ·
    refine ⟨43879804825970521875633011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29253203217313681250422007 43879804825970521875633011)
    ·
      refine ⟨65819707238955782813449517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43879804825970521875633011 65819707238955782813449517)
      ·
        refine ⟨24682390214608418555043569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65819707238955782813449517 24682390214608418555043569)
        ·
          refine ⟨18511792660956313916282677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24682390214608418555043569 18511792660956313916282677)
          ·
            refine ⟨1735480561964654429651501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18511792660956313916282677 1735480561964654429651501)
            ·
              refine ⟨650805210736745411119313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1735480561964654429651501 650805210736745411119313)
              ·
                refine ⟨488103908052559058339485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650805210736745411119313 488103908052559058339485)
                ·
                  refine ⟨183038965519709646877307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488103908052559058339485 183038965519709646877307)
                  ·
                    rfl

theorem cell21_802051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 3].length) (baseStart_802051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802051 prefixEnd_802051 := by exact prefixLift 802051
  have htrace : WordTrace (prefixWord ++ tailWord_802051) baseStart_802051 baseEnd_802051 := by
    simpa [prefixWord, tailWord_802051, baseEnd_802051] using wordTrace_append hprefix tailTrace_802051
  have hstable : (prefixWord ++ tailWord_802051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802051).length < 2 ^ (prefixWord ++ tailWord_802051).sum := by decide
  have hdescent : baseEnd_802051 < baseStart_802051 := by decide
  rcases family_descends (prefixWord ++ tailWord_802051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802062 : List Nat := [4, 1, 1, 2, 1, 3, 1, 8]
def baseStart_802062 : Nat := 118140960795 + 802062 * 2 ^ 59
def prefixEnd_802062 : Nat := 4983230072969 + 3 ^ 40 * 802062 * 2
def baseEnd_802062 : Nat := 61013825289858690731317

theorem tailTrace_802062 : CollatzResearch.WordTrace tailWord_802062 prefixEnd_802062 61013825289858690731317 := by
  unfold tailWord_802062
  simp only [CollatzResearch.WordTrace]
  refine ⟨3656700552534228766134055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19502402946849220086048293 3656700552534228766134055)
  ·
    refine ⟨5485050828801343149201083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3656700552534228766134055 5485050828801343149201083)
    ·
      refine ⟨8227576243202014723801625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5485050828801343149201083 8227576243202014723801625)
      ·
        refine ⟨6170682182401511042851219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8227576243202014723801625 6170682182401511042851219)
        ·
          refine ⟨9256023273602266564276829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6170682182401511042851219 9256023273602266564276829)
          ·
            refine ⟨3471008727600849961603811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9256023273602266564276829 3471008727600849961603811)
            ·
              refine ⟨5206513091401274942405717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3471008727600849961603811 5206513091401274942405717)
              ·
                refine ⟨61013825289858690731317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5206513091401274942405717 61013825289858690731317)
                ·
                  rfl

theorem cell21_802062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_802062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802062 prefixEnd_802062 := by exact prefixLift 802062
  have htrace : WordTrace (prefixWord ++ tailWord_802062) baseStart_802062 baseEnd_802062 := by
    simpa [prefixWord, tailWord_802062, baseEnd_802062] using wordTrace_append hprefix tailTrace_802062
  have hstable : (prefixWord ++ tailWord_802062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802062).length < 2 ^ (prefixWord ++ tailWord_802062).sum := by decide
  have hdescent : baseEnd_802062 < baseStart_802062 := by decide
  rcases family_descends (prefixWord ++ tailWord_802062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802102 : List Nat := [5, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_802102 : Nat := 118140960795 + 802102 * 2 ^ 59
def prefixEnd_802102 : Nat := 4983230072969 + 3 ^ 40 * 802102 * 2
def baseEnd_802102 : Nat := 183050604414544891527203

theorem tailTrace_802102 : CollatzResearch.WordTrace tailWord_802102 prefixEnd_802102 183050604414544891527203 := by
  unfold tailWord_802102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1828441458758057310033035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19503375560085944640352373 1828441458758057310033035)
  ·
    refine ⟨2742662188137085965049553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1828441458758057310033035 2742662188137085965049553)
    ·
      refine ⟨2056996641102814473787165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2742662188137085965049553 2056996641102814473787165)
      ·
        refine ⟨771373740413555427670187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2056996641102814473787165 771373740413555427670187)
        ·
          refine ⟨1157060610620333141505281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771373740413555427670187 1157060610620333141505281)
          ·
            refine ⟨867795457965249856128961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1157060610620333141505281 867795457965249856128961)
            ·
              refine ⟨650846593473937392096721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 867795457965249856128961 650846593473937392096721)
              ·
                refine ⟨488134945105453044072541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650846593473937392096721 488134945105453044072541)
                ·
                  refine ⟨183050604414544891527203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488134945105453044072541 183050604414544891527203)
                  ·
                    rfl

theorem cell21_802102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_802102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802102 prefixEnd_802102 := by exact prefixLift 802102
  have htrace : WordTrace (prefixWord ++ tailWord_802102) baseStart_802102 baseEnd_802102 := by
    simpa [prefixWord, tailWord_802102, baseEnd_802102] using wordTrace_append hprefix tailTrace_802102
  have hstable : (prefixWord ++ tailWord_802102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802102).length < 2 ^ (prefixWord ++ tailWord_802102).sum := by decide
  have hdescent : baseEnd_802102 < baseStart_802102 := by decide
  rcases family_descends (prefixWord ++ tailWord_802102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802124 : List Nat := [2, 2, 1, 3, 2, 2, 2, 3, 4]
def baseStart_802124 : Nat := 118140960795 + 802124 * 2 ^ 59
def prefixEnd_802124 : Nat := 4983230072969 + 3 ^ 40 * 802124 * 2
def baseEnd_802124 : Nat := 183055625114277742160491

theorem tailTrace_802124 : CollatzResearch.WordTrace tailWord_802124 prefixEnd_802124 183055625114277742160491 := by
  unfold tailWord_802124
  simp only [CollatzResearch.WordTrace]
  refine ⟨14627932873024607358914713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19503910497366143145219617 14627932873024607358914713)
  ·
    refine ⟨10970949654768455519186035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14627932873024607358914713 10970949654768455519186035)
    ·
      refine ⟨16456424482152683278779053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10970949654768455519186035 16456424482152683278779053)
      ·
        refine ⟨6171159180807256229542145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16456424482152683278779053 6171159180807256229542145)
        ·
          refine ⟨4628369385605442172156609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6171159180807256229542145 4628369385605442172156609)
          ·
            refine ⟨3471277039204081629117457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4628369385605442172156609 3471277039204081629117457)
            ·
              refine ⟨2603457779403061221838093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3471277039204081629117457 2603457779403061221838093)
              ·
                refine ⟨976296667276147958189285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2603457779403061221838093 976296667276147958189285)
                ·
                  refine ⟨183055625114277742160491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 976296667276147958189285 183055625114277742160491)
                  ·
                    rfl

theorem cell21_802124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_802124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802124 prefixEnd_802124 := by exact prefixLift 802124
  have htrace : WordTrace (prefixWord ++ tailWord_802124) baseStart_802124 baseEnd_802124 := by
    simpa [prefixWord, tailWord_802124, baseEnd_802124] using wordTrace_append hprefix tailTrace_802124
  have hstable : (prefixWord ++ tailWord_802124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802124).length < 2 ^ (prefixWord ++ tailWord_802124).sum := by decide
  have hdescent : baseEnd_802124 < baseStart_802124 := by decide
  rcases family_descends (prefixWord ++ tailWord_802124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802273 : List Nat := [1, 2, 3, 1, 2, 12]
def baseStart_802273 : Nat := 118140960795 + 802273 * 2 ^ 59
def prefixEnd_802273 : Nat := 4983230072969 + 3 ^ 40 * 802273 * 2
def baseEnd_802273 : Nat := 6781097368306910895439

theorem tailTrace_802273 : CollatzResearch.WordTrace tailWord_802273 prefixEnd_802273 6781097368306910895439 := by
  unfold tailWord_802273
  simp only [CollatzResearch.WordTrace]
  refine ⟨29261300222509413165003473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19507533481672942110002315 29261300222509413165003473)
  ·
    refine ⟨21945975166882059873752605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29261300222509413165003473 21945975166882059873752605)
    ·
      refine ⟨8229740687580772452657227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21945975166882059873752605 8229740687580772452657227)
      ·
        refine ⟨12344611031371158678985841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8229740687580772452657227 12344611031371158678985841)
        ·
          refine ⟨9258458273528369009239381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12344611031371158678985841 9258458273528369009239381)
          ·
            refine ⟨6781097368306910895439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9258458273528369009239381 6781097368306910895439)
            ·
              rfl

theorem cell21_802273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 12].length) (baseStart_802273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802273 prefixEnd_802273 := by exact prefixLift 802273
  have htrace : WordTrace (prefixWord ++ tailWord_802273) baseStart_802273 baseEnd_802273 := by
    simpa [prefixWord, tailWord_802273, baseEnd_802273] using wordTrace_append hprefix tailTrace_802273
  have hstable : (prefixWord ++ tailWord_802273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802273).length < 2 ^ (prefixWord ++ tailWord_802273).sum := by decide
  have hdescent : baseEnd_802273 < baseStart_802273 := by decide
  rcases family_descends (prefixWord ++ tailWord_802273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802279 : List Nat := [1, 1, 5, 2, 1, 2, 4, 2, 3]
def baseStart_802279 : Nat := 118140960795 + 802279 * 2 ^ 59
def prefixEnd_802279 : Nat := 4983230072969 + 3 ^ 40 * 802279 * 2
def baseEnd_802279 : Nat := 183090998226031917076841

theorem tailTrace_802279 : CollatzResearch.WordTrace tailWord_802279 prefixEnd_802279 183090998226031917076841 := by
  unfold tailWord_802279
  simp only [CollatzResearch.WordTrace]
  refine ⟨29261519060487676189721891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19507679373658450793147927 29261519060487676189721891)
  ·
    refine ⟨43892278590731514284582837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29261519060487676189721891 43892278590731514284582837)
    ·
      refine ⟨4114901117881079464179641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43892278590731514284582837 4114901117881079464179641)
      ·
        refine ⟨3086175838410809598134731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4114901117881079464179641 3086175838410809598134731)
        ·
          refine ⟨4629263757616214397202097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3086175838410809598134731 4629263757616214397202097)
          ·
            refine ⟨3471947818212160797901573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4629263757616214397202097 3471947818212160797901573)
            ·
              refine ⟨650990215914780149606545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3471947818212160797901573 650990215914780149606545)
              ·
                refine ⟨488242661936085112204909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650990215914780149606545 488242661936085112204909)
                ·
                  refine ⟨183090998226031917076841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488242661936085112204909 183090998226031917076841)
                  ·
                    rfl

theorem cell21_802279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 3].length) (baseStart_802279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802279 prefixEnd_802279 := by exact prefixLift 802279
  have htrace : WordTrace (prefixWord ++ tailWord_802279) baseStart_802279 baseEnd_802279 := by
    simpa [prefixWord, tailWord_802279, baseEnd_802279] using wordTrace_append hprefix tailTrace_802279
  have hstable : (prefixWord ++ tailWord_802279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802279).length < 2 ^ (prefixWord ++ tailWord_802279).sum := by decide
  have hdescent : baseEnd_802279 < baseStart_802279 := by decide
  rcases family_descends (prefixWord ++ tailWord_802279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802293 : List Nat := [1, 3, 5, 1, 1, 1, 2, 3, 4]
def baseStart_802293 : Nat := 118140960795 + 802293 * 2 ^ 59
def prefixEnd_802293 : Nat := 4983230072969 + 3 ^ 40 * 802293 * 2
def baseEnd_802293 : Nat := 183094193216771003843479

theorem tailTrace_802293 : CollatzResearch.WordTrace tailWord_802293 prefixEnd_802293 183094193216771003843479 := by
  unfold tailWord_802293
  simp only [CollatzResearch.WordTrace]
  refine ⟨29262029682436956580731533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19508019788291304387154355 29262029682436956580731533)
  ·
    refine ⟨10973261130913858717774325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29262029682436956580731533 10973261130913858717774325)
    ·
      refine ⟨1028743231023174254791343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10973261130913858717774325 1028743231023174254791343)
      ·
        refine ⟨1543114846534761382187015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1028743231023174254791343 1543114846534761382187015)
        ·
          refine ⟨2314672269802142073280523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1543114846534761382187015 2314672269802142073280523)
          ·
            refine ⟨3472008404703213109920785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2314672269802142073280523 3472008404703213109920785)
            ·
              refine ⟨2604006303527409832440589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3472008404703213109920785 2604006303527409832440589)
              ·
                refine ⟨976502363822778687165221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2604006303527409832440589 976502363822778687165221)
                ·
                  refine ⟨183094193216771003843479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 976502363822778687165221 183094193216771003843479)
                  ·
                    rfl

theorem cell21_802293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_802293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802293 prefixEnd_802293 := by exact prefixLift 802293
  have htrace : WordTrace (prefixWord ++ tailWord_802293) baseStart_802293 baseEnd_802293 := by
    simpa [prefixWord, tailWord_802293, baseEnd_802293] using wordTrace_append hprefix tailTrace_802293
  have hstable : (prefixWord ++ tailWord_802293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802293).length < 2 ^ (prefixWord ++ tailWord_802293).sum := by decide
  have hdescent : baseEnd_802293 < baseStart_802293 := by decide
  rcases family_descends (prefixWord ++ tailWord_802293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802338 : List Nat := [3, 3, 1, 1, 1, 1, 4, 4, 3]
def baseStart_802338 : Nat := 118140960795 + 802338 * 2 ^ 59
def prefixEnd_802338 : Nat := 4983230072969 + 3 ^ 40 * 802338 * 2
def baseEnd_802338 : Nat := 183104462829860925593387

theorem tailTrace_802338 : CollatzResearch.WordTrace tailWord_802338 prefixEnd_802338 183104462829860925593387 := by
  unfold tailWord_802338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7315917741818482316529917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19509113978182619510746445 7315917741818482316529917)
  ·
    refine ⟨2743469153181930868698719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7315917741818482316529917 2743469153181930868698719)
    ·
      refine ⟨4115203729772896303048079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2743469153181930868698719 4115203729772896303048079)
      ·
        refine ⟨6172805594659344454572119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4115203729772896303048079 6172805594659344454572119)
        ·
          refine ⟨9259208391989016681858179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6172805594659344454572119 9259208391989016681858179)
          ·
            refine ⟨13888812587983525022787269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9259208391989016681858179 13888812587983525022787269)
            ·
              refine ⟨2604152360246910941772613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13888812587983525022787269 2604152360246910941772613)
              ·
                refine ⟨488278567546295801582365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2604152360246910941772613 488278567546295801582365)
                ·
                  refine ⟨183104462829860925593387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488278567546295801582365 183104462829860925593387)
                  ·
                    rfl

theorem cell21_802338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_802338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802338 prefixEnd_802338 := by exact prefixLift 802338
  have htrace : WordTrace (prefixWord ++ tailWord_802338) baseStart_802338 baseEnd_802338 := by
    simpa [prefixWord, tailWord_802338, baseEnd_802338] using wordTrace_append hprefix tailTrace_802338
  have hstable : (prefixWord ++ tailWord_802338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802338).length < 2 ^ (prefixWord ++ tailWord_802338).sum := by decide
  have hdescent : baseEnd_802338 < baseStart_802338 := by decide
  rcases family_descends (prefixWord ++ tailWord_802338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802425 : List Nat := [1, 2, 1, 3, 3, 1, 1, 9]
def baseStart_802425 : Nat := 118140960795 + 802425 * 2 ^ 59
def prefixEnd_802425 : Nat := 4983230072969 + 3 ^ 40 * 802425 * 2
def baseEnd_802425 : Nat := 61041439138389369214403

theorem tailTrace_802425 : CollatzResearch.WordTrace tailWord_802425 prefixEnd_802425 61041439138389369214403 := by
  unfold tailWord_802425
  simp only [CollatzResearch.WordTrace]
  refine ⟨29266844117958743124536729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19511229411972495416357819 29266844117958743124536729)
  ·
    refine ⟨21950133088469057343402547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29266844117958743124536729 21950133088469057343402547)
    ·
      refine ⟨32925199632703586015103821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21950133088469057343402547 32925199632703586015103821)
      ·
        refine ⟨12346949862263844755663933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32925199632703586015103821 12346949862263844755663933)
        ·
          refine ⟨4630106198348941783373975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12346949862263844755663933 4630106198348941783373975)
          ·
            refine ⟨6945159297523412675060963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4630106198348941783373975 6945159297523412675060963)
            ·
              refine ⟨10417738946285119012591445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6945159297523412675060963 10417738946285119012591445)
              ·
                refine ⟨61041439138389369214403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10417738946285119012591445 61041439138389369214403)
                ·
                  rfl

theorem cell21_802425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 9].length) (baseStart_802425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802425 prefixEnd_802425 := by exact prefixLift 802425
  have htrace : WordTrace (prefixWord ++ tailWord_802425) baseStart_802425 baseEnd_802425 := by
    simpa [prefixWord, tailWord_802425, baseEnd_802425] using wordTrace_append hprefix tailTrace_802425
  have hstable : (prefixWord ++ tailWord_802425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802425).length < 2 ^ (prefixWord ++ tailWord_802425).sum := by decide
  have hdescent : baseEnd_802425 < baseStart_802425 := by decide
  rcases family_descends (prefixWord ++ tailWord_802425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802490 : List Nat := [3, 1, 1, 1, 2, 5, 2, 3, 3]
def baseStart_802490 : Nat := 118140960795 + 802490 * 2 ^ 59
def prefixEnd_802490 : Nat := 4983230072969 + 3 ^ 40 * 802490 * 2
def baseEnd_802490 : Nat := 183139151300742439059743

theorem tailTrace_802490 : CollatzResearch.WordTrace tailWord_802490 prefixEnd_802490 183139151300742439059743 := by
  unfold tailWord_802490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7317303715680814806413231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19512809908482172817101949 7317303715680814806413231)
  ·
    refine ⟨10975955573521222209619847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7317303715680814806413231 10975955573521222209619847)
    ·
      refine ⟨16463933360281833314429771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10975955573521222209619847 16463933360281833314429771)
      ·
        refine ⟨24695900040422749971644657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16463933360281833314429771 24695900040422749971644657)
        ·
          refine ⟨18521925030317062478733493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24695900040422749971644657 18521925030317062478733493)
          ·
            refine ⟨1736430471592224607381265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18521925030317062478733493 1736430471592224607381265)
            ·
              refine ⟨1302322853694168455535949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1736430471592224607381265 1302322853694168455535949)
              ·
                refine ⟨488371070135313170825981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1302322853694168455535949 488371070135313170825981)
                ·
                  refine ⟨183139151300742439059743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488371070135313170825981 183139151300742439059743)
                  ·
                    rfl

theorem cell21_802490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_802490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802490 prefixEnd_802490 := by exact prefixLift 802490
  have htrace : WordTrace (prefixWord ++ tailWord_802490) baseStart_802490 baseEnd_802490 := by
    simpa [prefixWord, tailWord_802490, baseEnd_802490] using wordTrace_append hprefix tailTrace_802490
  have hstable : (prefixWord ++ tailWord_802490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802490).length < 2 ^ (prefixWord ++ tailWord_802490).sum := by decide
  have hdescent : baseEnd_802490 < baseStart_802490 := by decide
  rcases family_descends (prefixWord ++ tailWord_802490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802532 : List Nat := [2, 3, 1, 1, 1, 3, 1, 4, 5]
def baseStart_802532 : Nat := 118140960795 + 802532 * 2 ^ 59
def prefixEnd_802532 : Nat := 4983230072969 + 3 ^ 40 * 802532 * 2
def baseEnd_802532 : Nat := 183148736272959699359657

theorem tailTrace_802532 : CollatzResearch.WordTrace tailWord_802532 prefixEnd_802532 183148736272959699359657 := by
  unfold tailWord_802532
  simp only [CollatzResearch.WordTrace]
  refine ⟨14635373364285550199340925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19513831152380733599121233 14635373364285550199340925)
  ·
    refine ⟨5488265011607081324752847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14635373364285550199340925 5488265011607081324752847)
    ·
      refine ⟨8232397517410621987129271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5488265011607081324752847 8232397517410621987129271)
      ·
        refine ⟨12348596276115932980693907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8232397517410621987129271 12348596276115932980693907)
        ·
          refine ⟨18522894414173899471040861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12348596276115932980693907 18522894414173899471040861)
          ·
            refine ⟨6946085405315212301640323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18522894414173899471040861 6946085405315212301640323)
            ·
              refine ⟨10419128107972818452460485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6946085405315212301640323 10419128107972818452460485)
              ·
                refine ⟨1953586520244903459836341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10419128107972818452460485 1953586520244903459836341)
                ·
                  refine ⟨183148736272959699359657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1953586520244903459836341 183148736272959699359657)
                  ·
                    rfl

theorem cell21_802532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_802532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802532 prefixEnd_802532 := by exact prefixLift 802532
  have htrace : WordTrace (prefixWord ++ tailWord_802532) baseStart_802532 baseEnd_802532 := by
    simpa [prefixWord, tailWord_802532, baseEnd_802532] using wordTrace_append hprefix tailTrace_802532
  have hstable : (prefixWord ++ tailWord_802532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802532).length < 2 ^ (prefixWord ++ tailWord_802532).sum := by decide
  have hdescent : baseEnd_802532 < baseStart_802532 := by decide
  rcases family_descends (prefixWord ++ tailWord_802532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802535 : List Nat := [1, 1, 5, 4, 1, 1, 1, 7]
def baseStart_802535 : Nat := 118140960795 + 802535 * 2 ^ 59
def prefixEnd_802535 : Nat := 4983230072969 + 3 ^ 40 * 802535 * 2
def baseEnd_802535 : Nat := 61049806971277453603217

theorem tailTrace_802535 : CollatzResearch.WordTrace tailWord_802535 prefixEnd_802535 61049806971277453603217 := by
  unfold tailWord_802535
  simp only [CollatzResearch.WordTrace]
  refine ⟨29270856147560231911041059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19513904098373487940694039 29270856147560231911041059)
  ·
    refine ⟨43906284221340347866561589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29270856147560231911041059 43906284221340347866561589)
    ·
      refine ⟨4116214145750657612490149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43906284221340347866561589 4116214145750657612490149)
      ·
        refine ⟨771790152328248302341903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4116214145750657612490149 771790152328248302341903)
        ·
          refine ⟨1157685228492372453512855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771790152328248302341903 1157685228492372453512855)
          ·
            refine ⟨1736527842738558680269283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157685228492372453512855 1736527842738558680269283)
            ·
              refine ⟨2604791764107838020403925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736527842738558680269283 2604791764107838020403925)
              ·
                refine ⟨61049806971277453603217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2604791764107838020403925 61049806971277453603217)
                ·
                  rfl

theorem cell21_802535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 7].length) (baseStart_802535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802535 prefixEnd_802535 := by exact prefixLift 802535
  have htrace : WordTrace (prefixWord ++ tailWord_802535) baseStart_802535 baseEnd_802535 := by
    simpa [prefixWord, tailWord_802535, baseEnd_802535] using wordTrace_append hprefix tailTrace_802535
  have hstable : (prefixWord ++ tailWord_802535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802535).length < 2 ^ (prefixWord ++ tailWord_802535).sum := by decide
  have hdescent : baseEnd_802535 < baseStart_802535 := by decide
  rcases family_descends (prefixWord ++ tailWord_802535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802617 : List Nat := [1, 2, 1, 7, 2, 1, 2, 2, 3]
def baseStart_802617 : Nat := 118140960795 + 802617 * 2 ^ 59
def prefixEnd_802617 : Nat := 4983230072969 + 3 ^ 40 * 802617 * 2
def baseEnd_802617 : Nat := 183168134431018440442817

theorem tailTrace_802617 : CollatzResearch.WordTrace tailWord_802617 prefixEnd_802617 183168134431018440442817 := by
  unfold tailWord_802617
  simp only [CollatzResearch.WordTrace]
  refine ⟨29273846933263159915526105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19515897955508773277017403 29273846933263159915526105)
  ·
    refine ⟨21955385199947369936644579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29273846933263159915526105 21955385199947369936644579)
    ·
      refine ⟨32933077799921054904966869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21955385199947369936644579 32933077799921054904966869)
      ·
        refine ⟨771869010935649724335161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 32933077799921054904966869 771869010935649724335161)
        ·
          refine ⟨578901758201737293251371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771869010935649724335161 578901758201737293251371)
          ·
            refine ⟨868352637302605939877057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578901758201737293251371 868352637302605939877057)
            ·
              refine ⟨651264477976954454907793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 868352637302605939877057 651264477976954454907793)
              ·
                refine ⟨488448358482715841180845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651264477976954454907793 488448358482715841180845)
                ·
                  refine ⟨183168134431018440442817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488448358482715841180845 183168134431018440442817)
                  ·
                    rfl

theorem cell21_802617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 3].length) (baseStart_802617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802617 prefixEnd_802617 := by exact prefixLift 802617
  have htrace : WordTrace (prefixWord ++ tailWord_802617) baseStart_802617 baseEnd_802617 := by
    simpa [prefixWord, tailWord_802617, baseEnd_802617] using wordTrace_append hprefix tailTrace_802617
  have hstable : (prefixWord ++ tailWord_802617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802617).length < 2 ^ (prefixWord ++ tailWord_802617).sum := by decide
  have hdescent : baseEnd_802617 < baseStart_802617 := by decide
  rcases family_descends (prefixWord ++ tailWord_802617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802667 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 9]
def baseStart_802667 : Nat := 118140960795 + 802667 * 2 ^ 59
def prefixEnd_802667 : Nat := 4983230072969 + 3 ^ 40 * 802667 * 2
def baseEnd_802667 : Nat := 183179545112229464609381

theorem tailTrace_802667 : CollatzResearch.WordTrace tailWord_802667 prefixEnd_802667 183179545112229464609381 := by
  unfold tailWord_802667
  simp only [CollatzResearch.WordTrace]
  refine ⟨29275670583082018454846255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19517113722054678969897503 29275670583082018454846255)
  ·
    refine ⟨43913505874623027682269383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29275670583082018454846255 43913505874623027682269383)
    ·
      refine ⟨65870258811934541523404075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43913505874623027682269383 65870258811934541523404075)
      ·
        refine ⟨98805388217901812285106113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65870258811934541523404075 98805388217901812285106113)
        ·
          refine ⟨74104041163426359213829585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98805388217901812285106113 74104041163426359213829585)
          ·
            refine ⟨55578030872569769410372189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74104041163426359213829585 55578030872569769410372189)
            ·
              refine ⟨20841761577213663528889571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55578030872569769410372189 20841761577213663528889571)
              ·
                refine ⟨31262642365820495293334357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20841761577213663528889571 31262642365820495293334357)
                ·
                  refine ⟨183179545112229464609381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31262642365820495293334357 183179545112229464609381)
                  ·
                    rfl

theorem cell21_802667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 9].length) (baseStart_802667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802667 prefixEnd_802667 := by exact prefixLift 802667
  have htrace : WordTrace (prefixWord ++ tailWord_802667) baseStart_802667 baseEnd_802667 := by
    simpa [prefixWord, tailWord_802667, baseEnd_802667] using wordTrace_append hprefix tailTrace_802667
  have hstable : (prefixWord ++ tailWord_802667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802667).length < 2 ^ (prefixWord ++ tailWord_802667).sum := by decide
  have hdescent : baseEnd_802667 < baseStart_802667 := by decide
  rcases family_descends (prefixWord ++ tailWord_802667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802670 : List Nat := [4, 1, 2, 3, 1, 2, 8]
def baseStart_802670 : Nat := 118140960795 + 802670 * 2 ^ 59
def prefixEnd_802670 : Nat := 4983230072969 + 3 ^ 40 * 802670 * 2
def baseEnd_802670 : Nat := 20353358861455791784375

theorem tailTrace_802670 : CollatzResearch.WordTrace tailWord_802670 prefixEnd_802670 20353358861455791784375 := by
  unfold tailWord_802670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3659472500258893745900683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19517186668047433311470309 3659472500258893745900683)
  ·
    refine ⟨5489208750388340618851025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3659472500258893745900683 5489208750388340618851025)
    ·
      refine ⟨4116906562791255464138269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5489208750388340618851025 4116906562791255464138269)
      ·
        refine ⟨1543839961046720799051851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4116906562791255464138269 1543839961046720799051851)
        ·
          refine ⟨2315759941570081198577777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1543839961046720799051851 2315759941570081198577777)
          ·
            refine ⟨1736819956177560898933333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2315759941570081198577777 1736819956177560898933333)
            ·
              refine ⟨20353358861455791784375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1736819956177560898933333 20353358861455791784375)
              ·
                rfl

theorem cell21_802670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 8].length) (baseStart_802670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802670 prefixEnd_802670 := by exact prefixLift 802670
  have htrace : WordTrace (prefixWord ++ tailWord_802670) baseStart_802670 baseEnd_802670 := by
    simpa [prefixWord, tailWord_802670, baseEnd_802670] using wordTrace_append hprefix tailTrace_802670
  have hstable : (prefixWord ++ tailWord_802670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802670).length < 2 ^ (prefixWord ++ tailWord_802670).sum := by decide
  have hdescent : baseEnd_802670 < baseStart_802670 := by decide
  rcases family_descends (prefixWord ++ tailWord_802670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802710 : List Nat := [5, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_802710 : Nat := 118140960795 + 802710 * 2 ^ 59
def prefixEnd_802710 : Nat := 4983230072969 + 3 ^ 40 * 802710 * 2
def baseEnd_802710 : Nat := 183189358298070945392627

theorem tailTrace_802710 : CollatzResearch.WordTrace tailWord_802710 prefixEnd_802710 183189358298070945392627 := by
  unfold tailWord_802710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1829827432620389799916349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19518159281284157865774389 1829827432620389799916349)
  ·
    refine ⟨686185287232646174968631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1829827432620389799916349 686185287232646174968631)
    ·
      refine ⟨1029277930848969262452947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 686185287232646174968631 1029277930848969262452947)
      ·
        refine ⟨1543916896273453893679421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1029277930848969262452947 1543916896273453893679421)
        ·
          refine ⟨578968836102545210129783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1543916896273453893679421 578968836102545210129783)
          ·
            refine ⟨868453254153817815194675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578968836102545210129783 868453254153817815194675)
            ·
              refine ⟨1302679881230726722792013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868453254153817815194675 1302679881230726722792013)
              ·
                refine ⟨488504955461522521047005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1302679881230726722792013 488504955461522521047005)
                ·
                  refine ⟨183189358298070945392627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488504955461522521047005 183189358298070945392627)
                  ·
                    rfl

theorem cell21_802710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_802710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802710 prefixEnd_802710 := by exact prefixLift 802710
  have htrace : WordTrace (prefixWord ++ tailWord_802710) baseStart_802710 baseEnd_802710 := by
    simpa [prefixWord, tailWord_802710, baseEnd_802710] using wordTrace_append hprefix tailTrace_802710
  have hstable : (prefixWord ++ tailWord_802710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802710).length < 2 ^ (prefixWord ++ tailWord_802710).sum := by decide
  have hdescent : baseEnd_802710 < baseStart_802710 := by decide
  rcases family_descends (prefixWord ++ tailWord_802710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802749 : List Nat := [1, 4, 1, 2, 3, 3, 2, 1, 4]
def baseStart_802749 : Nat := 118140960795 + 802749 * 2 ^ 59
def prefixEnd_802749 : Nat := 4983230072969 + 3 ^ 40 * 802749 * 2
def baseEnd_802749 : Nat := 183198258629415544242547

theorem tailTrace_802749 : CollatzResearch.WordTrace tailWord_802749 prefixEnd_802749 183198258629415544242547 := by
  unfold tailWord_802749
  simp only [CollatzResearch.WordTrace]
  refine ⟨29278661368784946459331301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19519107579189964306220867 29278661368784946459331301)
  ·
    refine ⟨5489749006647177461124619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29278661368784946459331301 5489749006647177461124619)
    ·
      refine ⟨8234623509970766191686929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5489749006647177461124619 8234623509970766191686929)
      ·
        refine ⟨6175967632478074643765197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8234623509970766191686929 6175967632478074643765197)
        ·
          refine ⟨2315987862179277991411949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6175967632478074643765197 2315987862179277991411949)
          ·
            refine ⟨868495448317229246779481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2315987862179277991411949 868495448317229246779481)
            ·
              refine ⟨651371586237921935084611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 868495448317229246779481 651371586237921935084611)
              ·
                refine ⟨977057379356882902626917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 651371586237921935084611 977057379356882902626917)
                ·
                  refine ⟨183198258629415544242547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 977057379356882902626917 183198258629415544242547)
                  ·
                    rfl

theorem cell21_802749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_802749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802749 prefixEnd_802749 := by exact prefixLift 802749
  have htrace : WordTrace (prefixWord ++ tailWord_802749) baseStart_802749 baseEnd_802749 := by
    simpa [prefixWord, tailWord_802749, baseEnd_802749] using wordTrace_append hprefix tailTrace_802749
  have hstable : (prefixWord ++ tailWord_802749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802749).length < 2 ^ (prefixWord ++ tailWord_802749).sum := by decide
  have hdescent : baseEnd_802749 < baseStart_802749 := by decide
  rcases family_descends (prefixWord ++ tailWord_802749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802780 : List Nat := [2, 2, 6, 1, 2, 8]
def baseStart_802780 : Nat := 118140960795 + 802780 * 2 ^ 59
def prefixEnd_802780 : Nat := 4983230072969 + 3 ^ 40 * 802780 * 2
def baseEnd_802780 : Nat := 6785382713028384415771

theorem tailTrace_802780 : CollatzResearch.WordTrace tailWord_802780 prefixEnd_802780 6785382713028384415771 := by
  unfold tailWord_802780
  simp only [CollatzResearch.WordTrace]
  refine ⟨14639896015836319376854897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19519861354448425835806529 14639896015836319376854897)
  ·
    refine ⟨10979922011877239532641173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14639896015836319376854897 10979922011877239532641173)
    ·
      refine ⟨514683844306745603092555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10979922011877239532641173 514683844306745603092555)
      ·
        refine ⟨772025766460118404638833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514683844306745603092555 772025766460118404638833)
        ·
          refine ⟨579019324845088803479125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 772025766460118404638833 579019324845088803479125)
          ·
            refine ⟨6785382713028384415771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 579019324845088803479125 6785382713028384415771)
            ·
              rfl

theorem cell21_802780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 8].length) (baseStart_802780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802780 prefixEnd_802780 := by exact prefixLift 802780
  have htrace : WordTrace (prefixWord ++ tailWord_802780) baseStart_802780 baseEnd_802780 := by
    simpa [prefixWord, tailWord_802780, baseEnd_802780] using wordTrace_append hprefix tailTrace_802780
  have hstable : (prefixWord ++ tailWord_802780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802780).length < 2 ^ (prefixWord ++ tailWord_802780).sum := by decide
  have hdescent : baseEnd_802780 < baseStart_802780 := by decide
  rcases family_descends (prefixWord ++ tailWord_802780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802853 : List Nat := [1, 3, 1, 2, 2, 3, 2, 4, 3]
def baseStart_802853 : Nat := 118140960795 + 802853 * 2 ^ 59
def prefixEnd_802853 : Nat := 4983230072969 + 3 ^ 40 * 802853 * 2
def baseEnd_802853 : Nat := 183221992846334474509001

theorem tailTrace_802853 : CollatzResearch.WordTrace tailWord_802853 prefixEnd_802853 183221992846334474509001 := by
  unfold tailWord_802853
  simp only [CollatzResearch.WordTrace]
  refine ⟨29282454560408172221117213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19521636373605448147411475 29282454560408172221117213)
  ·
    refine ⟨10980920460153064582918955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29282454560408172221117213 10980920460153064582918955)
    ·
      refine ⟨16471380690229596874378433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10980920460153064582918955 16471380690229596874378433)
      ·
        refine ⟨12353535517672197655783825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16471380690229596874378433 12353535517672197655783825)
        ·
          refine ⟨9265151638254148241837869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12353535517672197655783825 9265151638254148241837869)
          ·
            refine ⟨3474431864345305590689201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9265151638254148241837869 3474431864345305590689201)
            ·
              refine ⟨2605823898258979193016901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3474431864345305590689201 2605823898258979193016901)
              ·
                refine ⟨488591980923558598690669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2605823898258979193016901 488591980923558598690669)
                ·
                  refine ⟨183221992846334474509001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488591980923558598690669 183221992846334474509001)
                  ·
                    rfl

theorem cell21_802853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_802853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802853 prefixEnd_802853 := by exact prefixLift 802853
  have htrace : WordTrace (prefixWord ++ tailWord_802853) baseStart_802853 baseEnd_802853 := by
    simpa [prefixWord, tailWord_802853, baseEnd_802853] using wordTrace_append hprefix tailTrace_802853
  have hstable : (prefixWord ++ tailWord_802853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802853).length < 2 ^ (prefixWord ++ tailWord_802853).sum := by decide
  have hdescent : baseEnd_802853 < baseStart_802853 := by decide
  rcases family_descends (prefixWord ++ tailWord_802853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802898 : List Nat := [3, 2, 2, 1, 4, 2, 7]
def baseStart_802898 : Nat := 118140960795 + 802898 * 2 ^ 59
def prefixEnd_802898 : Nat := 4983230072969 + 3 ^ 40 * 802898 * 2
def baseEnd_802898 : Nat := 20359140273269377362101

theorem tailTrace_802898 : CollatzResearch.WordTrace tailWord_802898 prefixEnd_802898 20359140273269377362101 := by
  unfold tailWord_802898
  simp only [CollatzResearch.WordTrace]
  refine ⟨7321023961311286226626337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19522730563496763271003565 7321023961311286226626337)
  ·
    refine ⟨5490767970983464669969753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7321023961311286226626337 5490767970983464669969753)
    ·
      refine ⟨4118075978237598502477315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5490767970983464669969753 4118075978237598502477315)
      ·
        refine ⟨6177113967356397753715973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4118075978237598502477315 6177113967356397753715973)
        ·
          refine ⟨1158208868879324578821745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6177113967356397753715973 1158208868879324578821745)
          ·
            refine ⟨868656651659493434116309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1158208868879324578821745 868656651659493434116309)
            ·
              refine ⟨20359140273269377362101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 868656651659493434116309 20359140273269377362101)
              ·
                rfl

theorem cell21_802898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 7].length) (baseStart_802898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802898 prefixEnd_802898 := by exact prefixLift 802898
  have htrace : WordTrace (prefixWord ++ tailWord_802898) baseStart_802898 baseEnd_802898 := by
    simpa [prefixWord, tailWord_802898, baseEnd_802898] using wordTrace_append hprefix tailTrace_802898
  have hstable : (prefixWord ++ tailWord_802898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802898).length < 2 ^ (prefixWord ++ tailWord_802898).sum := by decide
  have hdescent : baseEnd_802898 < baseStart_802898 := by decide
  rcases family_descends (prefixWord ++ tailWord_802898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802912 : List Nat := [2, 1, 1, 3, 2, 3, 3, 1, 5]
def baseStart_802912 : Nat := 118140960795 + 802912 * 2 ^ 59
def prefixEnd_802912 : Nat := 4983230072969 + 3 ^ 40 * 802912 * 2
def baseEnd_802912 : Nat := 183235457450163483025547

theorem tailTrace_802912 : CollatzResearch.WordTrace tailWord_802912 prefixEnd_802912 183235457450163483025547 := by
  unfold tailWord_802912
  simp only [CollatzResearch.WordTrace]
  refine ⟨14642303233597212648757495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19523070978129616865009993 14642303233597212648757495)
  ·
    refine ⟨21963454850395818973136243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14642303233597212648757495 21963454850395818973136243)
    ·
      refine ⟨32945182275593728459704365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21963454850395818973136243 32945182275593728459704365)
      ·
        refine ⟨12354443353347648172389137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32945182275593728459704365 12354443353347648172389137)
        ·
          refine ⟨9265832515010736129291853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12354443353347648172389137 9265832515010736129291853)
          ·
            refine ⟨3474687193129026048484445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9265832515010736129291853 3474687193129026048484445)
            ·
              refine ⟨1303007697423384768181667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3474687193129026048484445 1303007697423384768181667)
              ·
                refine ⟨1954511546135077152272501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303007697423384768181667 1954511546135077152272501)
                ·
                  refine ⟨183235457450163483025547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1954511546135077152272501 183235457450163483025547)
                  ·
                    rfl

theorem cell21_802912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 5].length) (baseStart_802912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802912 prefixEnd_802912 := by exact prefixLift 802912
  have htrace : WordTrace (prefixWord ++ tailWord_802912) baseStart_802912 baseEnd_802912 := by
    simpa [prefixWord, tailWord_802912, baseEnd_802912] using wordTrace_append hprefix tailTrace_802912
  have hstable : (prefixWord ++ tailWord_802912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802912).length < 2 ^ (prefixWord ++ tailWord_802912).sum := by decide
  have hdescent : baseEnd_802912 < baseStart_802912 := by decide
  rcases family_descends (prefixWord ++ tailWord_802912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802966 : List Nat := [5, 3, 2, 1, 1, 2, 1, 6]
def baseStart_802966 : Nat := 118140960795 + 802966 * 2 ^ 59
def prefixEnd_802966 : Nat := 4983230072969 + 3 ^ 40 * 802966 * 2
def baseEnd_802966 : Nat := 61082593661957129708479

theorem tailTrace_802966 : CollatzResearch.WordTrace tailWord_802966 prefixEnd_802966 61082593661957129708479 := by
  unfold tailWord_802966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1830411000562424532498797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19524384005999195013320501 1830411000562424532498797)
  ·
    refine ⟨686404125210909199687049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1830411000562424532498797 686404125210909199687049)
    ·
      refine ⟨514803093908181899765287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 686404125210909199687049 514803093908181899765287)
      ·
        refine ⟨772204640862272849647931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514803093908181899765287 772204640862272849647931)
        ·
          refine ⟨1158306961293409274471897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 772204640862272849647931 1158306961293409274471897)
          ·
            refine ⟨868730220970056955853923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1158306961293409274471897 868730220970056955853923)
            ·
              refine ⟨1303095331455085433780885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868730220970056955853923 1303095331455085433780885)
              ·
                refine ⟨61082593661957129708479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1303095331455085433780885 61082593661957129708479)
                ·
                  rfl

theorem cell21_802966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_802966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_802966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_802966 prefixEnd_802966 := by exact prefixLift 802966
  have htrace : WordTrace (prefixWord ++ tailWord_802966) baseStart_802966 baseEnd_802966 := by
    simpa [prefixWord, tailWord_802966, baseEnd_802966] using wordTrace_append hprefix tailTrace_802966
  have hstable : (prefixWord ++ tailWord_802966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802966).length < 2 ^ (prefixWord ++ tailWord_802966).sum := by decide
  have hdescent : baseEnd_802966 < baseStart_802966 := by decide
  rcases family_descends (prefixWord ++ tailWord_802966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803042 : List Nat := [3, 3, 4, 1, 2, 1, 2, 5]
def baseStart_803042 : Nat := 118140960795 + 803042 * 2 ^ 59
def prefixEnd_803042 : Nat := 4983230072969 + 3 ^ 40 * 803042 * 2
def baseEnd_803042 : Nat := 61088375073770715286205

theorem tailTrace_803042 : CollatzResearch.WordTrace tailWord_803042 prefixEnd_803042 61088375073770715286205 := by
  unfold tailWord_803042
  simp only [CollatzResearch.WordTrace]
  refine ⟨7322336989180864374936845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19526231971148971666498253 7322336989180864374936845)
  ·
    refine ⟨2745876370942824140601317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7322336989180864374936845 2745876370942824140601317)
    ·
      refine ⟨514851819551779526362747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2745876370942824140601317 514851819551779526362747)
      ·
        refine ⟨772277729327669289544121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514851819551779526362747 772277729327669289544121)
        ·
          refine ⟨579208296995751967158091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 772277729327669289544121 579208296995751967158091)
          ·
            refine ⟨868812445493627950737137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579208296995751967158091 868812445493627950737137)
            ·
              refine ⟨651609334120220963052853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 868812445493627950737137 651609334120220963052853)
              ·
                refine ⟨61088375073770715286205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 651609334120220963052853 61088375073770715286205)
                ·
                  rfl

theorem cell21_803042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_803042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_803042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_803042 prefixEnd_803042 := by exact prefixLift 803042
  have htrace : WordTrace (prefixWord ++ tailWord_803042) baseStart_803042 baseEnd_803042 := by
    simpa [prefixWord, tailWord_803042, baseEnd_803042] using wordTrace_append hprefix tailTrace_803042
  have hstable : (prefixWord ++ tailWord_803042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803042).length < 2 ^ (prefixWord ++ tailWord_803042).sum := by decide
  have hdescent : baseEnd_803042 < baseStart_803042 := by decide
  rcases family_descends (prefixWord ++ tailWord_803042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803095 : List Nat := [1, 1, 3, 4, 1, 3, 1, 3, 4]
def baseStart_803095 : Nat := 118140960795 + 803095 * 2 ^ 59
def prefixEnd_803095 : Nat := 4983230072969 + 3 ^ 40 * 803095 * 2
def baseEnd_803095 : Nat := 183277220543395831475173

theorem tailTrace_803095 : CollatzResearch.WordTrace tailWord_803095 prefixEnd_803095 183277220543395831475173 := by
  unfold tailWord_803095
  simp only [CollatzResearch.WordTrace]
  refine ⟨29291281025531447551426739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19527520683687631700951159 29291281025531447551426739)
  ·
    refine ⟨43936921538297171327140109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29291281025531447551426739 43936921538297171327140109)
    ·
      refine ⟨16476345576861439247677541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43936921538297171327140109 16476345576861439247677541)
      ·
        refine ⟨3089314795661519858939539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16476345576861439247677541 3089314795661519858939539)
        ·
          refine ⟨4633972193492279788409309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3089314795661519858939539 4633972193492279788409309)
          ·
            refine ⟨1737739572559604920653491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4633972193492279788409309 1737739572559604920653491)
            ·
              refine ⟨2606609358839407380980237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1737739572559604920653491 2606609358839407380980237)
              ·
                refine ⟨977478509564777767867589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2606609358839407380980237 977478509564777767867589)
                ·
                  refine ⟨183277220543395831475173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 977478509564777767867589 183277220543395831475173)
                  ·
                    rfl

theorem cell21_803095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 4].length) (baseStart_803095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_803095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_803095 prefixEnd_803095 := by exact prefixLift 803095
  have htrace : WordTrace (prefixWord ++ tailWord_803095) baseStart_803095 baseEnd_803095 := by
    simpa [prefixWord, tailWord_803095, baseEnd_803095] using wordTrace_append hprefix tailTrace_803095
  have hstable : (prefixWord ++ tailWord_803095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803095).length < 2 ^ (prefixWord ++ tailWord_803095).sum := by decide
  have hdescent : baseEnd_803095 < baseStart_803095 := by decide
  rcases family_descends (prefixWord ++ tailWord_803095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803261 : List Nat := [1, 4, 1, 2, 2, 3, 2, 6]
def baseStart_803261 : Nat := 118140960795 + 803261 * 2 ^ 59
def prefixEnd_803261 : Nat := 4983230072969 + 3 ^ 40 * 803261 * 2
def baseEnd_803261 : Nat := 61105034668338810569389

theorem tailTrace_803261 : CollatzResearch.WordTrace tailWord_803261 prefixEnd_803261 61105034668338810569389 := by
  unfold tailWord_803261
  simp only [CollatzResearch.WordTrace]
  refine ⟨29297335542930057901969637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19531557028620038601313091 29297335542930057901969637)
  ·
    refine ⟨5493250414299385856619307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29297335542930057901969637 5493250414299385856619307)
    ·
      refine ⟨8239875621449078784928961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5493250414299385856619307 8239875621449078784928961)
      ·
        refine ⟨6179906716086809088696721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8239875621449078784928961 6179906716086809088696721)
        ·
          refine ⟨4634930037065106816522541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6179906716086809088696721 4634930037065106816522541)
          ·
            refine ⟨1738098763899415056195953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4634930037065106816522541 1738098763899415056195953)
            ·
              refine ⟨1303574072924561292146965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1738098763899415056195953 1303574072924561292146965)
              ·
                refine ⟨61105034668338810569389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1303574072924561292146965 61105034668338810569389)
                ·
                  rfl

theorem cell21_803261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 6].length) (baseStart_803261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_803261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_803261 prefixEnd_803261 := by exact prefixLift 803261
  have htrace : WordTrace (prefixWord ++ tailWord_803261) baseStart_803261 baseEnd_803261 := by
    simpa [prefixWord, tailWord_803261, baseEnd_803261] using wordTrace_append hprefix tailTrace_803261
  have hstable : (prefixWord ++ tailWord_803261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803261).length < 2 ^ (prefixWord ++ tailWord_803261).sum := by decide
  have hdescent : baseEnd_803261 < baseStart_803261 := by decide
  rcases family_descends (prefixWord ++ tailWord_803261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803368 : List Nat := [2, 1, 5, 2, 1, 1, 1, 3, 5]
def baseStart_803368 : Nat := 118140960795 + 803368 * 2 ^ 59
def prefixEnd_803368 : Nat := 4983230072969 + 3 ^ 40 * 803368 * 2
def baseEnd_803368 : Nat := 183339522862808023424615

theorem tailTrace_803368 : CollatzResearch.WordTrace tailWord_803368 prefixEnd_803368 183339522862808023424615 := by
  unfold tailWord_803368
  simp only [CollatzResearch.WordTrace]
  refine ⟨14650619076771207588057379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19534158769028276784076505 14650619076771207588057379)
  ·
    refine ⟨21975928615156811382086069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14650619076771207588057379 21975928615156811382086069)
    ·
      refine ⟨2060243307670951067070569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21975928615156811382086069 2060243307670951067070569)
      ·
        refine ⟨1545182480753213300302927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2060243307670951067070569 1545182480753213300302927)
        ·
          refine ⟨2317773721129819950454391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1545182480753213300302927 2317773721129819950454391)
          ·
            refine ⟨3476660581694729925681587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2317773721129819950454391 3476660581694729925681587)
            ·
              refine ⟨5214990872542094888522381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3476660581694729925681587 5214990872542094888522381)
              ·
                refine ⟨1955621577203285583195893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5214990872542094888522381 1955621577203285583195893)
                ·
                  refine ⟨183339522862808023424615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1955621577203285583195893 183339522862808023424615)
                  ·
                    rfl

theorem cell21_803368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_803368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_803368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_803368 prefixEnd_803368 := by exact prefixLift 803368
  have htrace : WordTrace (prefixWord ++ tailWord_803368) baseStart_803368 baseEnd_803368 := by
    simpa [prefixWord, tailWord_803368, baseEnd_803368] using wordTrace_append hprefix tailTrace_803368
  have hstable : (prefixWord ++ tailWord_803368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803368).length < 2 ^ (prefixWord ++ tailWord_803368).sum := by decide
  have hdescent : baseEnd_803368 < baseStart_803368 := by decide
  rcases family_descends (prefixWord ++ tailWord_803368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803503 : List Nat := [1, 1, 2, 1, 2, 6, 1, 2, 5]
def baseStart_803503 : Nat := 118140960795 + 803503 * 2 ^ 59
def prefixEnd_803503 : Nat := 4983230072969 + 3 ^ 40 * 803503 * 2
def baseEnd_803503 : Nat := 183370331702077788674339

theorem tailTrace_803503 : CollatzResearch.WordTrace tailWord_803503 prefixEnd_803503 183370331702077788674339 := by
  unfold tailWord_803503
  simp only [CollatzResearch.WordTrace]
  refine ⟨29306162008053333232279163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19537441338702222154852775 29306162008053333232279163)
  ·
    refine ⟨43959243012079999848418745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29306162008053333232279163 43959243012079999848418745)
    ·
      refine ⟨32969432259059999886314059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43959243012079999848418745 32969432259059999886314059)
      ·
        refine ⟨49454148388589999829471089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32969432259059999886314059 49454148388589999829471089)
        ·
          refine ⟨37090611291442499872103317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49454148388589999829471089 37090611291442499872103317)
          ·
            refine ⟨1738622404286367181504843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37090611291442499872103317 1738622404286367181504843)
            ·
              refine ⟨2607933606429550772257265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738622404286367181504843 2607933606429550772257265)
              ·
                refine ⟨1955950204822163079192949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2607933606429550772257265 1955950204822163079192949)
                ·
                  refine ⟨183370331702077788674339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1955950204822163079192949 183370331702077788674339)
                  ·
                    rfl

theorem cell21_803503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 5].length) (baseStart_803503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_803503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_803503 prefixEnd_803503 := by exact prefixLift 803503
  have htrace : WordTrace (prefixWord ++ tailWord_803503) baseStart_803503 baseEnd_803503 := by
    simpa [prefixWord, tailWord_803503, baseEnd_803503] using wordTrace_append hprefix tailTrace_803503
  have hstable : (prefixWord ++ tailWord_803503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803503).length < 2 ^ (prefixWord ++ tailWord_803503).sum := by decide
  have hdescent : baseEnd_803503 < baseStart_803503 := by decide
  rcases family_descends (prefixWord ++ tailWord_803503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803520 : List Nat := [2, 1, 1, 2, 4, 2, 1, 5, 3]
def baseStart_803520 : Nat := 118140960795 + 803520 * 2 ^ 59
def prefixEnd_803520 : Nat := 4983230072969 + 3 ^ 40 * 803520 * 2
def baseEnd_803520 : Nat := 183374211333689536890971

theorem tailTrace_803520 : CollatzResearch.WordTrace tailWord_803520 prefixEnd_803520 183374211333689536890971 := by
  unfold tailWord_803520
  simp only [CollatzResearch.WordTrace]
  refine ⟨14653391024495872567824007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19537854699327830090432009 14653391024495872567824007)
  ·
    refine ⟨21980086536743808851736011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14653391024495872567824007 21980086536743808851736011)
    ·
      refine ⟨32970129805115713277604017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21980086536743808851736011 32970129805115713277604017)
      ·
        refine ⟨24727597353836784958203013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32970129805115713277604017 24727597353836784958203013)
        ·
          refine ⟨4636424503844397179663065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24727597353836784958203013 4636424503844397179663065)
          ·
            refine ⟨3477318377883297884747299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4636424503844397179663065 3477318377883297884747299)
            ·
              refine ⟨5215977566824946827120949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3477318377883297884747299 5215977566824946827120949)
              ·
                refine ⟨488997896889838765042589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5215977566824946827120949 488997896889838765042589)
                ·
                  refine ⟨183374211333689536890971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488997896889838765042589 183374211333689536890971)
                  ·
                    rfl

theorem cell21_803520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 3].length) (baseStart_803520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_803520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_803520 prefixEnd_803520 := by exact prefixLift 803520
  have htrace : WordTrace (prefixWord ++ tailWord_803520) baseStart_803520 baseEnd_803520 := by
    simpa [prefixWord, tailWord_803520, baseEnd_803520] using wordTrace_append hprefix tailTrace_803520
  have hstable : (prefixWord ++ tailWord_803520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803520).length < 2 ^ (prefixWord ++ tailWord_803520).sum := by decide
  have hdescent : baseEnd_803520 < baseStart_803520 := by decide
  rcases family_descends (prefixWord ++ tailWord_803520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803526 : List Nat := [6, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_803526 : Nat := 118140960795 + 803526 * 2 ^ 59
def prefixEnd_803526 : Nat := 4983230072969 + 3 ^ 40 * 803526 * 2
def baseEnd_803526 : Nat := 183375580615434859790959

theorem tailTrace_803526 : CollatzResearch.WordTrace tailWord_803526 prefixEnd_803526 183375580615434859790959 := by
  unfold tailWord_803526
  simp only [CollatzResearch.WordTrace]
  refine ⟨915843777717812755011451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19538000591313338773577621 915843777717812755011451)
  ·
    refine ⟨1373765666576719132517177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 915843777717812755011451 1373765666576719132517177)
    ·
      refine ⟨1030324249932539349387883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1373765666576719132517177 1030324249932539349387883)
      ·
        refine ⟨1545486374898809024081825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1030324249932539349387883 1545486374898809024081825)
        ·
          refine ⟨1159114781174106768061369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1545486374898809024081825 1159114781174106768061369)
          ·
            refine ⟨869336085880580076046027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1159114781174106768061369 869336085880580076046027)
            ·
              refine ⟨1304004128820870114069041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869336085880580076046027 1304004128820870114069041)
              ·
                refine ⟨978003096615652585551781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1304004128820870114069041 978003096615652585551781)
                ·
                  refine ⟨183375580615434859790959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 978003096615652585551781 183375580615434859790959)
                  ·
                    rfl

theorem cell21_803526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_803526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_803526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_803526 prefixEnd_803526 := by exact prefixLift 803526
  have htrace : WordTrace (prefixWord ++ tailWord_803526) baseStart_803526 baseEnd_803526 := by
    simpa [prefixWord, tailWord_803526, baseEnd_803526] using wordTrace_append hprefix tailTrace_803526
  have hstable : (prefixWord ++ tailWord_803526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803526).length < 2 ^ (prefixWord ++ tailWord_803526).sum := by decide
  have hdescent : baseEnd_803526 < baseStart_803526 := by decide
  rcases family_descends (prefixWord ++ tailWord_803526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803534 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_803534 : Nat := 118140960795 + 803534 * 2 ^ 59
def prefixEnd_803534 : Nat := 4983230072969 + 3 ^ 40 * 803534 * 2
def baseEnd_803534 : Nat := 183377406324428623657609

theorem tailTrace_803534 : CollatzResearch.WordTrace tailWord_803534 prefixEnd_803534 183377406324428623657609 := by
  unfold tailWord_803534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3663411583867628190832207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19538195113960683684438437 3663411583867628190832207)
  ·
    refine ⟨5495117375801442286248311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3663411583867628190832207 5495117375801442286248311)
    ·
      refine ⟨8242676063702163429372467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5495117375801442286248311 8242676063702163429372467)
      ·
        refine ⟨12364014095553245144058701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8242676063702163429372467 12364014095553245144058701)
        ·
          refine ⟨4636505285832466929022013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12364014095553245144058701 4636505285832466929022013)
          ·
            refine ⟨1738689482187175098383255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4636505285832466929022013 1738689482187175098383255)
            ·
              refine ⟨2608034223280762647574883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738689482187175098383255 2608034223280762647574883)
              ·
                refine ⟨3912051334921143971362325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608034223280762647574883 3912051334921143971362325)
                ·
                  refine ⟨183377406324428623657609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3912051334921143971362325 183377406324428623657609)
                  ·
                    rfl

theorem cell21_803534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_803534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_803534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_803534 prefixEnd_803534 := by exact prefixLift 803534
  have htrace : WordTrace (prefixWord ++ tailWord_803534) baseStart_803534 baseEnd_803534 := by
    simpa [prefixWord, tailWord_803534, baseEnd_803534] using wordTrace_append hprefix tailTrace_803534
  have hstable : (prefixWord ++ tailWord_803534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803534).length < 2 ^ (prefixWord ++ tailWord_803534).sum := by decide
  have hdescent : baseEnd_803534 < baseStart_803534 := by decide
  rcases family_descends (prefixWord ++ tailWord_803534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803551 : List Nat := [1, 1, 2, 3, 2, 4, 3, 1, 4]
def baseStart_803551 : Nat := 118140960795 + 803551 * 2 ^ 59
def prefixEnd_803551 : Nat := 4983230072969 + 3 ^ 40 * 803551 * 2
def baseEnd_803551 : Nat := 183381285956040371874241

theorem tailTrace_803551 : CollatzResearch.WordTrace tailWord_803551 prefixEnd_803551 183381285956040371874241 := by
  unfold tailWord_803551
  simp only [CollatzResearch.WordTrace]
  refine ⟨29307912711879437430026507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19538608474586291620017671 29307912711879437430026507)
  ·
    refine ⟨43961869067819156145039761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29307912711879437430026507 43961869067819156145039761)
    ·
      refine ⟨32971401800864367108779821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43961869067819156145039761 32971401800864367108779821)
      ·
        refine ⟨12364275675324137665792433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32971401800864367108779821 12364275675324137665792433)
        ·
          refine ⟨9273206756493103249344325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12364275675324137665792433 9273206756493103249344325)
          ·
            refine ⟨1738726266842456859252061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9273206756493103249344325 1738726266842456859252061)
            ·
              refine ⟨652022350065921322219523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1738726266842456859252061 652022350065921322219523)
              ·
                refine ⟨978033525098881983329285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 652022350065921322219523 978033525098881983329285)
                ·
                  refine ⟨183381285956040371874241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 978033525098881983329285 183381285956040371874241)
                  ·
                    rfl

theorem cell21_803551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 4].length) (baseStart_803551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_803551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_803551 prefixEnd_803551 := by exact prefixLift 803551
  have htrace : WordTrace (prefixWord ++ tailWord_803551) baseStart_803551 baseEnd_803551 := by
    simpa [prefixWord, tailWord_803551, baseEnd_803551] using wordTrace_append hprefix tailTrace_803551
  have hstable : (prefixWord ++ tailWord_803551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803551).length < 2 ^ (prefixWord ++ tailWord_803551).sum := by decide
  have hdescent : baseEnd_803551 < baseStart_803551 := by decide
  rcases family_descends (prefixWord ++ tailWord_803551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803593 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 6]
def baseStart_803593 : Nat := 118140960795 + 803593 * 2 ^ 59
def prefixEnd_803593 : Nat := 4983230072969 + 3 ^ 40 * 803593 * 2
def baseEnd_803593 : Nat := 183390870928257632174155

theorem tailTrace_803593 : CollatzResearch.WordTrace tailWord_803593 prefixEnd_803593 183390870928257632174155 := by
  unfold tailWord_803593
  simp only [CollatzResearch.WordTrace]
  refine ⟨29309444577727278603055433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19539629718484852402036955 29309444577727278603055433)
  ·
    refine ⟨21982083433295458952291575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29309444577727278603055433 21982083433295458952291575)
    ·
      refine ⟨32973125149943188428437363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21982083433295458952291575 32973125149943188428437363)
      ·
        refine ⟨49459687724914782642656045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32973125149943188428437363 49459687724914782642656045)
        ·
          refine ⟨18547382896843043490996017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49459687724914782642656045 18547382896843043490996017)
          ·
            refine ⟨13910537172632282618247013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18547382896843043490996017 13910537172632282618247013)
            ·
              refine ⟨2608225719868552990921315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13910537172632282618247013 2608225719868552990921315)
              ·
                refine ⟨3912338579802829486381973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608225719868552990921315 3912338579802829486381973)
                ·
                  refine ⟨183390870928257632174155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3912338579802829486381973 183390870928257632174155)
                  ·
                    rfl

theorem cell21_803593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_803593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_803593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_803593 prefixEnd_803593 := by exact prefixLift 803593
  have htrace : WordTrace (prefixWord ++ tailWord_803593) baseStart_803593 baseEnd_803593 := by
    simpa [prefixWord, tailWord_803593, baseEnd_803593] using wordTrace_append hprefix tailTrace_803593
  have hstable : (prefixWord ++ tailWord_803593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803593).length < 2 ^ (prefixWord ++ tailWord_803593).sum := by decide
  have hdescent : baseEnd_803593 < baseStart_803593 := by decide
  rcases family_descends (prefixWord ++ tailWord_803593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803602 : List Nat := [3, 2, 4, 1, 3, 1, 2, 1, 4]
def baseStart_803602 : Nat := 118140960795 + 803602 * 2 ^ 59
def prefixEnd_803602 : Nat := 4983230072969 + 3 ^ 40 * 803602 * 2
def baseEnd_803602 : Nat := 183392924850875616524137

theorem tailTrace_803602 : CollatzResearch.WordTrace tailWord_803602 prefixEnd_803602 183392924850875616524137 := by
  unfold tailWord_803602
  simp only [CollatzResearch.WordTrace]
  refine ⟨7327443208673668285033265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19539848556463115426755373 7327443208673668285033265)
  ·
    refine ⟨5495582406505251213774949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7327443208673668285033265 5495582406505251213774949)
    ·
      refine ⟨1030421701219734602582803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5495582406505251213774949 1030421701219734602582803)
      ·
        refine ⟨1545632551829601903874205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1030421701219734602582803 1545632551829601903874205)
        ·
          refine ⟨579612206936100713952827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1545632551829601903874205 579612206936100713952827)
          ·
            refine ⟨869418310404151070929241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579612206936100713952827 869418310404151070929241)
            ·
              refine ⟨652063732803113303196931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 869418310404151070929241 652063732803113303196931)
              ·
                refine ⟨978095599204669954795397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 652063732803113303196931 978095599204669954795397)
                ·
                  refine ⟨183392924850875616524137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 978095599204669954795397 183392924850875616524137)
                  ·
                    rfl

theorem cell21_803602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_803602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_803602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_803602 prefixEnd_803602 := by exact prefixLift 803602
  have htrace : WordTrace (prefixWord ++ tailWord_803602) baseStart_803602 baseEnd_803602 := by
    simpa [prefixWord, tailWord_803602, baseEnd_803602] using wordTrace_append hprefix tailTrace_803602
  have hstable : (prefixWord ++ tailWord_803602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803602).length < 2 ^ (prefixWord ++ tailWord_803602).sum := by decide
  have hdescent : baseEnd_803602 < baseStart_803602 := by decide
  rcases family_descends (prefixWord ++ tailWord_803602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803610 : List Nat := [3, 1, 1, 3, 2, 1, 3, 3, 4]
def baseStart_803610 : Nat := 118140960795 + 803610 * 2 ^ 59
def prefixEnd_803610 : Nat := 4983230072969 + 3 ^ 40 * 803610 * 2
def baseEnd_803610 : Nat := 183394750559869380390787

theorem tailTrace_803610 : CollatzResearch.WordTrace tailWord_803610 prefixEnd_803610 183394750559869380390787 := by
  unfold tailWord_803610
  simp only [CollatzResearch.WordTrace]
  refine ⟨7327516154666422626606071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19540043079110460337616189 7327516154666422626606071)
  ·
    refine ⟨10991274231999633939909107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7327516154666422626606071 10991274231999633939909107)
    ·
      refine ⟨16486911347999450909863661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10991274231999633939909107 16486911347999450909863661)
      ·
        refine ⟨6182591755499794091198873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16486911347999450909863661 6182591755499794091198873)
        ·
          refine ⟨4636943816624845568399155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6182591755499794091198873 4636943816624845568399155)
          ·
            refine ⟨6955415724937268352598733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4636943816624845568399155 6955415724937268352598733)
            ·
              refine ⟨2608280896851475632224525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6955415724937268352598733 2608280896851475632224525)
              ·
                refine ⟨978105336319303362084197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2608280896851475632224525 978105336319303362084197)
                ·
                  refine ⟨183394750559869380390787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 978105336319303362084197 183394750559869380390787)
                  ·
                    rfl

theorem cell21_803610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_803610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_803610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_803610 prefixEnd_803610 := by exact prefixLift 803610
  have htrace : WordTrace (prefixWord ++ tailWord_803610) baseStart_803610 baseEnd_803610 := by
    simpa [prefixWord, tailWord_803610, baseEnd_803610] using wordTrace_append hprefix tailTrace_803610
  have hstable : (prefixWord ++ tailWord_803610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803610).length < 2 ^ (prefixWord ++ tailWord_803610).sum := by decide
  have hdescent : baseEnd_803610 < baseStart_803610 := by decide
  rcases family_descends (prefixWord ++ tailWord_803610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803624 : List Nat := [2, 1, 5, 1, 1, 1, 1, 9]
def baseStart_803624 : Nat := 118140960795 + 803624 * 2 ^ 59
def prefixEnd_803624 : Nat := 4983230072969 + 3 ^ 40 * 803624 * 2
def baseEnd_803624 : Nat := 61132648516869489052475

theorem tailTrace_803624 : CollatzResearch.WordTrace tailWord_803624 prefixEnd_803624 61132648516869489052475 := by
  unfold tailWord_803624
  simp only [CollatzResearch.WordTrace]
  refine ⟨14655287620307485448716963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19540383493743313931622617 14655287620307485448716963)
  ·
    refine ⟨21982931430461228173075445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14655287620307485448716963 21982931430461228173075445)
    ·
      refine ⟨2060899821605740141225823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21982931430461228173075445 2060899821605740141225823)
      ·
        refine ⟨3091349732408610211838735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2060899821605740141225823 3091349732408610211838735)
        ·
          refine ⟨4637024598612915317758103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3091349732408610211838735 4637024598612915317758103)
          ·
            refine ⟨6955536897919372976637155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4637024598612915317758103 6955536897919372976637155)
            ·
              refine ⟨10433305346879059464955733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6955536897919372976637155 10433305346879059464955733)
              ·
                refine ⟨61132648516869489052475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10433305346879059464955733 61132648516869489052475)
                ·
                  rfl

theorem cell21_803624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 9].length) (baseStart_803624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_803624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_803624 prefixEnd_803624 := by exact prefixLift 803624
  have htrace : WordTrace (prefixWord ++ tailWord_803624) baseStart_803624 baseEnd_803624 := by
    simpa [prefixWord, tailWord_803624, baseEnd_803624] using wordTrace_append hprefix tailTrace_803624
  have hstable : (prefixWord ++ tailWord_803624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803624).length < 2 ^ (prefixWord ++ tailWord_803624).sum := by decide
  have hdescent : baseEnd_803624 < baseStart_803624 := by decide
  rcases family_descends (prefixWord ++ tailWord_803624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803765 : List Nat := [1, 3, 3, 2, 1, 1, 5, 2, 3]
def baseStart_803765 : Nat := 118140960795 + 803765 * 2 ^ 59
def prefixEnd_803765 : Nat := 4983230072969 + 3 ^ 40 * 803765 * 2
def baseEnd_803765 : Nat := 183430123671623555307137

theorem tailTrace_803765 : CollatzResearch.WordTrace tailWord_803765 prefixEnd_803765 183430123671623555307137 := by
  unfold tailWord_803765
  simp only [CollatzResearch.WordTrace]
  refine ⟨29315717933104151978316749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19543811955402767985544499 29315717933104151978316749)
  ·
    refine ⟨10993394224914056991868781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29315717933104151978316749 10993394224914056991868781)
    ·
      refine ⟨4122522834342771371950793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10993394224914056991868781 4122522834342771371950793)
      ·
        refine ⟨3091892125757078528963095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4122522834342771371950793 3091892125757078528963095)
        ·
          refine ⟨4637838188635617793444643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3091892125757078528963095 4637838188635617793444643)
          ·
            refine ⟨6956757282953426690166965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4637838188635617793444643 6956757282953426690166965)
            ·
              refine ⟨652195995276883752203153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6956757282953426690166965 652195995276883752203153)
              ·
                refine ⟨489146996457662814152365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 652195995276883752203153 489146996457662814152365)
                ·
                  refine ⟨183430123671623555307137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 489146996457662814152365 183430123671623555307137)
                  ·
                    rfl

theorem cell21_803765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_803765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_803765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_803765 prefixEnd_803765 := by exact prefixLift 803765
  have htrace : WordTrace (prefixWord ++ tailWord_803765) baseStart_803765 baseEnd_803765 := by
    simpa [prefixWord, tailWord_803765, baseEnd_803765] using wordTrace_append hprefix tailTrace_803765
  have hstable : (prefixWord ++ tailWord_803765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803765).length < 2 ^ (prefixWord ++ tailWord_803765).sum := by decide
  have hdescent : baseEnd_803765 < baseStart_803765 := by decide
  rcases family_descends (prefixWord ++ tailWord_803765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803776 : List Nat := [2, 1, 1, 2, 3, 4, 2, 6]
def baseStart_803776 : Nat := 118140960795 + 803776 * 2 ^ 59
def prefixEnd_803776 : Nat := 4983230072969 + 3 ^ 40 * 803776 * 2
def baseEnd_803776 : Nat := 61144211340496660207927

theorem tailTrace_803776 : CollatzResearch.WordTrace tailWord_803776 prefixEnd_803776 61144211340496660207927 := by
  unfold tailWord_803776
  simp only [CollatzResearch.WordTrace]
  refine ⟨14658059568032150428483591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19544079424042867237978121 14658059568032150428483591)
  ·
    refine ⟨21987089352048225642725387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14658059568032150428483591 21987089352048225642725387)
    ·
      refine ⟨32980634028072338464088081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21987089352048225642725387 32980634028072338464088081)
      ·
        refine ⟨24735475521054253848066061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32980634028072338464088081 24735475521054253848066061)
        ·
          refine ⟨9275803320395345193024773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24735475521054253848066061 9275803320395345193024773)
          ·
            refine ⟨1739213122574127223692145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9275803320395345193024773 1739213122574127223692145)
            ·
              refine ⟨1304409841930595417769109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1739213122574127223692145 1304409841930595417769109)
              ·
                refine ⟨61144211340496660207927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1304409841930595417769109 61144211340496660207927)
                ·
                  rfl

theorem cell21_803776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 6].length) (baseStart_803776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_803776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_803776 prefixEnd_803776 := by exact prefixLift 803776
  have htrace : WordTrace (prefixWord ++ tailWord_803776) baseStart_803776 baseEnd_803776 := by
    simpa [prefixWord, tailWord_803776, baseEnd_803776] using wordTrace_append hprefix tailTrace_803776
  have hstable : (prefixWord ++ tailWord_803776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803776).length < 2 ^ (prefixWord ++ tailWord_803776).sum := by decide
  have hdescent : baseEnd_803776 < baseStart_803776 := by decide
  rcases family_descends (prefixWord ++ tailWord_803776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803866 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 7]
def baseStart_803866 : Nat := 118140960795 + 803866 * 2 ^ 59
def prefixEnd_803866 : Nat := 4983230072969 + 3 ^ 40 * 803866 * 2
def baseEnd_803866 : Nat := 183453173247669824123597

theorem tailTrace_803866 : CollatzResearch.WordTrace tailWord_803866 prefixEnd_803866 183453173247669824123597 := by
  unfold tailWord_803866
  simp only [CollatzResearch.WordTrace]
  refine ⟨7329850426434561556935863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19546267803825497485162301 7329850426434561556935863)
  ·
    refine ⟨10994775639651842335403795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7329850426434561556935863 10994775639651842335403795)
    ·
      refine ⟨16492163459477763503105693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10994775639651842335403795 16492163459477763503105693)
      ·
        refine ⟨6184561297304161313664635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16492163459477763503105693 6184561297304161313664635)
        ·
          refine ⟨9276841945956241970496953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6184561297304161313664635 9276841945956241970496953)
          ·
            refine ⟨6957631459467181477872715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9276841945956241970496953 6957631459467181477872715)
            ·
              refine ⟨10436447189200772216809073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6957631459467181477872715 10436447189200772216809073)
              ·
                refine ⟨7827335391900579162606805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10436447189200772216809073 7827335391900579162606805)
                ·
                  refine ⟨183453173247669824123597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7827335391900579162606805 183453173247669824123597)
                  ·
                    rfl

theorem cell21_803866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_803866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_803866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_803866 prefixEnd_803866 := by exact prefixLift 803866
  have htrace : WordTrace (prefixWord ++ tailWord_803866) baseStart_803866 baseEnd_803866 := by
    simpa [prefixWord, tailWord_803866, baseEnd_803866] using wordTrace_append hprefix tailTrace_803866
  have hstable : (prefixWord ++ tailWord_803866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803866).length < 2 ^ (prefixWord ++ tailWord_803866).sum := by decide
  have hdescent : baseEnd_803866 < baseStart_803866 := by decide
  rcases family_descends (prefixWord ++ tailWord_803866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803872 : List Nat := [2, 1, 1, 7, 1, 2, 1, 2, 4]
def baseStart_803872 : Nat := 118140960795 + 803872 * 2 ^ 59
def prefixEnd_803872 : Nat := 4983230072969 + 3 ^ 40 * 803872 * 2
def baseEnd_803872 : Nat := 183454542529415147023585

theorem tailTrace_803872 : CollatzResearch.WordTrace tailWord_803872 prefixEnd_803872 183454542529415147023585 := by
  unfold tailWord_803872
  simp only [CollatzResearch.WordTrace]
  refine ⟨14659810271858254626230935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19546413695811006168307913 14659810271858254626230935)
  ·
    refine ⟨21989715407787381939346403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14659810271858254626230935 21989715407787381939346403)
    ·
      refine ⟨32984573111681072909019605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21989715407787381939346403 32984573111681072909019605)
      ·
        refine ⟨773075932305025146305147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 32984573111681072909019605 773075932305025146305147)
        ·
          refine ⟨1159613898457537719457721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 773075932305025146305147 1159613898457537719457721)
          ·
            refine ⟨869710423843153289593291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1159613898457537719457721 869710423843153289593291)
            ·
              refine ⟨1304565635764729934389937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869710423843153289593291 1304565635764729934389937)
              ·
                refine ⟨978424226823547450792453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1304565635764729934389937 978424226823547450792453)
                ·
                  refine ⟨183454542529415147023585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 978424226823547450792453 183454542529415147023585)
                  ·
                    rfl

theorem cell21_803872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 4].length) (baseStart_803872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_803872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_803872 prefixEnd_803872 := by exact prefixLift 803872
  have htrace : WordTrace (prefixWord ++ tailWord_803872) baseStart_803872 baseEnd_803872 := by
    simpa [prefixWord, tailWord_803872, baseEnd_803872] using wordTrace_append hprefix tailTrace_803872
  have hstable : (prefixWord ++ tailWord_803872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803872).length < 2 ^ (prefixWord ++ tailWord_803872).sum := by decide
  have hdescent : baseEnd_803872 < baseStart_803872 := by decide
  rcases family_descends (prefixWord ++ tailWord_803872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803883 : List Nat := [1, 1, 1, 1, 2, 1, 5, 6, 3]
def baseStart_803883 : Nat := 118140960795 + 803883 * 2 ^ 59
def prefixEnd_803883 : Nat := 4983230072969 + 3 ^ 40 * 803883 * 2
def baseEnd_803883 : Nat := 183457052879281572340229

theorem tailTrace_803883 : CollatzResearch.WordTrace tailWord_803883 prefixEnd_803883 183457052879281572340229 := by
  unfold tailWord_803883
  simp only [CollatzResearch.WordTrace]
  refine ⟨29320021746676658131112303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19546681164451105420741535 29320021746676658131112303)
  ·
    refine ⟨43980032620014987196668455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29320021746676658131112303 43980032620014987196668455)
    ·
      refine ⟨65970048930022480795002683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43980032620014987196668455 65970048930022480795002683)
      ·
        refine ⟨98955073395033721192504025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65970048930022480795002683 98955073395033721192504025)
        ·
          refine ⟨74216305046275290894378019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98955073395033721192504025 74216305046275290894378019)
          ·
            refine ⟨111324457569412936341567029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74216305046275290894378019 111324457569412936341567029)
            ·
              refine ⟨10436667897132462782021909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111324457569412936341567029 10436667897132462782021909)
              ·
                refine ⟨489218807678084192907277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10436667897132462782021909 489218807678084192907277)
                ·
                  refine ⟨183457052879281572340229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 489218807678084192907277 183457052879281572340229)
                  ·
                    rfl

theorem cell21_803883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 3].length) (baseStart_803883 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_803883 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_803883 prefixEnd_803883 := by exact prefixLift 803883
  have htrace : WordTrace (prefixWord ++ tailWord_803883) baseStart_803883 baseEnd_803883 := by
    simpa [prefixWord, tailWord_803883, baseEnd_803883] using wordTrace_append hprefix tailTrace_803883
  have hstable : (prefixWord ++ tailWord_803883).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803883).length < 2 ^ (prefixWord ++ tailWord_803883).sum := by decide
  have hdescent : baseEnd_803883 < baseStart_803883 := by decide
  rcases family_descends (prefixWord ++ tailWord_803883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803917 : List Nat := [1, 6, 1, 1, 1, 2, 3, 3, 3]
def baseStart_803917 : Nat := 118140960795 + 803917 * 2 ^ 59
def prefixEnd_803917 : Nat := 4983230072969 + 3 ^ 40 * 803917 * 2
def baseEnd_803917 : Nat := 183464812142505068773493

theorem tailTrace_803917 : CollatzResearch.WordTrace tailWord_803917 prefixEnd_803917 183464812142505068773493 := by
  unfold tailWord_803917
  simp only [CollatzResearch.WordTrace]
  refine ⟨29321261828553481937850005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19547507885702321291900003 29321261828553481937850005)
  ·
    refine ⟨1374434148213444465836719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29321261828553481937850005 1374434148213444465836719)
    ·
      refine ⟨2061651222320166698755079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1374434148213444465836719 2061651222320166698755079)
      ·
        refine ⟨3092476833480250048132619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2061651222320166698755079 3092476833480250048132619)
        ·
          refine ⟨4638715250220375072198929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3092476833480250048132619 4638715250220375072198929)
          ·
            refine ⟨3479036437665281304149197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4638715250220375072198929 3479036437665281304149197)
            ·
              refine ⟨1304638664124480489055949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3479036437665281304149197 1304638664124480489055949)
              ·
                refine ⟨489239499046680183395981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1304638664124480489055949 489239499046680183395981)
                ·
                  refine ⟨183464812142505068773493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 489239499046680183395981 183464812142505068773493)
                  ·
                    rfl

theorem cell21_803917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_803917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_803917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_803917 prefixEnd_803917 := by exact prefixLift 803917
  have htrace : WordTrace (prefixWord ++ tailWord_803917) baseStart_803917 baseEnd_803917 := by
    simpa [prefixWord, tailWord_803917, baseEnd_803917] using wordTrace_append hprefix tailTrace_803917
  have hstable : (prefixWord ++ tailWord_803917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803917).length < 2 ^ (prefixWord ++ tailWord_803917).sum := by decide
  have hdescent : baseEnd_803917 < baseStart_803917 := by decide
  rcases family_descends (prefixWord ++ tailWord_803917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803934 : List Nat := [4, 4, 1, 1, 1, 3, 1, 1, 5]
def baseStart_803934 : Nat := 118140960795 + 803934 * 2 ^ 59
def prefixEnd_803934 : Nat := 4983230072969 + 3 ^ 40 * 803934 * 2
def baseEnd_803934 : Nat := 183468691774116816990125

theorem tailTrace_803934 : CollatzResearch.WordTrace tailWord_803934 prefixEnd_803934 183468691774116816990125 := by
  unfold tailWord_803934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3665235233686486730152357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19547921246327929227479237 3665235233686486730152357)
  ·
    refine ⟨687231606316216261903567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3665235233686486730152357 687231606316216261903567)
    ·
      refine ⟨1030847409474324392855351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 687231606316216261903567 1030847409474324392855351)
      ·
        refine ⟨1546271114211486589283027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1030847409474324392855351 1546271114211486589283027)
        ·
          refine ⟨2319406671317229883924541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1546271114211486589283027 2319406671317229883924541)
          ·
            refine ⟨869777501743961206471703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2319406671317229883924541 869777501743961206471703)
            ·
              refine ⟨1304666252615941809707555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869777501743961206471703 1304666252615941809707555)
              ·
                refine ⟨1956999378923912714561333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1304666252615941809707555 1956999378923912714561333)
                ·
                  refine ⟨183468691774116816990125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1956999378923912714561333 183468691774116816990125)
                  ·
                    rfl

theorem cell21_803934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_803934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_803934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_803934 prefixEnd_803934 := by exact prefixLift 803934
  have htrace : WordTrace (prefixWord ++ tailWord_803934) baseStart_803934 baseEnd_803934 := by
    simpa [prefixWord, tailWord_803934, baseEnd_803934] using wordTrace_append hprefix tailTrace_803934
  have hstable : (prefixWord ++ tailWord_803934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803934).length < 2 ^ (prefixWord ++ tailWord_803934).sum := by decide
  have hdescent : baseEnd_803934 < baseStart_803934 := by decide
  rcases family_descends (prefixWord ++ tailWord_803934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804004 : List Nat := [2, 3, 1, 2, 3, 1, 3, 6]
def baseStart_804004 : Nat := 118140960795 + 804004 * 2 ^ 59
def prefixEnd_804004 : Nat := 4983230072969 + 3 ^ 40 * 804004 * 2
def baseEnd_804004 : Nat := 61161555575937416941105

theorem tailTrace_804004 : CollatzResearch.WordTrace tailWord_804004 prefixEnd_804004 61161555575937416941105 := by
  unfold tailWord_804004
  simp only [CollatzResearch.WordTrace]
  refine ⟨14662217489619147898133533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19549623319492197197511377 14662217489619147898133533)
  ·
    refine ⟨5498331558607180461800075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14662217489619147898133533 5498331558607180461800075)
    ·
      refine ⟨8247497337910770692700113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5498331558607180461800075 8247497337910770692700113)
      ·
        refine ⟨6185623003433078019525085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8247497337910770692700113 6185623003433078019525085)
        ·
          refine ⟨2319608626287404257321907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6185623003433078019525085 2319608626287404257321907)
          ·
            refine ⟨3479412939431106385982861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319608626287404257321907 3479412939431106385982861)
            ·
              refine ⟨1304779852286664894743573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3479412939431106385982861 1304779852286664894743573)
              ·
                refine ⟨61161555575937416941105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1304779852286664894743573 61161555575937416941105)
                ·
                  rfl

theorem cell21_804004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 6].length) (baseStart_804004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_804004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_804004 prefixEnd_804004 := by exact prefixLift 804004
  have htrace : WordTrace (prefixWord ++ tailWord_804004) baseStart_804004 baseEnd_804004 := by
    simpa [prefixWord, tailWord_804004, baseEnd_804004] using wordTrace_append hprefix tailTrace_804004
  have hstable : (prefixWord ++ tailWord_804004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804004).length < 2 ^ (prefixWord ++ tailWord_804004).sum := by decide
  have hdescent : baseEnd_804004 < baseStart_804004 := by decide
  rcases family_descends (prefixWord ++ tailWord_804004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804018 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 7]
def baseStart_804018 : Nat := 118140960795 + 804018 * 2 ^ 59
def prefixEnd_804018 : Nat := 4983230072969 + 3 ^ 40 * 804018 * 2
def baseEnd_804018 : Nat := 183487861718551337589953

theorem tailTrace_804018 : CollatzResearch.WordTrace tailWord_804018 prefixEnd_804018 183487861718551337589953 := by
  unfold tailWord_804018
  simp only [CollatzResearch.WordTrace]
  refine ⟨7331236400296894046819177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19549963734125050791517805 7331236400296894046819177)
  ·
    refine ⟨5498427300222670535114383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7331236400296894046819177 5498427300222670535114383)
    ·
      refine ⟨8247640950334005802671575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5498427300222670535114383 8247640950334005802671575)
      ·
        refine ⟨12371461425501008704007363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8247640950334005802671575 12371461425501008704007363)
        ·
          refine ⟨18557192138251513056011045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12371461425501008704007363 18557192138251513056011045)
          ·
            refine ⟨3479473525922158698002071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18557192138251513056011045 3479473525922158698002071)
            ·
              refine ⟨5219210288883238047003107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3479473525922158698002071 5219210288883238047003107)
              ·
                refine ⟨7828815433324857070504661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5219210288883238047003107 7828815433324857070504661)
                ·
                  refine ⟨183487861718551337589953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7828815433324857070504661 183487861718551337589953)
                  ·
                    rfl

theorem cell21_804018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_804018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_804018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_804018 prefixEnd_804018 := by exact prefixLift 804018
  have htrace : WordTrace (prefixWord ++ tailWord_804018) baseStart_804018 baseEnd_804018 := by
    simpa [prefixWord, tailWord_804018, baseEnd_804018] using wordTrace_append hprefix tailTrace_804018
  have hstable : (prefixWord ++ tailWord_804018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804018).length < 2 ^ (prefixWord ++ tailWord_804018).sum := by decide
  have hdescent : baseEnd_804018 < baseStart_804018 := by decide
  rcases family_descends (prefixWord ++ tailWord_804018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804114 : List Nat := [3, 2, 4, 2, 1, 1, 2, 6]
def baseStart_804114 : Nat := 118140960795 + 804114 * 2 ^ 59
def prefixEnd_804114 : Nat := 4983230072969 + 3 ^ 40 * 804114 * 2
def baseEnd_804114 : Nat := 61169923408825501329919

theorem tailTrace_804114 : CollatzResearch.WordTrace tailWord_804114 prefixEnd_804114 61169923408825501329919 := by
  unfold tailWord_804114
  simp only [CollatzResearch.WordTrace]
  refine ⟨7332111752209946145692849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19552298005893189721847597 7332111752209946145692849)
  ·
    refine ⟨5499083814157459609269637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7332111752209946145692849 5499083814157459609269637)
    ·
      refine ⟨1031078215154523676738057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5499083814157459609269637 1031078215154523676738057)
      ·
        refine ⟨773308661365892757553543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1031078215154523676738057 773308661365892757553543)
        ·
          refine ⟨1159962992048839136330315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 773308661365892757553543 1159962992048839136330315)
          ·
            refine ⟨1739944488073258704495473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159962992048839136330315 1739944488073258704495473)
            ·
              refine ⟨1304958366054944028371605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1739944488073258704495473 1304958366054944028371605)
              ·
                refine ⟨61169923408825501329919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1304958366054944028371605 61169923408825501329919)
                ·
                  rfl

theorem cell21_804114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_804114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_804114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_804114 prefixEnd_804114 := by exact prefixLift 804114
  have htrace : WordTrace (prefixWord ++ tailWord_804114) baseStart_804114 baseEnd_804114 := by
    simpa [prefixWord, tailWord_804114, baseEnd_804114] using wordTrace_append hprefix tailTrace_804114
  have hstable : (prefixWord ++ tailWord_804114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804114).length < 2 ^ (prefixWord ++ tailWord_804114).sum := by decide
  have hdescent : baseEnd_804114 < baseStart_804114 := by decide
  rcases family_descends (prefixWord ++ tailWord_804114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804204 : List Nat := [2, 2, 1, 1, 5, 2, 2, 3, 3]
def baseStart_804204 : Nat := 118140960795 + 804204 * 2 ^ 59
def prefixEnd_804204 : Nat := 4983230072969 + 3 ^ 40 * 804204 * 2
def baseEnd_804204 : Nat := 183530309452656347489573

theorem tailTrace_804204 : CollatzResearch.WordTrace tailWord_804204 prefixEnd_804204 183530309452656347489573 := by
  unfold tailWord_804204
  simp only [CollatzResearch.WordTrace]
  refine ⟨14665864789256864976773833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19554486385675819969031777 14665864789256864976773833)
  ·
    refine ⟨10999398591942648732580375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14665864789256864976773833 10999398591942648732580375)
    ·
      refine ⟨16499097887913973098870563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10999398591942648732580375 16499097887913973098870563)
      ·
        refine ⟨24748646831870959648305845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16499097887913973098870563 24748646831870959648305845)
        ·
          refine ⟨2320185640487902467028673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24748646831870959648305845 2320185640487902467028673)
          ·
            refine ⟨1740139230365926850271505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2320185640487902467028673 1740139230365926850271505)
            ·
              refine ⟨1305104422774445137703629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1740139230365926850271505 1305104422774445137703629)
              ·
                refine ⟨489414158540416926638861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1305104422774445137703629 489414158540416926638861)
                ·
                  refine ⟨183530309452656347489573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 489414158540416926638861 183530309452656347489573)
                  ·
                    rfl

theorem cell21_804204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_804204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_804204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_804204 prefixEnd_804204 := by exact prefixLift 804204
  have htrace : WordTrace (prefixWord ++ tailWord_804204) baseStart_804204 baseEnd_804204 := by
    simpa [prefixWord, tailWord_804204, baseEnd_804204] using wordTrace_append hprefix tailTrace_804204
  have hstable : (prefixWord ++ tailWord_804204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804204).length < 2 ^ (prefixWord ++ tailWord_804204).sum := by decide
  have hdescent : baseEnd_804204 < baseStart_804204 := by decide
  rcases family_descends (prefixWord ++ tailWord_804204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804277 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 6]
def baseStart_804277 : Nat := 118140960795 + 804277 * 2 ^ 59
def prefixEnd_804277 : Nat := 4983230072969 + 3 ^ 40 * 804277 * 2
def baseEnd_804277 : Nat := 183546969047224442772757

theorem tailTrace_804277 : CollatzResearch.WordTrace tailWord_804277 prefixEnd_804277 183546969047224442772757 := by
  unfold tailWord_804277
  simp only [CollatzResearch.WordTrace]
  refine ⟨29334392107249263420955085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19556261404832842280636723 29334392107249263420955085)
  ·
    refine ⟨11000397040218473782858157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29334392107249263420955085 11000397040218473782858157)
    ·
      refine ⟨4125148890081927668571809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11000397040218473782858157 4125148890081927668571809)
      ·
        refine ⟨3093861667561445751428857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4125148890081927668571809 3093861667561445751428857)
        ·
          refine ⟨2320396250671084313571643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3093861667561445751428857 2320396250671084313571643)
          ·
            refine ⟨3480594376006626470357465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320396250671084313571643 3480594376006626470357465)
            ·
              refine ⟨2610445782004969852768099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3480594376006626470357465 2610445782004969852768099)
              ·
                refine ⟨3915668673007454779152149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2610445782004969852768099 3915668673007454779152149)
                ·
                  refine ⟨183546969047224442772757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3915668673007454779152149 183546969047224442772757)
                  ·
                    rfl

theorem cell21_804277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_804277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_804277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_804277 prefixEnd_804277 := by exact prefixLift 804277
  have htrace : WordTrace (prefixWord ++ tailWord_804277) baseStart_804277 baseEnd_804277 := by
    simpa [prefixWord, tailWord_804277, baseEnd_804277] using wordTrace_append hprefix tailTrace_804277
  have hstable : (prefixWord ++ tailWord_804277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804277).length < 2 ^ (prefixWord ++ tailWord_804277).sum := by decide
  have hdescent : baseEnd_804277 < baseStart_804277 := by decide
  rcases family_descends (prefixWord ++ tailWord_804277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804387 : List Nat := [1, 1, 1, 4, 6, 1, 1, 2, 4]
def baseStart_804387 : Nat := 118140960795 + 804387 * 2 ^ 59
def prefixEnd_804387 : Nat := 4983230072969 + 3 ^ 40 * 804387 * 2
def baseEnd_804387 : Nat := 183572072545888695939199

theorem tailTrace_804387 : CollatzResearch.WordTrace tailWord_804387 prefixEnd_804387 183572072545888695939199 := by
  unfold tailWord_804387
  simp only [CollatzResearch.WordTrace]
  refine ⟨29338404136850752207459415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19558936091233834804972943 29338404136850752207459415)
  ·
    refine ⟨44007606205276128311189123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29338404136850752207459415 44007606205276128311189123)
    ·
      refine ⟨66011409307914192466783685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44007606205276128311189123 66011409307914192466783685)
      ·
        refine ⟨12377139245233911087521941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66011409307914192466783685 12377139245233911087521941)
        ·
          refine ⟨580178402120339582227591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12377139245233911087521941 580178402120339582227591)
          ·
            refine ⟨870267603180509373341387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580178402120339582227591 870267603180509373341387)
            ·
              refine ⟨1305401404770764060012081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 870267603180509373341387 1305401404770764060012081)
              ·
                refine ⟨979051053578073045009061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1305401404770764060012081 979051053578073045009061)
                ·
                  refine ⟨183572072545888695939199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 979051053578073045009061 183572072545888695939199)
                  ·
                    rfl

theorem cell21_804387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 4].length) (baseStart_804387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_804387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_804387 prefixEnd_804387 := by exact prefixLift 804387
  have htrace : WordTrace (prefixWord ++ tailWord_804387) baseStart_804387 baseEnd_804387 := by
    simpa [prefixWord, tailWord_804387, baseEnd_804387] using wordTrace_append hprefix tailTrace_804387
  have hstable : (prefixWord ++ tailWord_804387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804387).length < 2 ^ (prefixWord ++ tailWord_804387).sum := by decide
  have hdescent : baseEnd_804387 < baseStart_804387 := by decide
  rcases family_descends (prefixWord ++ tailWord_804387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804508 : List Nat := [2, 2, 3, 2, 3, 1, 1, 4, 3]
def baseStart_804508 : Nat := 118140960795 + 804508 * 2 ^ 59
def prefixEnd_804508 : Nat := 4983230072969 + 3 ^ 40 * 804508 * 2
def baseEnd_804508 : Nat := 183599686394419374422285

theorem tailTrace_804508 : CollatzResearch.WordTrace tailWord_804508 prefixEnd_804508 183599686394419374422285 := by
  unfold tailWord_804508
  simp only [CollatzResearch.WordTrace]
  refine ⟨14671408684706194936307089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19561878246274926581742785 14671408684706194936307089)
  ·
    refine ⟨11003556513529646202230317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14671408684706194936307089 11003556513529646202230317)
    ·
      refine ⟨4126333692573617325836369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11003556513529646202230317 4126333692573617325836369)
      ·
        refine ⟨3094750269430212994377277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4126333692573617325836369 3094750269430212994377277)
        ·
          refine ⟨1160531351036329872891479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3094750269430212994377277 1160531351036329872891479)
          ·
            refine ⟨1740797026554494809337219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160531351036329872891479 1740797026554494809337219)
            ·
              refine ⟨2611195539831742214005829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1740797026554494809337219 2611195539831742214005829)
              ·
                refine ⟨489599163718451665126093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2611195539831742214005829 489599163718451665126093)
                ·
                  refine ⟨183599686394419374422285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 489599163718451665126093 183599686394419374422285)
                  ·
                    rfl

theorem cell21_804508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_804508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_804508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_804508 prefixEnd_804508 := by exact prefixLift 804508
  have htrace : WordTrace (prefixWord ++ tailWord_804508) baseStart_804508 baseEnd_804508 := by
    simpa [prefixWord, tailWord_804508, baseEnd_804508] using wordTrace_append hprefix tailTrace_804508
  have hstable : (prefixWord ++ tailWord_804508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804508).length < 2 ^ (prefixWord ++ tailWord_804508).sum := by decide
  have hdescent : baseEnd_804508 < baseStart_804508 := by decide
  rcases family_descends (prefixWord ++ tailWord_804508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804595 : List Nat := [1, 1, 1, 2, 2, 3, 6, 5]
def baseStart_804595 : Nat := 118140960795 + 804595 * 2 ^ 59
def prefixEnd_804595 : Nat := 4983230072969 + 3 ^ 40 * 804595 * 2
def baseEnd_804595 : Nat := 61206513659908852157369

theorem tailTrace_804595 : CollatzResearch.WordTrace tailWord_804595 prefixEnd_804595 61206513659908852157369 := by
  unfold tailWord_804595
  simp only [CollatzResearch.WordTrace]
  refine ⟨29345990520097203731031239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19563993680064802487354159 29345990520097203731031239)
  ·
    refine ⟨44018985780145805596546859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29345990520097203731031239 44018985780145805596546859)
    ·
      refine ⟨66028478670218708394820289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44018985780145805596546859 66028478670218708394820289)
      ·
        refine ⟨49521359002664031296115217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66028478670218708394820289 49521359002664031296115217)
        ·
          refine ⟨37141019251998023472086413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49521359002664031296115217 37141019251998023472086413)
          ·
            refine ⟨13927882219499258802032405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37141019251998023472086413 13927882219499258802032405)
            ·
              refine ⟨652869479039027756345269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13927882219499258802032405 652869479039027756345269)
              ·
                refine ⟨61206513659908852157369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 652869479039027756345269 61206513659908852157369)
                ·
                  rfl

theorem cell21_804595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 5].length) (baseStart_804595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_804595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_804595 prefixEnd_804595 := by exact prefixLift 804595
  have htrace : WordTrace (prefixWord ++ tailWord_804595) baseStart_804595 baseEnd_804595 := by
    simpa [prefixWord, tailWord_804595, baseEnd_804595] using wordTrace_append hprefix tailTrace_804595
  have hstable : (prefixWord ++ tailWord_804595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804595).length < 2 ^ (prefixWord ++ tailWord_804595).sum := by decide
  have hdescent : baseEnd_804595 < baseStart_804595 := by decide
  rcases family_descends (prefixWord ++ tailWord_804595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804609 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 7]
def baseStart_804609 : Nat := 118140960795 + 804609 * 2 ^ 59
def prefixEnd_804609 : Nat := 4983230072969 + 3 ^ 40 * 804609 * 2
def baseEnd_804609 : Nat := 183622735970465643238745

theorem tailTrace_804609 : CollatzResearch.WordTrace tailWord_804609 prefixEnd_804609 183622735970465643238745 := by
  unfold tailWord_804609
  simp only [CollatzResearch.WordTrace]
  refine ⟨29346501142046484122040881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19564334094697656081360587 29346501142046484122040881)
  ·
    refine ⟨22009875856534863091530661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29346501142046484122040881 22009875856534863091530661)
    ·
      refine ⟨4126851723100286829661999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22009875856534863091530661 4126851723100286829661999)
      ·
        refine ⟨6190277584650430244492999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4126851723100286829661999 6190277584650430244492999)
        ·
          refine ⟨9285416376975645366739499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6190277584650430244492999 9285416376975645366739499)
          ·
            refine ⟨13928124565463468050109249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9285416376975645366739499 13928124565463468050109249)
            ·
              refine ⟨10446093424097601037581937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13928124565463468050109249 10446093424097601037581937)
              ·
                refine ⟨7834570068073200778186453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10446093424097601037581937 7834570068073200778186453)
                ·
                  refine ⟨183622735970465643238745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7834570068073200778186453 183622735970465643238745)
                  ·
                    rfl

theorem cell21_804609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_804609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_804609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_804609 prefixEnd_804609 := by exact prefixLift 804609
  have htrace : WordTrace (prefixWord ++ tailWord_804609) baseStart_804609 baseEnd_804609 := by
    simpa [prefixWord, tailWord_804609, baseEnd_804609] using wordTrace_append hprefix tailTrace_804609
  have hstable : (prefixWord ++ tailWord_804609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804609).length < 2 ^ (prefixWord ++ tailWord_804609).sum := by decide
  have hdescent : baseEnd_804609 < baseStart_804609 := by decide
  rcases family_descends (prefixWord ++ tailWord_804609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804671 : List Nat := [1, 1, 2, 2, 7, 8]
def baseStart_804671 : Nat := 118140960795 + 804671 * 2 ^ 59
def prefixEnd_804671 : Nat := 4983230072969 + 3 ^ 40 * 804671 * 2
def baseEnd_804671 : Nat := 6801366119080270859455

theorem tailTrace_804671 : CollatzResearch.WordTrace tailWord_804671 prefixEnd_804671 6801366119080270859455 := by
  unfold tailWord_804671
  simp only [CollatzResearch.WordTrace]
  refine ⟨29348762467821868710797867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19565841645214579140531911 29348762467821868710797867)
  ·
    refine ⟨44023143701732803066196801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29348762467821868710797867 44023143701732803066196801)
    ·
      refine ⟨33017357776299602299647601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44023143701732803066196801 33017357776299602299647601)
      ·
        refine ⟨24763018332224701724735701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33017357776299602299647601 24763018332224701724735701)
        ·
          refine ⟨580383242161516446673493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 24763018332224701724735701 580383242161516446673493)
          ·
            refine ⟨6801366119080270859455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 580383242161516446673493 6801366119080270859455)
            ·
              rfl

theorem cell21_804671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 8].length) (baseStart_804671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_804671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_804671 prefixEnd_804671 := by exact prefixLift 804671
  have htrace : WordTrace (prefixWord ++ tailWord_804671) baseStart_804671 baseEnd_804671 := by
    simpa [prefixWord, tailWord_804671, baseEnd_804671] using wordTrace_append hprefix tailTrace_804671
  have hstable : (prefixWord ++ tailWord_804671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804671).length < 2 ^ (prefixWord ++ tailWord_804671).sum := by decide
  have hdescent : baseEnd_804671 < baseStart_804671 := by decide
  rcases family_descends (prefixWord ++ tailWord_804671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804761 : List Nat := [1, 2, 1, 2, 1, 3, 4, 2, 5]
def baseStart_804761 : Nat := 118140960795 + 804761 * 2 ^ 59
def prefixEnd_804761 : Nat := 4983230072969 + 3 ^ 40 * 804761 * 2
def baseEnd_804761 : Nat := 183657424441347156705101

theorem tailTrace_804761 : CollatzResearch.WordTrace tailWord_804761 prefixEnd_804761 183657424441347156705101 := by
  unfold tailWord_804761
  simp only [CollatzResearch.WordTrace]
  refine ⟨29352045037495814081574137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19568030024997209387716091 29352045037495814081574137)
  ·
    refine ⟨22014033778121860561180603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29352045037495814081574137 22014033778121860561180603)
    ·
      refine ⟨33021050667182790841770905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22014033778121860561180603 33021050667182790841770905)
      ·
        refine ⟨24765788000387093131328179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33021050667182790841770905 24765788000387093131328179)
        ·
          refine ⟨37148682000580639696992269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24765788000387093131328179 37148682000580639696992269)
          ·
            refine ⟨13930755750217739886372101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37148682000580639696992269 13930755750217739886372101)
            ·
              refine ⟨2612016703165826228694769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13930755750217739886372101 2612016703165826228694769)
              ·
                refine ⟨1959012527374369671521077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2612016703165826228694769 1959012527374369671521077)
                ·
                  refine ⟨183657424441347156705101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1959012527374369671521077 183657424441347156705101)
                  ·
                    rfl

theorem cell21_804761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_804761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_804761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_804761 prefixEnd_804761 := by exact prefixLift 804761
  have htrace : WordTrace (prefixWord ++ tailWord_804761) baseStart_804761 baseEnd_804761 := by
    simpa [prefixWord, tailWord_804761, baseEnd_804761] using wordTrace_append hprefix tailTrace_804761
  have hstable : (prefixWord ++ tailWord_804761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804761).length < 2 ^ (prefixWord ++ tailWord_804761).sum := by decide
  have hdescent : baseEnd_804761 < baseStart_804761 := by decide
  rcases family_descends (prefixWord ++ tailWord_804761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804764 : List Nat := [2, 2, 3, 3, 1, 1, 4, 5]
def baseStart_804764 : Nat := 118140960795 + 804764 * 2 ^ 59
def prefixEnd_804764 : Nat := 4983230072969 + 3 ^ 40 * 804764 * 2
def baseEnd_804764 : Nat := 61219369694073272718365

theorem tailTrace_804764 : CollatzResearch.WordTrace tailWord_804764 prefixEnd_804764 61219369694073272718365 := by
  unfold tailWord_804764
  simp only [CollatzResearch.WordTrace]
  refine ⟨14676077228242472796966673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19568102970989963729288897 14676077228242472796966673)
  ·
    refine ⟨11007057921181854597725005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14676077228242472796966673 11007057921181854597725005)
    ·
      refine ⟨4127646720443195474146877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11007057921181854597725005 4127646720443195474146877)
      ·
        refine ⟨1547867520166198302805079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4127646720443195474146877 1547867520166198302805079)
        ·
          refine ⟨2321801280249297454207619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1547867520166198302805079 2321801280249297454207619)
          ·
            refine ⟨3482701920373946181311429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2321801280249297454207619 3482701920373946181311429)
            ·
              refine ⟨653006610070114908995893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3482701920373946181311429 653006610070114908995893)
              ·
                refine ⟨61219369694073272718365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 653006610070114908995893 61219369694073272718365)
                ·
                  rfl

theorem cell21_804764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 5].length) (baseStart_804764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_804764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_804764 prefixEnd_804764 := by exact prefixLift 804764
  have htrace : WordTrace (prefixWord ++ tailWord_804764) baseStart_804764 baseEnd_804764 := by
    simpa [prefixWord, tailWord_804764, baseEnd_804764] using wordTrace_append hprefix tailTrace_804764
  have hstable : (prefixWord ++ tailWord_804764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804764).length < 2 ^ (prefixWord ++ tailWord_804764).sum := by decide
  have hdescent : baseEnd_804764 < baseStart_804764 := by decide
  rcases family_descends (prefixWord ++ tailWord_804764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804792 : List Nat := [2, 1, 2, 1, 2, 3, 2, 4, 4]
def baseStart_804792 : Nat := 118140960795 + 804792 * 2 ^ 59
def prefixEnd_804792 : Nat := 4983230072969 + 3 ^ 40 * 804792 * 2
def baseEnd_804792 : Nat := 183664499063697991688371

theorem tailTrace_804792 : CollatzResearch.WordTrace tailWord_804792 prefixEnd_804792 183664499063697991688371 := by
  unfold tailWord_804792
  simp only [CollatzResearch.WordTrace]
  refine ⟨14676587850191753187976315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19568783800255670917301753 14676587850191753187976315)
  ·
    refine ⟨22014881775287629781964473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14676587850191753187976315 22014881775287629781964473)
    ·
      refine ⟨16511161331465722336473355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22014881775287629781964473 16511161331465722336473355)
      ·
        refine ⟨24766741997198583504710033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16511161331465722336473355 24766741997198583504710033)
        ·
          refine ⟨18575056497898937628532525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24766741997198583504710033 18575056497898937628532525)
          ·
            refine ⟨6965646186712101610699697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18575056497898937628532525 6965646186712101610699697)
            ·
              refine ⟨5224234640034076208024773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6965646186712101610699697 5224234640034076208024773)
              ·
                refine ⟨979543995006389289004645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5224234640034076208024773 979543995006389289004645)
                ·
                  refine ⟨183664499063697991688371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 979543995006389289004645 183664499063697991688371)
                  ·
                    rfl

theorem cell21_804792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 4].length) (baseStart_804792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_804792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_804792 prefixEnd_804792 := by exact prefixLift 804792
  have htrace : WordTrace (prefixWord ++ tailWord_804792) baseStart_804792 baseEnd_804792 := by
    simpa [prefixWord, tailWord_804792, baseEnd_804792] using wordTrace_append hprefix tailTrace_804792
  have hstable : (prefixWord ++ tailWord_804792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804792).length < 2 ^ (prefixWord ++ tailWord_804792).sum := by decide
  have hdescent : baseEnd_804792 < baseStart_804792 := by decide
  rcases family_descends (prefixWord ++ tailWord_804792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804851 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 6]
def baseStart_804851 : Nat := 118140960795 + 804851 * 2 ^ 59
def prefixEnd_804851 : Nat := 4983230072969 + 3 ^ 40 * 804851 * 2
def baseEnd_804851 : Nat := 183677963667527000204917

theorem tailTrace_804851 : CollatzResearch.WordTrace tailWord_804851 prefixEnd_804851 183677963667527000204917 := by
  unfold tailWord_804851
  simp only [CollatzResearch.WordTrace]
  refine ⟨29355327607169759452350407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19570218404779839634900271 29355327607169759452350407)
  ·
    refine ⟨44032991410754639178525611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29355327607169759452350407 44032991410754639178525611)
    ·
      refine ⟨66049487116131958767788417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44032991410754639178525611 66049487116131958767788417)
      ·
        refine ⟨49537115337098969075841313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66049487116131958767788417 49537115337098969075841313)
        ·
          refine ⟨37152836502824226806880985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49537115337098969075841313 37152836502824226806880985)
          ·
            refine ⟨27864627377118170105160739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37152836502824226806880985 27864627377118170105160739)
            ·
              refine ⟨41796941065677255157741109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27864627377118170105160739 41796941065677255157741109)
              ·
                refine ⟨3918463224907242671038229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41796941065677255157741109 3918463224907242671038229)
                ·
                  refine ⟨183677963667527000204917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3918463224907242671038229 183677963667527000204917)
                  ·
                    rfl

theorem cell21_804851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 6].length) (baseStart_804851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_804851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_804851 prefixEnd_804851 := by exact prefixLift 804851
  have htrace : WordTrace (prefixWord ++ tailWord_804851) baseStart_804851 baseEnd_804851 := by
    simpa [prefixWord, tailWord_804851, baseEnd_804851] using wordTrace_append hprefix tailTrace_804851
  have hstable : (prefixWord ++ tailWord_804851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804851).length < 2 ^ (prefixWord ++ tailWord_804851).sum := by decide
  have hdescent : baseEnd_804851 < baseStart_804851 := by decide
  rcases family_descends (prefixWord ++ tailWord_804851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804913 : List Nat := [1, 2, 2, 3, 1, 3, 1, 3, 5]
def baseStart_804913 : Nat := 118140960795 + 804913 * 2 ^ 59
def prefixEnd_804913 : Nat := 4983230072969 + 3 ^ 40 * 804913 * 2
def baseEnd_804913 : Nat := 183692112912228670171457

theorem tailTrace_804913 : CollatzResearch.WordTrace tailWord_804913 prefixEnd_804913 183692112912228670171457 := by
  unfold tailWord_804913
  simp only [CollatzResearch.WordTrace]
  refine ⟨29357588932945144041107393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19571725955296762694071595 29357588932945144041107393)
  ·
    refine ⟨22018191699708858030830545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29357588932945144041107393 22018191699708858030830545)
    ·
      refine ⟨16513643774781643523122909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22018191699708858030830545 16513643774781643523122909)
      ·
        refine ⟨6192616415543116321171091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16513643774781643523122909 6192616415543116321171091)
        ·
          refine ⟨9288924623314674481756637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6192616415543116321171091 9288924623314674481756637)
          ·
            refine ⟨3483346733743002930658739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9288924623314674481756637 3483346733743002930658739)
            ·
              refine ⟨5225020100614504395988109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3483346733743002930658739 5225020100614504395988109)
              ·
                refine ⟨1959382537730439148495541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5225020100614504395988109 1959382537730439148495541)
                ·
                  refine ⟨183692112912228670171457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1959382537730439148495541 183692112912228670171457)
                  ·
                    rfl

theorem cell21_804913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_804913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_804913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_804913 prefixEnd_804913 := by exact prefixLift 804913
  have htrace : WordTrace (prefixWord ++ tailWord_804913) baseStart_804913 baseEnd_804913 := by
    simpa [prefixWord, tailWord_804913, baseEnd_804913] using wordTrace_append hprefix tailTrace_804913
  have hstable : (prefixWord ++ tailWord_804913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804913).length < 2 ^ (prefixWord ++ tailWord_804913).sum := by decide
  have hdescent : baseEnd_804913 < baseStart_804913 := by decide
  rcases family_descends (prefixWord ++ tailWord_804913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804978 : List Nat := [3, 2, 1, 2, 2, 4, 2, 1, 4]
def baseStart_804978 : Nat := 118140960795 + 804978 * 2 ^ 59
def prefixEnd_804978 : Nat := 4983230072969 + 3 ^ 40 * 804978 * 2
def baseEnd_804978 : Nat := 183706946797803001587991

theorem tailTrace_804978 : CollatzResearch.WordTrace tailWord_804978 prefixEnd_804978 183706946797803001587991 := by
  unfold tailWord_804978
  simp only [CollatzResearch.WordTrace]
  refine ⟨7339989919427415035555897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19573306451806440094815725 7339989919427415035555897)
  ·
    refine ⟨5504992439570561276666923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7339989919427415035555897 5504992439570561276666923)
    ·
      refine ⟨8257488659355841915000385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5504992439570561276666923 8257488659355841915000385)
      ·
        refine ⟨6193116494516881436250289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8257488659355841915000385 6193116494516881436250289)
        ·
          refine ⟨4644837370887661077187717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6193116494516881436250289 4644837370887661077187717)
          ·
            refine ⟨870907007041436451972697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4644837370887661077187717 870907007041436451972697)
            ·
              refine ⟨653180255281077338979523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 870907007041436451972697 653180255281077338979523)
              ·
                refine ⟨979770382921616008469285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 653180255281077338979523 979770382921616008469285)
                ·
                  refine ⟨183706946797803001587991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 979770382921616008469285 183706946797803001587991)
                  ·
                    rfl

theorem cell21_804978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_804978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_804978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_804978 prefixEnd_804978 := by exact prefixLift 804978
  have htrace : WordTrace (prefixWord ++ tailWord_804978) baseStart_804978 baseEnd_804978 := by
    simpa [prefixWord, tailWord_804978, baseEnd_804978] using wordTrace_append hprefix tailTrace_804978
  have hstable : (prefixWord ++ tailWord_804978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804978).length < 2 ^ (prefixWord ++ tailWord_804978).sum := by decide
  have hdescent : baseEnd_804978 < baseStart_804978 := by decide
  rcases family_descends (prefixWord ++ tailWord_804978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805023 : List Nat := [1, 1, 2, 6, 1, 2, 1, 4, 3]
def baseStart_805023 : Nat := 118140960795 + 805023 * 2 ^ 59
def prefixEnd_805023 : Nat := 4983230072969 + 3 ^ 40 * 805023 * 2
def baseEnd_805023 : Nat := 183717216410892923337899

theorem tailTrace_805023 : CollatzResearch.WordTrace tailWord_805023 prefixEnd_805023 183717216410892923337899 := by
  unfold tailWord_805023
  simp only [CollatzResearch.WordTrace]
  refine ⟨29361600962546632827611723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19574400641697755218407815 29361600962546632827611723)
  ·
    refine ⟨44042401443819949241417585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29361600962546632827611723 44042401443819949241417585)
    ·
      refine ⟨33031801082864961931063189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44042401443819949241417585 33031801082864961931063189)
      ·
        refine ⟨1548365675759295090518587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33031801082864961931063189 1548365675759295090518587)
        ·
          refine ⟨2322548513638942635777881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1548365675759295090518587 2322548513638942635777881)
          ·
            refine ⟨1741911385229206976833411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2322548513638942635777881 1741911385229206976833411)
            ·
              refine ⟨2612867077843810465250117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741911385229206976833411 2612867077843810465250117)
              ·
                refine ⟨489912577095714462234397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2612867077843810465250117 489912577095714462234397)
                ·
                  refine ⟨183717216410892923337899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 489912577095714462234397 183717216410892923337899)
                  ·
                    rfl

theorem cell21_805023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 3].length) (baseStart_805023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_805023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_805023 prefixEnd_805023 := by exact prefixLift 805023
  have htrace : WordTrace (prefixWord ++ tailWord_805023) baseStart_805023 baseEnd_805023 := by
    simpa [prefixWord, tailWord_805023, baseEnd_805023] using wordTrace_append hprefix tailTrace_805023
  have hstable : (prefixWord ++ tailWord_805023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805023).length < 2 ^ (prefixWord ++ tailWord_805023).sum := by decide
  have hdescent : baseEnd_805023 < baseStart_805023 := by decide
  rcases family_descends (prefixWord ++ tailWord_805023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805037 : List Nat := [1, 5, 2, 1, 2, 1, 2, 3, 4]
def baseStart_805037 : Nat := 118140960795 + 805037 * 2 ^ 59
def prefixEnd_805037 : Nat := 4983230072969 + 3 ^ 40 * 805037 * 2
def baseEnd_805037 : Nat := 183720411401632010104537

theorem tailTrace_805037 : CollatzResearch.WordTrace tailWord_805037 prefixEnd_805037 183720411401632010104537 := by
  unfold tailWord_805037
  simp only [CollatzResearch.WordTrace]
  refine ⟨29362111584495913218621365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19574741056330608812414243 29362111584495913218621365)
  ·
    refine ⟨2752697961046491864245753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29362111584495913218621365 2752697961046491864245753)
    ·
      refine ⟨2064523470784868898184315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2752697961046491864245753 2064523470784868898184315)
      ·
        refine ⟨3096785206177303347276473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2064523470784868898184315 3096785206177303347276473)
        ·
          refine ⟨2322588904632977510457355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3096785206177303347276473 2322588904632977510457355)
          ·
            refine ⟨3483883356949466265686033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2322588904632977510457355 3483883356949466265686033)
            ·
              refine ⟨2612912517712099699264525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3483883356949466265686033 2612912517712099699264525)
              ·
                refine ⟨979842194142037387224197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2612912517712099699264525 979842194142037387224197)
                ·
                  refine ⟨183720411401632010104537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 979842194142037387224197 183720411401632010104537)
                  ·
                    rfl

theorem cell21_805037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_805037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_805037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_805037 prefixEnd_805037 := by exact prefixLift 805037
  have htrace : WordTrace (prefixWord ++ tailWord_805037) baseStart_805037 baseEnd_805037 := by
    simpa [prefixWord, tailWord_805037, baseEnd_805037] using wordTrace_append hprefix tailTrace_805037
  have hstable : (prefixWord ++ tailWord_805037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805037).length < 2 ^ (prefixWord ++ tailWord_805037).sum := by decide
  have hdescent : baseEnd_805037 < baseStart_805037 := by decide
  rcases family_descends (prefixWord ++ tailWord_805037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805082 : List Nat := [3, 1, 1, 2, 2, 1, 4, 4, 3]
def baseStart_805082 : Nat := 118140960795 + 805082 * 2 ^ 59
def prefixEnd_805082 : Nat := 4983230072969 + 3 ^ 40 * 805082 * 2
def baseEnd_805082 : Nat := 183730681014721931854445

theorem tailTrace_805082 : CollatzResearch.WordTrace tailWord_805082 prefixEnd_805082 183730681014721931854445 := by
  unfold tailWord_805082
  simp only [CollatzResearch.WordTrace]
  refine ⟨7340938217333221476002375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19575835246221923936006333 7340938217333221476002375)
  ·
    refine ⟨11011407325999832214003563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7340938217333221476002375 11011407325999832214003563)
    ·
      refine ⟨16517110988999748321005345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11011407325999832214003563 16517110988999748321005345)
      ·
        refine ⟨12387833241749811240754009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16517110988999748321005345 12387833241749811240754009)
        ·
          refine ⟨9290874931312358430565507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12387833241749811240754009 9290874931312358430565507)
          ·
            refine ⟨13936312396968537645848261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9290874931312358430565507 13936312396968537645848261)
            ·
              refine ⟨2613058574431600808596549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13936312396968537645848261 2613058574431600808596549)
              ·
                refine ⟨489948482705925151611853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2613058574431600808596549 489948482705925151611853)
                ·
                  refine ⟨183730681014721931854445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 489948482705925151611853 183730681014721931854445)
                  ·
                    rfl

theorem cell21_805082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_805082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_805082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_805082 prefixEnd_805082 := by exact prefixLift 805082
  have htrace : WordTrace (prefixWord ++ tailWord_805082) baseStart_805082 baseEnd_805082 := by
    simpa [prefixWord, tailWord_805082, baseEnd_805082] using wordTrace_append hprefix tailTrace_805082
  have hstable : (prefixWord ++ tailWord_805082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805082).length < 2 ^ (prefixWord ++ tailWord_805082).sum := by decide
  have hdescent : baseEnd_805082 < baseStart_805082 := by decide
  rcases family_descends (prefixWord ++ tailWord_805082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805141 : List Nat := [1, 3, 2, 1, 2, 1, 5, 1, 5]
def baseStart_805141 : Nat := 118140960795 + 805141 * 2 ^ 59
def prefixEnd_805141 : Nat := 4983230072969 + 3 ^ 40 * 805141 * 2
def baseEnd_805141 : Nat := 183744145618550940370991

theorem tailTrace_805141 : CollatzResearch.WordTrace tailWord_805141 prefixEnd_805141 183744145618550940370991 := by
  unfold tailWord_805141
  simp only [CollatzResearch.WordTrace]
  refine ⟨29365904776119138980407277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19577269850746092653604851 29365904776119138980407277)
  ·
    refine ⟨11012214291044677117652729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29365904776119138980407277 11012214291044677117652729)
    ·
      refine ⟨8259160718283507838239547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11012214291044677117652729 8259160718283507838239547)
      ·
        refine ⟨12388741077425261757359321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8259160718283507838239547 12388741077425261757359321)
        ·
          refine ⟨9291555808068946318019491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12388741077425261757359321 9291555808068946318019491)
          ·
            refine ⟨13937333712103419477029237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9291555808068946318019491 13937333712103419477029237)
            ·
              refine ⟨1306625035509695575971491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13937333712103419477029237 1306625035509695575971491)
              ·
                refine ⟨1959937553264543363957237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1306625035509695575971491 1959937553264543363957237)
                ·
                  refine ⟨183744145618550940370991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1959937553264543363957237 183744145618550940370991)
                  ·
                    rfl

theorem cell21_805141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_805141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_805141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_805141 prefixEnd_805141 := by exact prefixLift 805141
  have htrace : WordTrace (prefixWord ++ tailWord_805141) baseStart_805141 baseEnd_805141 := by
    simpa [prefixWord, tailWord_805141, baseEnd_805141] using wordTrace_append hprefix tailTrace_805141
  have hstable : (prefixWord ++ tailWord_805141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805141).length < 2 ^ (prefixWord ++ tailWord_805141).sum := by decide
  have hdescent : baseEnd_805141 < baseStart_805141 := by decide
  rcases family_descends (prefixWord ++ tailWord_805141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805234 : List Nat := [3, 2, 1, 2, 1, 3, 1, 5, 3]
def baseStart_805234 : Nat := 118140960795 + 805234 * 2 ^ 59
def prefixEnd_805234 : Nat := 4983230072969 + 3 ^ 40 * 805234 * 2
def baseEnd_805234 : Nat := 183765369485603445320801

theorem tailTrace_805234 : CollatzResearch.WordTrace tailWord_805234 prefixEnd_805234 183765369485603445320801 := by
  unfold tailWord_805234
  simp only [CollatzResearch.WordTrace]
  refine ⟨7342324191195553965885689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19579531176521477242361837 7342324191195553965885689)
  ·
    refine ⟨5506743143396665474414267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7342324191195553965885689 5506743143396665474414267)
    ·
      refine ⟨8260114715094998211621401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5506743143396665474414267 8260114715094998211621401)
      ·
        refine ⟨6195086036321248658716051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8260114715094998211621401 6195086036321248658716051)
        ·
          refine ⟨9292629054481872988074077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6195086036321248658716051 9292629054481872988074077)
          ·
            refine ⟨3484735895430702370527779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9292629054481872988074077 3484735895430702370527779)
            ·
              refine ⟨5227103843146053555791669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3484735895430702370527779 5227103843146053555791669)
              ·
                refine ⟨490040985294942520855469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5227103843146053555791669 490040985294942520855469)
                ·
                  refine ⟨183765369485603445320801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 490040985294942520855469 183765369485603445320801)
                  ·
                    rfl

theorem cell21_805234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_805234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_805234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_805234 prefixEnd_805234 := by exact prefixLift 805234
  have htrace : WordTrace (prefixWord ++ tailWord_805234) baseStart_805234 baseEnd_805234 := by
    simpa [prefixWord, tailWord_805234, baseEnd_805234] using wordTrace_append hprefix tailTrace_805234
  have hstable : (prefixWord ++ tailWord_805234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805234).length < 2 ^ (prefixWord ++ tailWord_805234).sum := by decide
  have hdescent : baseEnd_805234 < baseStart_805234 := by decide
  rcases family_descends (prefixWord ++ tailWord_805234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805310 : List Nat := [4, 2, 1, 1, 1, 1, 2, 6, 3]
def baseStart_805310 : Nat := 118140960795 + 805310 * 2 ^ 59
def prefixEnd_805310 : Nat := 4983230072969 + 3 ^ 40 * 805310 * 2
def baseEnd_805310 : Nat := 183782713721044202053979

theorem tailTrace_805310 : CollatzResearch.WordTrace tailWord_805310 prefixEnd_805310 183782713721044202053979 := by
  unfold tailWord_805310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3671508589063360105413673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19581379141671253895539589 3671508589063360105413673)
  ·
    refine ⟨2753631441797520079060255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3671508589063360105413673 2753631441797520079060255)
    ·
      refine ⟨4130447162696280118590383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2753631441797520079060255 4130447162696280118590383)
      ·
        refine ⟨6195670744044420177885575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4130447162696280118590383 6195670744044420177885575)
        ·
          refine ⟨9293506116066630266828363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6195670744044420177885575 9293506116066630266828363)
          ·
            refine ⟨13940259174099945400242545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9293506116066630266828363 13940259174099945400242545)
            ·
              refine ⟨10455194380574959050181909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13940259174099945400242545 10455194380574959050181909)
              ·
                refine ⟨490087236589451205477277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10455194380574959050181909 490087236589451205477277)
                ·
                  refine ⟨183782713721044202053979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 490087236589451205477277 183782713721044202053979)
                  ·
                    rfl

theorem cell21_805310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_805310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_805310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_805310 prefixEnd_805310 := by exact prefixLift 805310
  have htrace : WordTrace (prefixWord ++ tailWord_805310) baseStart_805310 baseEnd_805310 := by
    simpa [prefixWord, tailWord_805310, baseEnd_805310] using wordTrace_append hprefix tailTrace_805310
  have hstable : (prefixWord ++ tailWord_805310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805310).length < 2 ^ (prefixWord ++ tailWord_805310).sum := by decide
  have hdescent : baseEnd_805310 < baseStart_805310 := by decide
  rcases family_descends (prefixWord ++ tailWord_805310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805313 : List Nat := [1, 2, 7, 1, 1, 1, 2, 6]
def baseStart_805313 : Nat := 118140960795 + 805313 * 2 ^ 59
def prefixEnd_805313 : Nat := 4983230072969 + 3 ^ 40 * 805313 * 2
def baseEnd_805313 : Nat := 61261132787305621167991

theorem tailTrace_805313 : CollatzResearch.WordTrace tailWord_805313 prefixEnd_805313 61261132787305621167991 := by
  unfold tailWord_805313
  simp only [CollatzResearch.WordTrace]
  refine ⟨29372178131496012355668593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19581452087664008237112395 29372178131496012355668593)
  ·
    refine ⟨22029133598622009266751445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29372178131496012355668593 22029133598622009266751445)
    ·
      refine ⟨516307818717703342189487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 22029133598622009266751445 516307818717703342189487)
      ·
        refine ⟨774461728076555013284231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516307818717703342189487 774461728076555013284231)
        ·
          refine ⟨1161692592114832519926347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774461728076555013284231 1161692592114832519926347)
          ·
            refine ⟨1742538888172248779889521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161692592114832519926347 1742538888172248779889521)
            ·
              refine ⟨1306904166129186584917141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1742538888172248779889521 1306904166129186584917141)
              ·
                refine ⟨61261132787305621167991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1306904166129186584917141 61261132787305621167991)
                ·
                  rfl

theorem cell21_805313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 6].length) (baseStart_805313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_805313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_805313 prefixEnd_805313 := by exact prefixLift 805313
  have htrace : WordTrace (prefixWord ++ tailWord_805313) baseStart_805313 baseEnd_805313 := by
    simpa [prefixWord, tailWord_805313, baseEnd_805313] using wordTrace_append hprefix tailTrace_805313
  have hstable : (prefixWord ++ tailWord_805313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805313).length < 2 ^ (prefixWord ++ tailWord_805313).sum := by decide
  have hdescent : baseEnd_805313 < baseStart_805313 := by decide
  rcases family_descends (prefixWord ++ tailWord_805313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805321 : List Nat := [1, 2, 1, 1, 2, 1, 5, 8]
def baseStart_805321 : Nat := 118140960795 + 805321 * 2 ^ 59
def prefixEnd_805321 : Nat := 4983230072969 + 3 ^ 40 * 805321 * 2
def baseEnd_805321 : Nat := 61261741356970209123541

theorem tailTrace_805321 : CollatzResearch.WordTrace tailWord_805321 prefixEnd_805321 61261741356970209123541 := by
  unfold tailWord_805321
  simp only [CollatzResearch.WordTrace]
  refine ⟨29372469915467029721959817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19581646610311353147973211 29372469915467029721959817)
  ·
    refine ⟨22029352436600272291469863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29372469915467029721959817 22029352436600272291469863)
    ·
      refine ⟨33044028654900408437204795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22029352436600272291469863 33044028654900408437204795)
      ·
        refine ⟨49566042982350612655807193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33044028654900408437204795 49566042982350612655807193)
        ·
          refine ⟨37174532236762959491855395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49566042982350612655807193 37174532236762959491855395)
          ·
            refine ⟨55761798355144439237783093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37174532236762959491855395 55761798355144439237783093)
            ·
              refine ⟨5227668595794791178542165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55761798355144439237783093 5227668595794791178542165)
              ·
                refine ⟨61261741356970209123541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5227668595794791178542165 61261741356970209123541)
                ·
                  rfl

theorem cell21_805321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 8].length) (baseStart_805321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_805321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_805321 prefixEnd_805321 := by exact prefixLift 805321
  have htrace : WordTrace (prefixWord ++ tailWord_805321) baseStart_805321 baseEnd_805321 := by
    simpa [prefixWord, tailWord_805321, baseEnd_805321] using wordTrace_append hprefix tailTrace_805321
  have hstable : (prefixWord ++ tailWord_805321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805321).length < 2 ^ (prefixWord ++ tailWord_805321).sum := by decide
  have hdescent : baseEnd_805321 < baseStart_805321 := by decide
  rcases family_descends (prefixWord ++ tailWord_805321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805389 : List Nat := [1, 7, 1, 1, 1, 2, 3, 5]
def baseStart_805389 : Nat := 118140960795 + 805389 * 2 ^ 59
def prefixEnd_805389 : Nat := 4983230072969 + 3 ^ 40 * 805389 * 2
def baseEnd_805389 : Nat := 61266914199119206745717

theorem tailTrace_805389 : CollatzResearch.WordTrace tailWord_805389 prefixEnd_805389 61266914199119206745717 := by
  unfold tailWord_805389
  simp only [CollatzResearch.WordTrace]
  refine ⟨29374950079220677335435221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19583300052813784890290147 29374950079220677335435221)
  ·
    refine ⟨688475392481734625049263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 29374950079220677335435221 688475392481734625049263)
    ·
      refine ⟨1032713088722601937573895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 688475392481734625049263 1032713088722601937573895)
      ·
        refine ⟨1549069633083902906360843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1032713088722601937573895 1549069633083902906360843)
        ·
          refine ⟨2323604449625854359541265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1549069633083902906360843 2323604449625854359541265)
          ·
            refine ⟨1742703337219390769655949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2323604449625854359541265 1742703337219390769655949)
            ·
              refine ⟨653513751457271538620981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1742703337219390769655949 653513751457271538620981)
              ·
                refine ⟨61266914199119206745717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 653513751457271538620981 61266914199119206745717)
                ·
                  rfl

theorem cell21_805389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 5].length) (baseStart_805389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_805389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_805389 prefixEnd_805389 := by exact prefixLift 805389
  have htrace : WordTrace (prefixWord ++ tailWord_805389) baseStart_805389 baseEnd_805389 := by
    simpa [prefixWord, tailWord_805389, baseEnd_805389] using wordTrace_append hprefix tailTrace_805389
  have hstable : (prefixWord ++ tailWord_805389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805389).length < 2 ^ (prefixWord ++ tailWord_805389).sum := by decide
  have hdescent : baseEnd_805389 < baseStart_805389 := by decide
  rcases family_descends (prefixWord ++ tailWord_805389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805473 : List Nat := [1, 2, 3, 1, 1, 4, 9]
def baseStart_805473 : Nat := 118140960795 + 805473 * 2 ^ 59
def prefixEnd_805473 : Nat := 4983230072969 + 3 ^ 40 * 805473 * 2
def baseEnd_805473 : Nat := 20424434726865793426331

theorem tailTrace_805473 : CollatzResearch.WordTrace tailWord_805473 prefixEnd_805473 20424434726865793426331 := by
  unfold tailWord_805473
  simp only [CollatzResearch.WordTrace]
  refine ⟨29378013810916359681493073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19585342540610906454328715 29378013810916359681493073)
  ·
    refine ⟨22033510358187269761119805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29378013810916359681493073 22033510358187269761119805)
    ·
      refine ⟨8262566384320226160419927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22033510358187269761119805 8262566384320226160419927)
      ·
        refine ⟨12393849576480339240629891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8262566384320226160419927 12393849576480339240629891)
        ·
          refine ⟨18590774364720508860944837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12393849576480339240629891 18590774364720508860944837)
          ·
            refine ⟨3485770193385095411427157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18590774364720508860944837 3485770193385095411427157)
            ·
              refine ⟨20424434726865793426331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3485770193385095411427157 20424434726865793426331)
              ·
                rfl

theorem cell21_805473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 9].length) (baseStart_805473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_805473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_805473 prefixEnd_805473 := by exact prefixLift 805473
  have htrace : WordTrace (prefixWord ++ tailWord_805473) baseStart_805473 baseEnd_805473 := by
    simpa [prefixWord, tailWord_805473, baseEnd_805473] using wordTrace_append hprefix tailTrace_805473
  have hstable : (prefixWord ++ tailWord_805473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805473).length < 2 ^ (prefixWord ++ tailWord_805473).sum := by decide
  have hdescent : baseEnd_805473 < baseStart_805473 := by decide
  rcases family_descends (prefixWord ++ tailWord_805473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805493 : List Nat := [1, 3, 4, 2, 2, 1, 1, 3, 4]
def baseStart_805493 : Nat := 118140960795 + 805493 * 2 ^ 59
def prefixEnd_805493 : Nat := 4983230072969 + 3 ^ 40 * 805493 * 2
def baseEnd_805493 : Nat := 183824476814276550503605

theorem tailTrace_805493 : CollatzResearch.WordTrace tailWord_805493 prefixEnd_805493 183824476814276550503605 := by
  unfold tailWord_805493
  simp only [CollatzResearch.WordTrace]
  refine ⟨29378743270843903097221133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19585828847229268731480755 29378743270843903097221133)
  ·
    refine ⟨11017028726566463661457925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29378743270843903097221133 11017028726566463661457925)
    ·
      refine ⟨2065692886231211936523361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11017028726566463661457925 2065692886231211936523361)
      ·
        refine ⟨1549269664673408952392521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2065692886231211936523361 1549269664673408952392521)
        ·
          refine ⟨1161952248505056714294391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1549269664673408952392521 1161952248505056714294391)
          ·
            refine ⟨1742928372757585071441587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161952248505056714294391 1742928372757585071441587)
            ·
              refine ⟨2614392559136377607162381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1742928372757585071441587 2614392559136377607162381)
              ·
                refine ⟨980397209676141602685893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2614392559136377607162381 980397209676141602685893)
                ·
                  refine ⟨183824476814276550503605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 980397209676141602685893 183824476814276550503605)
                  ·
                    rfl

theorem cell21_805493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_805493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_805493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_805493 prefixEnd_805493 := by exact prefixLift 805493
  have htrace : WordTrace (prefixWord ++ tailWord_805493) baseStart_805493 baseEnd_805493 := by
    simpa [prefixWord, tailWord_805493, baseEnd_805493] using wordTrace_append hprefix tailTrace_805493
  have hstable : (prefixWord ++ tailWord_805493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805493).length < 2 ^ (prefixWord ++ tailWord_805493).sum := by decide
  have hdescent : baseEnd_805493 < baseStart_805493 := by decide
  rcases family_descends (prefixWord ++ tailWord_805493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805586 : List Nat := [3, 2, 2, 2, 4, 1, 1, 2, 4]
def baseStart_805586 : Nat := 118140960795 + 805586 * 2 ^ 59
def prefixEnd_805586 : Nat := 4983230072969 + 3 ^ 40 * 805586 * 2
def baseEnd_805586 : Nat := 183845700681329055453415

theorem tailTrace_805586 : CollatzResearch.WordTrace tailWord_805586 prefixEnd_805586 183845700681329055453415 := by
  unfold tailWord_805586
  simp only [CollatzResearch.WordTrace]
  refine ⟨7345533814876744995089153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19588090173004653320237741 7345533814876744995089153)
  ·
    refine ⟨5509150361157558746316865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7345533814876744995089153 5509150361157558746316865)
    ·
      refine ⟨4131862770868169059737649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5509150361157558746316865 4131862770868169059737649)
      ·
        refine ⟨3098897078151126794803237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4131862770868169059737649 3098897078151126794803237)
        ·
          refine ⟨581043202153336274025607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3098897078151126794803237 581043202153336274025607)
          ·
            refine ⟨871564803230004411038411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581043202153336274025607 871564803230004411038411)
            ·
              refine ⟨1307347204845006616557617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871564803230004411038411 1307347204845006616557617)
              ·
                refine ⟨980510403633754962418213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1307347204845006616557617 980510403633754962418213)
                ·
                  refine ⟨183845700681329055453415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 980510403633754962418213 183845700681329055453415)
                  ·
                    rfl

theorem cell21_805586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_805586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_805586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_805586 prefixEnd_805586 := by exact prefixLift 805586
  have htrace : WordTrace (prefixWord ++ tailWord_805586) baseStart_805586 baseEnd_805586 := by
    simpa [prefixWord, tailWord_805586, baseEnd_805586] using wordTrace_append hprefix tailTrace_805586
  have hstable : (prefixWord ++ tailWord_805586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805586).length < 2 ^ (prefixWord ++ tailWord_805586).sum := by decide
  have hdescent : baseEnd_805586 < baseStart_805586 := by decide
  rcases family_descends (prefixWord ++ tailWord_805586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805715 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 9]
def baseStart_805715 : Nat := 118140960795 + 805715 * 2 ^ 59
def prefixEnd_805715 : Nat := 4983230072969 + 3 ^ 40 * 805715 * 2
def baseEnd_805715 : Nat := 183875140238853497803151

theorem tailTrace_805715 : CollatzResearch.WordTrace tailWord_805715 prefixEnd_805715 183875140238853497803151 := by
  unfold tailWord_805715
  simp only [CollatzResearch.WordTrace]
  refine ⟨29386840276039635011802599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19591226850693090007868399 29386840276039635011802599)
  ·
    refine ⟨44080260414059452517703899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29386840276039635011802599 44080260414059452517703899)
    ·
      refine ⟨66120390621089178776555849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44080260414059452517703899 66120390621089178776555849)
      ·
        refine ⟨49590292965816884082416887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66120390621089178776555849 49590292965816884082416887)
        ·
          refine ⟨74385439448725326123625331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49590292965816884082416887 74385439448725326123625331)
          ·
            refine ⟨111578159173087989185437997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74385439448725326123625331 111578159173087989185437997)
            ·
              refine ⟨41841809689907995944539249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111578159173087989185437997 41841809689907995944539249)
              ·
                refine ⟨31381357267430996958404437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41841809689907995944539249 31381357267430996958404437)
                ·
                  refine ⟨183875140238853497803151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31381357267430996958404437 183875140238853497803151)
                  ·
                    rfl

theorem cell21_805715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 9].length) (baseStart_805715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_805715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_805715 prefixEnd_805715 := by exact prefixLift 805715
  have htrace : WordTrace (prefixWord ++ tailWord_805715) baseStart_805715 baseEnd_805715 := by
    simpa [prefixWord, tailWord_805715, baseEnd_805715] using wordTrace_append hprefix tailTrace_805715
  have hstable : (prefixWord ++ tailWord_805715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805715).length < 2 ^ (prefixWord ++ tailWord_805715).sum := by decide
  have hdescent : baseEnd_805715 < baseStart_805715 := by decide
  rcases family_descends (prefixWord ++ tailWord_805715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805732 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 7]
def baseStart_805732 : Nat := 118140960795 + 805732 * 2 ^ 59
def prefixEnd_805732 : Nat := 4983230072969 + 3 ^ 40 * 805732 * 2
def baseEnd_805732 : Nat := 183879019870465246019783

theorem tailTrace_805732 : CollatzResearch.WordTrace tailWord_805732 prefixEnd_805732 183879019870465246019783 := by
  unfold tailWord_805732
  simp only [CollatzResearch.WordTrace]
  refine ⟨14693730158489023457585725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19591640211318697943447633 14693730158489023457585725)
  ·
    refine ⟨5510148809433383796594647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14693730158489023457585725 5510148809433383796594647)
    ·
      refine ⟨8265223214150075694891971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5510148809433383796594647 8265223214150075694891971)
      ·
        refine ⟨12397834821225113542337957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8265223214150075694891971 12397834821225113542337957)
        ·
          refine ⟨2324594028979708789188367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12397834821225113542337957 2324594028979708789188367)
          ·
            refine ⟨3486891043469563183782551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2324594028979708789188367 3486891043469563183782551)
            ·
              refine ⟨5230336565204344775673827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3486891043469563183782551 5230336565204344775673827)
              ·
                refine ⟨7845504847806517163510741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5230336565204344775673827 7845504847806517163510741)
                ·
                  refine ⟨183879019870465246019783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7845504847806517163510741 183879019870465246019783)
                  ·
                    rfl

theorem cell21_805732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_805732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_805732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_805732 prefixEnd_805732 := by exact prefixLift 805732
  have htrace : WordTrace (prefixWord ++ tailWord_805732) baseStart_805732 baseEnd_805732 := by
    simpa [prefixWord, tailWord_805732, baseEnd_805732] using wordTrace_append hprefix tailTrace_805732
  have hstable : (prefixWord ++ tailWord_805732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805732).length < 2 ^ (prefixWord ++ tailWord_805732).sum := by decide
  have hdescent : baseEnd_805732 < baseStart_805732 := by decide
  rcases family_descends (prefixWord ++ tailWord_805732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805794 : List Nat := [3, 3, 1, 2, 2, 2, 1, 7]
def baseStart_805794 : Nat := 118140960795 + 805794 * 2 ^ 59
def prefixEnd_805794 : Nat := 4983230072969 + 3 ^ 40 * 805794 * 2
def baseEnd_805794 : Nat := 61297723038388971995441

theorem tailTrace_805794 : CollatzResearch.WordTrace tailWord_805794 prefixEnd_805794 61297723038388971995441 := by
  unfold tailWord_805794
  simp only [CollatzResearch.WordTrace]
  refine ⟨7347430410688357875982109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19593147761835621002618957 7347430410688357875982109)
  ·
    refine ⟨2755286404008134203493291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7347430410688357875982109 2755286404008134203493291)
    ·
      refine ⟨4132929606012201305239937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2755286404008134203493291 4132929606012201305239937)
      ·
        refine ⟨3099697204509150978929953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4132929606012201305239937 3099697204509150978929953)
        ·
          refine ⟨2324772903381863234197465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3099697204509150978929953 2324772903381863234197465)
          ·
            refine ⟨1743579677536397425648099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2324772903381863234197465 1743579677536397425648099)
            ·
              refine ⟨2615369516304596138472149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743579677536397425648099 2615369516304596138472149)
              ·
                refine ⟨61297723038388971995441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2615369516304596138472149 61297723038388971995441)
                ·
                  rfl

theorem cell21_805794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_805794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_805794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_805794 prefixEnd_805794 := by exact prefixLift 805794
  have htrace : WordTrace (prefixWord ++ tailWord_805794) baseStart_805794 baseEnd_805794 := by
    simpa [prefixWord, tailWord_805794, baseEnd_805794] using wordTrace_append hprefix tailTrace_805794
  have hstable : (prefixWord ++ tailWord_805794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805794).length < 2 ^ (prefixWord ++ tailWord_805794).sum := by decide
  have hdescent : baseEnd_805794 < baseStart_805794 := by decide
  rcases family_descends (prefixWord ++ tailWord_805794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805839 : List Nat := [1, 1, 2, 1, 1, 7, 1, 3, 4]
def baseStart_805839 : Nat := 118140960795 + 805839 * 2 ^ 59
def prefixEnd_805839 : Nat := 4983230072969 + 3 ^ 40 * 805839 * 2
def baseEnd_805839 : Nat := 183903438728256837736231

theorem tailTrace_805839 : CollatzResearch.WordTrace tailWord_805839 prefixEnd_805839 183903438728256837736231 := by
  unfold tailWord_805839
  simp only [CollatzResearch.WordTrace]
  refine ⟨29391362927590404189316571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19594241951726936126211047 29391362927590404189316571)
  ·
    refine ⟨44087044391385606283974857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29391362927590404189316571 44087044391385606283974857)
    ·
      refine ⟨33065283293539204712981143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44087044391385606283974857 33065283293539204712981143)
      ·
        refine ⟨49597924940308807069471715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33065283293539204712981143 49597924940308807069471715)
        ·
          refine ⟨74396887410463210604207573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49597924940308807069471715 74396887410463210604207573)
          ·
            refine ⟨1743677048682731498536115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 74396887410463210604207573 1743677048682731498536115)
            ·
              refine ⟨2615515573024097247804173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743677048682731498536115 2615515573024097247804173)
              ·
                refine ⟨980818339884036467926565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2615515573024097247804173 980818339884036467926565)
                ·
                  refine ⟨183903438728256837736231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 980818339884036467926565 183903438728256837736231)
                  ·
                    rfl

theorem cell21_805839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 4].length) (baseStart_805839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_805839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_805839 prefixEnd_805839 := by exact prefixLift 805839
  have htrace : WordTrace (prefixWord ++ tailWord_805839) baseStart_805839 baseEnd_805839 := by
    simpa [prefixWord, tailWord_805839, baseEnd_805839] using wordTrace_append hprefix tailTrace_805839
  have hstable : (prefixWord ++ tailWord_805839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805839).length < 2 ^ (prefixWord ++ tailWord_805839).sum := by decide
  have hdescent : baseEnd_805839 < baseStart_805839 := by decide
  rcases family_descends (prefixWord ++ tailWord_805839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805870 : List Nat := [4, 1, 2, 1, 5, 8]
def baseStart_805870 : Nat := 118140960795 + 805870 * 2 ^ 59
def prefixEnd_805870 : Nat := 4983230072969 + 3 ^ 40 * 805870 * 2
def baseEnd_805870 : Nat := 6811500494466950841463

theorem tailTrace_805870 : CollatzResearch.WordTrace tailWord_805870 prefixEnd_805870 6811500494466950841463 := by
  unfold tailWord_805870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3674061698809762060461883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19594995726985397655796709 3674061698809762060461883)
  ·
    refine ⟨5511092548214643090692825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3674061698809762060461883 5511092548214643090692825)
    ·
      refine ⟨4133319411160982318019619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5511092548214643090692825 4133319411160982318019619)
      ·
        refine ⟨6199979116741473477029429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4133319411160982318019619 6199979116741473477029429)
        ·
          refine ⟨581248042194513138471509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6199979116741473477029429 581248042194513138471509)
          ·
            refine ⟨6811500494466950841463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 581248042194513138471509 6811500494466950841463)
            ·
              rfl

theorem cell21_805870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 8].length) (baseStart_805870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_805870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_805870 prefixEnd_805870 := by exact prefixLift 805870
  have htrace : WordTrace (prefixWord ++ tailWord_805870) baseStart_805870 baseEnd_805870 := by
    simpa [prefixWord, tailWord_805870, baseEnd_805870] using wordTrace_append hprefix tailTrace_805870
  have hstable : (prefixWord ++ tailWord_805870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805870).length < 2 ^ (prefixWord ++ tailWord_805870).sum := by decide
  have hdescent : baseEnd_805870 < baseStart_805870 := by decide
  rcases family_descends (prefixWord ++ tailWord_805870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806019 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 7]
def baseStart_806019 : Nat := 118140960795 + 806019 * 2 ^ 59
def prefixEnd_806019 : Nat := 4983230072969 + 3 ^ 40 * 806019 * 2
def baseEnd_806019 : Nat := 183944517180616524735863

theorem tailTrace_806019 : CollatzResearch.WordTrace tailWord_806019 prefixEnd_806019 183944517180616524735863 := by
  unfold tailWord_806019
  simp only [CollatzResearch.WordTrace]
  refine ⟨29397928066938294930869111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19598618711292196620579407 29397928066938294930869111)
  ·
    refine ⟨44096892100407442396303667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29397928066938294930869111 44096892100407442396303667)
    ·
      refine ⟨66145338150611163594455501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44096892100407442396303667 66145338150611163594455501)
      ·
        refine ⟨24804501806479186347920813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66145338150611163594455501 24804501806479186347920813)
        ·
          refine ⟨9301688177429694880470305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24804501806479186347920813 9301688177429694880470305)
          ·
            refine ⟨6976266133072271160352729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9301688177429694880470305 6976266133072271160352729)
            ·
              refine ⟨5232199599804203370264547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6976266133072271160352729 5232199599804203370264547)
              ·
                refine ⟨7848299399706305055396821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5232199599804203370264547 7848299399706305055396821)
                ·
                  refine ⟨183944517180616524735863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7848299399706305055396821 183944517180616524735863)
                  ·
                    rfl

theorem cell21_806019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 7].length) (baseStart_806019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_806019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_806019 prefixEnd_806019 := by exact prefixLift 806019
  have htrace : WordTrace (prefixWord ++ tailWord_806019) baseStart_806019 baseEnd_806019 := by
    simpa [prefixWord, tailWord_806019, baseEnd_806019] using wordTrace_append hprefix tailTrace_806019
  have hstable : (prefixWord ++ tailWord_806019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806019).length < 2 ^ (prefixWord ++ tailWord_806019).sum := by decide
  have hdescent : baseEnd_806019 < baseStart_806019 := by decide
  rcases family_descends (prefixWord ++ tailWord_806019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806053 : List Nat := [1, 3, 1, 2, 1, 5, 1, 4, 3]
def baseStart_806053 : Nat := 118140960795 + 806053 * 2 ^ 59
def prefixEnd_806053 : Nat := 4983230072969 + 3 ^ 40 * 806053 * 2
def baseEnd_806053 : Nat := 183952276443840021169127

theorem tailTrace_806053 : CollatzResearch.WordTrace tailWord_806053 prefixEnd_806053 183952276443840021169127 := by
  unfold tailWord_806053
  simp only [CollatzResearch.WordTrace]
  refine ⟨29399168148815118737606813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19599445432543412491737875 29399168148815118737606813)
  ·
    refine ⟨11024688055805669526602555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29399168148815118737606813 11024688055805669526602555)
    ·
      refine ⟨16537032083708504289903833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11024688055805669526602555 16537032083708504289903833)
      ·
        refine ⟨12402774062781378217427875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16537032083708504289903833 12402774062781378217427875)
        ·
          refine ⟨18604161094172067326141813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12402774062781378217427875 18604161094172067326141813)
          ·
            refine ⟨1744140102578631311825795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18604161094172067326141813 1744140102578631311825795)
            ·
              refine ⟨2616210153867946967738693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1744140102578631311825795 2616210153867946967738693)
              ·
                refine ⟨490539403850240056451005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2616210153867946967738693 490539403850240056451005)
                ·
                  refine ⟨183952276443840021169127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 490539403850240056451005 183952276443840021169127)
                  ·
                    rfl

theorem cell21_806053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_806053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_806053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_806053 prefixEnd_806053 := by exact prefixLift 806053
  have htrace : WordTrace (prefixWord ++ tailWord_806053) baseStart_806053 baseEnd_806053 := by
    simpa [prefixWord, tailWord_806053, baseEnd_806053] using wordTrace_append hprefix tailTrace_806053
  have hstable : (prefixWord ++ tailWord_806053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806053).length < 2 ^ (prefixWord ++ tailWord_806053).sum := by decide
  have hdescent : baseEnd_806053 < baseStart_806053 := by decide
  rcases family_descends (prefixWord ++ tailWord_806053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806112 : List Nat := [2, 1, 1, 3, 1, 5, 2, 1, 5]
def baseStart_806112 : Nat := 118140960795 + 806112 * 2 ^ 59
def prefixEnd_806112 : Nat := 4983230072969 + 3 ^ 40 * 806112 * 2
def baseEnd_806112 : Nat := 183965741047669029685673

theorem tailTrace_806112 : CollatzResearch.WordTrace tailWord_806112 prefixEnd_806112 183965741047669029685673 := by
  unfold tailWord_806112
  simp only [CollatzResearch.WordTrace]
  refine ⟨14700660027800685907002295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19600880037067581209336393 14700660027800685907002295)
  ·
    refine ⟨22050990041701028860503443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14700660027800685907002295 22050990041701028860503443)
    ·
      refine ⟨33076485062551543290755165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22050990041701028860503443 33076485062551543290755165)
      ·
        refine ⟨12403681898456828734033187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33076485062551543290755165 12403681898456828734033187)
        ·
          refine ⟨18605522847685243101049781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12403681898456828734033187 18605522847685243101049781)
          ·
            refine ⟨1744267766970491540723417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18605522847685243101049781 1744267766970491540723417)
            ·
              refine ⟨1308200825227868655542563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1744267766970491540723417 1308200825227868655542563)
              ·
                refine ⟨1962301237841802983313845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1308200825227868655542563 1962301237841802983313845)
                ·
                  refine ⟨183965741047669029685673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1962301237841802983313845 183965741047669029685673)
                  ·
                    rfl

theorem cell21_806112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 5].length) (baseStart_806112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_806112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_806112 prefixEnd_806112 := by exact prefixLift 806112
  have htrace : WordTrace (prefixWord ++ tailWord_806112) baseStart_806112 baseEnd_806112 := by
    simpa [prefixWord, tailWord_806112, baseEnd_806112] using wordTrace_append hprefix tailTrace_806112
  have hstable : (prefixWord ++ tailWord_806112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806112).length < 2 ^ (prefixWord ++ tailWord_806112).sum := by decide
  have hdescent : baseEnd_806112 < baseStart_806112 := by decide
  rcases family_descends (prefixWord ++ tailWord_806112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806132 : List Nat := [2, 6, 1, 2, 1, 1, 1, 7]
def baseStart_806132 : Nat := 118140960795 + 806132 * 2 ^ 59
def prefixEnd_806132 : Nat := 4983230072969 + 3 ^ 40 * 806132 * 2
def baseEnd_806132 : Nat := 61323435106717813117433

theorem tailTrace_806132 : CollatzResearch.WordTrace tailWord_806132 prefixEnd_806132 61323435106717813117433 := by
  unfold tailWord_806132
  simp only [CollatzResearch.WordTrace]
  refine ⟨14701024757764457614866325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19601366343685943486488433 14701024757764457614866325)
  ·
    refine ⟨689110535520208950696859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14701024757764457614866325 689110535520208950696859)
    ·
      refine ⟨1033665803280313426045289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 689110535520208950696859 1033665803280313426045289)
      ·
        refine ⟨775249352460235069533967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1033665803280313426045289 775249352460235069533967)
        ·
          refine ⟨1162874028690352604300951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775249352460235069533967 1162874028690352604300951)
          ·
            refine ⟨1744311043035528906451427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162874028690352604300951 1744311043035528906451427)
            ·
              refine ⟨2616466564553293359677141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1744311043035528906451427 2616466564553293359677141)
              ·
                refine ⟨61323435106717813117433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2616466564553293359677141 61323435106717813117433)
                ·
                  rfl

theorem cell21_806132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 7].length) (baseStart_806132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_806132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_806132 prefixEnd_806132 := by exact prefixLift 806132
  have htrace : WordTrace (prefixWord ++ tailWord_806132) baseStart_806132 baseEnd_806132 := by
    simpa [prefixWord, tailWord_806132, baseEnd_806132] using wordTrace_append hprefix tailTrace_806132
  have hstable : (prefixWord ++ tailWord_806132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806132).length < 2 ^ (prefixWord ++ tailWord_806132).sum := by decide
  have hdescent : baseEnd_806132 < baseStart_806132 := by decide
  rcases family_descends (prefixWord ++ tailWord_806132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806214 : List Nat := [6, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_806214 : Nat := 118140960795 + 806214 * 2 ^ 59
def prefixEnd_806214 : Nat := 4983230072969 + 3 ^ 40 * 806214 * 2
def baseEnd_806214 : Nat := 183989018837339518985465

theorem tailTrace_806214 : CollatzResearch.WordTrace tailWord_806214 prefixEnd_806214 183989018837339518985465 := by
  unfold tailWord_806214
  simp only [CollatzResearch.WordTrace]
  refine ⟨918907509413495101069303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19603360200821228822811797 918907509413495101069303)
  ·
    refine ⟨1378361264120242651603955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 918907509413495101069303 1378361264120242651603955)
    ·
      refine ⟨2067541896180363977405933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1378361264120242651603955 2067541896180363977405933)
      ·
        refine ⟨775328211067636491527225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2067541896180363977405933 775328211067636491527225)
        ·
          refine ⟨581496158300727368645419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 775328211067636491527225 581496158300727368645419)
          ·
            refine ⟨872244237451091052968129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581496158300727368645419 872244237451091052968129)
            ·
              refine ⟨654183178088318289726097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 872244237451091052968129 654183178088318289726097)
              ·
                refine ⟨490637383566238717294573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 654183178088318289726097 490637383566238717294573)
                ·
                  refine ⟨183989018837339518985465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 490637383566238717294573 183989018837339518985465)
                  ·
                    rfl

theorem cell21_806214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_806214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_806214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_806214 prefixEnd_806214 := by exact prefixLift 806214
  have htrace : WordTrace (prefixWord ++ tailWord_806214) baseStart_806214 baseEnd_806214 := by
    simpa [prefixWord, tailWord_806214, baseEnd_806214] using wordTrace_append hprefix tailTrace_806214
  have hstable : (prefixWord ++ tailWord_806214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806214).length < 2 ^ (prefixWord ++ tailWord_806214).sum := by decide
  have hdescent : baseEnd_806214 < baseStart_806214 := by decide
  rcases family_descends (prefixWord ++ tailWord_806214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806270 : List Nat := [4, 2, 3, 2, 1, 2, 1, 2, 4]
def baseStart_806270 : Nat := 118140960795 + 806270 * 2 ^ 59
def prefixEnd_806270 : Nat := 4983230072969 + 3 ^ 40 * 806270 * 2
def baseEnd_806270 : Nat := 184001798800295866052017

theorem tailTrace_806270 : CollatzResearch.WordTrace tailWord_806270 prefixEnd_806270 184001798800295866052017 := by
  unfold tailWord_806270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3675885348628620599782033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19604721859352643198837509 3675885348628620599782033)
  ·
    refine ⟨2756914011471465449836525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3675885348628620599782033 2756914011471465449836525)
    ·
      refine ⟨1033842754301799543688697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2756914011471465449836525 1033842754301799543688697)
      ·
        refine ⟨775382065726349657766523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1033842754301799543688697 775382065726349657766523)
        ·
          refine ⟨1163073098589524486649785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775382065726349657766523 1163073098589524486649785)
          ·
            refine ⟨872304823942143364987339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1163073098589524486649785 872304823942143364987339)
            ·
              refine ⟨1308457235913215047481009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872304823942143364987339 1308457235913215047481009)
              ·
                refine ⟨981342926934911285610757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1308457235913215047481009 981342926934911285610757)
                ·
                  refine ⟨184001798800295866052017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 981342926934911285610757 184001798800295866052017)
                  ·
                    rfl

theorem cell21_806270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_806270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_806270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_806270 prefixEnd_806270 := by exact prefixLift 806270
  have htrace : WordTrace (prefixWord ++ tailWord_806270) baseStart_806270 baseEnd_806270 := by
    simpa [prefixWord, tailWord_806270, baseEnd_806270] using wordTrace_append hprefix tailTrace_806270
  have hstable : (prefixWord ++ tailWord_806270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806270).length < 2 ^ (prefixWord ++ tailWord_806270).sum := by decide
  have hdescent : baseEnd_806270 < baseStart_806270 := by decide
  rcases family_descends (prefixWord ++ tailWord_806270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806402 : List Nat := [3, 4, 1, 2, 1, 1, 3, 6]
def baseStart_806402 : Nat := 118140960795 + 806402 * 2 ^ 59
def prefixEnd_806402 : Nat := 4983230072969 + 3 ^ 40 * 806402 * 2
def baseEnd_806402 : Nat := 61343974332897656617249

theorem tailTrace_806402 : CollatzResearch.WordTrace tailWord_806402 prefixEnd_806402 61343974332897656617249 := by
  unfold tailWord_806402
  simp only [CollatzResearch.WordTrace]
  refine ⟨7352974306137687835515365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19607931483033834228040973 7352974306137687835515365)
  ·
    refine ⟨1378682682400816469159131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7352974306137687835515365 1378682682400816469159131)
    ·
      refine ⟨2068024023601224703738697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1378682682400816469159131 2068024023601224703738697)
      ·
        refine ⟨1551018017700918527804023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2068024023601224703738697 1551018017700918527804023)
        ·
          refine ⟨2326527026551377791706035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1551018017700918527804023 2326527026551377791706035)
          ·
            refine ⟨3489790539827066687559053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326527026551377791706035 3489790539827066687559053)
            ·
              refine ⟨1308671452435150007834645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3489790539827066687559053 1308671452435150007834645)
              ·
                refine ⟨61343974332897656617249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1308671452435150007834645 61343974332897656617249)
                ·
                  rfl

theorem cell21_806402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_806402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_806402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_806402 prefixEnd_806402 := by exact prefixLift 806402
  have htrace : WordTrace (prefixWord ++ tailWord_806402) baseStart_806402 baseEnd_806402 := by
    simpa [prefixWord, tailWord_806402, baseEnd_806402] using wordTrace_append hprefix tailTrace_806402
  have hstable : (prefixWord ++ tailWord_806402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806402).length < 2 ^ (prefixWord ++ tailWord_806402).sum := by decide
  have hdescent : baseEnd_806402 < baseStart_806402 := by decide
  rcases family_descends (prefixWord ++ tailWord_806402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806433 : List Nat := [1, 2, 3, 2, 2, 3, 2, 3, 3]
def baseStart_806433 : Nat := 118140960795 + 806433 * 2 ^ 59
def prefixEnd_806433 : Nat := 4983230072969 + 3 ^ 40 * 806433 * 2
def baseEnd_806433 : Nat := 184038997621043804835017

theorem tailTrace_806433 : CollatzResearch.WordTrace tailWord_806433 prefixEnd_806433 184038997621043804835017 := by
  unfold tailWord_806433
  simp only [CollatzResearch.WordTrace]
  refine ⟨29413027887438443636439953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19608685258292295757626635 29413027887438443636439953)
  ·
    refine ⟨22059770915578832727329965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29413027887438443636439953 22059770915578832727329965)
    ·
      refine ⟨8272414093342062272748737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22059770915578832727329965 8272414093342062272748737)
      ·
        refine ⟨6204310570006546704561553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8272414093342062272748737 6204310570006546704561553)
        ·
          refine ⟨4653232927504910028421165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6204310570006546704561553 4653232927504910028421165)
          ·
            refine ⟨1744962347814341260657937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4653232927504910028421165 1744962347814341260657937)
            ·
              refine ⟨1308721760860755945493453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1744962347814341260657937 1308721760860755945493453)
              ·
                refine ⟨490770660322783479560045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1308721760860755945493453 490770660322783479560045)
                ·
                  refine ⟨184038997621043804835017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 490770660322783479560045 184038997621043804835017)
                  ·
                    rfl

theorem cell21_806433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 3].length) (baseStart_806433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_806433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_806433 prefixEnd_806433 := by exact prefixLift 806433
  have htrace : WordTrace (prefixWord ++ tailWord_806433) baseStart_806433 baseEnd_806433 := by
    simpa [prefixWord, tailWord_806433, baseEnd_806433] using wordTrace_append hprefix tailTrace_806433
  have hstable : (prefixWord ++ tailWord_806433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806433).length < 2 ^ (prefixWord ++ tailWord_806433).sum := by decide
  have hdescent : baseEnd_806433 < baseStart_806433 := by decide
  rcases family_descends (prefixWord ++ tailWord_806433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806506 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 6]
def baseStart_806506 : Nat := 118140960795 + 806506 * 2 ^ 59
def prefixEnd_806506 : Nat := 4983230072969 + 3 ^ 40 * 806506 * 2
def baseEnd_806506 : Nat := 184055657215611900118201

theorem tailTrace_806506 : CollatzResearch.WordTrace tailWord_806506 prefixEnd_806506 184055657215611900118201 := by
  unfold tailWord_806506
  simp only [CollatzResearch.WordTrace]
  refine ⟨7353922604043494275961843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19610460277449318069231581 7353922604043494275961843)
  ·
    refine ⟨11030883906065241413942765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7353922604043494275961843 11030883906065241413942765)
    ·
      refine ⟨4136581464774465530228537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11030883906065241413942765 4136581464774465530228537)
      ·
        refine ⟨3102436098580849147671403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4136581464774465530228537 3102436098580849147671403)
        ·
          refine ⟨4653654147871273721507105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3102436098580849147671403 4653654147871273721507105)
          ·
            refine ⟨3490240610903455291130329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4653654147871273721507105 3490240610903455291130329)
            ·
              refine ⟨2617680458177591468347747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3490240610903455291130329 2617680458177591468347747)
              ·
                refine ⟨3926520687266387202521621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2617680458177591468347747 3926520687266387202521621)
                ·
                  refine ⟨184055657215611900118201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3926520687266387202521621 184055657215611900118201)
                  ·
                    rfl

theorem cell21_806506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_806506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_806506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_806506 prefixEnd_806506 := by exact prefixLift 806506
  have htrace : WordTrace (prefixWord ++ tailWord_806506) baseStart_806506 baseEnd_806506 := by
    simpa [prefixWord, tailWord_806506, baseEnd_806506] using wordTrace_append hprefix tailTrace_806506
  have hstable : (prefixWord ++ tailWord_806506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806506).length < 2 ^ (prefixWord ++ tailWord_806506).sum := by decide
  have hdescent : baseEnd_806506 < baseStart_806506 := by decide
  rcases family_descends (prefixWord ++ tailWord_806506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806509 : List Nat := [1, 5, 1, 1, 4, 2, 1, 1, 5]
def baseStart_806509 : Nat := 118140960795 + 806509 * 2 ^ 59
def prefixEnd_806509 : Nat := 4983230072969 + 3 ^ 40 * 806509 * 2
def baseEnd_806509 : Nat := 184056341856484561568195

theorem tailTrace_806509 : CollatzResearch.WordTrace tailWord_806509 prefixEnd_806509 184056341856484561568195 := by
  unfold tailWord_806509
  simp only [CollatzResearch.WordTrace]
  refine ⟨29415799835163108616206581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19610533223442072410804387 29415799835163108616206581)
  ·
    refine ⟨2757731234546541432769367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29415799835163108616206581 2757731234546541432769367)
    ·
      refine ⟨4136596851819812149154051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2757731234546541432769367 4136596851819812149154051)
      ·
        refine ⟨6204895277729718223731077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4136596851819812149154051 6204895277729718223731077)
        ·
          refine ⟨1163417864574322166949577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6204895277729718223731077 1163417864574322166949577)
          ·
            refine ⟨872563398430741625212183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1163417864574322166949577 872563398430741625212183)
            ·
              refine ⟨1308845097646112437818275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872563398430741625212183 1308845097646112437818275)
              ·
                refine ⟨1963267646469168656727413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1308845097646112437818275 1963267646469168656727413)
                ·
                  refine ⟨184056341856484561568195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1963267646469168656727413 184056341856484561568195)
                  ·
                    rfl

theorem cell21_806509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_806509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_806509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_806509 prefixEnd_806509 := by exact prefixLift 806509
  have htrace : WordTrace (prefixWord ++ tailWord_806509) baseStart_806509 baseEnd_806509 := by
    simpa [prefixWord, tailWord_806509, baseEnd_806509] using wordTrace_append hprefix tailTrace_806509
  have hstable : (prefixWord ++ tailWord_806509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806509).length < 2 ^ (prefixWord ++ tailWord_806509).sum := by decide
  have hdescent : baseEnd_806509 < baseStart_806509 := by decide
  rcases family_descends (prefixWord ++ tailWord_806509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806565 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 6]
def baseStart_806565 : Nat := 118140960795 + 806565 * 2 ^ 59
def prefixEnd_806565 : Nat := 4983230072969 + 3 ^ 40 * 806565 * 2
def baseEnd_806565 : Nat := 184069121819440908634747

theorem tailTrace_806565 : CollatzResearch.WordTrace tailWord_806565 prefixEnd_806565 184069121819440908634747 := by
  unfold tailWord_806565
  simp only [CollatzResearch.WordTrace]
  refine ⟨29417842322960230180245149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19611894881973486786830099 29417842322960230180245149)
  ·
    refine ⟨11031690871110086317591931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29417842322960230180245149 11031690871110086317591931)
    ·
      refine ⟨16547536306665129476387897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11031690871110086317591931 16547536306665129476387897)
      ·
        refine ⟨12410652229998847107290923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16547536306665129476387897 12410652229998847107290923)
        ·
          refine ⟨18615978344998270660936385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12410652229998847107290923 18615978344998270660936385)
          ·
            refine ⟨13961983758748702995702289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18615978344998270660936385 13961983758748702995702289)
            ·
              refine ⟨10471487819061527246776717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13961983758748702995702289 10471487819061527246776717)
              ·
                refine ⟨3926807932148072717541269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10471487819061527246776717 3926807932148072717541269)
                ·
                  refine ⟨184069121819440908634747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3926807932148072717541269 184069121819440908634747)
                  ·
                    rfl

theorem cell21_806565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_806565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_806565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_806565 prefixEnd_806565 := by exact prefixLift 806565
  have htrace : WordTrace (prefixWord ++ tailWord_806565) baseStart_806565 baseEnd_806565 := by
    simpa [prefixWord, tailWord_806565, baseEnd_806565] using wordTrace_append hprefix tailTrace_806565
  have hstable : (prefixWord ++ tailWord_806565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806565).length < 2 ^ (prefixWord ++ tailWord_806565).sum := by decide
  have hdescent : baseEnd_806565 < baseStart_806565 := by decide
  rcases family_descends (prefixWord ++ tailWord_806565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806658 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 8]
def baseStart_806658 : Nat := 118140960795 + 806658 * 2 ^ 59
def prefixEnd_806658 : Nat := 4983230072969 + 3 ^ 40 * 806658 * 2
def baseEnd_806658 : Nat := 184090345686493413584557

theorem tailTrace_806658 : CollatzResearch.WordTrace tailWord_806658 prefixEnd_806658 184090345686493413584557 := by
  unfold tailWord_806658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7355308577905826765845157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19614156207748871375587085 7355308577905826765845157)
  ·
    refine ⟨1379120358357342518595967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7355308577905826765845157 1379120358357342518595967)
    ·
      refine ⟨2068680537536013777893951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1379120358357342518595967 2068680537536013777893951)
      ·
        refine ⟨3103020806304020666840927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2068680537536013777893951 3103020806304020666840927)
        ·
          refine ⟨4654531209456031000261391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3103020806304020666840927 4654531209456031000261391)
          ·
            refine ⟨6981796814184046500392087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4654531209456031000261391 6981796814184046500392087)
            ·
              refine ⟨10472695221276069750588131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6981796814184046500392087 10472695221276069750588131)
              ·
                refine ⟨15709042831914104625882197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10472695221276069750588131 15709042831914104625882197)
                ·
                  refine ⟨184090345686493413584557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15709042831914104625882197 184090345686493413584557)
                  ·
                    rfl

theorem cell21_806658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_806658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_806658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_806658 prefixEnd_806658 := by exact prefixLift 806658
  have htrace : WordTrace (prefixWord ++ tailWord_806658) baseStart_806658 baseEnd_806658 := by
    simpa [prefixWord, tailWord_806658, baseEnd_806658] using wordTrace_append hprefix tailTrace_806658
  have hstable : (prefixWord ++ tailWord_806658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806658).length < 2 ^ (prefixWord ++ tailWord_806658).sum := by decide
  have hdescent : baseEnd_806658 < baseStart_806658 := by decide
  rcases family_descends (prefixWord ++ tailWord_806658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806692 : List Nat := [2, 3, 1, 3, 2, 3, 2, 1, 4]
def baseStart_806692 : Nat := 118140960795 + 806692 * 2 ^ 59
def prefixEnd_806692 : Nat := 4983230072969 + 3 ^ 40 * 806692 * 2
def baseEnd_806692 : Nat := 184098104949716910017821

theorem tailTrace_806692 : CollatzResearch.WordTrace tailWord_806692 prefixEnd_806692 184098104949716910017821 := by
  unfold tailWord_806692
  simp only [CollatzResearch.WordTrace]
  refine ⟨14711237196750065435059165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19614982929000087246745553 14711237196750065435059165)
  ·
    refine ⟨5516713948781274538147187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14711237196750065435059165 5516713948781274538147187)
    ·
      refine ⟨8275070923171911807220781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5516713948781274538147187 8275070923171911807220781)
      ·
        refine ⟨3103151596189466927707793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8275070923171911807220781 3103151596189466927707793)
        ·
          refine ⟨2327363697142100195780845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3103151596189466927707793 2327363697142100195780845)
          ·
            refine ⟨872761386428287573417817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2327363697142100195780845 872761386428287573417817)
            ·
              refine ⟨654571039821215680063363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 872761386428287573417817 654571039821215680063363)
              ·
                refine ⟨981856559731823520095045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654571039821215680063363 981856559731823520095045)
                ·
                  refine ⟨184098104949716910017821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 981856559731823520095045 184098104949716910017821)
                  ·
                    rfl

theorem cell21_806692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_806692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_806692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_806692 prefixEnd_806692 := by exact prefixLift 806692
  have htrace : WordTrace (prefixWord ++ tailWord_806692) baseStart_806692 baseEnd_806692 := by
    simpa [prefixWord, tailWord_806692, baseEnd_806692] using wordTrace_append hprefix tailTrace_806692
  have hstable : (prefixWord ++ tailWord_806692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806692).length < 2 ^ (prefixWord ++ tailWord_806692).sum := by decide
  have hdescent : baseEnd_806692 < baseStart_806692 := by decide
  rcases family_descends (prefixWord ++ tailWord_806692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806737 : List Nat := [1, 2, 2, 1, 5, 1, 4, 2, 3]
def baseStart_806737 : Nat := 118140960795 + 806737 * 2 ^ 59
def prefixEnd_806737 : Nat := 4983230072969 + 3 ^ 40 * 806737 * 2
def baseEnd_806737 : Nat := 184108374562806831767729

theorem tailTrace_806737 : CollatzResearch.WordTrace tailWord_806737 prefixEnd_806737 184108374562806831767729 := by
  unfold tailWord_806737
  simp only [CollatzResearch.WordTrace]
  refine ⟨29424115678337103555506465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19616077118891402370337643 29424115678337103555506465)
  ·
    refine ⟨22068086758752827666629849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29424115678337103555506465 22068086758752827666629849)
    ·
      refine ⟨16551065069064620749972387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22068086758752827666629849 16551065069064620749972387)
      ·
        refine ⟨24826597603596931124958581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16551065069064620749972387 24826597603596931124958581)
        ·
          refine ⟨2327493525337212292964867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24826597603596931124958581 2327493525337212292964867)
          ·
            refine ⟨3491240288005818439447301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2327493525337212292964867 3491240288005818439447301)
            ·
              refine ⟨654607554001090957396369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3491240288005818439447301 654607554001090957396369)
              ·
                refine ⟨490955665500818218047277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 654607554001090957396369 490955665500818218047277)
                ·
                  refine ⟨184108374562806831767729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 490955665500818218047277 184108374562806831767729)
                  ·
                    rfl

theorem cell21_806737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 3].length) (baseStart_806737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_806737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_806737 prefixEnd_806737 := by exact prefixLift 806737
  have htrace : WordTrace (prefixWord ++ tailWord_806737) baseStart_806737 baseEnd_806737 := by
    simpa [prefixWord, tailWord_806737, baseEnd_806737] using wordTrace_append hprefix tailTrace_806737
  have hstable : (prefixWord ++ tailWord_806737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806737).length < 2 ^ (prefixWord ++ tailWord_806737).sum := by decide
  have hdescent : baseEnd_806737 < baseStart_806737 := by decide
  rcases family_descends (prefixWord ++ tailWord_806737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806785 : List Nat := [1, 2, 4, 4, 2, 1, 1, 2, 4]
def baseStart_806785 : Nat := 118140960795 + 806785 * 2 ^ 59
def prefixEnd_806785 : Nat := 4983230072969 + 3 ^ 40 * 806785 * 2
def baseEnd_806785 : Nat := 184119328816769414967631

theorem tailTrace_806785 : CollatzResearch.WordTrace tailWord_806785 prefixEnd_806785 184119328816769414967631 := by
  unfold tailWord_806785
  simp only [CollatzResearch.WordTrace]
  refine ⟨29425866382163207753253809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19617244254775471835502539 29425866382163207753253809)
  ·
    refine ⟨22069399786622405814940357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29425866382163207753253809 22069399786622405814940357)
    ·
      refine ⟨4138012459991701090301317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22069399786622405814940357 4138012459991701090301317)
      ·
        refine ⟨775877336248443954431497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4138012459991701090301317 775877336248443954431497)
        ·
          refine ⟨581908002186332965823623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 775877336248443954431497 581908002186332965823623)
          ·
            refine ⟨872862003279499448735435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581908002186332965823623 872862003279499448735435)
            ·
              refine ⟨1309293004919249173103153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872862003279499448735435 1309293004919249173103153)
              ·
                refine ⟨981969753689436879827365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1309293004919249173103153 981969753689436879827365)
                ·
                  refine ⟨184119328816769414967631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 981969753689436879827365 184119328816769414967631)
                  ·
                    rfl

theorem cell21_806785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 4].length) (baseStart_806785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_806785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_806785 prefixEnd_806785 := by exact prefixLift 806785
  have htrace : WordTrace (prefixWord ++ tailWord_806785) baseStart_806785 baseEnd_806785 := by
    simpa [prefixWord, tailWord_806785, baseEnd_806785] using wordTrace_append hprefix tailTrace_806785
  have hstable : (prefixWord ++ tailWord_806785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806785).length < 2 ^ (prefixWord ++ tailWord_806785).sum := by decide
  have hdescent : baseEnd_806785 < baseStart_806785 := by decide
  rcases family_descends (prefixWord ++ tailWord_806785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806793 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 6]
def baseStart_806793 : Nat := 118140960795 + 806793 * 2 ^ 59
def prefixEnd_806793 : Nat := 4983230072969 + 3 ^ 40 * 806793 * 2
def baseEnd_806793 : Nat := 184121154525763178834281

theorem tailTrace_806793 : CollatzResearch.WordTrace tailWord_806793 prefixEnd_806793 184121154525763178834281 := by
  unfold tailWord_806793
  simp only [CollatzResearch.WordTrace]
  refine ⟨29426158166134225119545033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19617438777422816746363355 29426158166134225119545033)
  ·
    refine ⟨22069618624600668839658775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29426158166134225119545033 22069618624600668839658775)
    ·
      refine ⟨33104427936901003259488163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22069618624600668839658775 33104427936901003259488163)
      ·
        refine ⟨49656641905351504889232245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33104427936901003259488163 49656641905351504889232245)
        ·
          refine ⟨4655310178626703583365523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49656641905351504889232245 4655310178626703583365523)
          ·
            refine ⟨6982965267940055375048285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4655310178626703583365523 6982965267940055375048285)
            ·
              refine ⟨2618611975477520765643107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6982965267940055375048285 2618611975477520765643107)
              ·
                refine ⟨3927917963216281148464661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2618611975477520765643107 3927917963216281148464661)
                ·
                  refine ⟨184121154525763178834281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3927917963216281148464661 184121154525763178834281)
                  ·
                    rfl

theorem cell21_806793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_806793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_806793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_806793 prefixEnd_806793 := by exact prefixLift 806793
  have htrace : WordTrace (prefixWord ++ tailWord_806793) baseStart_806793 baseEnd_806793 := by
    simpa [prefixWord, tailWord_806793, baseEnd_806793] using wordTrace_append hprefix tailTrace_806793
  have hstable : (prefixWord ++ tailWord_806793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806793).length < 2 ^ (prefixWord ++ tailWord_806793).sum := by decide
  have hdescent : baseEnd_806793 < baseStart_806793 := by decide
  rcases family_descends (prefixWord ++ tailWord_806793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806962 : List Nat := [3, 2, 1, 1, 2, 3, 3, 2, 4]
def baseStart_806962 : Nat := 118140960795 + 806962 * 2 ^ 59
def prefixEnd_806962 : Nat := 4983230072969 + 3 ^ 40 * 806962 * 2
def baseEnd_806962 : Nat := 184159722628256440517269

theorem tailTrace_806962 : CollatzResearch.WordTrace tailWord_806962 prefixEnd_806962 184159722628256440517269 := by
  unfold tailWord_806962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7358080525630491745611785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19621548068347977988298093 7358080525630491745611785)
  ·
    refine ⟨5518560394222868809208839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7358080525630491745611785 5518560394222868809208839)
    ·
      refine ⟨8277840591334303213813259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5518560394222868809208839 8277840591334303213813259)
      ·
        refine ⟨12416760887001454820719889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8277840591334303213813259 12416760887001454820719889)
        ·
          refine ⟨9312570665251091115539917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12416760887001454820719889 9312570665251091115539917)
          ·
            refine ⟨3492213999469159168327469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9312570665251091115539917 3492213999469159168327469)
            ·
              refine ⟨1309580249800934688122801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3492213999469159168327469 1309580249800934688122801)
              ·
                refine ⟨982185187350701016092101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1309580249800934688122801 982185187350701016092101)
                ·
                  refine ⟨184159722628256440517269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 982185187350701016092101 184159722628256440517269)
                  ·
                    rfl

theorem cell21_806962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_806962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_806962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_806962 prefixEnd_806962 := by exact prefixLift 806962
  have htrace : WordTrace (prefixWord ++ tailWord_806962) baseStart_806962 baseEnd_806962 := by
    simpa [prefixWord, tailWord_806962, baseEnd_806962] using wordTrace_append hprefix tailTrace_806962
  have hstable : (prefixWord ++ tailWord_806962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806962).length < 2 ^ (prefixWord ++ tailWord_806962).sum := by decide
  have hdescent : baseEnd_806962 < baseStart_806962 := by decide
  rcases family_descends (prefixWord ++ tailWord_806962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807007 : List Nat := [1, 1, 2, 3, 1, 1, 2, 7, 3]
def baseStart_807007 : Nat := 118140960795 + 807007 * 2 ^ 59
def prefixEnd_807007 : Nat := 4983230072969 + 3 ^ 40 * 807007 * 2
def baseEnd_807007 : Nat := 184169992241346362267177

theorem tailTrace_807007 : CollatzResearch.WordTrace tailWord_807007 prefixEnd_807007 184169992241346362267177 := by
  unfold tailWord_807007
  simp only [CollatzResearch.WordTrace]
  refine ⟨29433963387358939667835275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19622642258239293111890183 29433963387358939667835275)
  ·
    refine ⟨44150945081038409501752913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29433963387358939667835275 44150945081038409501752913)
    ·
      refine ⟨33113208810778807126314685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44150945081038409501752913 33113208810778807126314685)
      ·
        refine ⟨12417453304042052672368007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33113208810778807126314685 12417453304042052672368007)
        ·
          refine ⟨18626179956063079008552011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12417453304042052672368007 18626179956063079008552011)
          ·
            refine ⟨27939269934094618512828017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18626179956063079008552011 27939269934094618512828017)
            ·
              refine ⟨20954452450570963884621013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27939269934094618512828017 20954452450570963884621013)
              ·
                refine ⟨491119979310256966045805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20954452450570963884621013 491119979310256966045805)
                ·
                  refine ⟨184169992241346362267177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 491119979310256966045805 184169992241346362267177)
                  ·
                    rfl

theorem cell21_807007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 3].length) (baseStart_807007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807007 prefixEnd_807007 := by exact prefixLift 807007
  have htrace : WordTrace (prefixWord ++ tailWord_807007) baseStart_807007 baseEnd_807007 := by
    simpa [prefixWord, tailWord_807007, baseEnd_807007] using wordTrace_append hprefix tailTrace_807007
  have hstable : (prefixWord ++ tailWord_807007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807007).length < 2 ^ (prefixWord ++ tailWord_807007).sum := by decide
  have hdescent : baseEnd_807007 < baseStart_807007 := by decide
  rcases family_descends (prefixWord ++ tailWord_807007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807010 : List Nat := [3, 3, 2, 2, 3, 1, 7]
def baseStart_807010 : Nat := 118140960795 + 807010 * 2 ^ 59
def prefixEnd_807010 : Nat := 4983230072969 + 3 ^ 40 * 807010 * 2
def baseEnd_807010 : Nat := 20463408542468780413019

theorem tailTrace_807010 : CollatzResearch.WordTrace tailWord_807010 prefixEnd_807010 20463408542468780413019 := by
  unfold tailWord_807010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7358518201587017795048621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19622715204232047453462989 7358518201587017795048621)
  ·
    refine ⟨2759444325595131673143233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7358518201587017795048621 2759444325595131673143233)
    ·
      refine ⟨2069583244196348754857425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2759444325595131673143233 2069583244196348754857425)
      ·
        refine ⟨1552187433147261566143069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2069583244196348754857425 1552187433147261566143069)
        ·
          refine ⟨582070287430223087303651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1552187433147261566143069 582070287430223087303651)
          ·
            refine ⟨873105431145334630955477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582070287430223087303651 873105431145334630955477)
            ·
              refine ⟨20463408542468780413019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 873105431145334630955477 20463408542468780413019)
              ·
                rfl

theorem cell21_807010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 7].length) (baseStart_807010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807010 prefixEnd_807010 := by exact prefixLift 807010
  have htrace : WordTrace (prefixWord ++ tailWord_807010) baseStart_807010 baseEnd_807010 := by
    simpa [prefixWord, tailWord_807010, baseEnd_807010] using wordTrace_append hprefix tailTrace_807010
  have hstable : (prefixWord ++ tailWord_807010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807010).length < 2 ^ (prefixWord ++ tailWord_807010).sum := by decide
  have hdescent : baseEnd_807010 < baseStart_807010 := by decide
  rcases family_descends (prefixWord ++ tailWord_807010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807021 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 6]
def baseStart_807021 : Nat := 118140960795 + 807021 * 2 ^ 59
def prefixEnd_807021 : Nat := 4983230072969 + 3 ^ 40 * 807021 * 2
def baseEnd_807021 : Nat := 184173187232085449033815

theorem tailTrace_807021 : CollatzResearch.WordTrace tailWord_807021 prefixEnd_807021 184173187232085449033815 := by
  unfold tailWord_807021
  simp only [CollatzResearch.WordTrace]
  refine ⟨29434474009308220058844917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19622982672872146705896611 29434474009308220058844917)
  ·
    refine ⟨2759481938372645630516711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29434474009308220058844917 2759481938372645630516711)
    ·
      refine ⟨4139222907558968445775067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2759481938372645630516711 4139222907558968445775067)
      ·
        refine ⟨6208834361338452668662601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4139222907558968445775067 6208834361338452668662601)
        ·
          refine ⟨4656625771003839501496951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6208834361338452668662601 4656625771003839501496951)
          ·
            refine ⟨6984938656505759252245427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4656625771003839501496951 6984938656505759252245427)
            ·
              refine ⟨10477407984758638878368141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6984938656505759252245427 10477407984758638878368141)
              ·
                refine ⟨3929027994284489579388053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10477407984758638878368141 3929027994284489579388053)
                ·
                  refine ⟨184173187232085449033815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3929027994284489579388053 184173187232085449033815)
                  ·
                    rfl

theorem cell21_807021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_807021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807021 prefixEnd_807021 := by exact prefixLift 807021
  have htrace : WordTrace (prefixWord ++ tailWord_807021) baseStart_807021 baseEnd_807021 := by
    simpa [prefixWord, tailWord_807021, baseEnd_807021] using wordTrace_append hprefix tailTrace_807021
  have hstable : (prefixWord ++ tailWord_807021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807021).length < 2 ^ (prefixWord ++ tailWord_807021).sum := by decide
  have hdescent : baseEnd_807021 < baseStart_807021 := by decide
  rcases family_descends (prefixWord ++ tailWord_807021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807097 : List Nat := [1, 2, 1, 4, 1, 2, 1, 5, 4]
def baseStart_807097 : Nat := 118140960795 + 807097 * 2 ^ 59
def prefixEnd_807097 : Nat := 4983230072969 + 3 ^ 40 * 807097 * 2
def baseEnd_807097 : Nat := 184190531467526205766993

theorem tailTrace_807097 : CollatzResearch.WordTrace tailWord_807097 prefixEnd_807097 184190531467526205766993 := by
  unfold tailWord_807097
  simp only [CollatzResearch.WordTrace]
  refine ⟨29437245957032885038611545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19624830638021923359074363 29437245957032885038611545)
  ·
    refine ⟨22077934467774663778958659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29437245957032885038611545 22077934467774663778958659)
    ·
      refine ⟨33116901701661995668437989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22077934467774663778958659 33116901701661995668437989)
      ·
        refine ⟨6209419069061624187832123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33116901701661995668437989 6209419069061624187832123)
        ·
          refine ⟨9314128603592436281748185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6209419069061624187832123 9314128603592436281748185)
          ·
            refine ⟨6985596452694327211311139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9314128603592436281748185 6985596452694327211311139)
            ·
              refine ⟨10478394679041490816966709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6985596452694327211311139 10478394679041490816966709)
              ·
                refine ⟨982349501160139764090629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10478394679041490816966709 982349501160139764090629)
                ·
                  refine ⟨184190531467526205766993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 982349501160139764090629 184190531467526205766993)
                  ·
                    rfl

theorem cell21_807097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 4].length) (baseStart_807097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807097 prefixEnd_807097 := by exact prefixLift 807097
  have htrace : WordTrace (prefixWord ++ tailWord_807097) baseStart_807097 baseEnd_807097 := by
    simpa [prefixWord, tailWord_807097, baseEnd_807097] using wordTrace_append hprefix tailTrace_807097
  have hstable : (prefixWord ++ tailWord_807097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807097).length < 2 ^ (prefixWord ++ tailWord_807097).sum := by decide
  have hdescent : baseEnd_807097 < baseStart_807097 := by decide
  rcases family_descends (prefixWord ++ tailWord_807097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807176 : List Nat := [2, 1, 3, 2, 3, 1, 3, 3, 3]
def baseStart_807176 : Nat := 118140960795 + 807176 * 2 ^ 59
def prefixEnd_807176 : Nat := 4983230072969 + 3 ^ 40 * 807176 * 2
def baseEnd_807176 : Nat := 184208560343839623950165

theorem tailTrace_807176 : CollatzResearch.WordTrace tailWord_807176 prefixEnd_807176 184208560343839623950165 := by
  unfold tailWord_807176
  simp only [CollatzResearch.WordTrace]
  refine ⟨14720063661873340765368691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19626751549164454353824921 14720063661873340765368691)
  ·
    refine ⟨22080095492810011148053037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14720063661873340765368691 22080095492810011148053037)
    ·
      refine ⟨8280035809803754180519889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22080095492810011148053037 8280035809803754180519889)
      ·
        refine ⟨6210026857352815635389917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8280035809803754180519889 6210026857352815635389917)
        ·
          refine ⟨2328760071507305863271219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6210026857352815635389917 2328760071507305863271219)
          ·
            refine ⟨3493140107260958794906829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2328760071507305863271219 3493140107260958794906829)
            ·
              refine ⟨1309927540222859548090061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3493140107260958794906829 1309927540222859548090061)
              ·
                refine ⟨491222827583572330533773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1309927540222859548090061 491222827583572330533773)
                ·
                  refine ⟨184208560343839623950165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 491222827583572330533773 184208560343839623950165)
                  ·
                    rfl

theorem cell21_807176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 3].length) (baseStart_807176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807176 prefixEnd_807176 := by exact prefixLift 807176
  have htrace : WordTrace (prefixWord ++ tailWord_807176) baseStart_807176 baseEnd_807176 := by
    simpa [prefixWord, tailWord_807176, baseEnd_807176] using wordTrace_append hprefix tailTrace_807176
  have hstable : (prefixWord ++ tailWord_807176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807176).length < 2 ^ (prefixWord ++ tailWord_807176).sum := by decide
  have hdescent : baseEnd_807176 < baseStart_807176 := by decide
  rcases family_descends (prefixWord ++ tailWord_807176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807204 : List Nat := [2, 3, 1, 3, 1, 3, 2, 6]
def baseStart_807204 : Nat := 118140960795 + 807204 * 2 ^ 59
def prefixEnd_807204 : Nat := 4983230072969 + 3 ^ 40 * 807204 * 2
def baseEnd_807204 : Nat := 61404983441772599161147

theorem tailTrace_807204 : CollatzResearch.WordTrace tailWord_807204 prefixEnd_807204 61404983441772599161147 := by
  unfold tailWord_807204
  simp only [CollatzResearch.WordTrace]
  refine ⟨14720574283822621156378333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19627432378430161541837777 14720574283822621156378333)
  ·
    refine ⟨5520215356433482933641875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14720574283822621156378333 5520215356433482933641875)
    ·
      refine ⟨8280323034650224400462813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5520215356433482933641875 8280323034650224400462813)
      ·
        refine ⟨3105121137993834150173555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8280323034650224400462813 3105121137993834150173555)
        ·
          refine ⟨4657681706990751225260333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3105121137993834150173555 4657681706990751225260333)
          ·
            refine ⟨1746630640121531709472625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4657681706990751225260333 1746630640121531709472625)
            ·
              refine ⟨1309972980091148782104469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1746630640121531709472625 1309972980091148782104469)
              ·
                refine ⟨61404983441772599161147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1309972980091148782104469 61404983441772599161147)
                ·
                  rfl

theorem cell21_807204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 6].length) (baseStart_807204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807204 prefixEnd_807204 := by exact prefixLift 807204
  have htrace : WordTrace (prefixWord ++ tailWord_807204) baseStart_807204 baseEnd_807204 := by
    simpa [prefixWord, tailWord_807204, baseEnd_807204] using wordTrace_append hprefix tailTrace_807204
  have hstable : (prefixWord ++ tailWord_807204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807204).length < 2 ^ (prefixWord ++ tailWord_807204).sum := by decide
  have hdescent : baseEnd_807204 < baseStart_807204 := by decide
  rcases family_descends (prefixWord ++ tailWord_807204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807232 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 6]
def baseStart_807232 : Nat := 118140960795 + 807232 * 2 ^ 59
def prefixEnd_807232 : Nat := 4983230072969 + 3 ^ 40 * 807232 * 2
def baseEnd_807232 : Nat := 184221340306795971016717

theorem tailTrace_807232 : CollatzResearch.WordTrace tailWord_807232 prefixEnd_807232 184221340306795971016717 := by
  unfold tailWord_807232
  simp only [CollatzResearch.WordTrace]
  refine ⟨14721084905771901547387975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19628113207695868729850633 14721084905771901547387975)
  ·
    refine ⟨22081627358657852321081963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14721084905771901547387975 22081627358657852321081963)
    ·
      refine ⟨33122441037986778481622945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22081627358657852321081963 33122441037986778481622945)
      ·
        refine ⟨24841830778490083861217209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33122441037986778481622945 24841830778490083861217209)
        ·
          refine ⟨18631373083867562895912907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24841830778490083861217209 18631373083867562895912907)
          ·
            refine ⟨27947059625801344343869361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18631373083867562895912907 27947059625801344343869361)
            ·
              refine ⟨20960294719351008257902021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27947059625801344343869361 20960294719351008257902021)
              ·
                refine ⟨3930055259878314048356629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20960294719351008257902021 3930055259878314048356629)
                ·
                  refine ⟨184221340306795971016717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3930055259878314048356629 184221340306795971016717)
                  ·
                    rfl

theorem cell21_807232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_807232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807232 prefixEnd_807232 := by exact prefixLift 807232
  have htrace : WordTrace (prefixWord ++ tailWord_807232) baseStart_807232 baseEnd_807232 := by
    simpa [prefixWord, tailWord_807232, baseEnd_807232] using wordTrace_append hprefix tailTrace_807232
  have hstable : (prefixWord ++ tailWord_807232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807232).length < 2 ^ (prefixWord ++ tailWord_807232).sum := by decide
  have hdescent : baseEnd_807232 < baseStart_807232 := by decide
  rcases family_descends (prefixWord ++ tailWord_807232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807249 : List Nat := [1, 2, 2, 1, 4, 2, 1, 4, 4]
def baseStart_807249 : Nat := 118140960795 + 807249 * 2 ^ 59
def prefixEnd_807249 : Nat := 4983230072969 + 3 ^ 40 * 807249 * 2
def baseEnd_807249 : Nat := 184225219938407719233349

theorem tailTrace_807249 : CollatzResearch.WordTrace tailWord_807249 prefixEnd_807249 184225219938407719233349 := by
  unfold tailWord_807249
  simp only [CollatzResearch.WordTrace]
  refine ⟨29442789852482214998144801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19628526568321476665429867 29442789852482214998144801)
  ·
    refine ⟨22082092389361661248608601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29442789852482214998144801 22082092389361661248608601)
    ·
      refine ⟨16561569292021245936456451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22082092389361661248608601 16561569292021245936456451)
      ·
        refine ⟨24842353938031868904684677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16561569292021245936456451 24842353938031868904684677)
        ·
          refine ⟨4657941363380975419628377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24842353938031868904684677 4657941363380975419628377)
          ·
            refine ⟨3493456022535731564721283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4657941363380975419628377 3493456022535731564721283)
            ·
              refine ⟨5240184033803597347081925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3493456022535731564721283 5240184033803597347081925)
              ·
                refine ⟨982534506338174502577861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5240184033803597347081925 982534506338174502577861)
                ·
                  refine ⟨184225219938407719233349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 982534506338174502577861 184225219938407719233349)
                  ·
                    rfl

theorem cell21_807249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 4].length) (baseStart_807249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807249 prefixEnd_807249 := by exact prefixLift 807249
  have htrace : WordTrace (prefixWord ++ tailWord_807249) baseStart_807249 baseEnd_807249 := by
    simpa [prefixWord, tailWord_807249, baseEnd_807249] using wordTrace_append hprefix tailTrace_807249
  have hstable : (prefixWord ++ tailWord_807249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807249).length < 2 ^ (prefixWord ++ tailWord_807249).sum := by decide
  have hdescent : baseEnd_807249 < baseStart_807249 := by decide
  rcases family_descends (prefixWord ++ tailWord_807249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807252 : List Nat := [2, 4, 1, 1, 2, 3, 1, 4, 3]
def baseStart_807252 : Nat := 118140960795 + 807252 * 2 ^ 59
def prefixEnd_807252 : Nat := 4983230072969 + 3 ^ 40 * 807252 * 2
def baseEnd_807252 : Nat := 184225904579280380683343

theorem tailTrace_807252 : CollatzResearch.WordTrace tailWord_807252 prefixEnd_807252 184225904579280380683343 := by
  unfold tailWord_807252
  simp only [CollatzResearch.WordTrace]
  refine ⟨14721449635735673255252005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19628599514314231007002673 14721449635735673255252005)
  ·
    refine ⟨2760271806700438735359751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14721449635735673255252005 2760271806700438735359751)
    ·
      refine ⟨4140407710050658103039627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2760271806700438735359751 4140407710050658103039627)
      ·
        refine ⟨6210611565075987154559441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4140407710050658103039627 6210611565075987154559441)
        ·
          refine ⟨4657958673806990365919581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6210611565075987154559441 4657958673806990365919581)
          ·
            refine ⟨1746734502677621387219843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4657958673806990365919581 1746734502677621387219843)
            ·
              refine ⟨2620101754016432080829765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1746734502677621387219843 2620101754016432080829765)
              ·
                refine ⟨491269078878081015155581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2620101754016432080829765 491269078878081015155581)
                ·
                  refine ⟨184225904579280380683343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 491269078878081015155581 184225904579280380683343)
                  ·
                    rfl

theorem cell21_807252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_807252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807252 prefixEnd_807252 := by exact prefixLift 807252
  have htrace : WordTrace (prefixWord ++ tailWord_807252) baseStart_807252 baseEnd_807252 := by
    simpa [prefixWord, tailWord_807252, baseEnd_807252] using wordTrace_append hprefix tailTrace_807252
  have hstable : (prefixWord ++ tailWord_807252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807252).length < 2 ^ (prefixWord ++ tailWord_807252).sum := by decide
  have hdescent : baseEnd_807252 < baseStart_807252 := by decide
  rcases family_descends (prefixWord ++ tailWord_807252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807263 : List Nat := [1, 1, 2, 3, 1, 2, 5, 6]
def baseStart_807263 : Nat := 118140960795 + 807263 * 2 ^ 59
def prefixEnd_807263 : Nat := 4983230072969 + 3 ^ 40 * 807263 * 2
def baseEnd_807263 : Nat := 61409471643048935333329

theorem tailTrace_807263 : CollatzResearch.WordTrace tailWord_807263 prefixEnd_807263 61409471643048935333329 := by
  unfold tailWord_807263
  simp only [CollatzResearch.WordTrace]
  refine ⟨29443300474431495389154443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19628866982954330259436295 29443300474431495389154443)
  ·
    refine ⟨44164950711647243083731665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29443300474431495389154443 44164950711647243083731665)
    ·
      refine ⟨33123713033735432312798749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44164950711647243083731665 33123713033735432312798749)
      ·
        refine ⟨12421392387650787117299531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33123713033735432312798749 12421392387650787117299531)
        ·
          refine ⟨18632088581476180675949297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12421392387650787117299531 18632088581476180675949297)
          ·
            refine ⟨13974066436107135506961973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18632088581476180675949297 13974066436107135506961973)
            ·
              refine ⟨1310068728385043953777685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13974066436107135506961973 1310068728385043953777685)
              ·
                refine ⟨61409471643048935333329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1310068728385043953777685 61409471643048935333329)
                ·
                  rfl

theorem cell21_807263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 6].length) (baseStart_807263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807263 prefixEnd_807263 := by exact prefixLift 807263
  have htrace : WordTrace (prefixWord ++ tailWord_807263) baseStart_807263 baseEnd_807263 := by
    simpa [prefixWord, tailWord_807263, baseEnd_807263] using wordTrace_append hprefix tailTrace_807263
  have hstable : (prefixWord ++ tailWord_807263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807263).length < 2 ^ (prefixWord ++ tailWord_807263).sum := by decide
  have hdescent : baseEnd_807263 < baseStart_807263 := by decide
  rcases family_descends (prefixWord ++ tailWord_807263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807266 : List Nat := [3, 3, 2, 1, 1, 2, 2, 3, 4]
def baseStart_807266 : Nat := 118140960795 + 807266 * 2 ^ 59
def prefixEnd_807266 : Nat := 4983230072969 + 3 ^ 40 * 807266 * 2
def baseEnd_807266 : Nat := 184229099570019467449981

theorem tailTrace_807266 : CollatzResearch.WordTrace tailWord_807266 prefixEnd_807266 184229099570019467449981 := by
  unfold tailWord_807266
  simp only [CollatzResearch.WordTrace]
  refine ⟨7360852473355156725378413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19628939928947084601009101 7360852473355156725378413)
  ·
    refine ⟨2760319677508183772016905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7360852473355156725378413 2760319677508183772016905)
    ·
      refine ⟨2070239758131137829012679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2760319677508183772016905 2070239758131137829012679)
      ·
        refine ⟨3105359637196706743519019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2070239758131137829012679 3105359637196706743519019)
        ·
          refine ⟨4658039455795060115278529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3105359637196706743519019 4658039455795060115278529)
          ·
            refine ⟨3493529591846295086458897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4658039455795060115278529 3493529591846295086458897)
            ·
              refine ⟨2620147193884721314844173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3493529591846295086458897 2620147193884721314844173)
              ·
                refine ⟨982555197706770493066565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2620147193884721314844173 982555197706770493066565)
                ·
                  refine ⟨184229099570019467449981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 982555197706770493066565 184229099570019467449981)
                  ·
                    rfl

theorem cell21_807266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_807266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807266 prefixEnd_807266 := by exact prefixLift 807266
  have htrace : WordTrace (prefixWord ++ tailWord_807266) baseStart_807266 baseEnd_807266 := by
    simpa [prefixWord, tailWord_807266, baseEnd_807266] using wordTrace_append hprefix tailTrace_807266
  have hstable : (prefixWord ++ tailWord_807266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807266).length < 2 ^ (prefixWord ++ tailWord_807266).sum := by decide
  have hdescent : baseEnd_807266 < baseStart_807266 := by decide
  rcases family_descends (prefixWord ++ tailWord_807266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807280 : List Nat := [2, 1, 1, 1, 4, 4, 3, 5]
def baseStart_807280 : Nat := 118140960795 + 807280 * 2 ^ 59
def prefixEnd_807280 : Nat := 4983230072969 + 3 ^ 40 * 807280 * 2
def baseEnd_807280 : Nat := 61410764853586184738873

theorem tailTrace_807280 : CollatzResearch.WordTrace tailWord_807280 prefixEnd_807280 61410764853586184738873 := by
  unfold tailWord_807280
  simp only [CollatzResearch.WordTrace]
  refine ⟨14721960257684953646261647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19629280343579938195015529 14721960257684953646261647)
  ·
    refine ⟨22082940386527430469392471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14721960257684953646261647 22082940386527430469392471)
    ·
      refine ⟨33124410579791145704088707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22082940386527430469392471 33124410579791145704088707)
      ·
        refine ⟨49686615869686718556133061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33124410579791145704088707 49686615869686718556133061)
        ·
          refine ⟨9316240475566259729274949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49686615869686718556133061 9316240475566259729274949)
          ·
            refine ⟨1746795089168673699239053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9316240475566259729274949 1746795089168673699239053)
            ·
              refine ⟨655048158438252637214645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1746795089168673699239053 655048158438252637214645)
              ·
                refine ⟨61410764853586184738873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 655048158438252637214645 61410764853586184738873)
                ·
                  rfl

theorem cell21_807280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 5].length) (baseStart_807280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807280 prefixEnd_807280 := by exact prefixLift 807280
  have htrace : WordTrace (prefixWord ++ tailWord_807280) baseStart_807280 baseEnd_807280 := by
    simpa [prefixWord, tailWord_807280, baseEnd_807280] using wordTrace_append hprefix tailTrace_807280
  have hstable : (prefixWord ++ tailWord_807280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807280).length < 2 ^ (prefixWord ++ tailWord_807280).sum := by decide
  have hdescent : baseEnd_807280 < baseStart_807280 := by decide
  rcases family_descends (prefixWord ++ tailWord_807280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807286 : List Nat := [5, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_807286 : Nat := 118140960795 + 807286 * 2 ^ 59
def prefixEnd_807286 : Nat := 4983230072969 + 3 ^ 40 * 807286 * 2
def baseEnd_807286 : Nat := 184233663842503877116607

theorem tailTrace_807286 : CollatzResearch.WordTrace tailWord_807286 prefixEnd_807286 184233663842503877116607 := by
  unfold tailWord_807286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1840258709584260644827607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19629426235565446878161141 1840258709584260644827607)
  ·
    refine ⟨2760388064376390967241411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1840258709584260644827607 2760388064376390967241411)
    ·
      refine ⟨4140582096564586450862117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2760388064376390967241411 4140582096564586450862117)
      ·
        refine ⟨776359143105859959536647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4140582096564586450862117 776359143105859959536647)
        ·
          refine ⟨1164538714658789939304971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776359143105859959536647 1164538714658789939304971)
          ·
            refine ⟨1746808071988184908957457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164538714658789939304971 1746808071988184908957457)
            ·
              refine ⟨1310106053991138681718093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1746808071988184908957457 1310106053991138681718093)
              ·
                refine ⟨491289770246677005644285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1310106053991138681718093 491289770246677005644285)
                ·
                  refine ⟨184233663842503877116607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 491289770246677005644285 184233663842503877116607)
                  ·
                    rfl

theorem cell21_807286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_807286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807286 prefixEnd_807286 := by exact prefixLift 807286
  have htrace : WordTrace (prefixWord ++ tailWord_807286) baseStart_807286 baseEnd_807286 := by
    simpa [prefixWord, tailWord_807286, baseEnd_807286] using wordTrace_append hprefix tailTrace_807286
  have hstable : (prefixWord ++ tailWord_807286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807286).length < 2 ^ (prefixWord ++ tailWord_807286).sum := by decide
  have hdescent : baseEnd_807286 < baseStart_807286 := by decide
  rcases family_descends (prefixWord ++ tailWord_807286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807356 : List Nat := [2, 2, 2, 4, 1, 3, 7]
def baseStart_807356 : Nat := 118140960795 + 807356 * 2 ^ 59
def prefixEnd_807356 : Nat := 4983230072969 + 3 ^ 40 * 807356 * 2
def baseEnd_807356 : Nat := 20472182088466590105533

theorem tailTrace_807356 : CollatzResearch.WordTrace tailWord_807356 prefixEnd_807356 20472182088466590105533 := by
  unfold tailWord_807356
  simp only [CollatzResearch.WordTrace]
  refine ⟨14723346231547286136144961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19631128308729714848193281 14723346231547286136144961)
  ·
    refine ⟨11042509673660464602108721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14723346231547286136144961 11042509673660464602108721)
    ·
      refine ⟨8281882255245348451581541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11042509673660464602108721 8281882255245348451581541)
      ·
        refine ⟨1552852922858502834671539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8281882255245348451581541 1552852922858502834671539)
        ·
          refine ⟨2329279384287754252007309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1552852922858502834671539 2329279384287754252007309)
          ·
            refine ⟨873479769107907844502741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2329279384287754252007309 873479769107907844502741)
            ·
              refine ⟨20472182088466590105533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 873479769107907844502741 20472182088466590105533)
              ·
                rfl

theorem cell21_807356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 7].length) (baseStart_807356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807356 prefixEnd_807356 := by exact prefixLift 807356
  have htrace : WordTrace (prefixWord ++ tailWord_807356) baseStart_807356 baseEnd_807356 := by
    simpa [prefixWord, tailWord_807356, baseEnd_807356] using wordTrace_append hprefix tailTrace_807356
  have hstable : (prefixWord ++ tailWord_807356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807356).length < 2 ^ (prefixWord ++ tailWord_807356).sum := by decide
  have hdescent : baseEnd_807356 < baseStart_807356 := by decide
  rcases family_descends (prefixWord ++ tailWord_807356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807469 : List Nat := [1, 5, 4, 1, 1, 2, 1, 2, 4]
def baseStart_807469 : Nat := 118140960795 + 807469 * 2 ^ 59
def prefixEnd_807469 : Nat := 4983230072969 + 3 ^ 40 * 807469 * 2
def baseEnd_807469 : Nat := 184275426935736225566233

theorem tailTrace_807469 : CollatzResearch.WordTrace tailWord_807469 prefixEnd_807469 184275426935736225566233 := by
  unfold tailWord_807469
  simp only [CollatzResearch.WordTrace]
  refine ⟨29450813911685192571153461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19633875941123461714102307 29450813911685192571153461)
  ·
    refine ⟨2761013804220486803545637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29450813911685192571153461 2761013804220486803545637)
    ·
      refine ⟨517690088291341275664807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2761013804220486803545637 517690088291341275664807)
      ·
        refine ⟨776535132437011913497211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517690088291341275664807 776535132437011913497211)
        ·
          refine ⟨1164802698655517870245817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776535132437011913497211 1164802698655517870245817)
          ·
            refine ⟨873602023991638402684363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1164802698655517870245817 873602023991638402684363)
            ·
              refine ⟨1310403035987457604026545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873602023991638402684363 1310403035987457604026545)
              ·
                refine ⟨982802276990593203019909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1310403035987457604026545 982802276990593203019909)
                ·
                  refine ⟨184275426935736225566233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 982802276990593203019909 184275426935736225566233)
                  ·
                    rfl

theorem cell21_807469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_807469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807469 prefixEnd_807469 := by exact prefixLift 807469
  have htrace : WordTrace (prefixWord ++ tailWord_807469) baseStart_807469 baseEnd_807469 := by
    simpa [prefixWord, tailWord_807469, baseEnd_807469] using wordTrace_append hprefix tailTrace_807469
  have hstable : (prefixWord ++ tailWord_807469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807469).length < 2 ^ (prefixWord ++ tailWord_807469).sum := by decide
  have hdescent : baseEnd_807469 < baseStart_807469 := by decide
  rcases family_descends (prefixWord ++ tailWord_807469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807508 : List Nat := [2, 4, 1, 1, 1, 3, 4, 5]
def baseStart_807508 : Nat := 118140960795 + 807508 * 2 ^ 59
def prefixEnd_807508 : Nat := 4983230072969 + 3 ^ 40 * 807508 * 2
def baseEnd_807508 : Nat := 61428109089026941472051

theorem tailTrace_807508 : CollatzResearch.WordTrace tailWord_807508 prefixEnd_807508 61428109089026941472051 := by
  unfold tailWord_807508
  simp only [CollatzResearch.WordTrace]
  refine ⟨14726118179271951115911589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19634824239029268154548785 14726118179271951115911589)
  ·
    refine ⟨2761147158613490834233423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14726118179271951115911589 2761147158613490834233423)
    ·
      refine ⟨4141720737920236251350135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2761147158613490834233423 4141720737920236251350135)
      ·
        refine ⟨6212581106880354377025203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4141720737920236251350135 6212581106880354377025203)
        ·
          refine ⟨9318871660320531565537805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6212581106880354377025203 9318871660320531565537805)
          ·
            refine ⟨3494576872620199337076677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9318871660320531565537805 3494576872620199337076677)
            ·
              refine ⟨655233163616287375701877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3494576872620199337076677 655233163616287375701877)
              ·
                refine ⟨61428109089026941472051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 655233163616287375701877 61428109089026941472051)
                ·
                  rfl

theorem cell21_807508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 5].length) (baseStart_807508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807508 prefixEnd_807508 := by exact prefixLift 807508
  have htrace : WordTrace (prefixWord ++ tailWord_807508) baseStart_807508 baseEnd_807508 := by
    simpa [prefixWord, tailWord_807508, baseEnd_807508] using wordTrace_append hprefix tailTrace_807508
  have hstable : (prefixWord ++ tailWord_807508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807508).length < 2 ^ (prefixWord ++ tailWord_807508).sum := by decide
  have hdescent : baseEnd_807508 < baseStart_807508 := by decide
  rcases family_descends (prefixWord ++ tailWord_807508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807553 : List Nat := [1, 2, 4, 2, 1, 1, 3, 3, 4]
def baseStart_807553 : Nat := 118140960795 + 807553 * 2 ^ 59
def prefixEnd_807553 : Nat := 4983230072969 + 3 ^ 40 * 807553 * 2
def baseEnd_807553 : Nat := 184294596880170746166061

theorem tailTrace_807553 : CollatzResearch.WordTrace tailWord_807553 prefixEnd_807553 184294596880170746166061 := by
  unfold tailWord_807553
  simp only [CollatzResearch.WordTrace]
  refine ⟨29453877643380874917211313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19635918428920583278140875 29453877643380874917211313)
  ·
    refine ⟨22090408232535656187908485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29453877643380874917211313 22090408232535656187908485)
    ·
      refine ⟨4141951543600435535232841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22090408232535656187908485 4141951543600435535232841)
      ·
        refine ⟨3106463657700326651424631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4141951543600435535232841 3106463657700326651424631)
        ·
          refine ⟨4659695486550489977136947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3106463657700326651424631 4659695486550489977136947)
          ·
            refine ⟨6989543229825734965705421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4659695486550489977136947 6989543229825734965705421)
            ·
              refine ⟨2621078711184650612139533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6989543229825734965705421 2621078711184650612139533)
              ·
                refine ⟨982904516694243979552325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2621078711184650612139533 982904516694243979552325)
                ·
                  refine ⟨184294596880170746166061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 982904516694243979552325 184294596880170746166061)
                  ·
                    rfl

theorem cell21_807553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 4].length) (baseStart_807553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807553 prefixEnd_807553 := by exact prefixLift 807553
  have htrace : WordTrace (prefixWord ++ tailWord_807553) baseStart_807553 baseEnd_807553 := by
    simpa [prefixWord, tailWord_807553, baseEnd_807553] using wordTrace_append hprefix tailTrace_807553
  have hstable : (prefixWord ++ tailWord_807553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807553).length < 2 ^ (prefixWord ++ tailWord_807553).sum := by decide
  have hdescent : baseEnd_807553 < baseStart_807553 := by decide
  rcases family_descends (prefixWord ++ tailWord_807553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807601 : List Nat := [1, 2, 2, 6, 1, 2, 1, 6]
def baseStart_807601 : Nat := 118140960795 + 807601 * 2 ^ 59
def prefixEnd_807601 : Nat := 4983230072969 + 3 ^ 40 * 807601 * 2
def baseEnd_807601 : Nat := 61435183711377776455321

theorem tailTrace_807601 : CollatzResearch.WordTrace tailWord_807601 prefixEnd_807601 61435183711377776455321 := by
  unfold tailWord_807601
  simp only [CollatzResearch.WordTrace]
  refine ⟨29455628347206979114958657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19637085564804652743305771 29455628347206979114958657)
  ·
    refine ⟨22091721260405234336218993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29455628347206979114958657 22091721260405234336218993)
    ·
      refine ⟨16568790945303925752164245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22091721260405234336218993 16568790945303925752164245)
      ·
        refine ⟨776662075561121519632699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16568790945303925752164245 776662075561121519632699)
        ·
          refine ⟨1164993113341682279449049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776662075561121519632699 1164993113341682279449049)
          ·
            refine ⟨873744835006261709586787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1164993113341682279449049 873744835006261709586787)
            ·
              refine ⟨1310617252509392564380181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873744835006261709586787 1310617252509392564380181)
              ·
                refine ⟨61435183711377776455321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1310617252509392564380181 61435183711377776455321)
                ·
                  rfl

theorem cell21_807601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 6].length) (baseStart_807601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807601 prefixEnd_807601 := by exact prefixLift 807601
  have htrace : WordTrace (prefixWord ++ tailWord_807601) baseStart_807601 baseEnd_807601 := by
    simpa [prefixWord, tailWord_807601, baseEnd_807601] using wordTrace_append hprefix tailTrace_807601
  have hstable : (prefixWord ++ tailWord_807601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807601).length < 2 ^ (prefixWord ++ tailWord_807601).sum := by decide
  have hdescent : baseEnd_807601 < baseStart_807601 := by decide
  rcases family_descends (prefixWord ++ tailWord_807601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807657 : List Nat := [1, 2, 1, 1, 1, 2, 5, 3, 5]
def baseStart_807657 : Nat := 118140960795 + 807657 * 2 ^ 59
def prefixEnd_807657 : Nat := 4983230072969 + 3 ^ 40 * 807657 * 2
def baseEnd_807657 : Nat := 184318331097089676432515

theorem tailTrace_807657 : CollatzResearch.WordTrace tailWord_807657 prefixEnd_807657 184318331097089676432515 := by
  unfold tailWord_807657
  simp only [CollatzResearch.WordTrace]
  refine ⟨29457670835004100678997225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19638447223336067119331483 29457670835004100678997225)
  ·
    refine ⟨22093253126253075509247919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29457670835004100678997225 22093253126253075509247919)
    ·
      refine ⟨33139879689379613263871879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22093253126253075509247919 33139879689379613263871879)
      ·
        refine ⟨49709819534069419895807819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33139879689379613263871879 49709819534069419895807819)
        ·
          refine ⟨74564729301104129843711729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49709819534069419895807819 74564729301104129843711729)
          ·
            refine ⟨55923546975828097382783797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74564729301104129843711729 55923546975828097382783797)
            ·
              refine ⟨5242832528983884129635981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55923546975828097382783797 5242832528983884129635981)
              ·
                refine ⟨1966062198368956548613493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5242832528983884129635981 1966062198368956548613493)
                ·
                  refine ⟨184318331097089676432515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1966062198368956548613493 184318331097089676432515)
                  ·
                    rfl

theorem cell21_807657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_807657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807657 prefixEnd_807657 := by exact prefixLift 807657
  have htrace : WordTrace (prefixWord ++ tailWord_807657) baseStart_807657 baseEnd_807657 := by
    simpa [prefixWord, tailWord_807657, baseEnd_807657] using wordTrace_append hprefix tailTrace_807657
  have hstable : (prefixWord ++ tailWord_807657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807657).length < 2 ^ (prefixWord ++ tailWord_807657).sum := by decide
  have hdescent : baseEnd_807657 < baseStart_807657 := by decide
  rcases family_descends (prefixWord ++ tailWord_807657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807688 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 6]
def baseStart_807688 : Nat := 118140960795 + 807688 * 2 ^ 59
def prefixEnd_807688 : Nat := 4983230072969 + 3 ^ 40 * 807688 * 2
def baseEnd_807688 : Nat := 184325405719440511415785

theorem tailTrace_807688 : CollatzResearch.WordTrace tailWord_807688 prefixEnd_807688 184325405719440511415785 := by
  unfold tailWord_807688
  simp only [CollatzResearch.WordTrace]
  refine ⟨14729400748945896486687859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19639200998594528648917145 14729400748945896486687859)
  ·
    refine ⟨22094101123418844730031789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14729400748945896486687859 22094101123418844730031789)
    ·
      refine ⟨8285287921282066773761921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22094101123418844730031789 8285287921282066773761921)
      ·
        refine ⟨6213965940961550080321441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8285287921282066773761921 6213965940961550080321441)
        ·
          refine ⟨4660474455721162560241081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6213965940961550080321441 4660474455721162560241081)
          ·
            refine ⟨3495355841790871920180811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4660474455721162560241081 3495355841790871920180811)
            ·
              refine ⟨5243033762686307880271217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3495355841790871920180811 5243033762686307880271217)
              ·
                refine ⟨3932275322014730910203413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5243033762686307880271217 3932275322014730910203413)
                ·
                  refine ⟨184325405719440511415785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3932275322014730910203413 184325405719440511415785)
                  ·
                    rfl

theorem cell21_807688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_807688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807688 prefixEnd_807688 := by exact prefixLift 807688
  have htrace : WordTrace (prefixWord ++ tailWord_807688) baseStart_807688 baseEnd_807688 := by
    simpa [prefixWord, tailWord_807688, baseEnd_807688] using wordTrace_append hprefix tailTrace_807688
  have hstable : (prefixWord ++ tailWord_807688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807688).length < 2 ^ (prefixWord ++ tailWord_807688).sum := by decide
  have hdescent : baseEnd_807688 < baseStart_807688 := by decide
  rcases family_descends (prefixWord ++ tailWord_807688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807708 : List Nat := [2, 2, 3, 1, 1, 4, 3, 2, 3]
def baseStart_807708 : Nat := 118140960795 + 807708 * 2 ^ 59
def prefixEnd_807708 : Nat := 4983230072969 + 3 ^ 40 * 807708 * 2
def baseEnd_807708 : Nat := 184329969991924921082411

theorem tailTrace_807708 : CollatzResearch.WordTrace tailWord_807708 prefixEnd_807708 184329969991924921082411 := by
  unfold tailWord_807708
  simp only [CollatzResearch.WordTrace]
  refine ⟨14729765478909668194551889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19639687305212890926069185 14729765478909668194551889)
  ·
    refine ⟨11047324109182251145913917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14729765478909668194551889 11047324109182251145913917)
    ·
      refine ⟨4142746540943344179717719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11047324109182251145913917 4142746540943344179717719)
      ·
        refine ⟨6214119811415016269576579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4142746540943344179717719 6214119811415016269576579)
        ·
          refine ⟨9321179717122524404364869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6214119811415016269576579 9321179717122524404364869)
          ·
            refine ⟨1747721196960473325818413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9321179717122524404364869 1747721196960473325818413)
            ·
              refine ⟨655395448860177497181905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1747721196960473325818413 655395448860177497181905)
              ·
                refine ⟨491546586645133122886429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 655395448860177497181905 491546586645133122886429)
                ·
                  refine ⟨184329969991924921082411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 491546586645133122886429 184329969991924921082411)
                  ·
                    rfl

theorem cell21_807708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_807708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807708 prefixEnd_807708 := by exact prefixLift 807708
  have htrace : WordTrace (prefixWord ++ tailWord_807708) baseStart_807708 baseEnd_807708 := by
    simpa [prefixWord, tailWord_807708, baseEnd_807708] using wordTrace_append hprefix tailTrace_807708
  have hstable : (prefixWord ++ tailWord_807708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807708).length < 2 ^ (prefixWord ++ tailWord_807708).sum := by decide
  have hdescent : baseEnd_807708 < baseStart_807708 := by decide
  rcases family_descends (prefixWord ++ tailWord_807708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807767 : List Nat := [1, 1, 3, 2, 4, 2, 1, 4, 3]
def baseStart_807767 : Nat := 118140960795 + 807767 * 2 ^ 59
def prefixEnd_807767 : Nat := 4983230072969 + 3 ^ 40 * 807767 * 2
def baseEnd_807767 : Nat := 184343434595753929598957

theorem tailTrace_807767 : CollatzResearch.WordTrace tailWord_807767 prefixEnd_807767 184343434595753929598957 := by
  unfold tailWord_807767
  simp only [CollatzResearch.WordTrace]
  refine ⟨29461682864605589465501555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19641121909737059643667703 29461682864605589465501555)
  ·
    refine ⟨44192524296908384198252333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29461682864605589465501555 44192524296908384198252333)
    ·
      refine ⟨16572196611340644074344625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44192524296908384198252333 16572196611340644074344625)
      ·
        refine ⟨12429147458505483055758469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16572196611340644074344625 12429147458505483055758469)
        ·
          refine ⟨2330465148469778072954713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12429147458505483055758469 2330465148469778072954713)
          ·
            refine ⟨1747848861352333554716035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2330465148469778072954713 1747848861352333554716035)
            ·
              refine ⟨2621773292028500332074053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1747848861352333554716035 2621773292028500332074053)
              ·
                refine ⟨491582492255343812263885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2621773292028500332074053 491582492255343812263885)
                ·
                  refine ⟨184343434595753929598957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 491582492255343812263885 184343434595753929598957)
                  ·
                    rfl

theorem cell21_807767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 3].length) (baseStart_807767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807767 prefixEnd_807767 := by exact prefixLift 807767
  have htrace : WordTrace (prefixWord ++ tailWord_807767) baseStart_807767 baseEnd_807767 := by
    simpa [prefixWord, tailWord_807767, baseEnd_807767] using wordTrace_append hprefix tailTrace_807767
  have hstable : (prefixWord ++ tailWord_807767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807767).length < 2 ^ (prefixWord ++ tailWord_807767).sum := by decide
  have hdescent : baseEnd_807767 < baseStart_807767 := by decide
  rcases family_descends (prefixWord ++ tailWord_807767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807840 : List Nat := [2, 1, 1, 4, 1, 1, 2, 5, 4]
def baseStart_807840 : Nat := 118140960795 + 807840 * 2 ^ 59
def prefixEnd_807840 : Nat := 4983230072969 + 3 ^ 40 * 807840 * 2
def baseEnd_807840 : Nat := 184360094190322024882141

theorem tailTrace_807840 : CollatzResearch.WordTrace tailWord_807840 prefixEnd_807840 184360094190322024882141 := by
  unfold tailWord_807840
  simp only [CollatzResearch.WordTrace]
  refine ⟨14732172696670561466454487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19642896928894081955272649 14732172696670561466454487)
  ·
    refine ⟨22098259045005842199681731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14732172696670561466454487 22098259045005842199681731)
    ·
      refine ⟨33147388567508763299522597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22098259045005842199681731 33147388567508763299522597)
      ·
        refine ⟨6215135356407893118660487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33147388567508763299522597 6215135356407893118660487)
        ·
          refine ⟨9322703034611839677990731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6215135356407893118660487 9322703034611839677990731)
          ·
            refine ⟨13984054551917759516986097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9322703034611839677990731 13984054551917759516986097)
            ·
              refine ⟨10488040913938319637739573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13984054551917759516986097 10488040913938319637739573)
              ·
                refine ⟨983253835681717466038085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10488040913938319637739573 983253835681717466038085)
                ·
                  refine ⟨184360094190322024882141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 983253835681717466038085 184360094190322024882141)
                  ·
                    rfl

theorem cell21_807840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 4].length) (baseStart_807840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807840 prefixEnd_807840 := by exact prefixLift 807840
  have htrace : WordTrace (prefixWord ++ tailWord_807840) baseStart_807840 baseEnd_807840 := by
    simpa [prefixWord, tailWord_807840, baseEnd_807840] using wordTrace_append hprefix tailTrace_807840
  have hstable : (prefixWord ++ tailWord_807840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807840).length < 2 ^ (prefixWord ++ tailWord_807840).sum := by decide
  have hdescent : baseEnd_807840 < baseStart_807840 := by decide
  rcases family_descends (prefixWord ++ tailWord_807840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807947 : List Nat := [1, 1, 1, 1, 6, 4, 1, 6]
def baseStart_807947 : Nat := 118140960795 + 807947 * 2 ^ 59
def prefixEnd_807947 : Nat := 4983230072969 + 3 ^ 40 * 807947 * 2
def baseEnd_807947 : Nat := 61461504349371205532863

theorem tailTrace_807947 : CollatzResearch.WordTrace tailWord_807947 prefixEnd_807947 61461504349371205532863 := by
  unfold tailWord_807947
  simp only [CollatzResearch.WordTrace]
  refine ⟨29468248003953480207054095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19645498669302320138036063 29468248003953480207054095)
  ·
    refine ⟨44202372005930220310581143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29468248003953480207054095 44202372005930220310581143)
    ·
      refine ⟨66303558008895330465871715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44202372005930220310581143 66303558008895330465871715)
      ·
        refine ⟨99455337013342995698807573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66303558008895330465871715 99455337013342995698807573)
        ·
          refine ⟨4661968922500452923381605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 99455337013342995698807573 4661968922500452923381605)
          ·
            refine ⟨874119172968834923134051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4661968922500452923381605 874119172968834923134051)
            ·
              refine ⟨1311178759453252384701077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874119172968834923134051 1311178759453252384701077)
              ·
                refine ⟨61461504349371205532863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1311178759453252384701077 61461504349371205532863)
                ·
                  rfl

theorem cell21_807947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 6].length) (baseStart_807947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807947 prefixEnd_807947 := by exact prefixLift 807947
  have htrace : WordTrace (prefixWord ++ tailWord_807947) baseStart_807947 baseEnd_807947 := by
    simpa [prefixWord, tailWord_807947, baseEnd_807947] using wordTrace_append hprefix tailTrace_807947
  have hstable : (prefixWord ++ tailWord_807947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807947).length < 2 ^ (prefixWord ++ tailWord_807947).sum := by decide
  have hdescent : baseEnd_807947 < baseStart_807947 := by decide
  rcases family_descends (prefixWord ++ tailWord_807947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807964 : List Nat := [2, 2, 3, 1, 4, 1, 3, 5]
def baseStart_807964 : Nat := 118140960795 + 807964 * 2 ^ 59
def prefixEnd_807964 : Nat := 4983230072969 + 3 ^ 40 * 807964 * 2
def baseEnd_807964 : Nat := 61462797559908454938407

theorem tailTrace_807964 : CollatzResearch.WordTrace tailWord_807964 prefixEnd_807964 61462797559908454938407 := by
  unfold tailWord_807964
  simp only [CollatzResearch.WordTrace]
  refine ⟨14734434022445946055211473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19645912029927928073615297 14734434022445946055211473)
  ·
    refine ⟨11050825516834459541408605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14734434022445946055211473 11050825516834459541408605)
    ·
      refine ⟨4144059568812922328028227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11050825516834459541408605 4144059568812922328028227)
      ·
        refine ⟨6216089353219383492042341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4144059568812922328028227 6216089353219383492042341)
        ·
          refine ⟨1165516753728634404757939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6216089353219383492042341 1165516753728634404757939)
          ·
            refine ⟨1748275130592951607136909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165516753728634404757939 1748275130592951607136909)
            ·
              refine ⟨655603173972356852676341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1748275130592951607136909 655603173972356852676341)
              ·
                refine ⟨61462797559908454938407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 655603173972356852676341 61462797559908454938407)
                ·
                  rfl

theorem cell21_807964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 5].length) (baseStart_807964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807964 prefixEnd_807964 := by exact prefixLift 807964
  have htrace : WordTrace (prefixWord ++ tailWord_807964) baseStart_807964 baseEnd_807964 := by
    simpa [prefixWord, tailWord_807964, baseEnd_807964] using wordTrace_append hprefix tailTrace_807964
  have hstable : (prefixWord ++ tailWord_807964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807964).length < 2 ^ (prefixWord ++ tailWord_807964).sum := by decide
  have hdescent : baseEnd_807964 < baseStart_807964 := by decide
  rcases family_descends (prefixWord ++ tailWord_807964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807992 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 6]
def baseStart_807992 : Nat := 118140960795 + 807992 * 2 ^ 59
def prefixEnd_807992 : Nat := 4983230072969 + 3 ^ 40 * 807992 * 2
def baseEnd_807992 : Nat := 184394782661203538348497

theorem tailTrace_807992 : CollatzResearch.WordTrace tailWord_807992 prefixEnd_807992 184394782661203538348497 := by
  unfold tailWord_807992
  simp only [CollatzResearch.WordTrace]
  refine ⟨14734944644395226446221115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19646592859193635261628153 14734944644395226446221115)
  ·
    refine ⟨22102416966592839669331673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14734944644395226446221115 22102416966592839669331673)
    ·
      refine ⟨16576812724944629751998755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22102416966592839669331673 16576812724944629751998755)
      ·
        refine ⟨24865219087416944627998133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16576812724944629751998755 24865219087416944627998133)
        ·
          refine ⟨2331114289445338558874825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24865219087416944627998133 2331114289445338558874825)
          ·
            refine ⟨1748335717084003919156119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2331114289445338558874825 1748335717084003919156119)
            ·
              refine ⟨2622503575626005878734179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1748335717084003919156119 2622503575626005878734179)
              ·
                refine ⟨3933755363439008818101269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2622503575626005878734179 3933755363439008818101269)
                ·
                  refine ⟨184394782661203538348497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3933755363439008818101269 184394782661203538348497)
                  ·
                    rfl

theorem cell21_807992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_807992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_807992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_807992 prefixEnd_807992 := by exact prefixLift 807992
  have htrace : WordTrace (prefixWord ++ tailWord_807992) baseStart_807992 baseEnd_807992 := by
    simpa [prefixWord, tailWord_807992, baseEnd_807992] using wordTrace_append hprefix tailTrace_807992
  have hstable : (prefixWord ++ tailWord_807992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807992).length < 2 ^ (prefixWord ++ tailWord_807992).sum := by decide
  have hdescent : baseEnd_807992 < baseStart_807992 := by decide
  rcases family_descends (prefixWord ++ tailWord_807992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808029 : List Nat := [1, 4, 4, 1, 2, 2, 1, 3, 3]
def baseStart_808029 : Nat := 118140960795 + 808029 * 2 ^ 59
def prefixEnd_808029 : Nat := 4983230072969 + 3 ^ 40 * 808029 * 2
def baseEnd_808029 : Nat := 184403226565299696231755

theorem tailTrace_808029 : CollatzResearch.WordTrace tailWord_808029 prefixEnd_808029 184403226565299696231755 := by
  unfold tailWord_808029
  simp only [CollatzResearch.WordTrace]
  refine ⟨29471238789656408211539141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19647492526437605474359427 29471238789656408211539141)
  ·
    refine ⟨5525857273060576539663589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29471238789656408211539141 5525857273060576539663589)
    ·
      refine ⟨1036098238698858101186923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5525857273060576539663589 1036098238698858101186923)
      ·
        refine ⟨1554147358048287151780385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1036098238698858101186923 1554147358048287151780385)
        ·
          refine ⟨1165610518536215363835289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1554147358048287151780385 1165610518536215363835289)
          ·
            refine ⟨874207888902161522876467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1165610518536215363835289 874207888902161522876467)
            ·
              refine ⟨1311311833353242284314701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874207888902161522876467 1311311833353242284314701)
              ·
                refine ⟨491741937507465856618013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1311311833353242284314701 491741937507465856618013)
                ·
                  refine ⟨184403226565299696231755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 491741937507465856618013 184403226565299696231755)
                  ·
                    rfl

theorem cell21_808029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_808029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_808029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_808029 prefixEnd_808029 := by exact prefixLift 808029
  have htrace : WordTrace (prefixWord ++ tailWord_808029) baseStart_808029 baseEnd_808029 := by
    simpa [prefixWord, tailWord_808029, baseEnd_808029] using wordTrace_append hprefix tailTrace_808029
  have hstable : (prefixWord ++ tailWord_808029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808029).length < 2 ^ (prefixWord ++ tailWord_808029).sum := by decide
  have hdescent : baseEnd_808029 < baseStart_808029 := by decide
  rcases family_descends (prefixWord ++ tailWord_808029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808040 : List Nat := [2, 1, 4, 4, 1, 2, 7]
def baseStart_808040 : Nat := 118140960795 + 808040 * 2 ^ 59
def prefixEnd_808040 : Nat := 4983230072969 + 3 ^ 40 * 808040 * 2
def baseEnd_808040 : Nat := 20489526323907346838711

theorem tailTrace_808040 : CollatzResearch.WordTrace tailWord_808040 prefixEnd_808040 20489526323907346838711 := by
  unfold tailWord_808040
  simp only [CollatzResearch.WordTrace]
  refine ⟨14735819996308278545094787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19647759995077704726793049 14735819996308278545094787)
  ·
    refine ⟨22103729994462417817642181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14735819996308278545094787 22103729994462417817642181)
    ·
      refine ⟨4144449373961703340807909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22103729994462417817642181 4144449373961703340807909)
      ·
        refine ⟨777084257617819376401483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4144449373961703340807909 777084257617819376401483)
        ·
          refine ⟨1165626386426729064602225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777084257617819376401483 1165626386426729064602225)
          ·
            refine ⟨874219789820046798451669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1165626386426729064602225 874219789820046798451669)
            ·
              refine ⟨20489526323907346838711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 874219789820046798451669 20489526323907346838711)
              ·
                rfl

theorem cell21_808040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 7].length) (baseStart_808040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_808040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_808040 prefixEnd_808040 := by exact prefixLift 808040
  have htrace : WordTrace (prefixWord ++ tailWord_808040) baseStart_808040 baseEnd_808040 := by
    simpa [prefixWord, tailWord_808040, baseEnd_808040] using wordTrace_append hprefix tailTrace_808040
  have hstable : (prefixWord ++ tailWord_808040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808040).length < 2 ^ (prefixWord ++ tailWord_808040).sum := by decide
  have hdescent : baseEnd_808040 < baseStart_808040 := by decide
  rcases family_descends (prefixWord ++ tailWord_808040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808161 : List Nat := [1, 2, 3, 1, 3, 4, 1, 2, 4]
def baseStart_808161 : Nat := 118140960795 + 808161 * 2 ^ 59
def prefixEnd_808161 : Nat := 4983230072969 + 3 ^ 40 * 808161 * 2
def baseEnd_808161 : Nat := 184433350763696800031485

theorem tailTrace_808161 : CollatzResearch.WordTrace tailWord_808161 prefixEnd_808161 184433350763696800031485 := by
  unfold tailWord_808161
  simp only [CollatzResearch.WordTrace]
  refine ⟨29476053225178194755344337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19650702150118796503562891 29476053225178194755344337)
  ·
    refine ⟨22107039918883646066508253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29476053225178194755344337 22107039918883646066508253)
    ·
      refine ⟨8290139969581367274940595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22107039918883646066508253 8290139969581367274940595)
      ·
        refine ⟨12435209954372050912410893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8290139969581367274940595 12435209954372050912410893)
        ·
          refine ⟨4663203732889519092154085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12435209954372050912410893 4663203732889519092154085)
          ·
            refine ⟨874350699916784829778891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4663203732889519092154085 874350699916784829778891)
            ·
              refine ⟨1311526049875177244668337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874350699916784829778891 1311526049875177244668337)
              ·
                refine ⟨983644537406382933501253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1311526049875177244668337 983644537406382933501253)
                ·
                  refine ⟨184433350763696800031485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 983644537406382933501253 184433350763696800031485)
                  ·
                    rfl

theorem cell21_808161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 4].length) (baseStart_808161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_808161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_808161 prefixEnd_808161 := by exact prefixLift 808161
  have htrace : WordTrace (prefixWord ++ tailWord_808161) baseStart_808161 baseEnd_808161 := by
    simpa [prefixWord, tailWord_808161, baseEnd_808161] using wordTrace_append hprefix tailTrace_808161
  have hstable : (prefixWord ++ tailWord_808161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808161).length < 2 ^ (prefixWord ++ tailWord_808161).sum := by decide
  have hdescent : baseEnd_808161 < baseStart_808161 := by decide
  rcases family_descends (prefixWord ++ tailWord_808161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808178 : List Nat := [3, 2, 1, 3, 3, 1, 3, 1, 4]
def baseStart_808178 : Nat := 118140960795 + 808178 * 2 ^ 59
def prefixEnd_808178 : Nat := 4983230072969 + 3 ^ 40 * 808178 * 2
def baseEnd_808178 : Nat := 184437230395308548248117

theorem tailTrace_808178 : CollatzResearch.WordTrace tailWord_808178 prefixEnd_808178 184437230395308548248117 := by
  unfold tailWord_808178
  simp only [CollatzResearch.WordTrace]
  refine ⟨7369168316529151664678297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19651115510744404439142125 7369168316529151664678297)
  ·
    refine ⟨5526876237396863748508723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7369168316529151664678297 5526876237396863748508723)
    ·
      refine ⟨8290314356095295622763085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5526876237396863748508723 8290314356095295622763085)
      ·
        refine ⟨3108867883535735858536157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8290314356095295622763085 3108867883535735858536157)
        ·
          refine ⟨1165825456325900946951059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3108867883535735858536157 1165825456325900946951059)
          ·
            refine ⟨1748738184488851420426589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165825456325900946951059 1748738184488851420426589)
            ·
              refine ⟨655776819183319282659971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1748738184488851420426589 655776819183319282659971)
              ·
                refine ⟨983665228774978923989957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 655776819183319282659971 983665228774978923989957)
                ·
                  refine ⟨184437230395308548248117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 983665228774978923989957 184437230395308548248117)
                  ·
                    rfl

theorem cell21_808178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_808178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_808178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_808178 prefixEnd_808178 := by exact prefixLift 808178
  have htrace : WordTrace (prefixWord ++ tailWord_808178) baseStart_808178 baseEnd_808178 := by
    simpa [prefixWord, tailWord_808178, baseEnd_808178] using wordTrace_append hprefix tailTrace_808178
  have hstable : (prefixWord ++ tailWord_808178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808178).length < 2 ^ (prefixWord ++ tailWord_808178).sum := by decide
  have hdescent : baseEnd_808178 < baseStart_808178 := by decide
  rcases family_descends (prefixWord ++ tailWord_808178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808203 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 6]
def baseStart_808203 : Nat := 118140960795 + 808203 * 2 ^ 59
def prefixEnd_808203 : Nat := 4983230072969 + 3 ^ 40 * 808203 * 2
def baseEnd_808203 : Nat := 184442935735914060331399

theorem tailTrace_808203 : CollatzResearch.WordTrace tailWord_808203 prefixEnd_808203 184442935735914060331399 := by
  unfold tailWord_808203
  simp only [CollatzResearch.WordTrace]
  refine ⟨29477585091026035928373263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19651723394017357285582175 29477585091026035928373263)
  ·
    refine ⟨44216377636539053892559895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29477585091026035928373263 44216377636539053892559895)
    ·
      refine ⟨66324566454808580838839843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44216377636539053892559895 66324566454808580838839843)
      ·
        refine ⟨99486849682212871258259765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66324566454808580838839843 99486849682212871258259765)
        ·
          refine ⟨9326892157707456680461853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99486849682212871258259765 9326892157707456680461853)
          ·
            refine ⟨3497584559140296255173195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9326892157707456680461853 3497584559140296255173195)
            ·
              refine ⟨5246376838710444382759793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3497584559140296255173195 5246376838710444382759793)
              ·
                refine ⟨3934782629032833287069845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5246376838710444382759793 3934782629032833287069845)
                ·
                  refine ⟨184442935735914060331399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3934782629032833287069845 184442935735914060331399)
                  ·
                    rfl

theorem cell21_808203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 6].length) (baseStart_808203 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_808203 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_808203 prefixEnd_808203 := by exact prefixLift 808203
  have htrace : WordTrace (prefixWord ++ tailWord_808203) baseStart_808203 baseEnd_808203 := by
    simpa [prefixWord, tailWord_808203, baseEnd_808203] using wordTrace_append hprefix tailTrace_808203
  have hstable : (prefixWord ++ tailWord_808203).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808203).length < 2 ^ (prefixWord ++ tailWord_808203).sum := by decide
  have hdescent : baseEnd_808203 < baseStart_808203 := by decide
  rcases family_descends (prefixWord ++ tailWord_808203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808223 : List Nat := [1, 1, 2, 4, 5, 1, 1, 1, 5]
def baseStart_808223 : Nat := 118140960795 + 808223 * 2 ^ 59
def prefixEnd_808223 : Nat := 4983230072969 + 3 ^ 40 * 808223 * 2
def baseEnd_808223 : Nat := 184447500008398469998025

theorem tailTrace_808223 : CollatzResearch.WordTrace tailWord_808223 prefixEnd_808223 184447500008398469998025 := by
  unfold tailWord_808223
  simp only [CollatzResearch.WordTrace]
  refine ⟨29478314550953579344101323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19652209700635719562734215 29478314550953579344101323)
  ·
    refine ⟨44217471826430369016151985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29478314550953579344101323 44217471826430369016151985)
    ·
      refine ⟨33163103869822776762113989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44217471826430369016151985 33163103869822776762113989)
      ·
        refine ⟨6218081975591770642896373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33163103869822776762113989 6218081975591770642896373)
        ·
          refine ⟨582945185211728497771535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6218081975591770642896373 582945185211728497771535)
          ·
            refine ⟨874417777817592746657303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582945185211728497771535 874417777817592746657303)
            ·
              refine ⟨1311626666726389119985955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874417777817592746657303 1311626666726389119985955)
              ·
                refine ⟨1967440000089583679978933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311626666726389119985955 1967440000089583679978933)
                ·
                  refine ⟨184447500008398469998025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1967440000089583679978933 184447500008398469998025)
                  ·
                    rfl

theorem cell21_808223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 5].length) (baseStart_808223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_808223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_808223 prefixEnd_808223 := by exact prefixLift 808223
  have htrace : WordTrace (prefixWord ++ tailWord_808223) baseStart_808223 baseEnd_808223 := by
    simpa [prefixWord, tailWord_808223, baseEnd_808223] using wordTrace_append hprefix tailTrace_808223
  have hstable : (prefixWord ++ tailWord_808223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808223).length < 2 ^ (prefixWord ++ tailWord_808223).sum := by decide
  have hdescent : baseEnd_808223 < baseStart_808223 := by decide
  rcases family_descends (prefixWord ++ tailWord_808223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808248 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 7]
def baseStart_808248 : Nat := 118140960795 + 808248 * 2 ^ 59
def prefixEnd_808248 : Nat := 4983230072969 + 3 ^ 40 * 808248 * 2
def baseEnd_808248 : Nat := 184453205349003982081307

theorem tailTrace_808248 : CollatzResearch.WordTrace tailWord_808248 prefixEnd_808248 184453205349003982081307 := by
  unfold tailWord_808248
  simp only [CollatzResearch.WordTrace]
  refine ⟨14739613187931504306880699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19652817583908672409174265 14739613187931504306880699)
  ·
    refine ⟨22109419781897256460321049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14739613187931504306880699 22109419781897256460321049)
    ·
      refine ⟨16582064836422942345240787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22109419781897256460321049 16582064836422942345240787)
      ·
        refine ⟨24873097254634413517861181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16582064836422942345240787 24873097254634413517861181)
        ·
          refine ⟨9327411470487905069197943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24873097254634413517861181 9327411470487905069197943)
          ·
            refine ⟨13991117205731857603796915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9327411470487905069197943 13991117205731857603796915)
            ·
              refine ⟨20986675808597786405695373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13991117205731857603796915 20986675808597786405695373)
              ·
                refine ⟨7870003428224169902135765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20986675808597786405695373 7870003428224169902135765)
                ·
                  refine ⟨184453205349003982081307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7870003428224169902135765 184453205349003982081307)
                  ·
                    rfl

theorem cell21_808248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_808248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_808248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_808248 prefixEnd_808248 := by exact prefixLift 808248
  have htrace : WordTrace (prefixWord ++ tailWord_808248) baseStart_808248 baseEnd_808248 := by
    simpa [prefixWord, tailWord_808248, baseEnd_808248] using wordTrace_append hprefix tailTrace_808248
  have hstable : (prefixWord ++ tailWord_808248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808248).length < 2 ^ (prefixWord ++ tailWord_808248).sum := by decide
  have hdescent : baseEnd_808248 < baseStart_808248 := by decide
  rcases family_descends (prefixWord ++ tailWord_808248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808406 : List Nat := [5, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_808406 : Nat := 118140960795 + 808406 * 2 ^ 59
def prefixEnd_808406 : Nat := 4983230072969 + 3 ^ 40 * 808406 * 2
def baseEnd_808406 : Nat := 184489263101630818447651

theorem tailTrace_808406 : CollatzResearch.WordTrace tailWord_808406 prefixEnd_808406 184489263101630818447651 := by
  unfold tailWord_808406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1842811819330662599875817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19656659406193734398675381 1842811819330662599875817)
  ·
    refine ⟨1382108864497996949906863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1842811819330662599875817 1382108864497996949906863)
    ·
      refine ⟨2073163296746995424860295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1382108864497996949906863 2073163296746995424860295)
      ·
        refine ⟨3109744945120493137290443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2073163296746995424860295 3109744945120493137290443)
        ·
          refine ⟨4664617417680739705935665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3109744945120493137290443 4664617417680739705935665)
          ·
            refine ⟨3498463063260554779451749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4664617417680739705935665 3498463063260554779451749)
            ·
              refine ⟨655961824361354021147203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3498463063260554779451749 655961824361354021147203)
              ·
                refine ⟨983942736542031031720805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 655961824361354021147203 983942736542031031720805)
                ·
                  refine ⟨184489263101630818447651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 983942736542031031720805 184489263101630818447651)
                  ·
                    rfl

theorem cell21_808406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_808406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_808406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_808406 prefixEnd_808406 := by exact prefixLift 808406
  have htrace : WordTrace (prefixWord ++ tailWord_808406) baseStart_808406 baseEnd_808406 := by
    simpa [prefixWord, tailWord_808406, baseEnd_808406] using wordTrace_append hprefix tailTrace_808406
  have hstable : (prefixWord ++ tailWord_808406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808406).length < 2 ^ (prefixWord ++ tailWord_808406).sum := by decide
  have hdescent : baseEnd_808406 < baseStart_808406 := by decide
  rcases family_descends (prefixWord ++ tailWord_808406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808445 : List Nat := [1, 4, 1, 1, 1, 13]
def baseStart_808445 : Nat := 118140960795 + 808445 * 2 ^ 59
def prefixEnd_808445 : Nat := 4983230072969 + 3 ^ 40 * 808445 * 2
def baseEnd_808445 : Nat := 6833265312332422862873

theorem tailTrace_808445 : CollatzResearch.WordTrace tailWord_808445 prefixEnd_808445 6833265312332422862873 := by
  unfold tailWord_808445
  simp only [CollatzResearch.WordTrace]
  refine ⟨29486411556149311258682789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19657607704099540839121859 29486411556149311258682789)
  ·
    refine ⟨5528702166777995861003023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29486411556149311258682789 5528702166777995861003023)
    ·
      refine ⟨8293053250166993791504535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5528702166777995861003023 8293053250166993791504535)
      ·
        refine ⟨12439579875250490687256803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8293053250166993791504535 12439579875250490687256803)
        ·
          refine ⟨18659369812875736030885205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12439579875250490687256803 18659369812875736030885205)
          ·
            refine ⟨6833265312332422862873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 18659369812875736030885205 6833265312332422862873)
            ·
              rfl

theorem cell21_808445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 13].length) (baseStart_808445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_808445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_808445 prefixEnd_808445 := by exact prefixLift 808445
  have htrace : WordTrace (prefixWord ++ tailWord_808445) baseStart_808445 baseEnd_808445 := by
    simpa [prefixWord, tailWord_808445, baseEnd_808445] using wordTrace_append hprefix tailTrace_808445
  have hstable : (prefixWord ++ tailWord_808445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808445).length < 2 ^ (prefixWord ++ tailWord_808445).sum := by decide
  have hdescent : baseEnd_808445 < baseStart_808445 := by decide
  rcases family_descends (prefixWord ++ tailWord_808445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808454 : List Nat := [6, 2, 1, 1, 2, 2, 1, 6]
def baseStart_808454 : Nat := 118140960795 + 808454 * 2 ^ 59
def prefixEnd_808454 : Nat := 4983230072969 + 3 ^ 40 * 808454 * 2
def baseEnd_808454 : Nat := 61500072451864467215851

theorem tailTrace_808454 : CollatzResearch.WordTrace tailWord_808454 prefixEnd_808454 61500072451864467215851 := by
  unfold tailWord_808454
  simp only [CollatzResearch.WordTrace]
  refine ⟨921460619159897056117513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19657826542077803863840277 921460619159897056117513)
  ·
    refine ⟨691095464369922792088135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 921460619159897056117513 691095464369922792088135)
    ·
      refine ⟨1036643196554884188132203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 691095464369922792088135 1036643196554884188132203)
      ·
        refine ⟨1554964794832326282198305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1036643196554884188132203 1554964794832326282198305)
        ·
          refine ⟨1166223596124244711648729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1554964794832326282198305 1166223596124244711648729)
          ·
            refine ⟨874667697093183533736547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1166223596124244711648729 874667697093183533736547)
            ·
              refine ⟨1312001545639775300604821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874667697093183533736547 1312001545639775300604821)
              ·
                refine ⟨61500072451864467215851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1312001545639775300604821 61500072451864467215851)
                ·
                  rfl

theorem cell21_808454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_808454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_808454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_808454 prefixEnd_808454 := by exact prefixLift 808454
  have htrace : WordTrace (prefixWord ++ tailWord_808454) baseStart_808454 baseEnd_808454 := by
    simpa [prefixWord, tailWord_808454, baseEnd_808454] using wordTrace_append hprefix tailTrace_808454
  have hstable : (prefixWord ++ tailWord_808454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808454).length < 2 ^ (prefixWord ++ tailWord_808454).sum := by decide
  have hdescent : baseEnd_808454 < baseStart_808454 := by decide
  rcases family_descends (prefixWord ++ tailWord_808454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808735 : List Nat := [1, 1, 2, 4, 2, 1, 2, 4, 4]
def baseStart_808735 : Nat := 118140960795 + 808735 * 2 ^ 59
def prefixEnd_808735 : Nat := 4983230072969 + 3 ^ 40 * 808735 * 2
def baseEnd_808735 : Nat := 184564345383999357463645

theorem tailTrace_808735 : CollatzResearch.WordTrace tailWord_808735 prefixEnd_808735 184564345383999357463645 := by
  unfold tailWord_808735
  simp only [CollatzResearch.WordTrace]
  refine ⟨29496988725098690786739659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19664659150065793857826439 29496988725098690786739659)
  ·
    refine ⟨44245483087648036180109489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29496988725098690786739659 44245483087648036180109489)
    ·
      refine ⟨33184112315736027135082117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44245483087648036180109489 33184112315736027135082117)
      ·
        refine ⟨6222021059200505087827897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33184112315736027135082117 6222021059200505087827897)
        ·
          refine ⟨4666515794400378815870923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6222021059200505087827897 4666515794400378815870923)
          ·
            refine ⟨6999773691600568223806385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4666515794400378815870923 6999773691600568223806385)
            ·
              refine ⟨5249830268700426167854789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6999773691600568223806385 5249830268700426167854789)
              ·
                refine ⟨984343175381329906472773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5249830268700426167854789 984343175381329906472773)
                ·
                  refine ⟨184564345383999357463645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 984343175381329906472773 184564345383999357463645)
                  ·
                    rfl

theorem cell21_808735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 4].length) (baseStart_808735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_808735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_808735 prefixEnd_808735 := by exact prefixLift 808735
  have htrace : WordTrace (prefixWord ++ tailWord_808735) baseStart_808735 baseEnd_808735 := by
    simpa [prefixWord, tailWord_808735, baseEnd_808735] using wordTrace_append hprefix tailTrace_808735
  have hstable : (prefixWord ++ tailWord_808735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808735).length < 2 ^ (prefixWord ++ tailWord_808735).sum := by decide
  have hdescent : baseEnd_808735 < baseStart_808735 := by decide
  rcases family_descends (prefixWord ++ tailWord_808735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808766 : List Nat := [4, 2, 1, 2, 2, 1, 2, 7]
def baseStart_808766 : Nat := 118140960795 + 808766 * 2 ^ 59
def prefixEnd_808766 : Nat := 4983230072969 + 3 ^ 40 * 808766 * 2
def baseEnd_808766 : Nat := 61523806668783397482305

theorem tailTrace_808766 : CollatzResearch.WordTrace tailWord_808766 prefixEnd_808766 61523806668783397482305 := by
  unfold tailWord_808766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3687264923498297885139769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19665412925324255387412101 3687264923498297885139769)
  ·
    refine ⟨2765448692623723413854827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3687264923498297885139769 2765448692623723413854827)
    ·
      refine ⟨4148173038935585120782241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2765448692623723413854827 4148173038935585120782241)
      ·
        refine ⟨3111129779201688840586681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4148173038935585120782241 3111129779201688840586681)
        ·
          refine ⟨2333347334401266630440011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3111129779201688840586681 2333347334401266630440011)
          ·
            refine ⟨3500021001601899945660017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2333347334401266630440011 3500021001601899945660017)
            ·
              refine ⟨2625015751201424959245013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3500021001601899945660017 2625015751201424959245013)
              ·
                refine ⟨61523806668783397482305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2625015751201424959245013 61523806668783397482305)
                ·
                  rfl

theorem cell21_808766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_808766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_808766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_808766 prefixEnd_808766 := by exact prefixLift 808766
  have htrace : WordTrace (prefixWord ++ tailWord_808766) baseStart_808766 baseEnd_808766 := by
    simpa [prefixWord, tailWord_808766, baseEnd_808766] using wordTrace_append hprefix tailTrace_808766
  have hstable : (prefixWord ++ tailWord_808766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808766).length < 2 ^ (prefixWord ++ tailWord_808766).sum := by decide
  have hdescent : baseEnd_808766 < baseStart_808766 := by decide
  rcases family_descends (prefixWord ++ tailWord_808766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808842 : List Nat := [3, 1, 2, 4, 2, 1, 8]
def baseStart_808842 : Nat := 118140960795 + 808842 * 2 ^ 59
def prefixEnd_808842 : Nat := 4983230072969 + 3 ^ 40 * 808842 * 2
def baseEnd_808842 : Nat := 20509862693532327686677

theorem tailTrace_808842 : CollatzResearch.WordTrace tailWord_808842 prefixEnd_808842 20509862693532327686677 := by
  unfold tailWord_808842
  simp only [CollatzResearch.WordTrace]
  refine ⟨7375222833927762015221195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19667260890474032040589853 7375222833927762015221195)
  ·
    refine ⟨11062834250891643022831793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7375222833927762015221195 11062834250891643022831793)
    ·
      refine ⟨8297125688168732267123845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11062834250891643022831793 8297125688168732267123845)
      ·
        refine ⟨1555711066531637300085721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8297125688168732267123845 1555711066531637300085721)
        ·
          refine ⟨1166783299898727975064291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1555711066531637300085721 1166783299898727975064291)
          ·
            refine ⟨1750174949848091962596437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166783299898727975064291 1750174949848091962596437)
            ·
              refine ⟨20509862693532327686677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1750174949848091962596437 20509862693532327686677)
              ·
                rfl

theorem cell21_808842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 8].length) (baseStart_808842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_808842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_808842 prefixEnd_808842 := by exact prefixLift 808842
  have htrace : WordTrace (prefixWord ++ tailWord_808842) baseStart_808842 baseEnd_808842 := by
    simpa [prefixWord, tailWord_808842, baseEnd_808842] using wordTrace_append hprefix tailTrace_808842
  have hstable : (prefixWord ++ tailWord_808842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808842).length < 2 ^ (prefixWord ++ tailWord_808842).sum := by decide
  have hdescent : baseEnd_808842 < baseStart_808842 := by decide
  rcases family_descends (prefixWord ++ tailWord_808842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808921 : List Nat := [1, 2, 1, 2, 6, 2, 2, 1, 4]
def baseStart_808921 : Nat := 118140960795 + 808921 * 2 ^ 59
def prefixEnd_808921 : Nat := 4983230072969 + 3 ^ 40 * 808921 * 2
def baseEnd_808921 : Nat := 184606793118104367363265

theorem tailTrace_808921 : CollatzResearch.WordTrace tailWord_808921 prefixEnd_808921 184606793118104367363265 := by
  unfold tailWord_808921
  simp only [CollatzResearch.WordTrace]
  refine ⟨29503772702424844553010617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19669181801616563035340411 29503772702424844553010617)
  ·
    refine ⟨22127829526818633414757963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29503772702424844553010617 22127829526818633414757963)
    ·
      refine ⟨33191744290227950122136945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22127829526818633414757963 33191744290227950122136945)
      ·
        refine ⟨24893808217670962591602709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33191744290227950122136945 24893808217670962591602709)
        ·
          refine ⟨1166897260203326371481377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24893808217670962591602709 1166897260203326371481377)
          ·
            refine ⟨875172945152494778611033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1166897260203326371481377 875172945152494778611033)
            ·
              refine ⟨656379708864371083958275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875172945152494778611033 656379708864371083958275)
              ·
                refine ⟨984569563296556625937413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 656379708864371083958275 984569563296556625937413)
                ·
                  refine ⟨184606793118104367363265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 984569563296556625937413 184606793118104367363265)
                  ·
                    rfl

theorem cell21_808921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 4].length) (baseStart_808921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_808921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_808921 prefixEnd_808921 := by exact prefixLift 808921
  have htrace : WordTrace (prefixWord ++ tailWord_808921) baseStart_808921 baseEnd_808921 := by
    simpa [prefixWord, tailWord_808921, baseEnd_808921] using wordTrace_append hprefix tailTrace_808921
  have hstable : (prefixWord ++ tailWord_808921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808921).length < 2 ^ (prefixWord ++ tailWord_808921).sum := by decide
  have hdescent : baseEnd_808921 < baseStart_808921 := by decide
  rcases family_descends (prefixWord ++ tailWord_808921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808994 : List Nat := [3, 3, 1, 1, 1, 2, 5, 5]
def baseStart_808994 : Nat := 118140960795 + 808994 * 2 ^ 59
def prefixEnd_808994 : Nat := 4983230072969 + 3 ^ 40 * 808994 * 2
def baseEnd_808994 : Nat := 61541150904224154215483

theorem tailTrace_808994 : CollatzResearch.WordTrace tailWord_808994 prefixEnd_808994 61541150904224154215483 := by
  unfold tailWord_808994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7376608807790094505104509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19670956820773585346945357 7376608807790094505104509)
  ·
    refine ⟨2766228302921285439414191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7376608807790094505104509 2766228302921285439414191)
    ·
      refine ⟨4149342454381928159121287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2766228302921285439414191 4149342454381928159121287)
      ·
        refine ⟨6224013681572892238681931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4149342454381928159121287 6224013681572892238681931)
        ·
          refine ⟨9336020522359338358022897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6224013681572892238681931 9336020522359338358022897)
          ·
            refine ⟨7002015391769503768517173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9336020522359338358022897 7002015391769503768517173)
            ·
              refine ⟨656438942978390978298485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7002015391769503768517173 656438942978390978298485)
              ·
                refine ⟨61541150904224154215483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 656438942978390978298485 61541150904224154215483)
                ·
                  rfl

theorem cell21_808994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_808994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_808994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_808994 prefixEnd_808994 := by exact prefixLift 808994
  have htrace : WordTrace (prefixWord ++ tailWord_808994) baseStart_808994 baseEnd_808994 := by
    simpa [prefixWord, tailWord_808994, baseEnd_808994] using wordTrace_append hprefix tailTrace_808994
  have hstable : (prefixWord ++ tailWord_808994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808994).length < 2 ^ (prefixWord ++ tailWord_808994).sum := by decide
  have hdescent : baseEnd_808994 < baseStart_808994 := by decide
  rcases family_descends (prefixWord ++ tailWord_808994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809025 : List Nat := [1, 2, 5, 1, 2, 2, 2, 1, 5]
def baseStart_809025 : Nat := 118140960795 + 809025 * 2 ^ 59
def prefixEnd_809025 : Nat := 4983230072969 + 3 ^ 40 * 809025 * 2
def baseEnd_809025 : Nat := 184630527335023297629719

theorem tailTrace_809025 : CollatzResearch.WordTrace tailWord_809025 prefixEnd_809025 184630527335023297629719 := by
  unfold tailWord_809025
  simp only [CollatzResearch.WordTrace]
  refine ⟨29507565894048070314796529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19671710596032046876531019 29507565894048070314796529)
  ·
    refine ⟨22130674420536052736097397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29507565894048070314796529 22130674420536052736097397)
    ·
      refine ⟨2074750726925254944009131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22130674420536052736097397 2074750726925254944009131)
      ·
        refine ⟨3112126090387882416013697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2074750726925254944009131 3112126090387882416013697)
        ·
          refine ⟨2334094567790911812010273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3112126090387882416013697 2334094567790911812010273)
          ·
            refine ⟨1750570925843183859007705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2334094567790911812010273 1750570925843183859007705)
            ·
              refine ⟨1312928194382387894255779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1750570925843183859007705 1312928194382387894255779)
              ·
                refine ⟨1969392291573581841383669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1312928194382387894255779 1969392291573581841383669)
                ·
                  refine ⟨184630527335023297629719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1969392291573581841383669 184630527335023297629719)
                  ·
                    rfl

theorem cell21_809025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 5].length) (baseStart_809025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_809025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_809025 prefixEnd_809025 := by exact prefixLift 809025
  have htrace : WordTrace (prefixWord ++ tailWord_809025) baseStart_809025 baseEnd_809025 := by
    simpa [prefixWord, tailWord_809025, baseEnd_809025] using wordTrace_append hprefix tailTrace_809025
  have hstable : (prefixWord ++ tailWord_809025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809025).length < 2 ^ (prefixWord ++ tailWord_809025).sum := by decide
  have hdescent : baseEnd_809025 < baseStart_809025 := by decide
  rcases family_descends (prefixWord ++ tailWord_809025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809084 : List Nat := [2, 2, 2, 1, 1, 4, 3, 1, 5]
def baseStart_809084 : Nat := 118140960795 + 809084 * 2 ^ 59
def prefixEnd_809084 : Nat := 4983230072969 + 3 ^ 40 * 809084 * 2
def baseEnd_809084 : Nat := 184643991938852306146265

theorem tailTrace_809084 : CollatzResearch.WordTrace tailWord_809084 prefixEnd_809084 184643991938852306146265 := by
  unfold tailWord_809084
  simp only [CollatzResearch.WordTrace]
  refine ⟨14754858900417161695597153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19673145200556215594129537 14754858900417161695597153)
  ·
    refine ⟨11066144175312871271697865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14754858900417161695597153 11066144175312871271697865)
    ·
      refine ⟨8299608131484653453773399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11066144175312871271697865 8299608131484653453773399)
      ·
        refine ⟨12449412197226980180660099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8299608131484653453773399 12449412197226980180660099)
        ·
          refine ⟨18674118295840470270990149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12449412197226980180660099 18674118295840470270990149)
          ·
            refine ⟨3501397180470088175810653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18674118295840470270990149 3501397180470088175810653)
            ·
              refine ⟨1313023942676283065928995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3501397180470088175810653 1313023942676283065928995)
              ·
                refine ⟨1969535914014424598893493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313023942676283065928995 1969535914014424598893493)
                ·
                  refine ⟨184643991938852306146265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1969535914014424598893493 184643991938852306146265)
                  ·
                    rfl

theorem cell21_809084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_809084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_809084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_809084 prefixEnd_809084 := by exact prefixLift 809084
  have htrace : WordTrace (prefixWord ++ tailWord_809084) baseStart_809084 baseEnd_809084 := by
    simpa [prefixWord, tailWord_809084, baseEnd_809084] using wordTrace_append hprefix tailTrace_809084
  have hstable : (prefixWord ++ tailWord_809084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809084).length < 2 ^ (prefixWord ++ tailWord_809084).sum := by decide
  have hdescent : baseEnd_809084 < baseStart_809084 := by decide
  rcases family_descends (prefixWord ++ tailWord_809084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809191 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 6]
def baseStart_809191 : Nat := 118140960795 + 809191 * 2 ^ 59
def prefixEnd_809191 : Nat := 4983230072969 + 3 ^ 40 * 809191 * 2
def baseEnd_809191 : Nat := 184668410796643897862713

theorem tailTrace_809191 : CollatzResearch.WordTrace tailWord_809191 prefixEnd_809191 184668410796643897862713 := by
  unfold tailWord_809191
  simp only [CollatzResearch.WordTrace]
  refine ⟨29513620411446680665339427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19675746940964453776892951 29513620411446680665339427)
  ·
    refine ⟨44270430617170020998009141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29513620411446680665339427 44270430617170020998009141)
    ·
      refine ⟨4150352870359689468563357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44270430617170020998009141 4150352870359689468563357)
      ·
        refine ⟨1556382326384883550711259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4150352870359689468563357 1556382326384883550711259)
        ·
          refine ⟨2334573489577325326066889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1556382326384883550711259 2334573489577325326066889)
          ·
            refine ⟨1750930117182993994550167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2334573489577325326066889 1750930117182993994550167)
            ·
              refine ⟨2626395175774490991825251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1750930117182993994550167 2626395175774490991825251)
              ·
                refine ⟨3939592763661736487737877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2626395175774490991825251 3939592763661736487737877)
                ·
                  refine ⟨184668410796643897862713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3939592763661736487737877 184668410796643897862713)
                  ·
                    rfl

theorem cell21_809191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 6].length) (baseStart_809191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_809191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_809191 prefixEnd_809191 := by exact prefixLift 809191
  have htrace : WordTrace (prefixWord ++ tailWord_809191) baseStart_809191 baseEnd_809191 := by
    simpa [prefixWord, tailWord_809191, baseEnd_809191] using wordTrace_append hprefix tailTrace_809191
  have hstable : (prefixWord ++ tailWord_809191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809191).length < 2 ^ (prefixWord ++ tailWord_809191).sum := by decide
  have hdescent : baseEnd_809191 < baseStart_809191 := by decide
  rcases family_descends (prefixWord ++ tailWord_809191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809219 : List Nat := [1, 1, 1, 3, 2, 3, 1, 4, 5]
def baseStart_809219 : Nat := 118140960795 + 809219 * 2 ^ 59
def prefixEnd_809219 : Nat := 4983230072969 + 3 ^ 40 * 809219 * 2
def baseEnd_809219 : Nat := 184674800778122071395989

theorem tailTrace_809219 : CollatzResearch.WordTrace tailWord_809219 prefixEnd_809219 184674800778122071395989 := by
  unfold tailWord_809219
  simp only [CollatzResearch.WordTrace]
  refine ⟨29514641655345241447358711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19676427770230160964905807 29514641655345241447358711)
  ·
    refine ⟨44271962483017862171038067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29514641655345241447358711 44271962483017862171038067)
    ·
      refine ⟨66407943724526793256557101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44271962483017862171038067 66407943724526793256557101)
      ·
        refine ⟨24902978896697547471208913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66407943724526793256557101 24902978896697547471208913)
        ·
          refine ⟨18677234172523160603406685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24902978896697547471208913 18677234172523160603406685)
          ·
            refine ⟨7003962814696185226277507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18677234172523160603406685 7003962814696185226277507)
            ·
              refine ⟨10505944222044277839416261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7003962814696185226277507 10505944222044277839416261)
              ·
                refine ⟨1969864541633302094890549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10505944222044277839416261 1969864541633302094890549)
                ·
                  refine ⟨184674800778122071395989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1969864541633302094890549 184674800778122071395989)
                  ·
                    rfl

theorem cell21_809219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 5].length) (baseStart_809219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_809219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_809219 prefixEnd_809219 := by exact prefixLift 809219
  have htrace : WordTrace (prefixWord ++ tailWord_809219) baseStart_809219 baseEnd_809219 := by
    simpa [prefixWord, tailWord_809219, baseEnd_809219] using wordTrace_append hprefix tailTrace_809219
  have hstable : (prefixWord ++ tailWord_809219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809219).length < 2 ^ (prefixWord ++ tailWord_809219).sum := by decide
  have hdescent : baseEnd_809219 < baseStart_809219 := by decide
  rcases family_descends (prefixWord ++ tailWord_809219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809253 : List Nat := [1, 3, 1, 2, 5, 2, 1, 1, 5]
def baseStart_809253 : Nat := 118140960795 + 809253 * 2 ^ 59
def prefixEnd_809253 : Nat := 4983230072969 + 3 ^ 40 * 809253 * 2
def baseEnd_809253 : Nat := 184682560041345567829253

theorem tailTrace_809253 : CollatzResearch.WordTrace tailWord_809253 prefixEnd_809253 184682560041345567829253 := by
  unfold tailWord_809253
  simp only [CollatzResearch.WordTrace]
  refine ⟨29515881737222065254096413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19677254491481376836064275 29515881737222065254096413)
  ·
    refine ⟨11068455651458274470286155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29515881737222065254096413 11068455651458274470286155)
    ·
      refine ⟨16602683477187411705429233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11068455651458274470286155 16602683477187411705429233)
      ·
        refine ⟨12452012607890558779071925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16602683477187411705429233 12452012607890558779071925)
        ·
          refine ⟨1167376181989739885537993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12452012607890558779071925 1167376181989739885537993)
          ·
            refine ⟨875532136492304914153495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1167376181989739885537993 875532136492304914153495)
            ·
              refine ⟨1313298204738457371230243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875532136492304914153495 1313298204738457371230243)
              ·
                refine ⟨1969947307107686056845365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313298204738457371230243 1969947307107686056845365)
                ·
                  refine ⟨184682560041345567829253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1969947307107686056845365 184682560041345567829253)
                  ·
                    rfl

theorem cell21_809253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_809253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_809253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_809253 prefixEnd_809253 := by exact prefixLift 809253
  have htrace : WordTrace (prefixWord ++ tailWord_809253) baseStart_809253 baseEnd_809253 := by
    simpa [prefixWord, tailWord_809253, baseEnd_809253] using wordTrace_append hprefix tailTrace_809253
  have hstable : (prefixWord ++ tailWord_809253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809253).length < 2 ^ (prefixWord ++ tailWord_809253).sum := by decide
  have hdescent : baseEnd_809253 < baseStart_809253 := by decide
  rcases family_descends (prefixWord ++ tailWord_809253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809377 : List Nat := [1, 2, 3, 5, 1, 1, 3, 1, 4]
def baseStart_809377 : Nat := 118140960795 + 809377 * 2 ^ 59
def prefixEnd_809377 : Nat := 4983230072969 + 3 ^ 40 * 809377 * 2
def baseEnd_809377 : Nat := 184710858530748907762333

theorem tailTrace_809377 : CollatzResearch.WordTrace tailWord_809377 prefixEnd_809377 184710858530748907762333 := by
  unfold tailWord_809377
  simp only [CollatzResearch.WordTrace]
  refine ⟨29520404388772834431610385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19680269592515222954406923 29520404388772834431610385)
  ·
    refine ⟨22140303291579625823707789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29520404388772834431610385 22140303291579625823707789)
    ·
      refine ⟨8302613734342359683890421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22140303291579625823707789 8302613734342359683890421)
      ·
        refine ⟨778370037594596220364727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8302613734342359683890421 778370037594596220364727)
        ·
          refine ⟨1167555056391894330547091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778370037594596220364727 1167555056391894330547091)
          ·
            refine ⟨1751332584587841495820637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1167555056391894330547091 1751332584587841495820637)
            ·
              refine ⟨656749719220440560932739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1751332584587841495820637 656749719220440560932739)
              ·
                refine ⟨985124578830660841399109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 656749719220440560932739 985124578830660841399109)
                ·
                  refine ⟨184710858530748907762333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 985124578830660841399109 184710858530748907762333)
                  ·
                    rfl

theorem cell21_809377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 4].length) (baseStart_809377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_809377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_809377 prefixEnd_809377 := by exact prefixLift 809377
  have htrace : WordTrace (prefixWord ++ tailWord_809377) baseStart_809377 baseEnd_809377 := by
    simpa [prefixWord, tailWord_809377, baseEnd_809377] using wordTrace_append hprefix tailTrace_809377
  have hstable : (prefixWord ++ tailWord_809377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809377).length < 2 ^ (prefixWord ++ tailWord_809377).sum := by decide
  have hdescent : baseEnd_809377 < baseStart_809377 := by decide
  rcases family_descends (prefixWord ++ tailWord_809377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809405 : List Nat := [1, 4, 1, 2, 2, 2, 3, 3, 3]
def baseStart_809405 : Nat := 118140960795 + 809405 * 2 ^ 59
def prefixEnd_809405 : Nat := 4983230072969 + 3 ^ 40 * 809405 * 2
def baseEnd_809405 : Nat := 184717248512227081295609

theorem tailTrace_809405 : CollatzResearch.WordTrace tailWord_809405 prefixEnd_809405 184717248512227081295609 := by
  unfold tailWord_809405
  simp only [CollatzResearch.WordTrace]
  refine ⟨29521425632671395213629669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19680950421780930142419779 29521425632671395213629669)
  ·
    refine ⟨5535267306125886602555563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29521425632671395213629669 5535267306125886602555563)
    ·
      refine ⟨8302900959188829903833345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5535267306125886602555563 8302900959188829903833345)
      ·
        refine ⟨6227175719391622427875009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8302900959188829903833345 6227175719391622427875009)
        ·
          refine ⟨4670381789543716820906257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6227175719391622427875009 4670381789543716820906257)
          ·
            refine ⟨3502786342157787615679693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4670381789543716820906257 3502786342157787615679693)
            ·
              refine ⟨1313544878309170355879885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3502786342157787615679693 1313544878309170355879885)
              ·
                refine ⟨492579329365938883454957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1313544878309170355879885 492579329365938883454957)
                ·
                  refine ⟨184717248512227081295609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 492579329365938883454957 184717248512227081295609)
                  ·
                    rfl

theorem cell21_809405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_809405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_809405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_809405 prefixEnd_809405 := by exact prefixLift 809405
  have htrace : WordTrace (prefixWord ++ tailWord_809405) baseStart_809405 baseEnd_809405 := by
    simpa [prefixWord, tailWord_809405, baseEnd_809405] using wordTrace_append hprefix tailTrace_809405
  have hstable : (prefixWord ++ tailWord_809405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809405).length < 2 ^ (prefixWord ++ tailWord_809405).sum := by decide
  have hdescent : baseEnd_809405 < baseStart_809405 := by decide
  rcases family_descends (prefixWord ++ tailWord_809405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809416 : List Nat := [2, 1, 3, 1, 3, 2, 9]
def baseStart_809416 : Nat := 118140960795 + 809416 * 2 ^ 59
def prefixEnd_809416 : Nat := 4983230072969 + 3 ^ 40 * 809416 * 2
def baseEnd_809416 : Nat := 20524417651343722956917

theorem tailTrace_809416 : CollatzResearch.WordTrace tailWord_809416 prefixEnd_809416 20524417651343722956917 := by
  unfold tailWord_809416
  simp only [CollatzResearch.WordTrace]
  refine ⟨14760913417815772046140051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19681217890421029394853401 14760913417815772046140051)
  ·
    refine ⟨22141370126723658069210077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14760913417815772046140051 22141370126723658069210077)
    ·
      refine ⟨8303013797521371775953779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22141370126723658069210077 8303013797521371775953779)
      ·
        refine ⟨12454520696282057663930669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8303013797521371775953779 12454520696282057663930669)
        ·
          refine ⟨4670445261105771623974001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12454520696282057663930669 4670445261105771623974001)
          ·
            refine ⟨3502833945829328717980501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4670445261105771623974001 3502833945829328717980501)
            ·
              refine ⟨20524417651343722956917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3502833945829328717980501 20524417651343722956917)
              ·
                rfl

theorem cell21_809416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 9].length) (baseStart_809416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_809416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_809416 prefixEnd_809416 := by exact prefixLift 809416
  have htrace : WordTrace (prefixWord ++ tailWord_809416) baseStart_809416 baseEnd_809416 := by
    simpa [prefixWord, tailWord_809416, baseEnd_809416] using wordTrace_append hprefix tailTrace_809416
  have hstable : (prefixWord ++ tailWord_809416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809416).length < 2 ^ (prefixWord ++ tailWord_809416).sum := by decide
  have hdescent : baseEnd_809416 < baseStart_809416 := by decide
  rcases family_descends (prefixWord ++ tailWord_809416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809447 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 7]
def baseStart_809447 : Nat := 118140960795 + 809447 * 2 ^ 59
def prefixEnd_809447 : Nat := 4983230072969 + 3 ^ 40 * 809447 * 2
def baseEnd_809447 : Nat := 184726833484444341595523

theorem tailTrace_809447 : CollatzResearch.WordTrace tailWord_809447 prefixEnd_809447 184726833484444341595523 := by
  unfold tailWord_809447
  simp only [CollatzResearch.WordTrace]
  refine ⟨29522957498519236386658595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19681971665679490924439063 29522957498519236386658595)
  ·
    refine ⟨44284436247778854579987893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29522957498519236386658595 44284436247778854579987893)
    ·
      refine ⟨4151665898229267616873865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44284436247778854579987893 4151665898229267616873865)
      ·
        refine ⟨3113749423671950712655399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4151665898229267616873865 3113749423671950712655399)
        ·
          refine ⟨4670624135507926068983099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3113749423671950712655399 4670624135507926068983099)
          ·
            refine ⟨7005936203261889103474649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4670624135507926068983099 7005936203261889103474649)
            ·
              refine ⟨5254452152446416827605987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7005936203261889103474649 5254452152446416827605987)
              ·
                refine ⟨7881678228669625241408981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5254452152446416827605987 7881678228669625241408981)
                ·
                  refine ⟨184726833484444341595523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7881678228669625241408981 184726833484444341595523)
                  ·
                    rfl

theorem cell21_809447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 7].length) (baseStart_809447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_809447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_809447 prefixEnd_809447 := by exact prefixLift 809447
  have htrace : WordTrace (prefixWord ++ tailWord_809447) baseStart_809447 baseEnd_809447 := by
    simpa [prefixWord, tailWord_809447, baseEnd_809447] using wordTrace_append hprefix tailTrace_809447
  have hstable : (prefixWord ++ tailWord_809447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809447).length < 2 ^ (prefixWord ++ tailWord_809447).sum := by decide
  have hdescent : baseEnd_809447 < baseStart_809447 := by decide
  rcases family_descends (prefixWord ++ tailWord_809447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809464 : List Nat := [2, 1, 2, 1, 1, 4, 2, 5, 3]
def baseStart_809464 : Nat := 118140960795 + 809464 * 2 ^ 59
def prefixEnd_809464 : Nat := 4983230072969 + 3 ^ 40 * 809464 * 2
def baseEnd_809464 : Nat := 184730713116056089812155

theorem tailTrace_809464 : CollatzResearch.WordTrace tailWord_809464 prefixEnd_809464 184730713116056089812155 := by
  unfold tailWord_809464
  simp only [CollatzResearch.WordTrace]
  refine ⟨14761788769728824145013723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19682385026305098860018297 14761788769728824145013723)
  ·
    refine ⟨22142683154593236217520585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14761788769728824145013723 22142683154593236217520585)
    ·
      refine ⟨16607012365944927163140439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22142683154593236217520585 16607012365944927163140439)
      ·
        refine ⟨24910518548917390744710659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16607012365944927163140439 24910518548917390744710659)
        ·
          refine ⟨37365777823376086117065989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24910518548917390744710659 37365777823376086117065989)
          ·
            refine ⟨7006083341883016146949873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37365777823376086117065989 7006083341883016146949873)
            ·
              refine ⟨5254562506412262110212405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7006083341883016146949873 5254562506412262110212405)
              ·
                refine ⟨492615234976149572832413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5254562506412262110212405 492615234976149572832413)
                ·
                  refine ⟨184730713116056089812155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 492615234976149572832413 184730713116056089812155)
                  ·
                    rfl

theorem cell21_809464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 3].length) (baseStart_809464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_809464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_809464 prefixEnd_809464 := by exact prefixLift 809464
  have htrace : WordTrace (prefixWord ++ tailWord_809464) baseStart_809464 baseEnd_809464 := by
    simpa [prefixWord, tailWord_809464, baseEnd_809464] using wordTrace_append hprefix tailTrace_809464
  have hstable : (prefixWord ++ tailWord_809464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809464).length < 2 ^ (prefixWord ++ tailWord_809464).sum := by decide
  have hdescent : baseEnd_809464 < baseStart_809464 := by decide
  rcases family_descends (prefixWord ++ tailWord_809464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809661 : List Nat := [1, 4, 1, 2, 1, 5, 1, 6]
def baseStart_809661 : Nat := 118140960795 + 809661 * 2 ^ 59
def prefixEnd_809661 : Nat := 4983230072969 + 3 ^ 40 * 809661 * 2
def baseEnd_809661 : Nat := 61591890400009175009473

theorem tailTrace_809661 : CollatzResearch.WordTrace tailWord_809661 prefixEnd_809661 61591890400009175009473 := by
  unfold tailWord_809661
  simp only [CollatzResearch.WordTrace]
  refine ⟨29530762719743950934948837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19687175146495967289965891 29530762719743950934948837)
  ·
    refine ⟨5537018009951990800302907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29530762719743950934948837 5537018009951990800302907)
    ·
      refine ⟨8305527014927986200454361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5537018009951990800302907 8305527014927986200454361)
      ·
        refine ⟨6229145261195989650340771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8305527014927986200454361 6229145261195989650340771)
        ·
          refine ⟨9343717891793984475511157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6229145261195989650340771 9343717891793984475511157)
          ·
            refine ⟨875973552355686044579171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9343717891793984475511157 875973552355686044579171)
            ·
              refine ⟨1313960328533529066868757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875973552355686044579171 1313960328533529066868757)
              ·
                refine ⟨61591890400009175009473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1313960328533529066868757 61591890400009175009473)
                ·
                  rfl

theorem cell21_809661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 6].length) (baseStart_809661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_809661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_809661 prefixEnd_809661 := by exact prefixLift 809661
  have htrace : WordTrace (prefixWord ++ tailWord_809661) baseStart_809661 baseEnd_809661 := by
    simpa [prefixWord, tailWord_809661, baseEnd_809661] using wordTrace_append hprefix tailTrace_809661
  have hstable : (prefixWord ++ tailWord_809661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809661).length < 2 ^ (prefixWord ++ tailWord_809661).sum := by decide
  have hdescent : baseEnd_809661 < baseStart_809661 := by decide
  rcases family_descends (prefixWord ++ tailWord_809661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809689 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 6]
def baseStart_809689 : Nat := 118140960795 + 809689 * 2 ^ 59
def prefixEnd_809689 : Nat := 4983230072969 + 3 ^ 40 * 809689 * 2
def baseEnd_809689 : Nat := 184782061181505698561695

theorem tailTrace_809689 : CollatzResearch.WordTrace tailWord_809689 prefixEnd_809689 184782061181505698561695 := by
  unfold tailWord_809689
  simp only [CollatzResearch.WordTrace]
  refine ⟨29531783963642511716968121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19687855975761674477978747 29531783963642511716968121)
  ·
    refine ⟨22148837972731883787726091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29531783963642511716968121 22148837972731883787726091)
    ·
      refine ⟨33223256959097825681589137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22148837972731883787726091 33223256959097825681589137)
      ·
        refine ⟨24917442719323369261191853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33223256959097825681589137 24917442719323369261191853)
        ·
          refine ⟨9344041019746263472946945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24917442719323369261191853 9344041019746263472946945)
          ·
            refine ⟨7008030764809697604710209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9344041019746263472946945 7008030764809697604710209)
            ·
              refine ⟨5256023073607273203532657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7008030764809697604710209 5256023073607273203532657)
              ·
                refine ⟨3942017305205454902649493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5256023073607273203532657 3942017305205454902649493)
                ·
                  refine ⟨184782061181505698561695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3942017305205454902649493 184782061181505698561695)
                  ·
                    rfl

theorem cell21_809689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_809689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_809689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_809689 prefixEnd_809689 := by exact prefixLift 809689
  have htrace : WordTrace (prefixWord ++ tailWord_809689) baseStart_809689 baseEnd_809689 := by
    simpa [prefixWord, tailWord_809689, baseEnd_809689] using wordTrace_append hprefix tailTrace_809689
  have hstable : (prefixWord ++ tailWord_809689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809689).length < 2 ^ (prefixWord ++ tailWord_809689).sum := by decide
  have hdescent : baseEnd_809689 < baseStart_809689 := by decide
  rcases family_descends (prefixWord ++ tailWord_809689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809765 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 6]
def baseStart_809765 : Nat := 118140960795 + 809765 * 2 ^ 59
def prefixEnd_809765 : Nat := 4983230072969 + 3 ^ 40 * 809765 * 2
def baseEnd_809765 : Nat := 184799405416946455294873

theorem tailTrace_809765 : CollatzResearch.WordTrace tailWord_809765 prefixEnd_809765 184799405416946455294873 := by
  unfold tailWord_809765
  simp only [CollatzResearch.WordTrace]
  refine ⟨29534555911367176696734749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19689703940911451131156499 29534555911367176696734749)
  ·
    refine ⟨11075458466762691261275531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29534555911367176696734749 11075458466762691261275531)
    ·
      refine ⟨16613187700144036891913297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11075458466762691261275531 16613187700144036891913297)
      ·
        refine ⟨12459890775108027668934973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16613187700144036891913297 12459890775108027668934973)
        ·
          refine ⟨4672459040665510375850615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12459890775108027668934973 4672459040665510375850615)
          ·
            refine ⟨7008688560998265563775923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4672459040665510375850615 7008688560998265563775923)
            ·
              refine ⟨10513032841497398345663885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7008688560998265563775923 10513032841497398345663885)
              ·
                refine ⟨3942387315561524379623957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10513032841497398345663885 3942387315561524379623957)
                ·
                  refine ⟨184799405416946455294873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3942387315561524379623957 184799405416946455294873)
                  ·
                    rfl

theorem cell21_809765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_809765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_809765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_809765 prefixEnd_809765 := by exact prefixLift 809765
  have htrace : WordTrace (prefixWord ++ tailWord_809765) baseStart_809765 baseEnd_809765 := by
    simpa [prefixWord, tailWord_809765, baseEnd_809765] using wordTrace_append hprefix tailTrace_809765
  have hstable : (prefixWord ++ tailWord_809765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809765).length < 2 ^ (prefixWord ++ tailWord_809765).sum := by decide
  have hdescent : baseEnd_809765 < baseStart_809765 := by decide
  rcases family_descends (prefixWord ++ tailWord_809765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809855 : List Nat := [1, 1, 2, 2, 1, 1, 4, 9]
def baseStart_809855 : Nat := 118140960795 + 809855 * 2 ^ 59
def prefixEnd_809855 : Nat := 4983230072969 + 3 ^ 40 * 809855 * 2
def baseEnd_809855 : Nat := 61606648214375432931563

theorem tailTrace_809855 : CollatzResearch.WordTrace tailWord_809855 prefixEnd_809855 61606648214375432931563 := by
  unfold tailWord_809855
  simp only [CollatzResearch.WordTrace]
  refine ⟨29537838481041122067511019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19691892320694081378340679 29537838481041122067511019)
  ·
    refine ⟨44306757721561683101266529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29537838481041122067511019 44306757721561683101266529)
    ·
      refine ⟨33230068291171262325949897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44306757721561683101266529 33230068291171262325949897)
      ·
        refine ⟨24922551218378446744462423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33230068291171262325949897 24922551218378446744462423)
        ·
          refine ⟨37383826827567670116693635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24922551218378446744462423 37383826827567670116693635)
          ·
            refine ⟨56075740241351505175040453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37383826827567670116693635 56075740241351505175040453)
            ·
              refine ⟨10514201295253407220320085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56075740241351505175040453 10514201295253407220320085)
              ·
                refine ⟨61606648214375432931563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10514201295253407220320085 61606648214375432931563)
                ·
                  rfl

theorem cell21_809855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 9].length) (baseStart_809855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_809855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_809855 prefixEnd_809855 := by exact prefixLift 809855
  have htrace : WordTrace (prefixWord ++ tailWord_809855) baseStart_809855 baseEnd_809855 := by
    simpa [prefixWord, tailWord_809855, baseEnd_809855] using wordTrace_append hprefix tailTrace_809855
  have hstable : (prefixWord ++ tailWord_809855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809855).length < 2 ^ (prefixWord ++ tailWord_809855).sum := by decide
  have hdescent : baseEnd_809855 < baseStart_809855 := by decide
  rcases family_descends (prefixWord ++ tailWord_809855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809878 : List Nat := [5, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_809878 : Nat := 118140960795 + 809878 * 2 ^ 59
def prefixEnd_809878 : Nat := 4983230072969 + 3 ^ 40 * 809878 * 2
def baseEnd_809878 : Nat := 184825193556483369911309

theorem tailTrace_809878 : CollatzResearch.WordTrace tailWord_809878 prefixEnd_809878 184825193556483369911309 := by
  unfold tailWord_809878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1846167334997362312224893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19692451573305197997065525 1846167334997362312224893)
  ·
    refine ⟨692312750624010867084335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1846167334997362312224893 692312750624010867084335)
    ·
      refine ⟨1038469125936016300626503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 692312750624010867084335 1038469125936016300626503)
      ·
        refine ⟨1557703688904024450939755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1038469125936016300626503 1557703688904024450939755)
        ·
          refine ⟨2336555533356036676409633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1557703688904024450939755 2336555533356036676409633)
          ·
            refine ⟨1752416650017027507307225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2336555533356036676409633 1752416650017027507307225)
            ·
              refine ⟨1314312487512770630480419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1752416650017027507307225 1314312487512770630480419)
              ·
                refine ⟨1971468731269155945720629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1314312487512770630480419 1971468731269155945720629)
                ·
                  refine ⟨184825193556483369911309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1971468731269155945720629 184825193556483369911309)
                  ·
                    rfl

theorem cell21_809878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_809878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_809878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_809878 prefixEnd_809878 := by exact prefixLift 809878
  have htrace : WordTrace (prefixWord ++ tailWord_809878) baseStart_809878 baseEnd_809878 := by
    simpa [prefixWord, tailWord_809878, baseEnd_809878] using wordTrace_append hprefix tailTrace_809878
  have hstable : (prefixWord ++ tailWord_809878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809878).length < 2 ^ (prefixWord ++ tailWord_809878).sum := by decide
  have hdescent : baseEnd_809878 < baseStart_809878 := by decide
  rcases family_descends (prefixWord ++ tailWord_809878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809920 : List Nat := [2, 1, 1, 2, 3, 3, 3, 3, 3]
def baseStart_809920 : Nat := 118140960795 + 809920 * 2 ^ 59
def prefixEnd_809920 : Nat := 4983230072969 + 3 ^ 40 * 809920 * 2
def baseEnd_809920 : Nat := 184834778528700630211223

theorem tailTrace_809920 : CollatzResearch.WordTrace tailWord_809920 prefixEnd_809920 184834778528700630211223 := by
  unfold tailWord_809920
  simp only [CollatzResearch.WordTrace]
  refine ⟨14770104612902819084313607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19693472817203758779084809 14770104612902819084313607)
  ·
    refine ⟨22155156919354228626470411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14770104612902819084313607 22155156919354228626470411)
    ·
      refine ⟨33232735379031342939705617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22155156919354228626470411 33232735379031342939705617)
      ·
        refine ⟨24924551534273507204779213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33232735379031342939705617 24924551534273507204779213)
        ·
          refine ⟨9346706825352565201792205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24924551534273507204779213 9346706825352565201792205)
          ·
            refine ⟨3505015059507211950672077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9346706825352565201792205 3505015059507211950672077)
            ·
              refine ⟨1314380647315204481502029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3505015059507211950672077 1314380647315204481502029)
              ·
                refine ⟨492892742743201680563261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1314380647315204481502029 492892742743201680563261)
                ·
                  refine ⟨184834778528700630211223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 492892742743201680563261 184834778528700630211223)
                  ·
                    rfl

theorem cell21_809920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 3].length) (baseStart_809920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_809920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_809920 prefixEnd_809920 := by exact prefixLift 809920
  have htrace : WordTrace (prefixWord ++ tailWord_809920) baseStart_809920 baseEnd_809920 := by
    simpa [prefixWord, tailWord_809920, baseEnd_809920] using wordTrace_append hprefix tailTrace_809920
  have hstable : (prefixWord ++ tailWord_809920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809920).length < 2 ^ (prefixWord ++ tailWord_809920).sum := by decide
  have hdescent : baseEnd_809920 < baseStart_809920 := by decide
  rcases family_descends (prefixWord ++ tailWord_809920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809931 : List Nat := [1, 1, 1, 1, 3, 5, 9]
def baseStart_809931 : Nat := 118140960795 + 809931 * 2 ^ 59
def prefixEnd_809931 : Nat := 4983230072969 + 3 ^ 40 * 809931 * 2
def baseEnd_809931 : Nat := 20537476542063006169763

theorem tailTrace_809931 : CollatzResearch.WordTrace tailWord_809931 prefixEnd_809931 20537476542063006169763 := by
  unfold tailWord_809931
  simp only [CollatzResearch.WordTrace]
  refine ⟨29540610428765787047277647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19693740285843858031518431 29540610428765787047277647)
  ·
    refine ⟨44310915643148680570916471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29540610428765787047277647 44310915643148680570916471)
    ·
      refine ⟨66466373464723020856374707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44310915643148680570916471 66466373464723020856374707)
      ·
        refine ⟨99699560197084531284562061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66466373464723020856374707 99699560197084531284562061)
        ·
          refine ⟨37387335073906699231710773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99699560197084531284562061 37387335073906699231710773)
          ·
            refine ⟨3505062663178753052972885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37387335073906699231710773 3505062663178753052972885)
            ·
              refine ⟨20537476542063006169763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3505062663178753052972885 20537476542063006169763)
              ·
                rfl

theorem cell21_809931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 9].length) (baseStart_809931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_809931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_809931 prefixEnd_809931 := by exact prefixLift 809931
  have htrace : WordTrace (prefixWord ++ tailWord_809931) baseStart_809931 baseEnd_809931 := by
    simpa [prefixWord, tailWord_809931, baseEnd_809931] using wordTrace_append hprefix tailTrace_809931
  have hstable : (prefixWord ++ tailWord_809931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809931).length < 2 ^ (prefixWord ++ tailWord_809931).sum := by decide
  have hdescent : baseEnd_809931 < baseStart_809931 := by decide
  rcases family_descends (prefixWord ++ tailWord_809931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809979 : List Nat := [1, 1, 1, 1, 1, 3, 3, 7, 3]
def baseStart_809979 : Nat := 118140960795 + 809979 * 2 ^ 59
def prefixEnd_809979 : Nat := 4983230072969 + 3 ^ 40 * 809979 * 2
def baseEnd_809979 : Nat := 184848243132529638727769

theorem tailTrace_809979 : CollatzResearch.WordTrace tailWord_809979 prefixEnd_809979 184848243132529638727769 := by
  unfold tailWord_809979
  simp only [CollatzResearch.WordTrace]
  refine ⟨29542361132591891245024991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19694907421727927496683327 29542361132591891245024991)
  ·
    refine ⟨44313541698887836867537487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29542361132591891245024991 44313541698887836867537487)
    ·
      refine ⟨66470312548331755301306231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44313541698887836867537487 66470312548331755301306231)
      ·
        refine ⟨99705468822497632951959347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66470312548331755301306231 99705468822497632951959347)
        ·
          refine ⟨149558203233746449427939021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99705468822497632951959347 149558203233746449427939021)
          ·
            refine ⟨56084326212654918535477133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149558203233746449427939021 56084326212654918535477133)
            ·
              refine ⟨21031622329745594450803925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56084326212654918535477133 21031622329745594450803925)
              ·
                refine ⟨492928648353412369940717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21031622329745594450803925 492928648353412369940717)
                ·
                  refine ⟨184848243132529638727769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 492928648353412369940717 184848243132529638727769)
                  ·
                    rfl

theorem cell21_809979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 3].length) (baseStart_809979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_809979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_809979 prefixEnd_809979 := by exact prefixLift 809979
  have htrace : WordTrace (prefixWord ++ tailWord_809979) baseStart_809979 baseEnd_809979 := by
    simpa [prefixWord, tailWord_809979, baseEnd_809979] using wordTrace_append hprefix tailTrace_809979
  have hstable : (prefixWord ++ tailWord_809979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809979).length < 2 ^ (prefixWord ++ tailWord_809979).sum := by decide
  have hdescent : baseEnd_809979 < baseStart_809979 := by decide
  rcases family_descends (prefixWord ++ tailWord_809979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809996 : List Nat := [2, 2, 1, 2, 3, 3, 1, 4, 3]
def baseStart_809996 : Nat := 118140960795 + 809996 * 2 ^ 59
def prefixEnd_809996 : Nat := 4983230072969 + 3 ^ 40 * 809996 * 2
def baseEnd_809996 : Nat := 184852122764141386944401

theorem tailTrace_809996 : CollatzResearch.WordTrace tailWord_809996 prefixEnd_809996 184852122764141386944401 := by
  unfold tailWord_809996
  simp only [CollatzResearch.WordTrace]
  refine ⟨14771490586765151574196921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19695320782353535432262561 14771490586765151574196921)
  ·
    refine ⟨11078617940073863680647691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14771490586765151574196921 11078617940073863680647691)
    ·
      refine ⟨16617926910110795520971537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11078617940073863680647691 16617926910110795520971537)
      ·
        refine ⟨12463445182583096640728653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16617926910110795520971537 12463445182583096640728653)
        ·
          refine ⟨4673791943468661240273245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12463445182583096640728653 4673791943468661240273245)
          ·
            refine ⟨1752671978800747965102467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4673791943468661240273245 1752671978800747965102467)
            ·
              refine ⟨2629007968201121947653701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1752671978800747965102467 2629007968201121947653701)
              ·
                refine ⟨492938994037710365185069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2629007968201121947653701 492938994037710365185069)
                ·
                  refine ⟨184852122764141386944401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 492938994037710365185069 184852122764141386944401)
                  ·
                    rfl

theorem cell21_809996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_809996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_809996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_809996 prefixEnd_809996 := by exact prefixLift 809996
  have htrace : WordTrace (prefixWord ++ tailWord_809996) baseStart_809996 baseEnd_809996 := by
    simpa [prefixWord, tailWord_809996, baseEnd_809996] using wordTrace_append hprefix tailTrace_809996
  have hstable : (prefixWord ++ tailWord_809996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809996).length < 2 ^ (prefixWord ++ tailWord_809996).sum := by decide
  have hdescent : baseEnd_809996 < baseStart_809996 := by decide
  rcases family_descends (prefixWord ++ tailWord_809996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810055 : List Nat := [1, 1, 4, 1, 3, 3, 2, 1, 5]
def baseStart_810055 : Nat := 118140960795 + 810055 * 2 ^ 59
def prefixEnd_810055 : Nat := 4983230072969 + 3 ^ 40 * 810055 * 2
def baseEnd_810055 : Nat := 184865587367970395460947

theorem tailTrace_810055 : CollatzResearch.WordTrace tailWord_810055 prefixEnd_810055 184865587367970395460947 := by
  unfold tailWord_810055
  simp only [CollatzResearch.WordTrace]
  refine ⟨29545133080316556224791619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19696755386877704149861079 29545133080316556224791619)
  ·
    refine ⟨44317699620474834337187429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29545133080316556224791619 44317699620474834337187429)
    ·
      refine ⟨8309568678839031438222643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44317699620474834337187429 8309568678839031438222643)
      ·
        refine ⟨12464353018258547157333965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8309568678839031438222643 12464353018258547157333965)
        ·
          refine ⟨4674132381846955184000237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12464353018258547157333965 4674132381846955184000237)
          ·
            refine ⟨1752799643192608194000089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4674132381846955184000237 1752799643192608194000089)
            ·
              refine ⟨1314599732394456145500067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1752799643192608194000089 1314599732394456145500067)
              ·
                refine ⟨1971899598591684218250101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1314599732394456145500067 1971899598591684218250101)
                ·
                  refine ⟨184865587367970395460947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1971899598591684218250101 184865587367970395460947)
                  ·
                    rfl

theorem cell21_810055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 5].length) (baseStart_810055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810055 prefixEnd_810055 := by exact prefixLift 810055
  have htrace : WordTrace (prefixWord ++ tailWord_810055) baseStart_810055 baseEnd_810055 := by
    simpa [prefixWord, tailWord_810055, baseEnd_810055] using wordTrace_append hprefix tailTrace_810055
  have hstable : (prefixWord ++ tailWord_810055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810055).length < 2 ^ (prefixWord ++ tailWord_810055).sum := by decide
  have hdescent : baseEnd_810055 < baseStart_810055 := by decide
  rcases family_descends (prefixWord ++ tailWord_810055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810120 : List Nat := [2, 1, 3, 4, 2, 2, 2, 1, 4]
def baseStart_810120 : Nat := 118140960795 + 810120 * 2 ^ 59
def prefixEnd_810120 : Nat := 4983230072969 + 3 ^ 40 * 810120 * 2
def baseEnd_810120 : Nat := 184880421253544726877481

theorem tailTrace_810120 : CollatzResearch.WordTrace tailWord_810120 prefixEnd_810120 184880421253544726877481 := by
  unfold tailWord_810120
  simp only [CollatzResearch.WordTrace]
  refine ⟨14773751912540536162953907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19698335883387381550605209 14773751912540536162953907)
  ·
    refine ⟨22160627868810804244430861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14773751912540536162953907 22160627868810804244430861)
    ·
      refine ⟨8310235450804051591661573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22160627868810804244430861 8310235450804051591661573)
      ·
        refine ⟨1558169147025759673436545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8310235450804051591661573 1558169147025759673436545)
        ·
          refine ⟨1168626860269319755077409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1558169147025759673436545 1168626860269319755077409)
          ·
            refine ⟨876470145201989816308057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1168626860269319755077409 876470145201989816308057)
            ·
              refine ⟨657352608901492362231043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 876470145201989816308057 657352608901492362231043)
              ·
                refine ⟨986028913352238543346565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657352608901492362231043 986028913352238543346565)
                ·
                  refine ⟨184880421253544726877481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 986028913352238543346565 184880421253544726877481)
                  ·
                    rfl

theorem cell21_810120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 4].length) (baseStart_810120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810120 prefixEnd_810120 := by exact prefixLift 810120
  have htrace : WordTrace (prefixWord ++ tailWord_810120) baseStart_810120 baseEnd_810120 := by
    simpa [prefixWord, tailWord_810120, baseEnd_810120] using wordTrace_append hprefix tailTrace_810120
  have hstable : (prefixWord ++ tailWord_810120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810120).length < 2 ^ (prefixWord ++ tailWord_810120).sum := by decide
  have hdescent : baseEnd_810120 < baseStart_810120 := by decide
  rcases family_descends (prefixWord ++ tailWord_810120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810128 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 8]
def baseStart_810128 : Nat := 118140960795 + 810128 * 2 ^ 59
def prefixEnd_810128 : Nat := 4983230072969 + 3 ^ 40 * 810128 * 2
def baseEnd_810128 : Nat := 184882246962538490744131

theorem tailTrace_810128 : CollatzResearch.WordTrace tailWord_810128 prefixEnd_810128 184882246962538490744131 := by
  unfold tailWord_810128
  simp only [CollatzResearch.WordTrace]
  refine ⟨14773897804526044846099519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19698530406034726461466025 14773897804526044846099519)
  ·
    refine ⟨22160846706789067269149279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14773897804526044846099519 22160846706789067269149279)
    ·
      refine ⟨33241270060183600903723919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22160846706789067269149279 33241270060183600903723919)
      ·
        refine ⟨49861905090275401355585879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33241270060183600903723919 49861905090275401355585879)
        ·
          refine ⟨74792857635413102033378819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49861905090275401355585879 74792857635413102033378819)
          ·
            refine ⟨112189286453119653050068229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74792857635413102033378819 112189286453119653050068229)
            ·
              refine ⟨21035491209959934946887793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112189286453119653050068229 21035491209959934946887793)
              ·
                refine ⟨15776618407469951210165845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21035491209959934946887793 15776618407469951210165845)
                ·
                  refine ⟨184882246962538490744131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15776618407469951210165845 184882246962538490744131)
                  ·
                    rfl

theorem cell21_810128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_810128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810128 prefixEnd_810128 := by exact prefixLift 810128
  have htrace : WordTrace (prefixWord ++ tailWord_810128) baseStart_810128 baseEnd_810128 := by
    simpa [prefixWord, tailWord_810128, baseEnd_810128] using wordTrace_append hprefix tailTrace_810128
  have hstable : (prefixWord ++ tailWord_810128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810128).length < 2 ^ (prefixWord ++ tailWord_810128).sum := by decide
  have hdescent : baseEnd_810128 < baseStart_810128 := by decide
  rcases family_descends (prefixWord ++ tailWord_810128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810162 : List Nat := [3, 2, 1, 1, 1, 5, 2, 2, 4]
def baseStart_810162 : Nat := 118140960795 + 810162 * 2 ^ 59
def prefixEnd_810162 : Nat := 4983230072969 + 3 ^ 40 * 810162 * 2
def baseEnd_810162 : Nat := 184890006225761987177395

theorem tailTrace_810162 : CollatzResearch.WordTrace tailWord_810162 prefixEnd_810162 184890006225761987177395 := by
  unfold tailWord_810162
  simp only [CollatzResearch.WordTrace]
  refine ⟨7387258922732228374734185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19699357127285942332624493 7387258922732228374734185)
  ·
    refine ⟨5540444192049171281050639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7387258922732228374734185 5540444192049171281050639)
    ·
      refine ⟨8310666288073756921575959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5540444192049171281050639 8310666288073756921575959)
      ·
        refine ⟨12465999432110635382363939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8310666288073756921575959 12465999432110635382363939)
        ·
          refine ⟨18698999148165953073545909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12465999432110635382363939 18698999148165953073545909)
          ·
            refine ⟨1753031170140558100644929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18698999148165953073545909 1753031170140558100644929)
            ·
              refine ⟨1314773377605418575483697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1753031170140558100644929 1314773377605418575483697)
              ·
                refine ⟨986080033204063931612773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1314773377605418575483697 986080033204063931612773)
                ·
                  refine ⟨184890006225761987177395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 986080033204063931612773 184890006225761987177395)
                  ·
                    rfl

theorem cell21_810162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_810162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810162 prefixEnd_810162 := by exact prefixLift 810162
  have htrace : WordTrace (prefixWord ++ tailWord_810162) baseStart_810162 baseEnd_810162 := by
    simpa [prefixWord, tailWord_810162, baseEnd_810162] using wordTrace_append hprefix tailTrace_810162
  have hstable : (prefixWord ++ tailWord_810162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810162).length < 2 ^ (prefixWord ++ tailWord_810162).sum := by decide
  have hdescent : baseEnd_810162 < baseStart_810162 := by decide
  rcases family_descends (prefixWord ++ tailWord_810162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810182 : List Nat := [6, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_810182 : Nat := 118140960795 + 810182 * 2 ^ 59
def prefixEnd_810182 : Nat := 4983230072969 + 3 ^ 40 * 810182 * 2
def baseEnd_810182 : Nat := 184894570498246396844021

theorem tailTrace_810182 : CollatzResearch.WordTrace tailWord_810182 prefixEnd_810182 184894570498246396844021 := by
  unfold tailWord_810182
  simp only [CollatzResearch.WordTrace]
  refine ⟨923430160964264278583275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19699843433904304609776533 923430160964264278583275)
  ·
    refine ⟨1385145241446396417874913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 923430160964264278583275 1385145241446396417874913)
    ·
      refine ⟨1038858931084797313406185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1385145241446396417874913 1038858931084797313406185)
      ·
        refine ⟨779144198313597985054639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1038858931084797313406185 779144198313597985054639)
        ·
          refine ⟨1168716297470396977581959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779144198313597985054639 1168716297470396977581959)
          ·
            refine ⟨1753074446205595466372939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1168716297470396977581959 1753074446205595466372939)
            ·
              refine ⟨2629611669308393199559409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1753074446205595466372939 2629611669308393199559409)
              ·
                refine ⟨1972208751981294899669557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2629611669308393199559409 1972208751981294899669557)
                ·
                  refine ⟨184894570498246396844021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1972208751981294899669557 184894570498246396844021)
                  ·
                    rfl

theorem cell21_810182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_810182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810182 prefixEnd_810182 := by exact prefixLift 810182
  have htrace : WordTrace (prefixWord ++ tailWord_810182) baseStart_810182 baseEnd_810182 := by
    simpa [prefixWord, tailWord_810182, baseEnd_810182] using wordTrace_append hprefix tailTrace_810182
  have hstable : (prefixWord ++ tailWord_810182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810182).length < 2 ^ (prefixWord ++ tailWord_810182).sum := by decide
  have hdescent : baseEnd_810182 < baseStart_810182 := by decide
  rcases family_descends (prefixWord ++ tailWord_810182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810207 : List Nat := [1, 1, 2, 3, 2, 1, 3, 5, 3]
def baseStart_810207 : Nat := 118140960795 + 810207 * 2 ^ 59
def prefixEnd_810207 : Nat := 4983230072969 + 3 ^ 40 * 810207 * 2
def baseEnd_810207 : Nat := 184900275838851908927303

theorem tailTrace_810207 : CollatzResearch.WordTrace tailWord_810207 prefixEnd_810207 184900275838851908927303 := by
  unfold tailWord_810207
  simp only [CollatzResearch.WordTrace]
  refine ⟨29550676975765886184324875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19700451317177257456216583 29550676975765886184324875)
  ·
    refine ⟨44326015463648829276487313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29550676975765886184324875 44326015463648829276487313)
    ·
      refine ⟨33244511597736621957365485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44326015463648829276487313 33244511597736621957365485)
      ·
        refine ⟨12466691849151233234012057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33244511597736621957365485 12466691849151233234012057)
        ·
          refine ⟨9350018886863424925509043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12466691849151233234012057 9350018886863424925509043)
          ·
            refine ⟨14025028330295137388263565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9350018886863424925509043 14025028330295137388263565)
            ·
              refine ⟨5259385623860676520598837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14025028330295137388263565 5259385623860676520598837)
              ·
                refine ⟨493067402236938423806141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5259385623860676520598837 493067402236938423806141)
                ·
                  refine ⟨184900275838851908927303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 493067402236938423806141 184900275838851908927303)
                  ·
                    rfl

theorem cell21_810207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 3].length) (baseStart_810207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810207 prefixEnd_810207 := by exact prefixLift 810207
  have htrace : WordTrace (prefixWord ++ tailWord_810207) baseStart_810207 baseEnd_810207 := by
    simpa [prefixWord, tailWord_810207, baseEnd_810207] using wordTrace_append hprefix tailTrace_810207
  have hstable : (prefixWord ++ tailWord_810207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810207).length < 2 ^ (prefixWord ++ tailWord_810207).sum := by decide
  have hdescent : baseEnd_810207 < baseStart_810207 := by decide
  rcases family_descends (prefixWord ++ tailWord_810207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810252 : List Nat := [2, 2, 1, 2, 2, 3, 4, 5]
def baseStart_810252 : Nat := 118140960795 + 810252 * 2 ^ 59
def prefixEnd_810252 : Nat := 4983230072969 + 3 ^ 40 * 810252 * 2
def baseEnd_810252 : Nat := 61636848483980610225737

theorem tailTrace_810252 : CollatzResearch.WordTrace tailWord_810252 prefixEnd_810252 61636848483980610225737 := by
  unfold tailWord_810252
  simp only [CollatzResearch.WordTrace]
  refine ⟨14776159130301429434856505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19701545507068572579808673 14776159130301429434856505)
  ·
    refine ⟨11082119347726072076142379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14776159130301429434856505 11082119347726072076142379)
    ·
      refine ⟨16623179021589108114213569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11082119347726072076142379 16623179021589108114213569)
      ·
        refine ⟨12467384266191831085660177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16623179021589108114213569 12467384266191831085660177)
        ·
          refine ⟨9350538199643873314245133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12467384266191831085660177 9350538199643873314245133)
          ·
            refine ⟨3506451824866452492841925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9350538199643873314245133 3506451824866452492841925)
            ·
              refine ⟨657459717162459842407861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3506451824866452492841925 657459717162459842407861)
              ·
                refine ⟨61636848483980610225737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 657459717162459842407861 61636848483980610225737)
                ·
                  rfl

theorem cell21_810252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 5].length) (baseStart_810252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810252 prefixEnd_810252 := by exact prefixLift 810252
  have htrace : WordTrace (prefixWord ++ tailWord_810252) baseStart_810252 baseEnd_810252 := by
    simpa [prefixWord, tailWord_810252, baseEnd_810252] using wordTrace_append hprefix tailTrace_810252
  have hstable : (prefixWord ++ tailWord_810252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810252).length < 2 ^ (prefixWord ++ tailWord_810252).sum := by decide
  have hdescent : baseEnd_810252 < baseStart_810252 := by decide
  rcases family_descends (prefixWord ++ tailWord_810252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810311 : List Nat := [1, 1, 4, 1, 2, 3, 2, 7]
def baseStart_810311 : Nat := 118140960795 + 810311 * 2 ^ 59
def prefixEnd_810311 : Nat := 4983230072969 + 3 ^ 40 * 810311 * 2
def baseEnd_810311 : Nat := 61641336685256946397919

theorem tailTrace_810311 : CollatzResearch.WordTrace tailWord_810311 prefixEnd_810311 61641336685256946397919 := by
  unfold tailWord_810311
  simp only [CollatzResearch.WordTrace]
  refine ⟨29554470167389111946110787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19702980111592741297407191 29554470167389111946110787)
  ·
    refine ⟨44331705251083667919166181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29554470167389111946110787 44331705251083667919166181)
    ·
      refine ⟨8312194734578187734843659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44331705251083667919166181 8312194734578187734843659)
      ·
        refine ⟨12468292101867281602265489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8312194734578187734843659 12468292101867281602265489)
        ·
          refine ⟨9351219076400461201699117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12468292101867281602265489 9351219076400461201699117)
          ·
            refine ⟨3506707153650172950637169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9351219076400461201699117 3506707153650172950637169)
            ·
              refine ⟨2630030365237629712977877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3506707153650172950637169 2630030365237629712977877)
              ·
                refine ⟨61641336685256946397919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2630030365237629712977877 61641336685256946397919)
                ·
                  rfl

theorem cell21_810311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 7].length) (baseStart_810311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810311 prefixEnd_810311 := by exact prefixLift 810311
  have htrace : WordTrace (prefixWord ++ tailWord_810311) baseStart_810311 baseEnd_810311 := by
    simpa [prefixWord, tailWord_810311, baseEnd_810311] using wordTrace_append hprefix tailTrace_810311
  have hstable : (prefixWord ++ tailWord_810311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810311).length < 2 ^ (prefixWord ++ tailWord_810311).sum := by decide
  have hdescent : baseEnd_810311 < baseStart_810311 := by decide
  rcases family_descends (prefixWord ++ tailWord_810311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810376 : List Nat := [2, 1, 3, 3, 1, 3, 2, 3, 3]
def baseStart_810376 : Nat := 118140960795 + 810376 * 2 ^ 59
def prefixEnd_810376 : Nat := 4983230072969 + 3 ^ 40 * 810376 * 2
def baseEnd_810376 : Nat := 184938843941345170610291

theorem tailTrace_810376 : CollatzResearch.WordTrace tailWord_810376 prefixEnd_810376 184938843941345170610291 := by
  unfold tailWord_810376
  simp only [CollatzResearch.WordTrace]
  refine ⟨14778420456076814023613491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19704560608102418698151321 14778420456076814023613491)
  ·
    refine ⟨22167630684115221035420237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14778420456076814023613491 22167630684115221035420237)
    ·
      refine ⟨8312861506543207888282589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22167630684115221035420237 8312861506543207888282589)
      ·
        refine ⟨3117323064953702958105971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8312861506543207888282589 3117323064953702958105971)
        ·
          refine ⟨4675984597430554437158957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3117323064953702958105971 4675984597430554437158957)
          ·
            refine ⟨1753494224036457913934609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4675984597430554437158957 1753494224036457913934609)
            ·
              refine ⟨1315120668027343435450957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1753494224036457913934609 1315120668027343435450957)
              ·
                refine ⟨493170250510253788294109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1315120668027343435450957 493170250510253788294109)
                ·
                  refine ⟨184938843941345170610291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 493170250510253788294109 184938843941345170610291)
                  ·
                    rfl

theorem cell21_810376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 3].length) (baseStart_810376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810376 prefixEnd_810376 := by exact prefixLift 810376
  have htrace : WordTrace (prefixWord ++ tailWord_810376) baseStart_810376 baseEnd_810376 := by
    simpa [prefixWord, tailWord_810376, baseEnd_810376] using wordTrace_append hprefix tailTrace_810376
  have hstable : (prefixWord ++ tailWord_810376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810376).length < 2 ^ (prefixWord ++ tailWord_810376).sum := by decide
  have hdescent : baseEnd_810376 < baseStart_810376 := by decide
  rcases family_descends (prefixWord ++ tailWord_810376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810421 : List Nat := [1, 3, 3, 2, 2, 3, 2, 5]
def baseStart_810421 : Nat := 118140960795 + 810421 * 2 ^ 59
def prefixEnd_810421 : Nat := 4983230072969 + 3 ^ 40 * 810421 * 2
def baseEnd_810421 : Nat := 61649704518145030786733

theorem tailTrace_810421 : CollatzResearch.WordTrace tailWord_810421 prefixEnd_810421 61649704518145030786733 := by
  unfold tailWord_810421
  simp only [CollatzResearch.WordTrace]
  refine ⟨29558482196990600732615117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19705654797993733821743411 29558482196990600732615117)
  ·
    refine ⟨11084430823871475274730669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29558482196990600732615117 11084430823871475274730669)
    ·
      refine ⟨4156661558951803228024001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11084430823871475274730669 4156661558951803228024001)
      ·
        refine ⟨3117496169213852421018001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4156661558951803228024001 3117496169213852421018001)
        ·
          refine ⟨2338122126910389315763501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3117496169213852421018001 2338122126910389315763501)
          ·
            refine ⟨876795797591395993411313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2338122126910389315763501 876795797591395993411313)
            ·
              refine ⟨657596848193546995058485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 876795797591395993411313 657596848193546995058485)
              ·
                refine ⟨61649704518145030786733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 657596848193546995058485 61649704518145030786733)
                ·
                  rfl

theorem cell21_810421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 5].length) (baseStart_810421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810421 prefixEnd_810421 := by exact prefixLift 810421
  have htrace : WordTrace (prefixWord ++ tailWord_810421) baseStart_810421 baseEnd_810421 := by
    simpa [prefixWord, tailWord_810421, baseEnd_810421] using wordTrace_append hprefix tailTrace_810421
  have hstable : (prefixWord ++ tailWord_810421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810421).length < 2 ^ (prefixWord ++ tailWord_810421).sum := by decide
  have hdescent : baseEnd_810421 < baseStart_810421 := by decide
  rcases family_descends (prefixWord ++ tailWord_810421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810432 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 6]
def baseStart_810432 : Nat := 118140960795 + 810432 * 2 ^ 59
def prefixEnd_810432 : Nat := 4983230072969 + 3 ^ 40 * 810432 * 2
def baseEnd_810432 : Nat := 184951623904301517676843

theorem tailTrace_810432 : CollatzResearch.WordTrace tailWord_810432 prefixEnd_810432 184951623904301517676843 := by
  unfold tailWord_810432
  simp only [CollatzResearch.WordTrace]
  refine ⟨14779441699975374805632775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19705922266633833074177033 14779441699975374805632775)
  ·
    refine ⟨22169162549963062208449163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14779441699975374805632775 22169162549963062208449163)
    ·
      refine ⟨33253743824944593312673745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22169162549963062208449163 33253743824944593312673745)
      ·
        refine ⟨24940307868708444984505309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33253743824944593312673745 24940307868708444984505309)
        ·
          refine ⟨9352615450765666869189491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24940307868708444984505309 9352615450765666869189491)
          ·
            refine ⟨14028923176148500303784237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9352615450765666869189491 14028923176148500303784237)
            ·
              refine ⟨5260846191055687613919089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14028923176148500303784237 5260846191055687613919089)
              ·
                refine ⟨3945634643291765710439317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5260846191055687613919089 3945634643291765710439317)
                ·
                  refine ⟨184951623904301517676843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3945634643291765710439317 184951623904301517676843)
                  ·
                    rfl

theorem cell21_810432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_810432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810432 prefixEnd_810432 := by exact prefixLift 810432
  have htrace : WordTrace (prefixWord ++ tailWord_810432) baseStart_810432 baseEnd_810432 := by
    simpa [prefixWord, tailWord_810432, baseEnd_810432] using wordTrace_append hprefix tailTrace_810432
  have hstable : (prefixWord ++ tailWord_810432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810432).length < 2 ^ (prefixWord ++ tailWord_810432).sum := by decide
  have hdescent : baseEnd_810432 < baseStart_810432 := by decide
  rcases family_descends (prefixWord ++ tailWord_810432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810435 : List Nat := [1, 1, 1, 3, 1, 1, 7, 3, 3]
def baseStart_810435 : Nat := 118140960795 + 810435 * 2 ^ 59
def prefixEnd_810435 : Nat := 4983230072969 + 3 ^ 40 * 810435 * 2
def baseEnd_810435 : Nat := 184952308545174179126837

theorem tailTrace_810435 : CollatzResearch.WordTrace tailWord_810435 prefixEnd_810435 184952308545174179126837 := by
  unfold tailWord_810435
  simp only [CollatzResearch.WordTrace]
  refine ⟨29558992818939881123624759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19705995212626587415749839 29558992818939881123624759)
  ·
    refine ⟨44338489228409821685437139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29558992818939881123624759 44338489228409821685437139)
    ·
      refine ⟨66507733842614732528155709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44338489228409821685437139 66507733842614732528155709)
      ·
        refine ⟨24940400190980524698058391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66507733842614732528155709 24940400190980524698058391)
        ·
          refine ⟨37410600286470787047087587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24940400190980524698058391 37410600286470787047087587)
          ·
            refine ⟨56115900429706180570631381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37410600286470787047087587 56115900429706180570631381)
            ·
              refine ⟨1315216416321238607124173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 56115900429706180570631381 1315216416321238607124173)
              ·
                refine ⟨493206156120464477671565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1315216416321238607124173 493206156120464477671565)
                ·
                  refine ⟨184952308545174179126837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 493206156120464477671565 184952308545174179126837)
                  ·
                    rfl

theorem cell21_810435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 3].length) (baseStart_810435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810435 prefixEnd_810435 := by exact prefixLift 810435
  have htrace : WordTrace (prefixWord ++ tailWord_810435) baseStart_810435 baseEnd_810435 := by
    simpa [prefixWord, tailWord_810435, baseEnd_810435] using wordTrace_append hprefix tailTrace_810435
  have hstable : (prefixWord ++ tailWord_810435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810435).length < 2 ^ (prefixWord ++ tailWord_810435).sum := by decide
  have hdescent : baseEnd_810435 < baseStart_810435 := by decide
  rcases family_descends (prefixWord ++ tailWord_810435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810452 : List Nat := [2, 4, 1, 2, 3, 2, 1, 1, 5]
def baseStart_810452 : Nat := 118140960795 + 810452 * 2 ^ 59
def prefixEnd_810452 : Nat := 4983230072969 + 3 ^ 40 * 810452 * 2
def baseEnd_810452 : Nat := 184956188176785927343469

theorem tailTrace_810452 : CollatzResearch.WordTrace tailWord_810452 prefixEnd_810452 184956188176785927343469 := by
  unfold tailWord_810452
  simp only [CollatzResearch.WordTrace]
  refine ⟨14779806429939146513496805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19706408573252195351329073 14779806429939146513496805)
  ·
    refine ⟨2771213705613589971280651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14779806429939146513496805 2771213705613589971280651)
    ·
      refine ⟨4156820558420384956920977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2771213705613589971280651 4156820558420384956920977)
      ·
        refine ⟨3117615418815288717690733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4156820558420384956920977 3117615418815288717690733)
        ·
          refine ⟨1169105782055733269134025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3117615418815288717690733 1169105782055733269134025)
          ·
            refine ⟨876829336541799951850519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1169105782055733269134025 876829336541799951850519)
            ·
              refine ⟨1315244004812699927775779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876829336541799951850519 1315244004812699927775779)
              ·
                refine ⟨1972866007219049891663669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1315244004812699927775779 1972866007219049891663669)
                ·
                  refine ⟨184956188176785927343469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1972866007219049891663669 184956188176785927343469)
                  ·
                    rfl

theorem cell21_810452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_810452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810452 prefixEnd_810452 := by exact prefixLift 810452
  have htrace : WordTrace (prefixWord ++ tailWord_810452) baseStart_810452 baseEnd_810452 := by
    simpa [prefixWord, tailWord_810452, baseEnd_810452] using wordTrace_append hprefix tailTrace_810452
  have hstable : (prefixWord ++ tailWord_810452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810452).length < 2 ^ (prefixWord ++ tailWord_810452).sum := by decide
  have hdescent : baseEnd_810452 < baseStart_810452 := by decide
  rcases family_descends (prefixWord ++ tailWord_810452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810463 : List Nat := [1, 1, 2, 3, 3, 1, 4, 6]
def baseStart_810463 : Nat := 118140960795 + 810463 * 2 ^ 59
def prefixEnd_810463 : Nat := 4983230072969 + 3 ^ 40 * 810463 * 2
def baseEnd_810463 : Nat := 61652899508884117553371

theorem tailTrace_810463 : CollatzResearch.WordTrace tailWord_810463 prefixEnd_810463 61652899508884117553371 := by
  unfold tailWord_810463
  simp only [CollatzResearch.WordTrace]
  refine ⟨29560014062838441905644043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19706676041892294603762695 29560014062838441905644043)
  ·
    refine ⟨44340021094257662858466065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29560014062838441905644043 44340021094257662858466065)
    ·
      refine ⟨33255015820693247143849549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44340021094257662858466065 33255015820693247143849549)
      ·
        refine ⟨12470630932759967678943581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33255015820693247143849549 12470630932759967678943581)
        ·
          refine ⟨4676486599784987879603843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12470630932759967678943581 4676486599784987879603843)
          ·
            refine ⟨7014729899677481819405765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4676486599784987879603843 7014729899677481819405765)
            ·
              refine ⟨1315261856189527841138581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7014729899677481819405765 1315261856189527841138581)
              ·
                refine ⟨61652899508884117553371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1315261856189527841138581 61652899508884117553371)
                ·
                  rfl

theorem cell21_810463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 6].length) (baseStart_810463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810463 prefixEnd_810463 := by exact prefixLift 810463
  have htrace : WordTrace (prefixWord ++ tailWord_810463) baseStart_810463 baseEnd_810463 := by
    simpa [prefixWord, tailWord_810463, baseEnd_810463] using wordTrace_append hprefix tailTrace_810463
  have hstable : (prefixWord ++ tailWord_810463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810463).length < 2 ^ (prefixWord ++ tailWord_810463).sum := by decide
  have hdescent : baseEnd_810463 < baseStart_810463 := by decide
  rcases family_descends (prefixWord ++ tailWord_810463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810525 : List Nat := [1, 4, 2, 2, 1, 1, 1, 5, 4]
def baseStart_810525 : Nat := 118140960795 + 810525 * 2 ^ 59
def prefixEnd_810525 : Nat := 4983230072969 + 3 ^ 40 * 810525 * 2
def baseEnd_810525 : Nat := 184972847771354022626653

theorem tailTrace_810525 : CollatzResearch.WordTrace tailWord_810525 prefixEnd_810525 184972847771354022626653 := by
  unfold tailWord_810525
  simp only [CollatzResearch.WordTrace]
  refine ⟨29562275388613826494401029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19708183592409217662934019 29562275388613826494401029)
  ·
    refine ⟨5542926635365092467700193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29562275388613826494401029 5542926635365092467700193)
    ·
      refine ⟨4157194976523819350775145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5542926635365092467700193 4157194976523819350775145)
      ·
        refine ⟨3117896232392864513081359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4157194976523819350775145 3117896232392864513081359)
        ·
          refine ⟨4676844348589296769622039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3117896232392864513081359 4676844348589296769622039)
          ·
            refine ⟨7015266522883945154433059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4676844348589296769622039 7015266522883945154433059)
            ·
              refine ⟨10522899784325917731649589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7015266522883945154433059 10522899784325917731649589)
              ·
                refine ⟨986521854780554787342149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10522899784325917731649589 986521854780554787342149)
                ·
                  refine ⟨184972847771354022626653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 986521854780554787342149 184972847771354022626653)
                  ·
                    rfl

theorem cell21_810525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_810525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810525 prefixEnd_810525 := by exact prefixLift 810525
  have htrace : WordTrace (prefixWord ++ tailWord_810525) baseStart_810525 baseEnd_810525 := by
    simpa [prefixWord, tailWord_810525, baseEnd_810525] using wordTrace_append hprefix tailTrace_810525
  have hstable : (prefixWord ++ tailWord_810525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810525).length < 2 ^ (prefixWord ++ tailWord_810525).sum := by decide
  have hdescent : baseEnd_810525 < baseStart_810525 := by decide
  rcases family_descends (prefixWord ++ tailWord_810525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810570 : List Nat := [3, 1, 2, 1, 1, 3, 4, 1, 5]
def baseStart_810570 : Nat := 118140960795 + 810570 * 2 ^ 59
def prefixEnd_810570 : Nat := 4983230072969 + 3 ^ 40 * 810570 * 2
def baseEnd_810570 : Nat := 184983117384443944376561

theorem tailTrace_810570 : CollatzResearch.WordTrace tailWord_810570 prefixEnd_810570 184983117384443944376561 := by
  unfold tailWord_810570
  simp only [CollatzResearch.WordTrace]
  refine ⟨7390979168362699794947291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19709277782300532786526109 7390979168362699794947291)
  ·
    refine ⟨11086468752544049692420937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7390979168362699794947291 11086468752544049692420937)
    ·
      refine ⟨8314851564408037269315703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11086468752544049692420937 8314851564408037269315703)
      ·
        refine ⟨12472277346612055903973555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8314851564408037269315703 12472277346612055903973555)
        ·
          refine ⟨18708416019918083855960333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12472277346612055903973555 18708416019918083855960333)
          ·
            refine ⟨7015656007469281445985125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18708416019918083855960333 7015656007469281445985125)
            ·
              refine ⟨1315435501400490271122211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7015656007469281445985125 1315435501400490271122211)
              ·
                refine ⟨1973153252100735406683317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1315435501400490271122211 1973153252100735406683317)
                ·
                  refine ⟨184983117384443944376561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1973153252100735406683317 184983117384443944376561)
                  ·
                    rfl

theorem cell21_810570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_810570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810570 prefixEnd_810570 := by exact prefixLift 810570
  have htrace : WordTrace (prefixWord ++ tailWord_810570) baseStart_810570 baseEnd_810570 := by
    simpa [prefixWord, tailWord_810570, baseEnd_810570] using wordTrace_append hprefix tailTrace_810570
  have hstable : (prefixWord ++ tailWord_810570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810570).length < 2 ^ (prefixWord ++ tailWord_810570).sum := by decide
  have hdescent : baseEnd_810570 < baseStart_810570 := by decide
  rcases family_descends (prefixWord ++ tailWord_810570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810705 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 7]
def baseStart_810705 : Nat := 118140960795 + 810705 * 2 ^ 59
def prefixEnd_810705 : Nat := 4983230072969 + 3 ^ 40 * 810705 * 2
def baseEnd_810705 : Nat := 185013926223713709626285

theorem tailTrace_810705 : CollatzResearch.WordTrace tailWord_810705 prefixEnd_810705 185013926223713709626285 := by
  unfold tailWord_810705
  simp only [CollatzResearch.WordTrace]
  refine ⟨29568840527961717235953569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19712560351974478157302379 29568840527961717235953569)
  ·
    refine ⟨22176630395971287926965177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29568840527961717235953569 22176630395971287926965177)
    ·
      refine ⟨16632472796978465945223883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22176630395971287926965177 16632472796978465945223883)
      ·
        refine ⟨24948709195467698917835825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16632472796978465945223883 24948709195467698917835825)
        ·
          refine ⟨18711531896600774188376869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24948709195467698917835825 18711531896600774188376869)
          ·
            refine ⟨3508412230612645160320663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18711531896600774188376869 3508412230612645160320663)
            ·
              refine ⟨5262618345918967740480995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3508412230612645160320663 5262618345918967740480995)
              ·
                refine ⟨7893927518878451610721493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5262618345918967740480995 7893927518878451610721493)
                ·
                  refine ⟨185013926223713709626285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7893927518878451610721493 185013926223713709626285)
                  ·
                    rfl

theorem cell21_810705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_810705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810705 prefixEnd_810705 := by exact prefixLift 810705
  have htrace : WordTrace (prefixWord ++ tailWord_810705) baseStart_810705 baseEnd_810705 := by
    simpa [prefixWord, tailWord_810705, baseEnd_810705] using wordTrace_append hprefix tailTrace_810705
  have hstable : (prefixWord ++ tailWord_810705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810705).length < 2 ^ (prefixWord ++ tailWord_810705).sum := by decide
  have hdescent : baseEnd_810705 < baseStart_810705 := by decide
  rcases family_descends (prefixWord ++ tailWord_810705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810736 : List Nat := [2, 1, 1, 1, 3, 1, 2, 6, 4]
def baseStart_810736 : Nat := 118140960795 + 810736 * 2 ^ 59
def prefixEnd_810736 : Nat := 4983230072969 + 3 ^ 40 * 810736 * 2
def baseEnd_810736 : Nat := 185021000846064544609555

theorem tailTrace_810736 : CollatzResearch.WordTrace tailWord_810736 prefixEnd_810736 185021000846064544609555 := by
  unfold tailWord_810736
  simp only [CollatzResearch.WordTrace]
  refine ⟨14784985595424704765166031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19713314127232939686888041 14784985595424704765166031)
  ·
    refine ⟨22177478393137057147749047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14784985595424704765166031 22177478393137057147749047)
    ·
      refine ⟨33266217589705585721623571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22177478393137057147749047 33266217589705585721623571)
      ·
        refine ⟨49899326384558378582435357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33266217589705585721623571 49899326384558378582435357)
        ·
          refine ⟨18712247394209391968413259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49899326384558378582435357 18712247394209391968413259)
          ·
            refine ⟨28068371091314087952619889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18712247394209391968413259 28068371091314087952619889)
            ·
              refine ⟨21051278318485565964464917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28068371091314087952619889 21051278318485565964464917)
              ·
                refine ⟨986778671179010904584293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21051278318485565964464917 986778671179010904584293)
                ·
                  refine ⟨185021000846064544609555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 986778671179010904584293 185021000846064544609555)
                  ·
                    rfl

theorem cell21_810736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 4].length) (baseStart_810736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810736 prefixEnd_810736 := by exact prefixLift 810736
  have htrace : WordTrace (prefixWord ++ tailWord_810736) baseStart_810736 baseEnd_810736 := by
    simpa [prefixWord, tailWord_810736, baseEnd_810736] using wordTrace_append hprefix tailTrace_810736
  have hstable : (prefixWord ++ tailWord_810736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810736).length < 2 ^ (prefixWord ++ tailWord_810736).sum := by decide
  have hdescent : baseEnd_810736 < baseStart_810736 := by decide
  rcases family_descends (prefixWord ++ tailWord_810736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810795 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 10]
def baseStart_810795 : Nat := 118140960795 + 810795 * 2 ^ 59
def prefixEnd_810795 : Nat := 4983230072969 + 3 ^ 40 * 810795 * 2
def baseEnd_810795 : Nat := 185034465449893553126101

theorem tailTrace_810795 : CollatzResearch.WordTrace tailWord_810795 prefixEnd_810795 185034465449893553126101 := by
  unfold tailWord_810795
  simp only [CollatzResearch.WordTrace]
  refine ⟨29572123097635662606729839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19714748731757108404486559 29572123097635662606729839)
  ·
    refine ⟨44358184646453493910094759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29572123097635662606729839 44358184646453493910094759)
    ·
      refine ⟨66537276969680240865142139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44358184646453493910094759 66537276969680240865142139)
      ·
        refine ⟨99805915454520361297713209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66537276969680240865142139 99805915454520361297713209)
        ·
          refine ⟨74854436590890270973284907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99805915454520361297713209 74854436590890270973284907)
          ·
            refine ⟨112281654886335406459927361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74854436590890270973284907 112281654886335406459927361)
            ·
              refine ⟨84211241164751554844945521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112281654886335406459927361 84211241164751554844945521)
              ·
                refine ⟨63158430873563666133709141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84211241164751554844945521 63158430873563666133709141)
                ·
                  refine ⟨185034465449893553126101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 63158430873563666133709141 185034465449893553126101)
                  ·
                    rfl

theorem cell21_810795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 10].length) (baseStart_810795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810795 prefixEnd_810795 := by exact prefixLift 810795
  have htrace : WordTrace (prefixWord ++ tailWord_810795) baseStart_810795 baseEnd_810795 := by
    simpa [prefixWord, tailWord_810795, baseEnd_810795] using wordTrace_append hprefix tailTrace_810795
  have hstable : (prefixWord ++ tailWord_810795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810795).length < 2 ^ (prefixWord ++ tailWord_810795).sum := by decide
  have hdescent : baseEnd_810795 < baseStart_810795 := by decide
  rcases family_descends (prefixWord ++ tailWord_810795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810826 : List Nat := [3, 1, 2, 1, 1, 1, 3, 9]
def baseStart_810826 : Nat := 118140960795 + 810826 * 2 ^ 59
def prefixEnd_810826 : Nat := 4983230072969 + 3 ^ 40 * 810826 * 2
def baseEnd_810826 : Nat := 61680513357414796036457

theorem tailTrace_810826 : CollatzResearch.WordTrace tailWord_810826 prefixEnd_810826 61680513357414796036457 := by
  unfold tailWord_810826
  simp only [CollatzResearch.WordTrace]
  refine ⟨7393313440130838725277083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19715502507015569934072221 7393313440130838725277083)
  ·
    refine ⟨11089970160196258087915625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7393313440130838725277083 11089970160196258087915625)
    ·
      refine ⟨8317477620147193565936719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11089970160196258087915625 8317477620147193565936719)
      ·
        refine ⟨12476216430220790348905079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8317477620147193565936719 12476216430220790348905079)
        ·
          refine ⟨18714324645331185523357619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12476216430220790348905079 18714324645331185523357619)
          ·
            refine ⟨28071486967996778285036429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18714324645331185523357619 28071486967996778285036429)
            ·
              refine ⟨10526807612998791856888661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28071486967996778285036429 10526807612998791856888661)
              ·
                refine ⟨61680513357414796036457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10526807612998791856888661 61680513357414796036457)
                ·
                  rfl

theorem cell21_810826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_810826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810826 prefixEnd_810826 := by exact prefixLift 810826
  have htrace : WordTrace (prefixWord ++ tailWord_810826) baseStart_810826 baseEnd_810826 := by
    simpa [prefixWord, tailWord_810826, baseEnd_810826] using wordTrace_append hprefix tailTrace_810826
  have hstable : (prefixWord ++ tailWord_810826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810826).length < 2 ^ (prefixWord ++ tailWord_810826).sum := by decide
  have hdescent : baseEnd_810826 < baseStart_810826 := by decide
  rcases family_descends (prefixWord ++ tailWord_810826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810871 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 10]
def baseStart_810871 : Nat := 118140960795 + 810871 * 2 ^ 59
def prefixEnd_810871 : Nat := 4983230072969 + 3 ^ 40 * 810871 * 2
def baseEnd_810871 : Nat := 185051809685334309859279

theorem tailTrace_810871 : CollatzResearch.WordTrace tailWord_810871 prefixEnd_810871 185051809685334309859279 := by
  unfold tailWord_810871
  simp only [CollatzResearch.WordTrace]
  refine ⟨29574895045360327586496467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19716596696906885057664311 29574895045360327586496467)
  ·
    refine ⟨44362342568040491379744701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29574895045360327586496467 44362342568040491379744701)
    ·
      refine ⟨16635878463015184267404263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44362342568040491379744701 16635878463015184267404263)
      ·
        refine ⟨24953817694522776401106395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16635878463015184267404263 24953817694522776401106395)
        ·
          refine ⟨37430726541784164601659593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24953817694522776401106395 37430726541784164601659593)
          ·
            refine ⟨28073044906338123451244695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37430726541784164601659593 28073044906338123451244695)
            ·
              refine ⟨42109567359507185176867043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28073044906338123451244695 42109567359507185176867043)
              ·
                refine ⟨63164351039260777765300565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42109567359507185176867043 63164351039260777765300565)
                ·
                  refine ⟨185051809685334309859279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 63164351039260777765300565 185051809685334309859279)
                  ·
                    rfl

theorem cell21_810871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 10].length) (baseStart_810871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810871 prefixEnd_810871 := by exact prefixLift 810871
  have htrace : WordTrace (prefixWord ++ tailWord_810871) baseStart_810871 baseEnd_810871 := by
    simpa [prefixWord, tailWord_810871, baseEnd_810871] using wordTrace_append hprefix tailTrace_810871
  have hstable : (prefixWord ++ tailWord_810871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810871).length < 2 ^ (prefixWord ++ tailWord_810871).sum := by decide
  have hdescent : baseEnd_810871 < baseStart_810871 := by decide
  rcases family_descends (prefixWord ++ tailWord_810871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810964 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 6]
def baseStart_810964 : Nat := 118140960795 + 810964 * 2 ^ 59
def prefixEnd_810964 : Nat := 4983230072969 + 3 ^ 40 * 810964 * 2
def baseEnd_810964 : Nat := 185073033552386814809089

theorem tailTrace_810964 : CollatzResearch.WordTrace tailWord_810964 prefixEnd_810964 185073033552386814809089 := by
  unfold tailWord_810964
  simp only [CollatzResearch.WordTrace]
  refine ⟨14789143517011702234815973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19718858022682269646421297 14789143517011702234815973)
  ·
    refine ⟨2772964409439694169027995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14789143517011702234815973 2772964409439694169027995)
    ·
      refine ⟨4159446614159541253541993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2772964409439694169027995 4159446614159541253541993)
      ·
        refine ⟨3119584960619655940156495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4159446614159541253541993 3119584960619655940156495)
        ·
          refine ⟨4679377440929483910234743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3119584960619655940156495 4679377440929483910234743)
          ·
            refine ⟨7019066161394225865352115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4679377440929483910234743 7019066161394225865352115)
            ·
              refine ⟨10528599242091338798028173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7019066161394225865352115 10528599242091338798028173)
              ·
                refine ⟨3948224715784252049260565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10528599242091338798028173 3948224715784252049260565)
                ·
                  refine ⟨185073033552386814809089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3948224715784252049260565 185073033552386814809089)
                  ·
                    rfl

theorem cell21_810964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_810964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810964 prefixEnd_810964 := by exact prefixLift 810964
  have htrace : WordTrace (prefixWord ++ tailWord_810964) baseStart_810964 baseEnd_810964 := by
    simpa [prefixWord, tailWord_810964, baseEnd_810964] using wordTrace_append hprefix tailTrace_810964
  have hstable : (prefixWord ++ tailWord_810964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810964).length < 2 ^ (prefixWord ++ tailWord_810964).sum := by decide
  have hdescent : baseEnd_810964 < baseStart_810964 := by decide
  rcases family_descends (prefixWord ++ tailWord_810964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810967 : List Nat := [1, 1, 3, 2, 1, 1, 7, 2, 3]
def baseStart_810967 : Nat := 118140960795 + 810967 * 2 ^ 59
def prefixEnd_810967 : Nat := 4983230072969 + 3 ^ 40 * 810967 * 2
def baseEnd_810967 : Nat := 185073718193259476259083

theorem tailTrace_810967 : CollatzResearch.WordTrace tailWord_810967 prefixEnd_810967 185073718193259476259083 := by
  unfold tailWord_810967
  simp only [CollatzResearch.WordTrace]
  refine ⟨29578396453012535981991155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19718930968675023987994103 29578396453012535981991155)
  ·
    refine ⟨44367594679518803972986733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29578396453012535981991155 44367594679518803972986733)
    ·
      refine ⟨16637848004819551489870025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44367594679518803972986733 16637848004819551489870025)
      ·
        refine ⟨12478386003614663617402519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16637848004819551489870025 12478386003614663617402519)
        ·
          refine ⟨18717579005421995426103779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12478386003614663617402519 18717579005421995426103779)
          ·
            refine ⟨28076368508132993139155669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18717579005421995426103779 28076368508132993139155669)
            ·
              refine ⟨658039886909367026698961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28076368508132993139155669 658039886909367026698961)
              ·
                refine ⟨493529915182025270024221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 658039886909367026698961 493529915182025270024221)
                ·
                  refine ⟨185073718193259476259083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 493529915182025270024221 185073718193259476259083)
                  ·
                    rfl

theorem cell21_810967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 3].length) (baseStart_810967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_810967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_810967 prefixEnd_810967 := by exact prefixLift 810967
  have htrace : WordTrace (prefixWord ++ tailWord_810967) baseStart_810967 baseEnd_810967 := by
    simpa [prefixWord, tailWord_810967, baseEnd_810967] using wordTrace_append hprefix tailTrace_810967
  have hstable : (prefixWord ++ tailWord_810967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810967).length < 2 ^ (prefixWord ++ tailWord_810967).sum := by decide
  have hdescent : baseEnd_810967 < baseStart_810967 := by decide
  rcases family_descends (prefixWord ++ tailWord_810967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811012 : List Nat := [2, 3, 2, 4, 2, 8]
def baseStart_811012 : Nat := 118140960795 + 811012 * 2 ^ 59
def prefixEnd_811012 : Nat := 4983230072969 + 3 ^ 40 * 811012 * 2
def baseEnd_811012 : Nat := 6854962511346274000333

theorem tailTrace_811012 : CollatzResearch.WordTrace tailWord_811012 prefixEnd_811012 6854962511346274000333 := by
  unfold tailWord_811012
  simp only [CollatzResearch.WordTrace]
  refine ⟨14790018868924754333689645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19720025158566339111586193 14790018868924754333689645)
  ·
    refine ⟨5546257075846782875133617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14790018868924754333689645 5546257075846782875133617)
    ·
      refine ⟨4159692806885087156350213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5546257075846782875133617 4159692806885087156350213)
      ·
        refine ⟨779942401290953841815665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4159692806885087156350213 779942401290953841815665)
        ·
          refine ⟨584956800968215381361749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 779942401290953841815665 584956800968215381361749)
          ·
            refine ⟨6854962511346274000333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 584956800968215381361749 6854962511346274000333)
            ·
              rfl

theorem cell21_811012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 8].length) (baseStart_811012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811012 prefixEnd_811012 := by exact prefixLift 811012
  have htrace : WordTrace (prefixWord ++ tailWord_811012) baseStart_811012 baseEnd_811012 := by
    simpa [prefixWord, tailWord_811012, baseEnd_811012] using wordTrace_append hprefix tailTrace_811012
  have hstable : (prefixWord ++ tailWord_811012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811012).length < 2 ^ (prefixWord ++ tailWord_811012).sum := by decide
  have hdescent : baseEnd_811012 < baseStart_811012 := by decide
  rcases family_descends (prefixWord ++ tailWord_811012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811119 : List Nat := [1, 1, 2, 1, 3, 6, 1, 3, 3]
def baseStart_811119 : Nat := 118140960795 + 811119 * 2 ^ 59
def prefixEnd_811119 : Nat := 4983230072969 + 3 ^ 40 * 811119 * 2
def baseEnd_811119 : Nat := 185108406664140989725439

theorem tailTrace_811119 : CollatzResearch.WordTrace tailWord_811119 prefixEnd_811119 185108406664140989725439 := by
  unfold tailWord_811119
  simp only [CollatzResearch.WordTrace]
  refine ⟨29583940348461865941524411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19722626898974577294349607 29583940348461865941524411)
  ·
    refine ⟨44375910522692798912286617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29583940348461865941524411 44375910522692798912286617)
    ·
      refine ⟨33281932892019599184214963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44375910522692798912286617 33281932892019599184214963)
      ·
        refine ⟨49922899338029398776322445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33281932892019599184214963 49922899338029398776322445)
        ·
          refine ⟨18721087251761024541120917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49922899338029398776322445 18721087251761024541120917)
          ·
            refine ⟨877550964926298025365043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18721087251761024541120917 877550964926298025365043)
            ·
              refine ⟨1316326447389447038047565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877550964926298025365043 1316326447389447038047565)
              ·
                refine ⟨493622417771042639267837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1316326447389447038047565 493622417771042639267837)
                ·
                  refine ⟨185108406664140989725439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 493622417771042639267837 185108406664140989725439)
                  ·
                    rfl

theorem cell21_811119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 3].length) (baseStart_811119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811119 prefixEnd_811119 := by exact prefixLift 811119
  have htrace : WordTrace (prefixWord ++ tailWord_811119) baseStart_811119 baseEnd_811119 := by
    simpa [prefixWord, tailWord_811119, baseEnd_811119] using wordTrace_append hprefix tailTrace_811119
  have hstable : (prefixWord ++ tailWord_811119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811119).length < 2 ^ (prefixWord ++ tailWord_811119).sum := by decide
  have hdescent : baseEnd_811119 < baseStart_811119 := by decide
  rcases family_descends (prefixWord ++ tailWord_811119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811192 : List Nat := [2, 1, 2, 1, 2, 1, 6, 2, 4]
def baseStart_811192 : Nat := 118140960795 + 811192 * 2 ^ 59
def prefixEnd_811192 : Nat := 4983230072969 + 3 ^ 40 * 811192 * 2
def baseEnd_811192 : Nat := 185125066258709085008623

theorem tailTrace_811192 : CollatzResearch.WordTrace tailWord_811192 prefixEnd_811192 185125066258709085008623 := by
  unfold tailWord_811192
  simp only [CollatzResearch.WordTrace]
  refine ⟨14793301438598699704465915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19724401918131599605954553 14793301438598699704465915)
  ·
    refine ⟨22189952157898049556698873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14793301438598699704465915 22189952157898049556698873)
    ·
      refine ⟨16642464118423537167524155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22189952157898049556698873 16642464118423537167524155)
      ·
        refine ⟨24963696177635305751286233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16642464118423537167524155 24963696177635305751286233)
        ·
          refine ⟨18722772133226479313464675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24963696177635305751286233 18722772133226479313464675)
          ·
            refine ⟨28084158199839718970197013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18722772133226479313464675 28084158199839718970197013)
            ·
              refine ⟨1316444915617486826727985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28084158199839718970197013 1316444915617486826727985)
              ·
                refine ⟨987333686713115120045989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1316444915617486826727985 987333686713115120045989)
                ·
                  refine ⟨185125066258709085008623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 987333686713115120045989 185125066258709085008623)
                  ·
                    rfl

theorem cell21_811192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 4].length) (baseStart_811192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811192 prefixEnd_811192 := by exact prefixLift 811192
  have htrace : WordTrace (prefixWord ++ tailWord_811192) baseStart_811192 baseEnd_811192 := by
    simpa [prefixWord, tailWord_811192, baseEnd_811192] using wordTrace_append hprefix tailTrace_811192
  have hstable : (prefixWord ++ tailWord_811192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811192).length < 2 ^ (prefixWord ++ tailWord_811192).sum := by decide
  have hdescent : baseEnd_811192 < baseStart_811192 := by decide
  rcases family_descends (prefixWord ++ tailWord_811192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811251 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 6]
def baseStart_811251 : Nat := 118140960795 + 811251 * 2 ^ 59
def prefixEnd_811251 : Nat := 4983230072969 + 3 ^ 40 * 811251 * 2
def baseEnd_811251 : Nat := 185138530862538093525169

theorem tailTrace_811251 : CollatzResearch.WordTrace tailWord_811251 prefixEnd_811251 185138530862538093525169 := by
  unfold tailWord_811251
  simp only [CollatzResearch.WordTrace]
  refine ⟨29588754783983652485329607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19725836522655768323553071 29588754783983652485329607)
  ·
    refine ⟨44383132175975478727994411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29588754783983652485329607 44383132175975478727994411)
    ·
      refine ⟨66574698263963218091991617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44383132175975478727994411 66574698263963218091991617)
      ·
        refine ⟨49931023697972413568993713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66574698263963218091991617 49931023697972413568993713)
        ·
          refine ⟨37448267773479310176745285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49931023697972413568993713 37448267773479310176745285)
          ·
            refine ⟨7021550207527370658139741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37448267773479310176745285 7021550207527370658139741)
            ·
              refine ⟨2633081327822763996802403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7021550207527370658139741 2633081327822763996802403)
              ·
                refine ⟨3949621991734145995203605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2633081327822763996802403 3949621991734145995203605)
                ·
                  refine ⟨185138530862538093525169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3949621991734145995203605 185138530862538093525169)
                  ·
                    rfl

theorem cell21_811251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 6].length) (baseStart_811251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811251 prefixEnd_811251 := by exact prefixLift 811251
  have htrace : WordTrace (prefixWord ++ tailWord_811251) baseStart_811251 baseEnd_811251 := by
    simpa [prefixWord, tailWord_811251, baseEnd_811251] using wordTrace_append hprefix tailTrace_811251
  have hstable : (prefixWord ++ tailWord_811251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811251).length < 2 ^ (prefixWord ++ tailWord_811251).sum := by decide
  have hdescent : baseEnd_811251 < baseStart_811251 := by decide
  rcases family_descends (prefixWord ++ tailWord_811251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811389 : List Nat := [1, 4, 1, 1, 2, 4, 1, 2, 5]
def baseStart_811389 : Nat := 118140960795 + 811389 * 2 ^ 59
def prefixEnd_811389 : Nat := 4983230072969 + 3 ^ 40 * 811389 * 2
def baseEnd_811389 : Nat := 185170024342680520224887

theorem tailTrace_811389 : CollatzResearch.WordTrace tailWord_811389 prefixEnd_811389 185170024342680520224887 := by
  unfold tailWord_811389
  simp only [CollatzResearch.WordTrace]
  refine ⟨29593788057483702053853221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19729192038322468035902147 29593788057483702053853221)
  ·
    refine ⟨5548835260778194135097479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29593788057483702053853221 5548835260778194135097479)
    ·
      refine ⟨8323252891167291202646219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5548835260778194135097479 8323252891167291202646219)
      ·
        refine ⟨12484879336750936803969329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8323252891167291202646219 12484879336750936803969329)
        ·
          refine ⟨9363659502563202602976997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12484879336750936803969329 9363659502563202602976997)
          ·
            refine ⟨1755686156730600488058187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9363659502563202602976997 1755686156730600488058187)
            ·
              refine ⟨2633529235095900732087281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1755686156730600488058187 2633529235095900732087281)
              ·
                refine ⟨1975146926321925549065461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2633529235095900732087281 1975146926321925549065461)
                ·
                  refine ⟨185170024342680520224887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1975146926321925549065461 185170024342680520224887)
                  ·
                    rfl

theorem cell21_811389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_811389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811389 prefixEnd_811389 := by exact prefixLift 811389
  have htrace : WordTrace (prefixWord ++ tailWord_811389) baseStart_811389 baseEnd_811389 := by
    simpa [prefixWord, tailWord_811389, baseEnd_811389] using wordTrace_append hprefix tailTrace_811389
  have hstable : (prefixWord ++ tailWord_811389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811389).length < 2 ^ (prefixWord ++ tailWord_811389).sum := by decide
  have hdescent : baseEnd_811389 < baseStart_811389 := by decide
  rcases family_descends (prefixWord ++ tailWord_811389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811417 : List Nat := [1, 2, 1, 2, 1, 4, 10]
def baseStart_811417 : Nat := 118140960795 + 811417 * 2 ^ 59
def prefixEnd_811417 : Nat := 4983230072969 + 3 ^ 40 * 811417 * 2
def baseEnd_811417 : Nat := 20575157147128743750907

theorem tailTrace_811417 : CollatzResearch.WordTrace tailWord_811417 prefixEnd_811417 20575157147128743750907 := by
  unfold tailWord_811417
  simp only [CollatzResearch.WordTrace]
  refine ⟨29594809301382262835872505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19729872867588175223915003 29594809301382262835872505)
  ·
    refine ⟨22196106976036697126904379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29594809301382262835872505 22196106976036697126904379)
    ·
      refine ⟨33294160464055045690356569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22196106976036697126904379 33294160464055045690356569)
      ·
        refine ⟨24970620348041284267767427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33294160464055045690356569 24970620348041284267767427)
        ·
          refine ⟨37455930522061926401651141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24970620348041284267767427 37455930522061926401651141)
          ·
            refine ⟨7022986972886611200309589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37455930522061926401651141 7022986972886611200309589)
            ·
              refine ⟨20575157147128743750907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7022986972886611200309589 20575157147128743750907)
              ·
                rfl

theorem cell21_811417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 10].length) (baseStart_811417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811417 prefixEnd_811417 := by exact prefixLift 811417
  have htrace : WordTrace (prefixWord ++ tailWord_811417) baseStart_811417 baseEnd_811417 := by
    simpa [prefixWord, tailWord_811417, baseEnd_811417] using wordTrace_append hprefix tailTrace_811417
  have hstable : (prefixWord ++ tailWord_811417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811417).length < 2 ^ (prefixWord ++ tailWord_811417).sum := by decide
  have hdescent : baseEnd_811417 < baseStart_811417 := by decide
  rcases family_descends (prefixWord ++ tailWord_811417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811496 : List Nat := [2, 1, 4, 1, 1, 4, 1, 3, 4]
def baseStart_811496 : Nat := 118140960795 + 811496 * 2 ^ 59
def prefixEnd_811496 : Nat := 4983230072969 + 3 ^ 40 * 811496 * 2
def baseEnd_811496 : Nat := 185194443200472111941335

theorem tailTrace_811496 : CollatzResearch.WordTrace tailWord_811496 prefixEnd_811496 185194443200472111941335 := by
  unfold tailWord_811496
  simp only [CollatzResearch.WordTrace]
  refine ⟨14798845334048029663999171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19731793778730706218665561 14798845334048029663999171)
  ·
    refine ⟨22198268001072044495998757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14798845334048029663999171 22198268001072044495998757)
    ·
      refine ⟨4162175250201008342999767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22198268001072044495998757 4162175250201008342999767)
      ·
        refine ⟨6243262875301512514499651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4162175250201008342999767 6243262875301512514499651)
        ·
          refine ⟨9364894312952268771749477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6243262875301512514499651 9364894312952268771749477)
          ·
            refine ⟨1755917683678550394703027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9364894312952268771749477 1755917683678550394703027)
            ·
              refine ⟨2633876525517825592054541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1755917683678550394703027 2633876525517825592054541)
              ·
                refine ⟨987703697069184597020453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2633876525517825592054541 987703697069184597020453)
                ·
                  refine ⟨185194443200472111941335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 987703697069184597020453 185194443200472111941335)
                  ·
                    rfl

theorem cell21_811496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 4].length) (baseStart_811496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811496 prefixEnd_811496 := by exact prefixLift 811496
  have htrace : WordTrace (prefixWord ++ tailWord_811496) baseStart_811496 baseEnd_811496 := by
    simpa [prefixWord, tailWord_811496, baseEnd_811496] using wordTrace_append hprefix tailTrace_811496
  have hstable : (prefixWord ++ tailWord_811496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811496).length < 2 ^ (prefixWord ++ tailWord_811496).sum := by decide
  have hdescent : baseEnd_811496 < baseStart_811496 := by decide
  rcases family_descends (prefixWord ++ tailWord_811496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811510 : List Nat := [5, 1, 1, 1, 2, 1, 1, 9]
def baseStart_811510 : Nat := 118140960795 + 811510 * 2 ^ 59
def prefixEnd_811510 : Nat := 4983230072969 + 3 ^ 40 * 811510 * 2
def baseEnd_811510 : Nat := 61732546063737066235991

theorem tailTrace_811510 : CollatzResearch.WordTrace tailWord_811510 prefixEnd_811510 61732546063737066235991 := by
  unfold tailWord_811510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1849887580627833732437999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19732134193363559812671989 1849887580627833732437999)
  ·
    refine ⟨2774831370941750598656999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1849887580627833732437999 2774831370941750598656999)
    ·
      refine ⟨4162247056412625897985499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2774831370941750598656999 4162247056412625897985499)
      ·
        refine ⟨6243370584618938846978249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4162247056412625897985499 6243370584618938846978249)
        ·
          refine ⟨4682527938464204135233687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6243370584618938846978249 4682527938464204135233687)
          ·
            refine ⟨7023791907696306202850531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4682527938464204135233687 7023791907696306202850531)
            ·
              refine ⟨10535687861544459304275797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7023791907696306202850531 10535687861544459304275797)
              ·
                refine ⟨61732546063737066235991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10535687861544459304275797 61732546063737066235991)
                ·
                  rfl

theorem cell21_811510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_811510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_811510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_811510 prefixEnd_811510 := by exact prefixLift 811510
  have htrace : WordTrace (prefixWord ++ tailWord_811510) baseStart_811510 baseEnd_811510 := by
    simpa [prefixWord, tailWord_811510, baseEnd_811510] using wordTrace_append hprefix tailTrace_811510
  have hstable : (prefixWord ++ tailWord_811510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811510).length < 2 ^ (prefixWord ++ tailWord_811510).sum := by decide
  have hdescent : baseEnd_811510 < baseStart_811510 := by decide
  rcases family_descends (prefixWord ++ tailWord_811510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
