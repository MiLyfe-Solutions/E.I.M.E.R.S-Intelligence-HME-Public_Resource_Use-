import V185TrunkScan23Chunk0242

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1437611 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 4]
def baseStart_1437611 : Nat := 118140960795 + 1437611 * 2 ^ 59
def prefixEnd_1437611 : Nat := 4983230072969 + 3 ^ 40 * 1437611 * 2
def baseEnd_1437611 : Nat := 738185437190880074051053

theorem tailTrace_1437611 : CollatzResearch.WordTrace tailWord_1437611 prefixEnd_1437611 738185437190880074051053 := by
  unfold tailWord_1437611
  simp only [CollatzResearch.WordTrace]
  refine ⟨52433980794788346256712687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34955987196525564171141791 52433980794788346256712687)
  ·
    refine ⟨78650971192182519385069031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52433980794788346256712687 78650971192182519385069031)
    ·
      refine ⟨117976456788273779077603547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78650971192182519385069031 117976456788273779077603547)
      ·
        refine ⟨176964685182410668616405321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117976456788273779077603547 176964685182410668616405321)
        ·
          refine ⟨132723513886808001462303991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176964685182410668616405321 132723513886808001462303991)
          ·
            refine ⟨199085270830212002193455987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132723513886808001462303991 199085270830212002193455987)
            ·
              refine ⟨298627906245318003290183981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199085270830212002193455987 298627906245318003290183981)
              ·
                refine ⟨111985464841994251233818993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298627906245318003290183981 111985464841994251233818993)
                ·
                  refine ⟨83989098631495688425364245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111985464841994251233818993 83989098631495688425364245)
                  ·
                    refine ⟨3936988998351360394938949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83989098631495688425364245 3936988998351360394938949)
                    ·
                      refine ⟨738185437190880074051053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3936988998351360394938949 738185437190880074051053)
                      ·
                        rfl

theorem cell23_1437611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 4].length) (baseStart_1437611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437611 prefixEnd_1437611 := by exact prefixLift 1437611
  have htrace : WordTrace (prefixWord ++ tailWord_1437611) baseStart_1437611 baseEnd_1437611 := by
    simpa [prefixWord, tailWord_1437611, baseEnd_1437611] using wordTrace_append hprefix tailTrace_1437611
  have hstable : (prefixWord ++ tailWord_1437611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437611).length < 2 ^ (prefixWord ++ tailWord_1437611).sum := by decide
  have hdescent : baseEnd_1437611 < baseStart_1437611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437625 : List Nat := [1, 2, 1, 4, 2, 1, 3, 3, 2, 4]
def baseStart_1437625 : Nat := 118140960795 + 1437625 * 2 ^ 59
def prefixEnd_1437625 : Nat := 4983230072969 + 3 ^ 40 * 1437625 * 2
def baseEnd_1437625 : Nat := 246064208640014339758663

theorem tailTrace_1437625 : CollatzResearch.WordTrace tailWord_1437625 prefixEnd_1437625 246064208640014339758663 := by
  unfold tailWord_1437625
  simp only [CollatzResearch.WordTrace]
  refine ⟨52434491416737626647722329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34956327611158417765148219 52434491416737626647722329)
  ·
    refine ⟨39325868562553219985791747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52434491416737626647722329 39325868562553219985791747)
    ·
      refine ⟨58988802843829829978687621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39325868562553219985791747 58988802843829829978687621)
      ·
        refine ⟨11060400533218093121003929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58988802843829829978687621 11060400533218093121003929)
        ·
          refine ⟨8295300399913569840752947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11060400533218093121003929 8295300399913569840752947)
          ·
            refine ⟨12442950599870354761129421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8295300399913569840752947 12442950599870354761129421)
            ·
              refine ⟨4666106474951383035423533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12442950599870354761129421 4666106474951383035423533)
              ·
                refine ⟨1749789928106768638283825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4666106474951383035423533 1749789928106768638283825)
                ·
                  refine ⟨1312342446080076478712869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1749789928106768638283825 1312342446080076478712869)
                  ·
                    refine ⟨246064208640014339758663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1312342446080076478712869 246064208640014339758663)
                    ·
                      rfl

theorem cell23_1437625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 4].length) (baseStart_1437625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437625 prefixEnd_1437625 := by exact prefixLift 1437625
  have htrace : WordTrace (prefixWord ++ tailWord_1437625) baseStart_1437625 baseEnd_1437625 := by
    simpa [prefixWord, tailWord_1437625, baseEnd_1437625] using wordTrace_append hprefix tailTrace_1437625
  have hstable : (prefixWord ++ tailWord_1437625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437625).length < 2 ^ (prefixWord ++ tailWord_1437625).sum := by decide
  have hdescent : baseEnd_1437625 < baseStart_1437625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437641 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 1, 4, 6]
def baseStart_1437641 : Nat := 118140960795 + 1437641 * 2 ^ 59
def prefixEnd_1437641 : Nat := 4983230072969 + 3 ^ 40 * 1437641 * 2
def baseEnd_1437641 : Nat := 738200841610514956675915

theorem tailTrace_1437641 : CollatzResearch.WordTrace tailWord_1437641 prefixEnd_1437641 738200841610514956675915 := by
  unfold tailWord_1437641
  simp only [CollatzResearch.WordTrace]
  refine ⟨52435074984679661380304777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34956716656453107586869851 52435074984679661380304777)
  ·
    refine ⟨39326306238509746035228583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52435074984679661380304777 39326306238509746035228583)
    ·
      refine ⟨58989459357764619052842875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39326306238509746035228583 58989459357764619052842875)
      ·
        refine ⟨88484189036646928579264313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58989459357764619052842875 88484189036646928579264313)
        ·
          refine ⟨66363141777485196434448235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88484189036646928579264313 66363141777485196434448235)
          ·
            refine ⟨99544712666227794651672353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66363141777485196434448235 99544712666227794651672353)
            ·
              refine ⟨74658534499670845988754265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99544712666227794651672353 74658534499670845988754265)
              ·
                refine ⟨55993900874753134491565699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74658534499670845988754265 55993900874753134491565699)
                ·
                  refine ⟨83990851312129701737348549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55993900874753134491565699 83990851312129701737348549)
                  ·
                    refine ⟨15748284621024319075752853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83990851312129701737348549 15748284621024319075752853)
                    ·
                      refine ⟨738200841610514956675915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15748284621024319075752853 738200841610514956675915)
                      ·
                        rfl

theorem cell23_1437641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_1437641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437641 prefixEnd_1437641 := by exact prefixLift 1437641
  have htrace : WordTrace (prefixWord ++ tailWord_1437641) baseStart_1437641 baseEnd_1437641 := by
    simpa [prefixWord, tailWord_1437641, baseEnd_1437641] using wordTrace_append hprefix tailTrace_1437641
  have hstable : (prefixWord ++ tailWord_1437641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437641).length < 2 ^ (prefixWord ++ tailWord_1437641).sum := by decide
  have hdescent : baseEnd_1437641 < baseStart_1437641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437648 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 3]
def baseStart_1437648 : Nat := 118140960795 + 1437648 * 2 ^ 59
def prefixEnd_1437648 : Nat := 4983230072969 + 3 ^ 40 * 1437648 * 2
def baseEnd_1437648 : Nat := 738204435975096429288383

theorem tailTrace_1437648 : CollatzResearch.WordTrace tailWord_1437648 prefixEnd_1437648 738204435975096429288383 := by
  unfold tailWord_1437648
  simp only [CollatzResearch.WordTrace]
  refine ⟨26217665147827150787904799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34956886863769534383873065 26217665147827150787904799)
  ·
    refine ⟨39326497721740726181857199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26217665147827150787904799 39326497721740726181857199)
    ·
      refine ⟨58989746582611089272785799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39326497721740726181857199 58989746582611089272785799)
      ·
        refine ⟨88484619873916633909178699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58989746582611089272785799 88484619873916633909178699)
        ·
          refine ⟨132726929810874950863768049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88484619873916633909178699 132726929810874950863768049)
          ·
            refine ⟨99545197358156213147826037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132726929810874950863768049 99545197358156213147826037)
            ·
              refine ⟨9332362252327144982608691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99545197358156213147826037 9332362252327144982608691)
              ·
                refine ⟨13998543378490717473913037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9332362252327144982608691 13998543378490717473913037)
                ·
                  refine ⟨5249453766934019052717389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13998543378490717473913037 5249453766934019052717389)
                  ·
                    refine ⟨1968545162600257144769021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5249453766934019052717389 1968545162600257144769021)
                    ·
                      refine ⟨738204435975096429288383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1968545162600257144769021 738204435975096429288383)
                      ·
                        rfl

theorem cell23_1437648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 3].length) (baseStart_1437648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437648 prefixEnd_1437648 := by exact prefixLift 1437648
  have htrace : WordTrace (prefixWord ++ tailWord_1437648) baseStart_1437648 baseEnd_1437648 := by
    simpa [prefixWord, tailWord_1437648, baseEnd_1437648] using wordTrace_append hprefix tailTrace_1437648
  have hstable : (prefixWord ++ tailWord_1437648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437648).length < 2 ^ (prefixWord ++ tailWord_1437648).sum := by decide
  have hdescent : baseEnd_1437648 < baseStart_1437648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437665 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 4, 1, 3]
def baseStart_1437665 : Nat := 118140960795 + 1437665 * 2 ^ 59
def prefixEnd_1437665 : Nat := 4983230072969 + 3 ^ 40 * 1437665 * 2
def baseEnd_1437665 : Nat := 738213165146222862775805

theorem tailTrace_1437665 : CollatzResearch.WordTrace tailWord_1437665 prefixEnd_1437665 738213165146222862775805 := by
  unfold tailWord_1437665
  simp only [CollatzResearch.WordTrace]
  refine ⟨52435950336592713479178449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34957300224395142319452299 52435950336592713479178449)
  ·
    refine ⟨39326962752444535109383837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52435950336592713479178449 39326962752444535109383837)
    ·
      refine ⟨14747611032166700666018939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39326962752444535109383837 14747611032166700666018939)
      ·
        refine ⟨22121416548250050999028409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14747611032166700666018939 22121416548250050999028409)
        ·
          refine ⟨16591062411187538249271307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22121416548250050999028409 16591062411187538249271307)
          ·
            refine ⟨24886593616781307373906961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16591062411187538249271307 24886593616781307373906961)
            ·
              refine ⟨18664945212585980530430221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24886593616781307373906961 18664945212585980530430221)
              ·
                refine ⟨6999354454719742698911333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18664945212585980530430221 6999354454719742698911333)
                ·
                  refine ⟨1312378960259951756045875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6999354454719742698911333 1312378960259951756045875)
                  ·
                    refine ⟨1968568440389927634068813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1312378960259951756045875 1968568440389927634068813)
                    ·
                      refine ⟨738213165146222862775805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1968568440389927634068813 738213165146222862775805)
                      ·
                        rfl

theorem cell23_1437665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_1437665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437665 prefixEnd_1437665 := by exact prefixLift 1437665
  have htrace : WordTrace (prefixWord ++ tailWord_1437665) baseStart_1437665 baseEnd_1437665 := by
    simpa [prefixWord, tailWord_1437665, baseEnd_1437665] using wordTrace_append hprefix tailTrace_1437665
  have hstable : (prefixWord ++ tailWord_1437665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437665).length < 2 ^ (prefixWord ++ tailWord_1437665).sum := by decide
  have hdescent : baseEnd_1437665 < baseStart_1437665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437692 : List Nat := [2, 2, 2, 1, 2, 2, 2, 4, 1, 3, 2]
def baseStart_1437692 : Nat := 118140960795 + 1437692 * 2 ^ 59
def prefixEnd_1437692 : Nat := 4983230072969 + 3 ^ 40 * 1437692 * 2
def baseEnd_1437692 : Nat := 738227029123894257138181

theorem tailTrace_1437692 : CollatzResearch.WordTrace tailWord_1437692 prefixEnd_1437692 738227029123894257138181 := by
  unfold tailWord_1437692
  simp only [CollatzResearch.WordTrace]
  refine ⟨26218467553747448545205665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34957956738329931393607553 26218467553747448545205665)
  ·
    refine ⟨19663850665310586408904249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26218467553747448545205665 19663850665310586408904249)
    ·
      refine ⟨14747887998982939806678187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19663850665310586408904249 14747887998982939806678187)
      ·
        refine ⟨22121831998474409710017281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14747887998982939806678187 22121831998474409710017281)
        ·
          refine ⟨16591373998855807282512961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22121831998474409710017281 16591373998855807282512961)
          ·
            refine ⟨12443530499141855461884721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16591373998855807282512961 12443530499141855461884721)
            ·
              refine ⟨9332647874356391596413541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12443530499141855461884721 9332647874356391596413541)
              ·
                refine ⟨1749871476441823424327539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9332647874356391596413541 1749871476441823424327539)
                ·
                  refine ⟨2624807214662735136491309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1749871476441823424327539 2624807214662735136491309)
                  ·
                    refine ⟨984302705498525676184241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2624807214662735136491309 984302705498525676184241)
                    ·
                      refine ⟨738227029123894257138181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 984302705498525676184241 738227029123894257138181)
                      ·
                        rfl

theorem cell23_1437692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_1437692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437692 prefixEnd_1437692 := by exact prefixLift 1437692
  have htrace : WordTrace (prefixWord ++ tailWord_1437692) baseStart_1437692 baseEnd_1437692 := by
    simpa [prefixWord, tailWord_1437692, baseEnd_1437692] using wordTrace_append hprefix tailTrace_1437692
  have hstable : (prefixWord ++ tailWord_1437692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437692).length < 2 ^ (prefixWord ++ tailWord_1437692).sum := by decide
  have hdescent : baseEnd_1437692 < baseStart_1437692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437708 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 1, 3, 5]
def baseStart_1437708 : Nat := 118140960795 + 1437708 * 2 ^ 59
def prefixEnd_1437708 : Nat := 4983230072969 + 3 ^ 40 * 1437708 * 2
def baseEnd_1437708 : Nat := 738235244814366194538107

theorem tailTrace_1437708 : CollatzResearch.WordTrace tailWord_1437708 prefixEnd_1437708 738235244814366194538107 := by
  unfold tailWord_1437708
  simp only [CollatzResearch.WordTrace]
  refine ⟨26218759337718465911496889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34958345783624621215329185 26218759337718465911496889)
  ·
    refine ⟨19664069503288849433622667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26218759337718465911496889 19664069503288849433622667)
    ·
      refine ⟨29496104254933274150434001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19664069503288849433622667 29496104254933274150434001)
      ·
        refine ⟨22122078191199955612825501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29496104254933274150434001 22122078191199955612825501)
        ·
          refine ⟨8295779321699983354809563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22122078191199955612825501 8295779321699983354809563)
          ·
            refine ⟨12443668982549975032214345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8295779321699983354809563 12443668982549975032214345)
            ·
              refine ⟨9332751736912481274160759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12443668982549975032214345 9332751736912481274160759)
              ·
                refine ⟨13999127605368721911241139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9332751736912481274160759 13999127605368721911241139)
                ·
                  refine ⟨20998691408053082866861709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13999127605368721911241139 20998691408053082866861709)
                  ·
                    refine ⟨7874509278019906075073141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20998691408053082866861709 7874509278019906075073141)
                    ·
                      refine ⟨738235244814366194538107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7874509278019906075073141 738235244814366194538107)
                      ·
                        rfl

theorem cell23_1437708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_1437708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437708 prefixEnd_1437708 := by exact prefixLift 1437708
  have htrace : WordTrace (prefixWord ++ tailWord_1437708) baseStart_1437708 baseEnd_1437708 := by
    simpa [prefixWord, tailWord_1437708, baseEnd_1437708] using wordTrace_append hprefix tailTrace_1437708
  have hstable : (prefixWord ++ tailWord_1437708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437708).length < 2 ^ (prefixWord ++ tailWord_1437708).sum := by decide
  have hdescent : baseEnd_1437708 < baseStart_1437708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437716 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_1437716 : Nat := 118140960795 + 1437716 * 2 ^ 59
def prefixEnd_1437716 : Nat := 4983230072969 + 3 ^ 40 * 1437716 * 2
def baseEnd_1437716 : Nat := 738239352659602163238071

theorem tailTrace_1437716 : CollatzResearch.WordTrace tailWord_1437716 prefixEnd_1437716 738239352659602163238071 := by
  unfold tailWord_1437716
  simp only [CollatzResearch.WordTrace]
  refine ⟨26218905229703974594642501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34958540306271966126190001 26218905229703974594642501)
  ·
    refine ⟨4916044730569495236495469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26218905229703974594642501 4916044730569495236495469)
    ·
      refine ⟨1843516773963560713685801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4916044730569495236495469 1843516773963560713685801)
      ·
        refine ⟨1382637580472670535264351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1843516773963560713685801 1382637580472670535264351)
        ·
          refine ⟨2073956370709005802896527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1382637580472670535264351 2073956370709005802896527)
          ·
            refine ⟨3110934556063508704344791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2073956370709005802896527 3110934556063508704344791)
            ·
              refine ⟨4666401834095263056517187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3110934556063508704344791 4666401834095263056517187)
              ·
                refine ⟨6999602751142894584775781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4666401834095263056517187 6999602751142894584775781)
                ·
                  refine ⟨1312425515839292734645459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6999602751142894584775781 1312425515839292734645459)
                  ·
                    refine ⟨1968638273758939101968189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1312425515839292734645459 1968638273758939101968189)
                    ·
                      refine ⟨738239352659602163238071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1968638273758939101968189 738239352659602163238071)
                      ·
                        rfl

theorem cell23_1437716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_1437716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437716 prefixEnd_1437716 := by exact prefixLift 1437716
  have htrace : WordTrace (prefixWord ++ tailWord_1437716) baseStart_1437716 baseEnd_1437716 := by
    simpa [prefixWord, tailWord_1437716, baseEnd_1437716] using wordTrace_append hprefix tailTrace_1437716
  have hstable : (prefixWord ++ tailWord_1437716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437716).length < 2 ^ (prefixWord ++ tailWord_1437716).sum := by decide
  have hdescent : baseEnd_1437716 < baseStart_1437716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437765 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 1, 7, 2]
def baseStart_1437765 : Nat := 118140960795 + 1437765 * 2 ^ 59
def prefixEnd_1437765 : Nat := 4983230072969 + 3 ^ 40 * 1437765 * 2
def baseEnd_1437765 : Nat := 738264513211672471525345

theorem tailTrace_1437765 : CollatzResearch.WordTrace tailWord_1437765 prefixEnd_1437765 738264513211672471525345 := by
  unfold tailWord_1437765
  simp only [CollatzResearch.WordTrace]
  refine ⟨52439597636230430557818749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34959731757486953705212499 52439597636230430557818749)
  ·
    refine ⟨19664849113586411459182031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52439597636230430557818749 19664849113586411459182031)
    ·
      refine ⟨29497273670379617188773047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19664849113586411459182031 29497273670379617188773047)
      ·
        refine ⟨44245910505569425783159571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29497273670379617188773047 44245910505569425783159571)
        ·
          refine ⟨66368865758354138674739357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44245910505569425783159571 66368865758354138674739357)
          ·
            refine ⟨24888324659382802003027259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66368865758354138674739357 24888324659382802003027259)
            ·
              refine ⟨37332486989074203004540889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24888324659382802003027259 37332486989074203004540889)
              ·
                refine ⟨27999365241805652253405667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37332486989074203004540889 27999365241805652253405667)
                ·
                  refine ⟨41999047862708478380108501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27999365241805652253405667 41999047862708478380108501)
                  ·
                    refine ⟨984352684282229962033793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41999047862708478380108501 984352684282229962033793)
                    ·
                      refine ⟨738264513211672471525345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 984352684282229962033793 738264513211672471525345)
                      ·
                        rfl

theorem cell23_1437765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 7, 2].length) (baseStart_1437765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437765 prefixEnd_1437765 := by exact prefixLift 1437765
  have htrace : WordTrace (prefixWord ++ tailWord_1437765) baseStart_1437765 baseEnd_1437765 := by
    simpa [prefixWord, tailWord_1437765, baseEnd_1437765] using wordTrace_append hprefix tailTrace_1437765
  have hstable : (prefixWord ++ tailWord_1437765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437765).length < 2 ^ (prefixWord ++ tailWord_1437765).sum := by decide
  have hdescent : baseEnd_1437765 < baseStart_1437765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437790 : List Nat := [4, 4, 1, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_1437790 : Nat := 118140960795 + 1437790 * 2 ^ 59
def prefixEnd_1437790 : Nat := 4983230072969 + 3 ^ 40 * 1437790 * 2
def baseEnd_1437790 : Nat := 738277350228034873712731

theorem tailTrace_1437790 : CollatzResearch.WordTrace tailWord_1437790 prefixEnd_1437790 738277350228034873712731 := by
  unfold tailWord_1437790
  simp only [CollatzResearch.WordTrace]
  refine ⟨6555063682642482478434853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34960339640759906551652549 6555063682642482478434853)
  ·
    refine ⟨1229074440495465464706535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6555063682642482478434853 1229074440495465464706535)
    ·
      refine ⟨1843611660743198197059803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1229074440495465464706535 1843611660743198197059803)
      ·
        refine ⟨2765417491114797295589705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1843611660743198197059803 2765417491114797295589705)
        ·
          refine ⟨2074063118336097971692279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2765417491114797295589705 2074063118336097971692279)
          ·
            refine ⟨3111094677504146957538419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2074063118336097971692279 3111094677504146957538419)
            ·
              refine ⟨4666642016256220436307629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3111094677504146957538419 4666642016256220436307629)
              ·
                refine ⟨1749990756096082663615361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4666642016256220436307629 1749990756096082663615361)
                ·
                  refine ⟨1312493067072061997711521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1749990756096082663615361 1312493067072061997711521)
                  ·
                    refine ⟨984369800304046498283641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1312493067072061997711521 984369800304046498283641)
                    ·
                      refine ⟨738277350228034873712731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 984369800304046498283641 738277350228034873712731)
                      ·
                        rfl

theorem cell23_1437790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_1437790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437790 prefixEnd_1437790 := by exact prefixLift 1437790
  have htrace : WordTrace (prefixWord ++ tailWord_1437790) baseStart_1437790 baseEnd_1437790 := by
    simpa [prefixWord, tailWord_1437790, baseEnd_1437790] using wordTrace_append hprefix tailTrace_1437790
  have hstable : (prefixWord ++ tailWord_1437790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437790).length < 2 ^ (prefixWord ++ tailWord_1437790).sum := by decide
  have hdescent : baseEnd_1437790 < baseStart_1437790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437886 : List Nat := [4, 2, 1, 1, 5, 1, 1, 2, 6]
def baseStart_1437886 : Nat := 118140960795 + 1437886 * 2 ^ 59
def prefixEnd_1437886 : Nat := 4983230072969 + 3 ^ 40 * 1437886 * 2
def baseEnd_1437886 : Nat := 82036293818985166456921

theorem tailTrace_1437886 : CollatzResearch.WordTrace tailWord_1437886 prefixEnd_1437886 82036293818985166456921 := by
  unfold tailWord_1437886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6555501358599008527871689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34962673912528045481982341 6555501358599008527871689)
  ·
    refine ⟨4916626018949256395903767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6555501358599008527871689 4916626018949256395903767)
    ·
      refine ⟨7374939028423884593855651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4916626018949256395903767 7374939028423884593855651)
      ·
        refine ⟨11062408542635826890783477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7374939028423884593855651 11062408542635826890783477)
        ·
          refine ⟨1037100800872108771010951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11062408542635826890783477 1037100800872108771010951)
          ·
            refine ⟨1555651201308163156516427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037100800872108771010951 1555651201308163156516427)
            ·
              refine ⟨2333476801962244734774641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1555651201308163156516427 2333476801962244734774641)
              ·
                refine ⟨1750107601471683551080981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2333476801962244734774641 1750107601471683551080981)
                ·
                  refine ⟨82036293818985166456921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1750107601471683551080981 82036293818985166456921)
                  ·
                    rfl

theorem cell23_1437886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_1437886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437886 prefixEnd_1437886 := by exact prefixLift 1437886
  have htrace : WordTrace (prefixWord ++ tailWord_1437886) baseStart_1437886 baseEnd_1437886 := by
    simpa [prefixWord, tailWord_1437886, baseEnd_1437886] using wordTrace_append hprefix tailTrace_1437886
  have hstable : (prefixWord ++ tailWord_1437886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437886).length < 2 ^ (prefixWord ++ tailWord_1437886).sum := by decide
  have hdescent : baseEnd_1437886 < baseStart_1437886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437905 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 3, 1, 5]
def baseStart_1437905 : Nat := 118140960795 + 1437905 * 2 ^ 59
def prefixEnd_1437905 : Nat := 4983230072969 + 3 ^ 40 * 1437905 * 2
def baseEnd_1437905 : Nat := 738336400503301923774701

theorem tailTrace_1437905 : CollatzResearch.WordTrace tailWord_1437905 prefixEnd_1437905 738336400503301923774701 := by
  unfold tailWord_1437905
  simp only [CollatzResearch.WordTrace]
  refine ⟨52444703855723234467915169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34963135903815489645276779 52444703855723234467915169)
  ·
    refine ⟨39333527891792425850936377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52444703855723234467915169 39333527891792425850936377)
    ·
      refine ⟨29500145918844319388202283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39333527891792425850936377 29500145918844319388202283)
      ·
        refine ⟨44250218878266479082303425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29500145918844319388202283 44250218878266479082303425)
        ·
          refine ⟨33187664158699859311727569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44250218878266479082303425 33187664158699859311727569)
          ·
            refine ⟨24890748119024894483795677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33187664158699859311727569 24890748119024894483795677)
            ·
              refine ⟨9334030544634335431423379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24890748119024894483795677 9334030544634335431423379)
              ·
                refine ⟨14001045816951503147135069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9334030544634335431423379 14001045816951503147135069)
                ·
                  refine ⟨5250392181356813680175651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14001045816951503147135069 5250392181356813680175651)
                  ·
                    refine ⟨7875588272035220520263477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5250392181356813680175651 7875588272035220520263477)
                    ·
                      refine ⟨738336400503301923774701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7875588272035220520263477 738336400503301923774701)
                      ·
                        rfl

theorem cell23_1437905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_1437905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437905 prefixEnd_1437905 := by exact prefixLift 1437905
  have htrace : WordTrace (prefixWord ++ tailWord_1437905) baseStart_1437905 baseEnd_1437905 := by
    simpa [prefixWord, tailWord_1437905, baseEnd_1437905] using wordTrace_append hprefix tailTrace_1437905
  have hstable : (prefixWord ++ tailWord_1437905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437905).length < 2 ^ (prefixWord ++ tailWord_1437905).sum := by decide
  have hdescent : baseEnd_1437905 < baseStart_1437905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437912 : List Nat := [2, 1, 2, 2, 4, 1, 3, 1, 1, 6]
def baseStart_1437912 : Nat := 118140960795 + 1437912 * 2 ^ 59
def prefixEnd_1437912 : Nat := 4983230072969 + 3 ^ 40 * 1437912 * 2
def baseEnd_1437912 : Nat := 246113331622627798795723

theorem tailTrace_1437912 : CollatzResearch.WordTrace tailWord_1437912 prefixEnd_1437912 246113331622627798795723 := by
  unfold tailWord_1437912
  simp only [CollatzResearch.WordTrace]
  refine ⟨26222479583348937331709995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34963306111131916442279993 26222479583348937331709995)
  ·
    refine ⟨39333719375023405997564993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26222479583348937331709995 39333719375023405997564993)
    ·
      refine ⟨29500289531267554498173745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39333719375023405997564993 29500289531267554498173745)
      ·
        refine ⟨22125217148450665873630309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29500289531267554498173745 22125217148450665873630309)
        ·
          refine ⟨4148478215334499851305683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22125217148450665873630309 4148478215334499851305683)
          ·
            refine ⟨6222717323001749776958525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4148478215334499851305683 6222717323001749776958525)
            ·
              refine ⟨2333518996125656166359447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6222717323001749776958525 2333518996125656166359447)
              ·
                refine ⟨3500278494188484249539171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2333518996125656166359447 3500278494188484249539171)
                ·
                  refine ⟨5250417741282726374308757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3500278494188484249539171 5250417741282726374308757)
                  ·
                    refine ⟨246113331622627798795723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5250417741282726374308757 246113331622627798795723)
                    ·
                      rfl

theorem cell23_1437912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_1437912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437912 prefixEnd_1437912 := by exact prefixLift 1437912
  have htrace : WordTrace (prefixWord ++ tailWord_1437912) baseStart_1437912 baseEnd_1437912 := by
    simpa [prefixWord, tailWord_1437912, baseEnd_1437912] using wordTrace_append hprefix tailTrace_1437912
  have hstable : (prefixWord ++ tailWord_1437912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437912).length < 2 ^ (prefixWord ++ tailWord_1437912).sum := by decide
  have hdescent : baseEnd_1437912 < baseStart_1437912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437955 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 2, 7]
def baseStart_1437955 : Nat := 118140960795 + 1437955 * 2 ^ 59
def prefixEnd_1437955 : Nat := 4983230072969 + 3 ^ 40 * 1437955 * 2
def baseEnd_1437955 : Nat := 246120691512008909383157

theorem tailTrace_1437955 : CollatzResearch.WordTrace tailWord_1437955 prefixEnd_1437955 246120691512008909383157 := by
  unfold tailWord_1437955
  simp only [CollatzResearch.WordTrace]
  refine ⟨52446527505542093007235319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34964351670361395338156879 52446527505542093007235319)
  ·
    refine ⟨78669791258313139510852979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52446527505542093007235319 78669791258313139510852979)
    ·
      refine ⟨118004686887469709266279469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78669791258313139510852979 118004686887469709266279469)
      ·
        refine ⟨44251757582801140974854801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118004686887469709266279469 44251757582801140974854801)
        ·
          refine ⟨33188818187100855731141101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44251757582801140974854801 33188818187100855731141101)
          ·
            refine ⟨12445806820162820899177913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33188818187100855731141101 12445806820162820899177913)
            ·
              refine ⟨9334355115122115674383435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12445806820162820899177913 9334355115122115674383435)
              ·
                refine ⟨14001532672683173511575153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9334355115122115674383435 14001532672683173511575153)
                ·
                  refine ⟨10501149504512380133681365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14001532672683173511575153 10501149504512380133681365)
                  ·
                    refine ⟨246120691512008909383157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10501149504512380133681365 246120691512008909383157)
                    ·
                      rfl

theorem cell23_1437955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 7].length) (baseStart_1437955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437955 prefixEnd_1437955 := by exact prefixLift 1437955
  have htrace : WordTrace (prefixWord ++ tailWord_1437955) baseStart_1437955 baseEnd_1437955 := by
    simpa [prefixWord, tailWord_1437955, baseEnd_1437955] using wordTrace_append hprefix tailTrace_1437955
  have hstable : (prefixWord ++ tailWord_1437955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437955).length < 2 ^ (prefixWord ++ tailWord_1437955).sum := by decide
  have hdescent : baseEnd_1437955 < baseStart_1437955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1437959 : List Nat := [1, 1, 4, 5, 1, 1, 2, 8]
def baseStart_1437959 : Nat := 118140960795 + 1437959 * 2 ^ 59
def prefixEnd_1437959 : Nat := 4983230072969 + 3 ^ 40 * 1437959 * 2
def baseEnd_1437959 : Nat := 27346819572542396759239

theorem tailTrace_1437959 : CollatzResearch.WordTrace tailWord_1437959 prefixEnd_1437959 27346819572542396759239 := by
  unfold tailWord_1437959
  simp only [CollatzResearch.WordTrace]
  refine ⟨52446673397527601690380931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34964448931685067793587287 52446673397527601690380931)
  ·
    refine ⟨78670010096291402535571397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52446673397527601690380931 78670010096291402535571397)
    ·
      refine ⟨14750626893054637975419637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78670010096291402535571397 14750626893054637975419637)
      ·
        refine ⟨1382871271223872310195591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14750626893054637975419637 1382871271223872310195591)
        ·
          refine ⟨2074306906835808465293387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1382871271223872310195591 2074306906835808465293387)
          ·
            refine ⟨3111460360253712697940081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2074306906835808465293387 3111460360253712697940081)
            ·
              refine ⟨2333595270190284523455061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3111460360253712697940081 2333595270190284523455061)
              ·
                refine ⟨27346819572542396759239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2333595270190284523455061 27346819572542396759239)
                ·
                  rfl

theorem cell23_1437959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 8].length) (baseStart_1437959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1437959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1437959 prefixEnd_1437959 := by exact prefixLift 1437959
  have htrace : WordTrace (prefixWord ++ tailWord_1437959) baseStart_1437959 baseEnd_1437959 := by
    simpa [prefixWord, tailWord_1437959, baseEnd_1437959] using wordTrace_append hprefix tailTrace_1437959
  have hstable : (prefixWord ++ tailWord_1437959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1437959).length < 2 ^ (prefixWord ++ tailWord_1437959).sum := by decide
  have hdescent : baseEnd_1437959 < baseStart_1437959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1437959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438012 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 1, 6, 3]
def baseStart_1438012 : Nat := 118140960795 + 1438012 * 2 ^ 59
def prefixEnd_1438012 : Nat := 4983230072969 + 3 ^ 40 * 1438012 * 2
def baseEnd_1438012 : Nat := 738391342933333005136709

theorem tailTrace_1438012 : CollatzResearch.WordTrace tailWord_1438012 prefixEnd_1438012 738391342933333005136709 := by
  unfold tailWord_1438012
  simp only [CollatzResearch.WordTrace]
  refine ⟨26224303233167795871030145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34965737644223727828040193 26224303233167795871030145)
  ·
    refine ⟨19668227424875846903272609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26224303233167795871030145 19668227424875846903272609)
    ·
      refine ⟨14751170568656885177454457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19668227424875846903272609 14751170568656885177454457)
      ·
        refine ⟨11063377926492663883090843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14751170568656885177454457 11063377926492663883090843)
        ·
          refine ⟨16595066889738995824636265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11063377926492663883090843 16595066889738995824636265)
          ·
            refine ⟨12446300167304246868477199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16595066889738995824636265 12446300167304246868477199)
            ·
              refine ⟨18669450250956370302715799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12446300167304246868477199 18669450250956370302715799)
              ·
                refine ⟨28004175376434555454073699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18669450250956370302715799 28004175376434555454073699)
                ·
                  refine ⟨42006263064651833181110549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28004175376434555454073699 42006263064651833181110549)
                  ·
                    refine ⟨1969043581155554680364557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42006263064651833181110549 1969043581155554680364557)
                    ·
                      refine ⟨738391342933333005136709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1969043581155554680364557 738391342933333005136709)
                      ·
                        rfl

theorem cell23_1438012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_1438012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438012 prefixEnd_1438012 := by exact prefixLift 1438012
  have htrace : WordTrace (prefixWord ++ tailWord_1438012) baseStart_1438012 baseEnd_1438012 := by
    simpa [prefixWord, tailWord_1438012, baseEnd_1438012] using wordTrace_append hprefix tailTrace_1438012
  have hstable : (prefixWord ++ tailWord_1438012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438012).length < 2 ^ (prefixWord ++ tailWord_1438012).sum := by decide
  have hdescent : baseEnd_1438012 < baseStart_1438012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438032 : List Nat := [2, 1, 1, 1, 1, 7, 1, 2, 7]
def baseStart_1438032 : Nat := 118140960795 + 1438032 * 2 ^ 59
def prefixEnd_1438032 : Nat := 4983230072969 + 3 ^ 40 * 1438032 * 2
def baseEnd_1438032 : Nat := 82044623616269214098513

theorem tailTrace_1438032 : CollatzResearch.WordTrace tailWord_1438032 prefixEnd_1438032 82044623616269214098513 := by
  unfold tailWord_1438032
  simp only [CollatzResearch.WordTrace]
  refine ⟨26224667963131567578894175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34966223950842090105192233 26224667963131567578894175)
  ·
    refine ⟨39337001944697351368341263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26224667963131567578894175 39337001944697351368341263)
    ·
      refine ⟨59005502917046027052511895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39337001944697351368341263 59005502917046027052511895)
      ·
        refine ⟨88508254375569040578767843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59005502917046027052511895 88508254375569040578767843)
        ·
          refine ⟨132762381563353560868151765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88508254375569040578767843 132762381563353560868151765)
          ·
            refine ⟨3111618317891099082847307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 132762381563353560868151765 3111618317891099082847307)
            ·
              refine ⟨4667427476836648624270961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3111618317891099082847307 4667427476836648624270961)
              ·
                refine ⟨3500570607627486468203221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4667427476836648624270961 3500570607627486468203221)
                ·
                  refine ⟨82044623616269214098513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3500570607627486468203221 82044623616269214098513)
                  ·
                    rfl

theorem cell23_1438032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 7].length) (baseStart_1438032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438032 prefixEnd_1438032 := by exact prefixLift 1438032
  have htrace : WordTrace (prefixWord ++ tailWord_1438032) baseStart_1438032 baseEnd_1438032 := by
    simpa [prefixWord, tailWord_1438032, baseEnd_1438032] using wordTrace_append hprefix tailTrace_1438032
  have hstable : (prefixWord ++ tailWord_1438032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438032).length < 2 ^ (prefixWord ++ tailWord_1438032).sum := by decide
  have hdescent : baseEnd_1438032 < baseStart_1438032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438042 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3]
def baseStart_1438042 : Nat := 118140960795 + 1438042 * 2 ^ 59
def prefixEnd_1438042 : Nat := 4983230072969 + 3 ^ 40 * 1438042 * 2
def baseEnd_1438042 : Nat := 738406747352967887761571

theorem tailTrace_1438042 : CollatzResearch.WordTrace tailWord_1438042 prefixEnd_1438042 738406747352967887761571 := by
  unfold tailWord_1438042
  simp only [CollatzResearch.WordTrace]
  refine ⟨13112425164056726716413095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34966467104151271243768253 13112425164056726716413095)
  ·
    refine ⟨19668637746085090074619643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13112425164056726716413095 19668637746085090074619643)
    ·
      refine ⟨29502956619127635111929465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19668637746085090074619643 29502956619127635111929465)
      ·
        refine ⟨22127217464345726333947099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29502956619127635111929465 22127217464345726333947099)
        ·
          refine ⟨33190826196518589500920649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22127217464345726333947099 33190826196518589500920649)
          ·
            refine ⟨24893119647388942125690487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33190826196518589500920649 24893119647388942125690487)
            ·
              refine ⟨37339679471083413188535731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24893119647388942125690487 37339679471083413188535731)
              ·
                refine ⟨56009519206625119782803597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37339679471083413188535731 56009519206625119782803597)
                ·
                  refine ⟨21003569702484419918551349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56009519206625119782803597 21003569702484419918551349)
                  ·
                    refine ⟨1969084659607914367364189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21003569702484419918551349 1969084659607914367364189)
                    ·
                      refine ⟨738406747352967887761571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1969084659607914367364189 738406747352967887761571)
                      ·
                        rfl

theorem cell23_1438042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_1438042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438042 prefixEnd_1438042 := by exact prefixLift 1438042
  have htrace : WordTrace (prefixWord ++ tailWord_1438042) baseStart_1438042 baseEnd_1438042 := by
    simpa [prefixWord, tailWord_1438042, baseEnd_1438042] using wordTrace_append hprefix tailTrace_1438042
  have hstable : (prefixWord ++ tailWord_1438042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438042).length < 2 ^ (prefixWord ++ tailWord_1438042).sum := by decide
  have hdescent : baseEnd_1438042 < baseStart_1438042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438060 : List Nat := [2, 2, 1, 1, 6, 2, 1, 2, 2, 2, 2]
def baseStart_1438060 : Nat := 118140960795 + 1438060 * 2 ^ 59
def prefixEnd_1438060 : Nat := 4983230072969 + 3 ^ 40 * 1438060 * 2
def baseEnd_1438060 : Nat := 738415990004748817336489

theorem tailTrace_1438060 : CollatzResearch.WordTrace tailWord_1438060 prefixEnd_1438060 738415990004748817336489 := by
  unfold tailWord_1438060
  simp only [CollatzResearch.WordTrace]
  refine ⟨26225178585080847969903817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34966904780107797293205089 26225178585080847969903817)
  ·
    refine ⟨19668883938810635977427863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26225178585080847969903817 19668883938810635977427863)
    ·
      refine ⟨29503325908215953966141795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19668883938810635977427863 29503325908215953966141795)
      ·
        refine ⟨44254988862323930949212693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29503325908215953966141795 44254988862323930949212693)
        ·
          refine ⟨2074452602921434263244345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44254988862323930949212693 2074452602921434263244345)
          ·
            refine ⟨1555839452191075697433259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2074452602921434263244345 1555839452191075697433259)
            ·
              refine ⟨2333759178286613546149889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1555839452191075697433259 2333759178286613546149889)
              ·
                refine ⟨1750319383714960159612417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2333759178286613546149889 1750319383714960159612417)
                ·
                  refine ⟨1312739537786220119709313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1750319383714960159612417 1312739537786220119709313)
                  ·
                    refine ⟨984554653339665089781985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1312739537786220119709313 984554653339665089781985)
                    ·
                      refine ⟨738415990004748817336489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 984554653339665089781985 738415990004748817336489)
                      ·
                        rfl

theorem cell23_1438060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 2, 2].length) (baseStart_1438060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438060 prefixEnd_1438060 := by exact prefixLift 1438060
  have htrace : WordTrace (prefixWord ++ tailWord_1438060) baseStart_1438060 baseEnd_1438060 := by
    simpa [prefixWord, tailWord_1438060, baseEnd_1438060] using wordTrace_append hprefix tailTrace_1438060
  have hstable : (prefixWord ++ tailWord_1438060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438060).length < 2 ^ (prefixWord ++ tailWord_1438060).sum := by decide
  have hdescent : baseEnd_1438060 < baseStart_1438060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438100 : List Nat := [2, 4, 2, 1, 4, 1, 1, 3, 5]
def baseStart_1438100 : Nat := 118140960795 + 1438100 * 2 ^ 59
def prefixEnd_1438100 : Nat := 4983230072969 + 3 ^ 40 * 1438100 * 2
def baseEnd_1438100 : Nat := 82048503247880962315145

theorem tailTrace_1438100 : CollatzResearch.WordTrace tailWord_1438100 prefixEnd_1438100 82048503247880962315145 := by
  unfold tailWord_1438100
  simp only [CollatzResearch.WordTrace]
  refine ⟨26225908045008391385631877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34967877393344521847509169 26225908045008391385631877)
  ·
    refine ⟨4917357758439073384805977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26225908045008391385631877 4917357758439073384805977)
    ·
      refine ⟨3688018318829305038604483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4917357758439073384805977 3688018318829305038604483)
      ·
        refine ⟨5532027478243957557906725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3688018318829305038604483 5532027478243957557906725)
        ·
          refine ⟨1037255152170742042107511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5532027478243957557906725 1037255152170742042107511)
          ·
            refine ⟨1555882728256113063161267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037255152170742042107511 1555882728256113063161267)
            ·
              refine ⟨2333824092384169594741901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1555882728256113063161267 2333824092384169594741901)
              ·
                refine ⟨875184034644063598028213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2333824092384169594741901 875184034644063598028213)
                ·
                  refine ⟨82048503247880962315145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 875184034644063598028213 82048503247880962315145)
                  ·
                    rfl

theorem cell23_1438100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_1438100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438100 prefixEnd_1438100 := by exact prefixLift 1438100
  have htrace : WordTrace (prefixWord ++ tailWord_1438100) baseStart_1438100 baseEnd_1438100 := by
    simpa [prefixWord, tailWord_1438100, baseEnd_1438100] using wordTrace_append hprefix tailTrace_1438100
  have hstable : (prefixWord ++ tailWord_1438100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438100).length < 2 ^ (prefixWord ++ tailWord_1438100).sum := by decide
  have hdescent : baseEnd_1438100 < baseStart_1438100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438176 : List Nat := [2, 1, 1, 3, 1, 1, 3, 4, 2, 3, 2]
def baseStart_1438176 : Nat := 118140960795 + 1438176 * 2 ^ 59
def prefixEnd_1438176 : Nat := 4983230072969 + 3 ^ 40 * 1438176 * 2
def baseEnd_1438176 : Nat := 738475553760670363485955

theorem tailTrace_1438176 : CollatzResearch.WordTrace tailWord_1438176 prefixEnd_1438176 738475553760670363485955 := by
  unfold tailWord_1438176
  simp only [CollatzResearch.WordTrace]
  refine ⟨26227294018870723875515191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34969725358494298500686921 26227294018870723875515191)
  ·
    refine ⟨39340941028306085813272787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26227294018870723875515191 39340941028306085813272787)
    ·
      refine ⟨59011411542459128719909181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39340941028306085813272787 59011411542459128719909181)
      ·
        refine ⟨22129279328422173269965943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59011411542459128719909181 22129279328422173269965943)
        ·
          refine ⟨33193918992633259904948915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22129279328422173269965943 33193918992633259904948915)
          ·
            refine ⟨49790878488949889857423373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33193918992633259904948915 49790878488949889857423373)
            ·
              refine ⟨18671579433356208696533765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49790878488949889857423373 18671579433356208696533765)
              ·
                refine ⟨3500921143754289130600081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18671579433356208696533765 3500921143754289130600081)
                ·
                  refine ⟨2625690857815716847950061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3500921143754289130600081 2625690857815716847950061)
                  ·
                    refine ⟨984634071680893817981273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2625690857815716847950061 984634071680893817981273)
                    ·
                      refine ⟨738475553760670363485955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 984634071680893817981273 738475553760670363485955)
                      ·
                        rfl

theorem cell23_1438176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_1438176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438176 prefixEnd_1438176 := by exact prefixLift 1438176
  have htrace : WordTrace (prefixWord ++ tailWord_1438176) baseStart_1438176 baseEnd_1438176 := by
    simpa [prefixWord, tailWord_1438176, baseEnd_1438176] using wordTrace_append hprefix tailTrace_1438176
  have hstable : (prefixWord ++ tailWord_1438176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438176).length < 2 ^ (prefixWord ++ tailWord_1438176).sum := by decide
  have hdescent : baseEnd_1438176 < baseStart_1438176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438210 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_1438210 : Nat := 118140960795 + 1438210 * 2 ^ 59
def prefixEnd_1438210 : Nat := 4983230072969 + 3 ^ 40 * 1438210 * 2
def baseEnd_1438210 : Nat := 738493012102923230460799

theorem tailTrace_1438210 : CollatzResearch.WordTrace tailWord_1438210 prefixEnd_1438210 738493012102923230460799 := by
  unfold tailWord_1438210
  simp only [CollatzResearch.WordTrace]
  refine ⟨13113957029904567889442021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34970552079745514371845389 13113957029904567889442021)
  ·
    refine ⟨2458866943107106479270379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13113957029904567889442021 2458866943107106479270379)
    ·
      refine ⟨3688300414660659718905569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2458866943107106479270379 3688300414660659718905569)
      ·
        refine ⟨2766225310995494789179177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3688300414660659718905569 2766225310995494789179177)
        ·
          refine ⟨2074668983246621091884383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2766225310995494789179177 2074668983246621091884383)
          ·
            refine ⟨3112003474869931637826575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2074668983246621091884383 3112003474869931637826575)
            ·
              refine ⟨4668005212304897456739863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3112003474869931637826575 4668005212304897456739863)
              ·
                refine ⟨7002007818457346185109795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4668005212304897456739863 7002007818457346185109795)
                ·
                  refine ⟨10503011727686019277664693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7002007818457346185109795 10503011727686019277664693)
                  ·
                    refine ⟨984657349470564307281065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10503011727686019277664693 984657349470564307281065)
                    ·
                      refine ⟨738493012102923230460799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 984657349470564307281065 738493012102923230460799)
                      ·
                        rfl

theorem cell23_1438210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_1438210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438210 prefixEnd_1438210 := by exact prefixLift 1438210
  have htrace : WordTrace (prefixWord ++ tailWord_1438210) baseStart_1438210 baseEnd_1438210 := by
    simpa [prefixWord, tailWord_1438210, baseEnd_1438210] using wordTrace_append hprefix tailTrace_1438210
  have hstable : (prefixWord ++ tailWord_1438210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438210).length < 2 ^ (prefixWord ++ tailWord_1438210).sum := by decide
  have hdescent : baseEnd_1438210 < baseStart_1438210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438250 : List Nat := [3, 1, 4, 1, 1, 3, 3, 1, 2, 4]
def baseStart_1438250 : Nat := 118140960795 + 1438250 * 2 ^ 59
def prefixEnd_1438250 : Nat := 4983230072969 + 3 ^ 40 * 1438250 * 2
def baseEnd_1438250 : Nat := 246171183776367691320205

theorem tailTrace_1438250 : CollatzResearch.WordTrace tailWord_1438250 prefixEnd_1438250 246171183776367691320205 := by
  unfold tailWord_1438250
  simp only [CollatzResearch.WordTrace]
  refine ⟨13114321759868339597306051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34971524692982238926149469 13114321759868339597306051)
  ·
    refine ⟨19671482639802509395959077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13114321759868339597306051 19671482639802509395959077)
    ·
      refine ⟨3688402994962970511742327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19671482639802509395959077 3688402994962970511742327)
      ·
        refine ⟨5532604492444455767613491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3688402994962970511742327 5532604492444455767613491)
        ·
          refine ⟨8298906738666683651420237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5532604492444455767613491 8298906738666683651420237)
          ·
            refine ⟨3112090027000006369282589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8298906738666683651420237 3112090027000006369282589)
            ·
              refine ⟨1167033760125002388480971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3112090027000006369282589 1167033760125002388480971)
              ·
                refine ⟨1750550640187503582721457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1167033760125002388480971 1750550640187503582721457)
                ·
                  refine ⟨1312912980140627687041093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1750550640187503582721457 1312912980140627687041093)
                  ·
                    refine ⟨246171183776367691320205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1312912980140627687041093 246171183776367691320205)
                    ·
                      rfl

theorem cell23_1438250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_1438250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438250 prefixEnd_1438250 := by exact prefixLift 1438250
  have htrace : WordTrace (prefixWord ++ tailWord_1438250) baseStart_1438250 baseEnd_1438250 := by
    simpa [prefixWord, tailWord_1438250, baseEnd_1438250] using wordTrace_append hprefix tailTrace_1438250
  have hstable : (prefixWord ++ tailWord_1438250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438250).length < 2 ^ (prefixWord ++ tailWord_1438250).sum := by decide
  have hdescent : baseEnd_1438250 < baseStart_1438250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438256 : List Nat := [2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 3]
def baseStart_1438256 : Nat := 118140960795 + 1438256 * 2 ^ 59
def prefixEnd_1438256 : Nat := 4983230072969 + 3 ^ 40 * 1438256 * 2
def baseEnd_1438256 : Nat := 738516632213030050485587

theorem tailTrace_1438256 : CollatzResearch.WordTrace tailWord_1438256 prefixEnd_1438256 738516632213030050485587 := by
  unfold tailWord_1438256
  simp only [CollatzResearch.WordTrace]
  refine ⟨26228752938725810706971311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34971670584967747609295081 26228752938725810706971311)
  ·
    refine ⟨39343129408088716060456967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26228752938725810706971311 39343129408088716060456967)
    ·
      refine ⟨59014694112133074090685451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39343129408088716060456967 59014694112133074090685451)
      ·
        refine ⟨88522041168199611136028177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59014694112133074090685451 88522041168199611136028177)
        ·
          refine ⟨66391530876149708352021133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88522041168199611136028177 66391530876149708352021133)
          ·
            refine ⟨24896824078556140632007925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66391530876149708352021133 24896824078556140632007925)
            ·
              refine ⟨2334077257364638184250743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24896824078556140632007925 2334077257364638184250743)
              ·
                refine ⟨3501115886046957276376115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2334077257364638184250743 3501115886046957276376115)
                ·
                  refine ⟨5251673829070435914564173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3501115886046957276376115 5251673829070435914564173)
                  ·
                    refine ⟨1969377685901413467961565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5251673829070435914564173 1969377685901413467961565)
                    ·
                      refine ⟨738516632213030050485587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1969377685901413467961565 738516632213030050485587)
                      ·
                        rfl

theorem cell23_1438256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 3].length) (baseStart_1438256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438256 prefixEnd_1438256 := by exact prefixLift 1438256
  have htrace : WordTrace (prefixWord ++ tailWord_1438256) baseStart_1438256 baseEnd_1438256 := by
    simpa [prefixWord, tailWord_1438256, baseEnd_1438256] using wordTrace_append hprefix tailTrace_1438256
  have hstable : (prefixWord ++ tailWord_1438256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438256).length < 2 ^ (prefixWord ++ tailWord_1438256).sum := by decide
  have hdescent : baseEnd_1438256 < baseStart_1438256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438273 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_1438273 : Nat := 118140960795 + 1438273 * 2 ^ 59
def prefixEnd_1438273 : Nat := 4983230072969 + 3 ^ 40 * 1438273 * 2
def baseEnd_1438273 : Nat := 738525361384156483973009

theorem tailTrace_1438273 : CollatzResearch.WordTrace tailWord_1438273 prefixEnd_1438273 738525361384156483973009 := by
  unfold tailWord_1438273
  simp only [CollatzResearch.WordTrace]
  refine ⟨52458125918390033317311473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34972083945593355544874315 52458125918390033317311473)
  ·
    refine ⟨39343594438792524987983605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52458125918390033317311473 39343594438792524987983605)
    ·
      refine ⟨3688461978636799217623463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39343594438792524987983605 3688461978636799217623463)
      ·
        refine ⟨5532692967955198826435195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3688461978636799217623463 5532692967955198826435195)
        ·
          refine ⟨8299039451932798239652793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5532692967955198826435195 8299039451932798239652793)
          ·
            refine ⟨6224279588949598679739595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8299039451932798239652793 6224279588949598679739595)
            ·
              refine ⟨9336419383424398019609393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6224279588949598679739595 9336419383424398019609393)
              ·
                refine ⟨7002314537568298514707045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9336419383424398019609393 7002314537568298514707045)
                ·
                  refine ⟨1312933975794055971507571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7002314537568298514707045 1312933975794055971507571)
                  ·
                    refine ⟨1969400963691083957261357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1312933975794055971507571 1969400963691083957261357)
                    ·
                      refine ⟨738525361384156483973009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1969400963691083957261357 738525361384156483973009)
                      ·
                        rfl

theorem cell23_1438273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_1438273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438273 prefixEnd_1438273 := by exact prefixLift 1438273
  have htrace : WordTrace (prefixWord ++ tailWord_1438273) baseStart_1438273 baseEnd_1438273 := by
    simpa [prefixWord, tailWord_1438273, baseEnd_1438273] using wordTrace_append hprefix tailTrace_1438273
  have hstable : (prefixWord ++ tailWord_1438273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438273).length < 2 ^ (prefixWord ++ tailWord_1438273).sum := by decide
  have hdescent : baseEnd_1438273 < baseStart_1438273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438283 : List Nat := [1, 1, 1, 1, 3, 1, 6, 3, 1, 3, 2]
def baseStart_1438283 : Nat := 118140960795 + 1438283 * 2 ^ 59
def prefixEnd_1438283 : Nat := 4983230072969 + 3 ^ 40 * 1438283 * 2
def baseEnd_1438283 : Nat := 738530496190701444847963

theorem tailTrace_1438283 : CollatzResearch.WordTrace tailWord_1438283 prefixEnd_1438283 738530496190701444847963 := by
  unfold tailWord_1438283
  simp only [CollatzResearch.WordTrace]
  refine ⟨52458490648353805025175503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34972327098902536683450335 52458490648353805025175503)
  ·
    refine ⟨78687735972530707537763255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52458490648353805025175503 78687735972530707537763255)
    ·
      refine ⟨118031603958796061306644883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78687735972530707537763255 118031603958796061306644883)
      ·
        refine ⟨177047405938194091959967325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118031603958796061306644883 177047405938194091959967325)
        ·
          refine ⟨66392777226822784484987747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177047405938194091959967325 66392777226822784484987747)
          ·
            refine ⟨99589165840234176727481621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66392777226822784484987747 99589165840234176727481621)
            ·
              refine ⟨4668242148760977034100701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99589165840234176727481621 4668242148760977034100701)
              ·
                refine ⟨1750590805785366387787763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4668242148760977034100701 1750590805785366387787763)
                ·
                  refine ⟨2625886208678049581681645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1750590805785366387787763 2625886208678049581681645)
                  ·
                    refine ⟨984707328254268593130617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2625886208678049581681645 984707328254268593130617)
                    ·
                      refine ⟨738530496190701444847963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 984707328254268593130617 738530496190701444847963)
                      ·
                        rfl

theorem cell23_1438283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 3, 2].length) (baseStart_1438283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438283 prefixEnd_1438283 := by exact prefixLift 1438283
  have htrace : WordTrace (prefixWord ++ tailWord_1438283) baseStart_1438283 baseEnd_1438283 := by
    simpa [prefixWord, tailWord_1438283, baseEnd_1438283] using wordTrace_append hprefix tailTrace_1438283
  have hstable : (prefixWord ++ tailWord_1438283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438283).length < 2 ^ (prefixWord ++ tailWord_1438283).sum := by decide
  have hdescent : baseEnd_1438283 < baseStart_1438283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438317 : List Nat := [1, 5, 1, 1, 3, 3, 1, 2, 1, 3, 2]
def baseStart_1438317 : Nat := 118140960795 + 1438317 * 2 ^ 59
def prefixEnd_1438317 : Nat := 4983230072969 + 3 ^ 40 * 1438317 * 2
def baseEnd_1438317 : Nat := 738547954532954311822807

theorem tailTrace_1438317 : CollatzResearch.WordTrace tailWord_1438317 prefixEnd_1438317 738547954532954311822807 := by
  unfold tailWord_1438317
  simp only [CollatzResearch.WordTrace]
  refine ⟨52459730730230628831913205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34973153820153752554608803 52459730730230628831913205)
  ·
    refine ⟨4918099755959121452991863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52459730730230628831913205 4918099755959121452991863)
    ·
      refine ⟨7377149633938682179487795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4918099755959121452991863 7377149633938682179487795)
      ·
        refine ⟨11065724450908023269231693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7377149633938682179487795 11065724450908023269231693)
        ·
          refine ⟨4149646669090508725961885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11065724450908023269231693 4149646669090508725961885)
          ·
            refine ⟨1556117500908940772235707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4149646669090508725961885 1556117500908940772235707)
            ·
              refine ⟨2334176251363411158353561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1556117500908940772235707 2334176251363411158353561)
              ·
                refine ⟨1750632188522558368765171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2334176251363411158353561 1750632188522558368765171)
                ·
                  refine ⟨2625948282783837553147757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1750632188522558368765171 2625948282783837553147757)
                  ·
                    refine ⟨984730606043939082430409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2625948282783837553147757 984730606043939082430409)
                    ·
                      refine ⟨738547954532954311822807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 984730606043939082430409 738547954532954311822807)
                      ·
                        rfl

theorem cell23_1438317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_1438317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438317 prefixEnd_1438317 := by exact prefixLift 1438317
  have htrace : WordTrace (prefixWord ++ tailWord_1438317) baseStart_1438317 baseEnd_1438317 := by
    simpa [prefixWord, tailWord_1438317, baseEnd_1438317] using wordTrace_append hprefix tailTrace_1438317
  have hstable : (prefixWord ++ tailWord_1438317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438317).length < 2 ^ (prefixWord ++ tailWord_1438317).sum := by decide
  have hdescent : baseEnd_1438317 < baseStart_1438317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438319 : List Nat := [1, 1, 2, 1, 3, 2, 2, 4, 7]
def baseStart_1438319 : Nat := 118140960795 + 1438319 * 2 ^ 59
def prefixEnd_1438319 : Nat := 4983230072969 + 3 ^ 40 * 1438319 * 2
def baseEnd_1438319 : Nat := 82060997943807033777533

theorem tailTrace_1438319 : CollatzResearch.WordTrace tailWord_1438319 prefixEnd_1438319 82060997943807033777533 := by
  unfold tailWord_1438319
  simp only [CollatzResearch.WordTrace]
  refine ⟨52459803676223383173486011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34973202450815588782324007 52459803676223383173486011)
  ·
    refine ⟨78689705514335074760229017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52459803676223383173486011 78689705514335074760229017)
    ·
      refine ⟨59017279135751306070171763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78689705514335074760229017 59017279135751306070171763)
      ·
        refine ⟨88525918703626959105257645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59017279135751306070171763 88525918703626959105257645)
        ·
          refine ⟨33197219513860109664471617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88525918703626959105257645 33197219513860109664471617)
          ·
            refine ⟨24897914635395082248353713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33197219513860109664471617 24897914635395082248353713)
            ·
              refine ⟨18673435976546311686265285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24897914635395082248353713 18673435976546311686265285)
              ·
                refine ⟨3501269245602433441174741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18673435976546311686265285 3501269245602433441174741)
                ·
                  refine ⟨82060997943807033777533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3501269245602433441174741 82060997943807033777533)
                  ·
                    rfl

theorem cell23_1438319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 7].length) (baseStart_1438319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438319 prefixEnd_1438319 := by exact prefixLift 1438319
  have htrace : WordTrace (prefixWord ++ tailWord_1438319) baseStart_1438319 baseEnd_1438319 := by
    simpa [prefixWord, tailWord_1438319, baseEnd_1438319] using wordTrace_append hprefix tailTrace_1438319
  have hstable : (prefixWord ++ tailWord_1438319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438319).length < 2 ^ (prefixWord ++ tailWord_1438319).sum := by decide
  have hdescent : baseEnd_1438319 < baseStart_1438319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438383 : List Nat := [1, 1, 2, 1, 2, 7, 1, 1, 2, 5]
def baseStart_1438383 : Nat := 118140960795 + 1438383 * 2 ^ 59
def prefixEnd_1438383 : Nat := 4983230072969 + 3 ^ 40 * 1438383 * 2
def baseEnd_1438383 : Nat := 246193948085383684532501

theorem tailTrace_1438383 : CollatzResearch.WordTrace tailWord_1438383 prefixEnd_1438383 246193948085383684532501 := by
  unfold tailWord_1438383
  simp only [CollatzResearch.WordTrace]
  refine ⟨52462137947991522103815803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34974758631994348069210535 52462137947991522103815803)
  ·
    refine ⟨78693206921987283155723705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52462137947991522103815803 78693206921987283155723705)
    ·
      refine ⟨59019905191490462366792779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78693206921987283155723705 59019905191490462366792779)
      ·
        refine ⟨88529857787235693550189169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59019905191490462366792779 88529857787235693550189169)
        ·
          refine ⟨66397393340426770162641877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88529857787235693550189169 66397393340426770162641877)
          ·
            refine ⟨1556188906416252425686919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 66397393340426770162641877 1556188906416252425686919)
            ·
              refine ⟨2334283359624378638530379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1556188906416252425686919 2334283359624378638530379)
              ·
                refine ⟨3501425039436567957795569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2334283359624378638530379 3501425039436567957795569)
                ·
                  refine ⟨2626068779577425968346677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3501425039436567957795569 2626068779577425968346677)
                  ·
                    refine ⟨246193948085383684532501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2626068779577425968346677 246193948085383684532501)
                    ·
                      rfl

theorem cell23_1438383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 5].length) (baseStart_1438383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438383 prefixEnd_1438383 := by exact prefixLift 1438383
  have htrace : WordTrace (prefixWord ++ tailWord_1438383) baseStart_1438383 baseEnd_1438383 := by
    simpa [prefixWord, tailWord_1438383, baseEnd_1438383] using wordTrace_append hprefix tailTrace_1438383
  have hstable : (prefixWord ++ tailWord_1438383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438383).length < 2 ^ (prefixWord ++ tailWord_1438383).sum := by decide
  have hdescent : baseEnd_1438383 < baseStart_1438383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438447 : List Nat := [1, 1, 2, 1, 5, 4, 1, 3, 1, 4]
def baseStart_1438447 : Nat := 118140960795 + 1438447 * 2 ^ 59
def prefixEnd_1438447 : Nat := 4983230072969 + 3 ^ 40 * 1438447 * 2
def baseEnd_1438447 : Nat := 246204902339346267732403

theorem tailTrace_1438447 : CollatzResearch.WordTrace tailWord_1438447 prefixEnd_1438447 246204902339346267732403 := by
  unfold tailWord_1438447
  simp only [CollatzResearch.WordTrace]
  refine ⟨52464472219759661034145595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34976314813173107356097063 52464472219759661034145595)
  ·
    refine ⟨78696708329639491551218393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52464472219759661034145595 78696708329639491551218393)
    ·
      refine ⟨59022531247229618663413795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78696708329639491551218393 59022531247229618663413795)
      ·
        refine ⟨88533796870844427995120693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59022531247229618663413795 88533796870844427995120693)
        ·
          refine ⟨8300043456641665124542565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88533796870844427995120693 8300043456641665124542565)
          ·
            refine ⟨1556258148120312210851731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8300043456641665124542565 1556258148120312210851731)
            ·
              refine ⟨2334387222180468316277597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1556258148120312210851731 2334387222180468316277597)
              ·
                refine ⟨875395208317675618604099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2334387222180468316277597 875395208317675618604099)
                ·
                  refine ⟨1313092812476513427906149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875395208317675618604099 1313092812476513427906149)
                  ·
                    refine ⟨246204902339346267732403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1313092812476513427906149 246204902339346267732403)
                    ·
                      rfl

theorem cell23_1438447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 1, 4].length) (baseStart_1438447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438447 prefixEnd_1438447 := by exact prefixLift 1438447
  have htrace : WordTrace (prefixWord ++ tailWord_1438447) baseStart_1438447 baseEnd_1438447 := by
    simpa [prefixWord, tailWord_1438447, baseEnd_1438447] using wordTrace_append hprefix tailTrace_1438447
  have hstable : (prefixWord ++ tailWord_1438447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438447).length < 2 ^ (prefixWord ++ tailWord_1438447).sum := by decide
  have hdescent : baseEnd_1438447 < baseStart_1438447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438476 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 2, 5, 4]
def baseStart_1438476 : Nat := 118140960795 + 1438476 * 2 ^ 59
def prefixEnd_1438476 : Nat := 4983230072969 + 3 ^ 40 * 1438476 * 2
def baseEnd_1438476 : Nat := 738629597957019189734575

theorem tailTrace_1438476 : CollatzResearch.WordTrace tailWord_1438476 prefixEnd_1438476 738629597957019189734575 := by
  unfold tailWord_1438476
  simp only [CollatzResearch.WordTrace]
  refine ⟨26232764968327299493475641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34977019957769732657967521 26232764968327299493475641)
  ·
    refine ⟨19674573726245474620106731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26232764968327299493475641 19674573726245474620106731)
    ·
      refine ⟨29511860589368211930160097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19674573726245474620106731 29511860589368211930160097)
      ·
        refine ⟨22133895442026158947620073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29511860589368211930160097 22133895442026158947620073)
        ·
          refine ⟨16600421581519619210715055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22133895442026158947620073 16600421581519619210715055)
          ·
            refine ⟨24900632372279428816072583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16600421581519619210715055 24900632372279428816072583)
            ·
              refine ⟨37350948558419143224108875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24900632372279428816072583 37350948558419143224108875)
              ·
                refine ⟨56026422837628714836163313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37350948558419143224108875 56026422837628714836163313)
                ·
                  refine ⟨42019817128221536127122485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56026422837628714836163313 42019817128221536127122485)
                  ·
                    refine ⟨3939357855770769011917733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42019817128221536127122485 3939357855770769011917733)
                    ·
                      refine ⟨738629597957019189734575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3939357855770769011917733 738629597957019189734575)
                      ·
                        rfl

theorem cell23_1438476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_1438476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438476 prefixEnd_1438476 := by exact prefixLift 1438476
  have htrace : WordTrace (prefixWord ++ tailWord_1438476) baseStart_1438476 baseEnd_1438476 := by
    simpa [prefixWord, tailWord_1438476, baseEnd_1438476] using wordTrace_append hprefix tailTrace_1438476
  have hstable : (prefixWord ++ tailWord_1438476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438476).length < 2 ^ (prefixWord ++ tailWord_1438476).sum := by decide
  have hdescent : baseEnd_1438476 < baseStart_1438476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438520 : List Nat := [2, 1, 2, 1, 3, 2, 4, 2, 2, 4]
def baseStart_1438520 : Nat := 118140960795 + 1438520 * 2 ^ 59
def prefixEnd_1438520 : Nat := 4983230072969 + 3 ^ 40 * 1438520 * 2
def baseEnd_1438520 : Nat := 246217397035272339194791

theorem tailTrace_1438520 : CollatzResearch.WordTrace tailWord_1438520 prefixEnd_1438520 246217397035272339194791 := by
  unfold tailWord_1438520
  simp only [CollatzResearch.WordTrace]
  refine ⟨26233567374247597250776507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34978089832330129667702009 26233567374247597250776507)
  ·
    refine ⟨39350351061371395876164761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26233567374247597250776507 39350351061371395876164761)
    ·
      refine ⟨29512763296028546907123571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39350351061371395876164761 29512763296028546907123571)
      ·
        refine ⟨44269144944042820360685357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29512763296028546907123571 44269144944042820360685357)
        ·
          refine ⟨16600929354016057635257009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44269144944042820360685357 16600929354016057635257009)
          ·
            refine ⟨12450697015512043226442757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16600929354016057635257009 12450697015512043226442757)
            ·
              refine ⟨2334505690408508104958017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12450697015512043226442757 2334505690408508104958017)
              ·
                refine ⟨1750879267806381078718513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2334505690408508104958017 1750879267806381078718513)
                ·
                  refine ⟨1313159450854785809038885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1750879267806381078718513 1313159450854785809038885)
                  ·
                    refine ⟨246217397035272339194791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1313159450854785809038885 246217397035272339194791)
                    ·
                      rfl

theorem cell23_1438520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 2, 4].length) (baseStart_1438520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438520 prefixEnd_1438520 := by exact prefixLift 1438520
  have htrace : WordTrace (prefixWord ++ tailWord_1438520) baseStart_1438520 baseEnd_1438520 := by
    simpa [prefixWord, tailWord_1438520, baseEnd_1438520] using wordTrace_append hprefix tailTrace_1438520
  have hstable : (prefixWord ++ tailWord_1438520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438520).length < 2 ^ (prefixWord ++ tailWord_1438520).sum := by decide
  have hdescent : baseEnd_1438520 < baseStart_1438520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438540 : List Nat := [2, 2, 1, 3, 3, 2, 2, 1, 1, 2, 4]
def baseStart_1438540 : Nat := 118140960795 + 1438540 * 2 ^ 59
def prefixEnd_1438540 : Nat := 4983230072969 + 3 ^ 40 * 1438540 * 2
def baseEnd_1438540 : Nat := 738662460718906939334281

theorem tailTrace_1438540 : CollatzResearch.WordTrace tailWord_1438540 prefixEnd_1438540 738662460718906939334281 := by
  unfold tailWord_1438540
  simp only [CollatzResearch.WordTrace]
  refine ⟨26233932104211368958640537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34978576138948491944854049 26233932104211368958640537)
  ·
    refine ⟨19675449078158526718980403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26233932104211368958640537 19675449078158526718980403)
    ·
      refine ⟨29513173617237790078470605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19675449078158526718980403 29513173617237790078470605)
      ·
        refine ⟨11067440106464171279426477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29513173617237790078470605 11067440106464171279426477)
        ·
          refine ⟨4150290039924064229784929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11067440106464171279426477 4150290039924064229784929)
          ·
            refine ⟨3112717529943048172338697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4150290039924064229784929 3112717529943048172338697)
            ·
              refine ⟨2334538147457286129254023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3112717529943048172338697 2334538147457286129254023)
              ·
                refine ⟨3501807221185929193881035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2334538147457286129254023 3501807221185929193881035)
                ·
                  refine ⟨5252710831778893790821553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3501807221185929193881035 5252710831778893790821553)
                  ·
                    refine ⟨3939533123834170343116165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5252710831778893790821553 3939533123834170343116165)
                    ·
                      refine ⟨738662460718906939334281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3939533123834170343116165 738662460718906939334281)
                      ·
                        rfl

theorem cell23_1438540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_1438540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438540 prefixEnd_1438540 := by exact prefixLift 1438540
  have htrace : WordTrace (prefixWord ++ tailWord_1438540) baseStart_1438540 baseEnd_1438540 := by
    simpa [prefixWord, tailWord_1438540, baseEnd_1438540] using wordTrace_append hprefix tailTrace_1438540
  have hstable : (prefixWord ++ tailWord_1438540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438540).length < 2 ^ (prefixWord ++ tailWord_1438540).sum := by decide
  have hdescent : baseEnd_1438540 < baseStart_1438540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438560 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 4, 1, 3]
def baseStart_1438560 : Nat := 118140960795 + 1438560 * 2 ^ 59
def prefixEnd_1438560 : Nat := 4983230072969 + 3 ^ 40 * 1438560 * 2
def baseEnd_1438560 : Nat := 738672730331996861084189

theorem tailTrace_1438560 : CollatzResearch.WordTrace tailWord_1438560 prefixEnd_1438560 738672730331996861084189 := by
  unfold tailWord_1438560
  simp only [CollatzResearch.WordTrace]
  refine ⟨26234296834175140666504567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34979062445566854222006089 26234296834175140666504567)
  ·
    refine ⟨39351445251262710999756851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26234296834175140666504567 39351445251262710999756851)
    ·
      refine ⟨59027167876894066499635277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39351445251262710999756851 59027167876894066499635277)
      ·
        refine ⟨22135187953835274937363229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59027167876894066499635277 22135187953835274937363229)
        ·
          refine ⟨8300695482688228101511211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22135187953835274937363229 8300695482688228101511211)
          ·
            refine ⟨12451043224032342152266817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8300695482688228101511211 12451043224032342152266817)
            ·
              refine ⟨9338282418024256614200113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12451043224032342152266817 9338282418024256614200113)
              ·
                refine ⟨7003711813518192460650085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9338282418024256614200113 7003711813518192460650085)
                ·
                  refine ⟨1313195965034661086371891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7003711813518192460650085 1313195965034661086371891)
                  ·
                    refine ⟨1969793947551991629557837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1313195965034661086371891 1969793947551991629557837)
                    ·
                      refine ⟨738672730331996861084189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1969793947551991629557837 738672730331996861084189)
                      ·
                        rfl

theorem cell23_1438560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_1438560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438560 prefixEnd_1438560 := by exact prefixLift 1438560
  have htrace : WordTrace (prefixWord ++ tailWord_1438560) baseStart_1438560 baseEnd_1438560 := by
    simpa [prefixWord, tailWord_1438560, baseEnd_1438560] using wordTrace_append hprefix tailTrace_1438560
  have hstable : (prefixWord ++ tailWord_1438560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438560).length < 2 ^ (prefixWord ++ tailWord_1438560).sum := by decide
  have hdescent : baseEnd_1438560 < baseStart_1438560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438564 : List Nat := [2, 3, 1, 1, 4, 3, 2, 1, 1, 2, 3]
def baseStart_1438564 : Nat := 118140960795 + 1438564 * 2 ^ 59
def prefixEnd_1438564 : Nat := 4983230072969 + 3 ^ 40 * 1438564 * 2
def baseEnd_1438564 : Nat := 738674784254614845434171

theorem tailTrace_1438564 : CollatzResearch.WordTrace tailWord_1438564 prefixEnd_1438564 738674784254614845434171 := by
  unfold tailWord_1438564
  simp only [CollatzResearch.WordTrace]
  refine ⟨26234369780167895008077373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34979159706890526677436497 26234369780167895008077373)
  ·
    refine ⟨9837888667562960628029015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26234369780167895008077373 9837888667562960628029015)
    ·
      refine ⟨14756833001344440942043523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9837888667562960628029015 14756833001344440942043523)
      ·
        refine ⟨22135249502016661413065285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14756833001344440942043523 22135249502016661413065285)
        ·
          refine ⟨4150359281628124014949741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22135249502016661413065285 4150359281628124014949741)
          ·
            refine ⟨1556384730610546505606153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4150359281628124014949741 1556384730610546505606153)
            ·
              refine ⟨1167288547957909879204615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1556384730610546505606153 1167288547957909879204615)
              ·
                refine ⟨1750932821936864818806923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1167288547957909879204615 1750932821936864818806923)
                ·
                  refine ⟨2626399232905297228210385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1750932821936864818806923 2626399232905297228210385)
                  ·
                    refine ⟨1969799424678972921157789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2626399232905297228210385 1969799424678972921157789)
                    ·
                      refine ⟨738674784254614845434171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1969799424678972921157789 738674784254614845434171)
                      ·
                        rfl

theorem cell23_1438564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_1438564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438564 prefixEnd_1438564 := by exact prefixLift 1438564
  have htrace : WordTrace (prefixWord ++ tailWord_1438564) baseStart_1438564 baseEnd_1438564 := by
    simpa [prefixWord, tailWord_1438564, baseEnd_1438564] using wordTrace_append hprefix tailTrace_1438564
  have hstable : (prefixWord ++ tailWord_1438564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438564).length < 2 ^ (prefixWord ++ tailWord_1438564).sum := by decide
  have hdescent : baseEnd_1438564 < baseStart_1438564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438577 : List Nat := [1, 2, 2, 2, 1, 4, 3, 2, 2, 1, 3]
def baseStart_1438577 : Nat := 118140960795 + 1438577 * 2 ^ 59
def prefixEnd_1438577 : Nat := 4983230072969 + 3 ^ 40 * 1438577 * 2
def baseEnd_1438577 : Nat := 738681459503123294571611

theorem tailTrace_1438577 : CollatzResearch.WordTrace tailWord_1438577 prefixEnd_1438577 738681459503123294571611 := by
  unfold tailWord_1438577
  simp only [CollatzResearch.WordTrace]
  refine ⟨52469213709288693236377985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34979475806192462157585323 52469213709288693236377985)
  ·
    refine ⟨39351910281966519927283489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52469213709288693236377985 39351910281966519927283489)
    ·
      refine ⟨29513932711474889945462617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39351910281966519927283489 29513932711474889945462617)
      ·
        refine ⟨22135449533606167459096963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29513932711474889945462617 22135449533606167459096963)
        ·
          refine ⟨33203174300409251188645445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22135449533606167459096963 33203174300409251188645445)
          ·
            refine ⟨6225595181326734597871021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33203174300409251188645445 6225595181326734597871021)
            ·
              refine ⟨2334598192997525474201633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6225595181326734597871021 2334598192997525474201633)
              ·
                refine ⟨1750948644748144105651225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2334598192997525474201633 1750948644748144105651225)
                ·
                  refine ⟨1313211483561108079238419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1750948644748144105651225 1313211483561108079238419)
                  ·
                    refine ⟨1969817225341662118857629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1313211483561108079238419 1969817225341662118857629)
                    ·
                      refine ⟨738681459503123294571611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1969817225341662118857629 738681459503123294571611)
                      ·
                        rfl

theorem cell23_1438577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_1438577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438577 prefixEnd_1438577 := by exact prefixLift 1438577
  have htrace : WordTrace (prefixWord ++ tailWord_1438577) baseStart_1438577 baseEnd_1438577 := by
    simpa [prefixWord, tailWord_1438577, baseEnd_1438577] using wordTrace_append hprefix tailTrace_1438577
  have hstable : (prefixWord ++ tailWord_1438577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438577).length < 2 ^ (prefixWord ++ tailWord_1438577).sum := by decide
  have hdescent : baseEnd_1438577 < baseStart_1438577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438603 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 3]
def baseStart_1438603 : Nat := 118140960795 + 1438603 * 2 ^ 59
def prefixEnd_1438603 : Nat := 4983230072969 + 3 ^ 40 * 1438603 * 2
def baseEnd_1438603 : Nat := 738694810000140192846491

theorem tailTrace_1438603 : CollatzResearch.WordTrace tailWord_1438603 prefixEnd_1438603 738694810000140192846491 := by
  unfold tailWord_1438603
  simp only [CollatzResearch.WordTrace]
  refine ⟨52470162007194499676824463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34980108004796333117882975 52470162007194499676824463)
  ·
    refine ⟨78705243010791749515236695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52470162007194499676824463 78705243010791749515236695)
    ·
      refine ⟨118057864516187624272855043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78705243010791749515236695 118057864516187624272855043)
      ·
        refine ⟨177086796774281436409282565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118057864516187624272855043 177086796774281436409282565)
        ·
          refine ⟨33203774395177769326740481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177086796774281436409282565 33203774395177769326740481)
          ·
            refine ⟨24902830796383326995055361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33203774395177769326740481 24902830796383326995055361)
            ·
              refine ⟨18677123097287495246291521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24902830796383326995055361 18677123097287495246291521)
              ·
                refine ⟨14007842322965621434718641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18677123097287495246291521 14007842322965621434718641)
                ·
                  refine ⟨10505881742224216076038981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14007842322965621434718641 10505881742224216076038981)
                  ·
                    refine ⟨1969852826667040514257309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10505881742224216076038981 1969852826667040514257309)
                    ·
                      refine ⟨738694810000140192846491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1969852826667040514257309 738694810000140192846491)
                      ·
                        rfl

theorem cell23_1438603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 3].length) (baseStart_1438603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438603 prefixEnd_1438603 := by exact prefixLift 1438603
  have htrace : WordTrace (prefixWord ++ tailWord_1438603) baseStart_1438603 baseEnd_1438603 := by
    simpa [prefixWord, tailWord_1438603, baseEnd_1438603] using wordTrace_append hprefix tailTrace_1438603
  have hstable : (prefixWord ++ tailWord_1438603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438603).length < 2 ^ (prefixWord ++ tailWord_1438603).sum := by decide
  have hdescent : baseEnd_1438603 < baseStart_1438603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438670 : List Nat := [4, 1, 1, 1, 2, 3, 1, 3, 2, 5]
def baseStart_1438670 : Nat := 118140960795 + 1438670 * 2 ^ 59
def prefixEnd_1438670 : Nat := 4983230072969 + 3 ^ 40 * 1438670 * 2
def baseEnd_1438670 : Nat := 246243071067997143569561

theorem tailTrace_1438670 : CollatzResearch.WordTrace tailWord_1438670 prefixEnd_1438670 246243071067997143569561 := by
  unfold tailWord_1438670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6559075712243971264939183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34981737131967846746342309 6559075712243971264939183)
  ·
    refine ⟨9838613568365956897408775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6559075712243971264939183 9838613568365956897408775)
    ·
      refine ⟨14757920352548935346113163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9838613568365956897408775 14757920352548935346113163)
      ·
        refine ⟨22136880528823403019169745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14757920352548935346113163 22136880528823403019169745)
        ·
          refine ⟨16602660396617552264377309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22136880528823403019169745 16602660396617552264377309)
          ·
            refine ⟨6225997648731582099141491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16602660396617552264377309 6225997648731582099141491)
            ·
              refine ⟨9338996473097373148712237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6225997648731582099141491 9338996473097373148712237)
              ·
                refine ⟨3502123677411514930767089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9338996473097373148712237 3502123677411514930767089)
                ·
                  refine ⟨2626592758058636198075317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3502123677411514930767089 2626592758058636198075317)
                  ·
                    refine ⟨246243071067997143569561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2626592758058636198075317 246243071067997143569561)
                    ·
                      rfl

theorem cell23_1438670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_1438670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438670 prefixEnd_1438670 := by exact prefixLift 1438670
  have htrace : WordTrace (prefixWord ++ tailWord_1438670) baseStart_1438670 baseEnd_1438670 := by
    simpa [prefixWord, tailWord_1438670, baseEnd_1438670] using wordTrace_append hprefix tailTrace_1438670
  have hstable : (prefixWord ++ tailWord_1438670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438670).length < 2 ^ (prefixWord ++ tailWord_1438670).sum := by decide
  have hdescent : baseEnd_1438670 < baseStart_1438670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438734 : List Nat := [4, 1, 1, 2, 2, 2, 1, 5, 1, 4]
def baseStart_1438734 : Nat := 118140960795 + 1438734 * 2 ^ 59
def prefixEnd_1438734 : Nat := 4983230072969 + 3 ^ 40 * 1438734 * 2
def baseEnd_1438734 : Nat := 246254025321959726769463

theorem tailTrace_1438734 : CollatzResearch.WordTrace tailWord_1438734 prefixEnd_1438734 246254025321959726769463 := by
  unfold tailWord_1438734
  simp only [CollatzResearch.WordTrace]
  refine ⟨6559367496214988631230407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34983293313146606033228837 6559367496214988631230407)
  ·
    refine ⟨9839051244322482946845611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6559367496214988631230407 9839051244322482946845611)
    ·
      refine ⟨14758576866483724420268417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9839051244322482946845611 14758576866483724420268417)
      ·
        refine ⟨11068932649862793315201313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14758576866483724420268417 11068932649862793315201313)
        ·
          refine ⟨8301699487397094986400985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11068932649862793315201313 8301699487397094986400985)
          ·
            refine ⟨6226274615547821239800739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8301699487397094986400985 6226274615547821239800739)
            ·
              refine ⟨9339411923321731859701109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6226274615547821239800739 9339411923321731859701109)
              ·
                refine ⟨875569867811412361846979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9339411923321731859701109 875569867811412361846979)
                ·
                  refine ⟨1313354801717118542770469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875569867811412361846979 1313354801717118542770469)
                  ·
                    refine ⟨246254025321959726769463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1313354801717118542770469 246254025321959726769463)
                    ·
                      rfl

theorem cell23_1438734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_1438734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438734 prefixEnd_1438734 := by exact prefixLift 1438734
  have htrace : WordTrace (prefixWord ++ tailWord_1438734) baseStart_1438734 baseEnd_1438734 := by
    simpa [prefixWord, tailWord_1438734, baseEnd_1438734] using wordTrace_append hprefix tailTrace_1438734
  have hstable : (prefixWord ++ tailWord_1438734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438734).length < 2 ^ (prefixWord ++ tailWord_1438734).sum := by decide
  have hdescent : baseEnd_1438734 < baseStart_1438734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438777 : List Nat := [1, 2, 1, 5, 2, 1, 1, 4, 1, 5]
def baseStart_1438777 : Nat := 118140960795 + 1438777 * 2 ^ 59
def prefixEnd_1438777 : Nat := 4983230072969 + 3 ^ 40 * 1438777 * 2
def baseEnd_1438777 : Nat := 246261385211340837356897

theorem tailTrace_1438777 : CollatzResearch.WordTrace tailWord_1438777 prefixEnd_1438777 246261385211340837356897 := by
  unfold tailWord_1438777
  simp only [CollatzResearch.WordTrace]
  refine ⟨52476508308564127393658585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34984338872376084929105723 52476508308564127393658585)
  ·
    refine ⟨39357381231423095545243939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52476508308564127393658585 39357381231423095545243939)
    ·
      refine ⟨59036071847134643317865909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39357381231423095545243939 59036071847134643317865909)
      ·
        refine ⟨5534631735668872811049929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59036071847134643317865909 5534631735668872811049929)
        ·
          refine ⟨4150973801751654608287447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5534631735668872811049929 4150973801751654608287447)
          ·
            refine ⟨6226460702627481912431171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4150973801751654608287447 6226460702627481912431171)
            ·
              refine ⟨9339691053941222868646757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6226460702627481912431171 9339691053941222868646757)
              ·
                refine ⟨1751192072613979287871267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9339691053941222868646757 1751192072613979287871267)
                ·
                  refine ⟨2626788108920968931806901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751192072613979287871267 2626788108920968931806901)
                  ·
                    refine ⟨246261385211340837356897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2626788108920968931806901 246261385211340837356897)
                    ·
                      rfl

theorem cell23_1438777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 5].length) (baseStart_1438777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438777 prefixEnd_1438777 := by exact prefixLift 1438777
  have htrace : WordTrace (prefixWord ++ tailWord_1438777) baseStart_1438777 baseEnd_1438777 := by
    simpa [prefixWord, tailWord_1438777, baseEnd_1438777] using wordTrace_append hprefix tailTrace_1438777
  have hstable : (prefixWord ++ tailWord_1438777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438777).length < 2 ^ (prefixWord ++ tailWord_1438777).sum := by decide
  have hdescent : baseEnd_1438777 < baseStart_1438777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438791 : List Nat := [1, 1, 4, 1, 3, 2, 3, 3, 1, 1, 3]
def baseStart_1438791 : Nat := 118140960795 + 1438791 * 2 ^ 59
def prefixEnd_1438791 : Nat := 4983230072969 + 3 ^ 40 * 1438791 * 2
def baseEnd_1438791 : Nat := 738791344363185457295627

theorem tailTrace_1438791 : CollatzResearch.WordTrace tailWord_1438791 prefixEnd_1438791 738791344363185457295627 := by
  unfold tailWord_1438791
  simp only [CollatzResearch.WordTrace]
  refine ⟨52477018930513407784668227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34984679287008938523112151 52477018930513407784668227)
  ·
    refine ⟨78715528395770111677002341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52477018930513407784668227 78715528395770111677002341)
    ·
      refine ⟨14759161574206895939437939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78715528395770111677002341 14759161574206895939437939)
      ·
        refine ⟨22138742361310343909156909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14759161574206895939437939 22138742361310343909156909)
        ·
          refine ⟨8302028385491378965933841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22138742361310343909156909 8302028385491378965933841)
          ·
            refine ⟨6226521289118534224450381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8302028385491378965933841 6226521289118534224450381)
            ·
              refine ⟨2334945483419450334168893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6226521289118534224450381 2334945483419450334168893)
              ·
                refine ⟨875604556282293875313335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2334945483419450334168893 875604556282293875313335)
                ·
                  refine ⟨1313406834423440812970003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875604556282293875313335 1313406834423440812970003)
                  ·
                    refine ⟨1970110251635161219455005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1313406834423440812970003 1970110251635161219455005)
                    ·
                      refine ⟨738791344363185457295627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1970110251635161219455005 738791344363185457295627)
                      ·
                        rfl

theorem cell23_1438791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 1, 1, 3].length) (baseStart_1438791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438791 prefixEnd_1438791 := by exact prefixLift 1438791
  have htrace : WordTrace (prefixWord ++ tailWord_1438791) baseStart_1438791 baseEnd_1438791 := by
    simpa [prefixWord, tailWord_1438791, baseEnd_1438791] using wordTrace_append hprefix tailTrace_1438791
  have hstable : (prefixWord ++ tailWord_1438791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438791).length < 2 ^ (prefixWord ++ tailWord_1438791).sum := by decide
  have hdescent : baseEnd_1438791 < baseStart_1438791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438807 : List Nat := [1, 1, 3, 2, 2, 1, 1, 6, 2, 4]
def baseStart_1438807 : Nat := 118140960795 + 1438807 * 2 ^ 59
def prefixEnd_1438807 : Nat := 4983230072969 + 3 ^ 40 * 1438807 * 2
def baseEnd_1438807 : Nat := 246266520017885798231851

theorem tailTrace_1438807 : CollatzResearch.WordTrace tailWord_1438807 prefixEnd_1438807 246266520017885798231851 := by
  unfold tailWord_1438807
  simp only [CollatzResearch.WordTrace]
  refine ⟨52477602498455442517250675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34985068332303628344833783 52477602498455442517250675)
  ·
    refine ⟨78716403747683163775876013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52477602498455442517250675 78716403747683163775876013)
    ·
      refine ⟨29518651405381186415953505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78716403747683163775876013 29518651405381186415953505)
      ·
        refine ⟨22138988554035889811965129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29518651405381186415953505 22138988554035889811965129)
        ·
          refine ⟨16604241415526917358973847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22138988554035889811965129 16604241415526917358973847)
          ·
            refine ⟨24906362123290376038460771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16604241415526917358973847 24906362123290376038460771)
            ·
              refine ⟨37359543184935564057691157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24906362123290376038460771 37359543184935564057691157)
              ·
                refine ⟨1751228586793854565204273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37359543184935564057691157 1751228586793854565204273)
                ·
                  refine ⟨1313421440095390923903205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1751228586793854565204273 1313421440095390923903205)
                  ·
                    refine ⟨246266520017885798231851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1313421440095390923903205 246266520017885798231851)
                    ·
                      rfl

theorem cell23_1438807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_1438807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438807 prefixEnd_1438807 := by exact prefixLift 1438807
  have htrace : WordTrace (prefixWord ++ tailWord_1438807) baseStart_1438807 baseEnd_1438807 := by
    simpa [prefixWord, tailWord_1438807, baseEnd_1438807] using wordTrace_append hprefix tailTrace_1438807
  have hstable : (prefixWord ++ tailWord_1438807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438807).length < 2 ^ (prefixWord ++ tailWord_1438807).sum := by decide
  have hdescent : baseEnd_1438807 < baseStart_1438807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438810 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4]
def baseStart_1438810 : Nat := 118140960795 + 1438810 * 2 ^ 59
def prefixEnd_1438810 : Nat := 4983230072969 + 3 ^ 40 * 1438810 * 2
def baseEnd_1438810 : Nat := 738801100495620882958039

theorem tailTrace_1438810 : CollatzResearch.WordTrace tailWord_1438810 prefixEnd_1438810 738801100495620882958039 := by
  unfold tailWord_1438810
  simp only [CollatzResearch.WordTrace]
  refine ⟨13119427979361143507402471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34985141278296382686406589 13119427979361143507402471)
  ·
    refine ⟨19679141969041715261103707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13119427979361143507402471 19679141969041715261103707)
    ·
      refine ⟨29518712953562572891655561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19679141969041715261103707 29518712953562572891655561)
      ·
        refine ⟨22139034715171929668741671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29518712953562572891655561 22139034715171929668741671)
        ·
          refine ⟨33208552072757894503112507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22139034715171929668741671 33208552072757894503112507)
          ·
            refine ⟨49812828109136841754668761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33208552072757894503112507 49812828109136841754668761)
            ·
              refine ⟨37359621081852631316001571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49812828109136841754668761 37359621081852631316001571)
              ·
                refine ⟨56039431622778946974002357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37359621081852631316001571 56039431622778946974002357)
                ·
                  refine ⟨5253696714635526278812721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56039431622778946974002357 5253696714635526278812721)
                  ·
                    refine ⟨3940272535976644709109541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5253696714635526278812721 3940272535976644709109541)
                    ·
                      refine ⟨738801100495620882958039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3940272535976644709109541 738801100495620882958039)
                      ·
                        rfl

theorem cell23_1438810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_1438810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438810 prefixEnd_1438810 := by exact prefixLift 1438810
  have htrace : WordTrace (prefixWord ++ tailWord_1438810) baseStart_1438810 baseEnd_1438810 := by
    simpa [prefixWord, tailWord_1438810, baseEnd_1438810] using wordTrace_append hprefix tailTrace_1438810
  have hstable : (prefixWord ++ tailWord_1438810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438810).length < 2 ^ (prefixWord ++ tailWord_1438810).sum := by decide
  have hdescent : baseEnd_1438810 < baseStart_1438810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438860 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 2, 2, 5]
def baseStart_1438860 : Nat := 118140960795 + 1438860 * 2 ^ 59
def prefixEnd_1438860 : Nat := 4983230072969 + 3 ^ 40 * 1438860 * 2
def baseEnd_1438860 : Nat := 738826774528345687332809

theorem tailTrace_1438860 : CollatzResearch.WordTrace tailWord_1438860 prefixEnd_1438860 738826774528345687332809 := by
  unfold tailWord_1438860
  simp only [CollatzResearch.WordTrace]
  refine ⟨26239767783631716284465017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34986357044842288379286689 26239767783631716284465017)
  ·
    refine ⟨19679825837723787213348763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26239767783631716284465017 19679825837723787213348763)
    ·
      refine ⟨29519738756585680820023145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19679825837723787213348763 29519738756585680820023145)
      ·
        refine ⟨22139804067439260615017359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29519738756585680820023145 22139804067439260615017359)
        ·
          refine ⟨33209706101158890922526039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22139804067439260615017359 33209706101158890922526039)
          ·
            refine ⟨49814559151738336383789059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33209706101158890922526039 49814559151738336383789059)
            ·
              refine ⟨74721838727607504575683589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49814559151738336383789059 74721838727607504575683589)
              ·
                refine ⟨14010344761426407107940673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74721838727607504575683589 14010344761426407107940673)
                ·
                  refine ⟨10507758571069805330955505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14010344761426407107940673 10507758571069805330955505)
                  ·
                    refine ⟨7880818928302353998216629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10507758571069805330955505 7880818928302353998216629)
                    ·
                      refine ⟨738826774528345687332809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7880818928302353998216629 738826774528345687332809)
                      ·
                        rfl

theorem cell23_1438860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_1438860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438860 prefixEnd_1438860 := by exact prefixLift 1438860
  have htrace : WordTrace (prefixWord ++ tailWord_1438860) baseStart_1438860 baseEnd_1438860 := by
    simpa [prefixWord, tailWord_1438860, baseEnd_1438860] using wordTrace_append hprefix tailTrace_1438860
  have hstable : (prefixWord ++ tailWord_1438860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438860).length < 2 ^ (prefixWord ++ tailWord_1438860).sum := by decide
  have hdescent : baseEnd_1438860 < baseStart_1438860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438902 : List Nat := [5, 1, 3, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_1438902 : Nat := 118140960795 + 1438902 * 2 ^ 59
def prefixEnd_1438902 : Nat := 4983230072969 + 3 ^ 40 * 1438902 * 2
def baseEnd_1438902 : Nat := 738848340715834523007617

theorem tailTrace_1438902 : CollatzResearch.WordTrace tailWord_1438902 prefixEnd_1438902 738848340715834523007617 := by
  unfold tailWord_1438902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3280066714569454608872435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34987378288740849161305973 3280066714569454608872435)
  ·
    refine ⟨4920100071854181913308653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3280066714569454608872435 4920100071854181913308653)
    ·
      refine ⟨1845037526945318217490745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4920100071854181913308653 1845037526945318217490745)
      ·
        refine ⟨1383778145208988663118059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1845037526945318217490745 1383778145208988663118059)
        ·
          refine ⟨2075667217813482994677089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1383778145208988663118059 2075667217813482994677089)
          ·
            refine ⟨1556750413360112246007817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2075667217813482994677089 1556750413360112246007817)
            ·
              refine ⟨1167562810020084184505863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1556750413360112246007817 1167562810020084184505863)
              ·
                refine ⟨1751344215030126276758795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1167562810020084184505863 1751344215030126276758795)
                ·
                  refine ⟨2627016322545189415138193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751344215030126276758795 2627016322545189415138193)
                  ·
                    refine ⟨1970262241908892061353645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2627016322545189415138193 1970262241908892061353645)
                    ·
                      refine ⟨738848340715834523007617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1970262241908892061353645 738848340715834523007617)
                      ·
                        rfl

theorem cell23_1438902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_1438902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438902 prefixEnd_1438902 := by exact prefixLift 1438902
  have htrace : WordTrace (prefixWord ++ tailWord_1438902) baseStart_1438902 baseEnd_1438902 := by
    simpa [prefixWord, tailWord_1438902, baseEnd_1438902] using wordTrace_append hprefix tailTrace_1438902
  have hstable : (prefixWord ++ tailWord_1438902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438902).length < 2 ^ (prefixWord ++ tailWord_1438902).sum := by decide
  have hdescent : baseEnd_1438902 < baseStart_1438902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438908 : List Nat := [2, 2, 2, 3, 2, 1, 4, 1, 1, 3, 2]
def baseStart_1438908 : Nat := 118140960795 + 1438908 * 2 ^ 59
def prefixEnd_1438908 : Nat := 4983230072969 + 3 ^ 40 * 1438908 * 2
def baseEnd_1438908 : Nat := 738851421599761499532589

theorem tailTrace_1438908 : CollatzResearch.WordTrace tailWord_1438908 prefixEnd_1438908 738851421599761499532589 := by
  unfold tailWord_1438908
  simp only [CollatzResearch.WordTrace]
  refine ⟨26240643135544768383338689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34987524180726357844451585 26240643135544768383338689)
  ·
    refine ⟨19680482351658576287504017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26240643135544768383338689 19680482351658576287504017)
    ·
      refine ⟨14760361763743932215628013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19680482351658576287504017 14760361763743932215628013)
      ·
        refine ⟨5535135661403974580860505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14760361763743932215628013 5535135661403974580860505)
        ·
          refine ⟨4151351746052980935645379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5535135661403974580860505 4151351746052980935645379)
          ·
            refine ⟨6227027619079471403468069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4151351746052980935645379 6227027619079471403468069)
            ·
              refine ⟨1167567678577400888150263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6227027619079471403468069 1167567678577400888150263)
              ·
                refine ⟨1751351517866101332225395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1167567678577400888150263 1751351517866101332225395)
                ·
                  refine ⟨2627027276799151998338093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751351517866101332225395 2627027276799151998338093)
                  ·
                    refine ⟨985135228799681999376785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2627027276799151998338093 985135228799681999376785)
                    ·
                      refine ⟨738851421599761499532589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 985135228799681999376785 738851421599761499532589)
                      ·
                        rfl

theorem cell23_1438908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_1438908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438908 prefixEnd_1438908 := by exact prefixLift 1438908
  have htrace : WordTrace (prefixWord ++ tailWord_1438908) baseStart_1438908 baseEnd_1438908 := by
    simpa [prefixWord, tailWord_1438908, baseEnd_1438908] using wordTrace_append hprefix tailTrace_1438908
  have hstable : (prefixWord ++ tailWord_1438908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438908).length < 2 ^ (prefixWord ++ tailWord_1438908).sum := by decide
  have hdescent : baseEnd_1438908 < baseStart_1438908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438974 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_1438974 : Nat := 118140960795 + 1438974 * 2 ^ 59
def prefixEnd_1438974 : Nat := 4983230072969 + 3 ^ 40 * 1438974 * 2
def baseEnd_1438974 : Nat := 246295103774319413769095

theorem tailTrace_1438974 : CollatzResearch.WordTrace tailWord_1438974 prefixEnd_1438974 246295103774319413769095 := by
  unfold tailWord_1438974
  simp only [CollatzResearch.WordTrace]
  refine ⟨6560461686106303754822497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34989128992566953359053317 6560461686106303754822497)
  ·
    refine ⟨4920346264579727816116873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6560461686106303754822497 4920346264579727816116873)
    ·
      refine ⟨3690259698434795862087655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4920346264579727816116873 3690259698434795862087655)
      ·
        refine ⟨5535389547652193793131483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3690259698434795862087655 5535389547652193793131483)
        ·
          refine ⟨8303084321478290689697225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5535389547652193793131483 8303084321478290689697225)
          ·
            refine ⟨6227313241108718017272919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8303084321478290689697225 6227313241108718017272919)
            ·
              refine ⟨9340969861663077025909379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6227313241108718017272919 9340969861663077025909379)
              ·
                refine ⟨14011454792494615538864069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9340969861663077025909379 14011454792494615538864069)
                ·
                  refine ⟨2627147773592740413537013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14011454792494615538864069 2627147773592740413537013)
                  ·
                    refine ⟨246295103774319413769095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2627147773592740413537013 246295103774319413769095)
                    ·
                      rfl

theorem cell23_1438974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_1438974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438974 prefixEnd_1438974 := by exact prefixLift 1438974
  have htrace : WordTrace (prefixWord ++ tailWord_1438974) baseStart_1438974 baseEnd_1438974 := by
    simpa [prefixWord, tailWord_1438974, baseEnd_1438974] using wordTrace_append hprefix tailTrace_1438974
  have hstable : (prefixWord ++ tailWord_1438974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438974).length < 2 ^ (prefixWord ++ tailWord_1438974).sum := by decide
  have hdescent : baseEnd_1438974 < baseStart_1438974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438978 : List Nat := [3, 4, 1, 1, 4, 1, 1, 1, 7]
def baseStart_1438978 : Nat := 118140960795 + 1438978 * 2 ^ 59
def prefixEnd_1438978 : Nat := 4983230072969 + 3 ^ 40 * 1438978 * 2
def baseEnd_1438978 : Nat := 82098596138397358406363

theorem tailTrace_1438978 : CollatzResearch.WordTrace tailWord_1438978 prefixEnd_1438978 82098596138397358406363 := by
  unfold tailWord_1438978
  simp only [CollatzResearch.WordTrace]
  refine ⟨13120959845208984680431397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34989226253890625814483725 13120959845208984680431397)
  ·
    refine ⟨2460179970976684627580887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13120959845208984680431397 2460179970976684627580887)
    ·
      refine ⟨3690269956465026941371331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2460179970976684627580887 3690269956465026941371331)
      ·
        refine ⟨5535404934697540412056997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3690269956465026941371331 5535404934697540412056997)
        ·
          refine ⟨1037888425255788827260687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5535404934697540412056997 1037888425255788827260687)
          ·
            refine ⟨1556832637883683240891031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037888425255788827260687 1556832637883683240891031)
            ·
              refine ⟨2335248956825524861336547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1556832637883683240891031 2335248956825524861336547)
              ·
                refine ⟨3502873435238287292004821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2335248956825524861336547 3502873435238287292004821)
                ·
                  refine ⟨82098596138397358406363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3502873435238287292004821 82098596138397358406363)
                  ·
                    rfl

theorem cell23_1438978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_1438978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438978 prefixEnd_1438978 := by exact prefixLift 1438978
  have htrace : WordTrace (prefixWord ++ tailWord_1438978) baseStart_1438978 baseEnd_1438978 := by
    simpa [prefixWord, tailWord_1438978, baseEnd_1438978] using wordTrace_append hprefix tailTrace_1438978
  have hstable : (prefixWord ++ tailWord_1438978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438978).length < 2 ^ (prefixWord ++ tailWord_1438978).sum := by decide
  have hdescent : baseEnd_1438978 < baseStart_1438978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1438984 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 1, 2, 5]
def baseStart_1438984 : Nat := 118140960795 + 1438984 * 2 ^ 59
def prefixEnd_1438984 : Nat := 4983230072969 + 3 ^ 40 * 1438984 * 2
def baseEnd_1438984 : Nat := 738890446129503202182239

theorem tailTrace_1438984 : CollatzResearch.WordTrace tailWord_1438984 prefixEnd_1438984 738890446129503202182239 := by
  unfold tailWord_1438984
  simp only [CollatzResearch.WordTrace]
  refine ⟨26242029109407100873222003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34989372145876134497629337 26242029109407100873222003)
  ·
    refine ⟨39363043664110651309833005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26242029109407100873222003 39363043664110651309833005)
    ·
      refine ⟨14761141374041494241187377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39363043664110651309833005 14761141374041494241187377)
      ·
        refine ⟨11070856030531120680890533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14761141374041494241187377 11070856030531120680890533)
        ·
          refine ⟨2075785505724585127666975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11070856030531120680890533 2075785505724585127666975)
          ·
            refine ⟨3113678258586877691500463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2075785505724585127666975 3113678258586877691500463)
            ·
              refine ⟨4670517387880316537250695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3113678258586877691500463 4670517387880316537250695)
              ·
                refine ⟨7005776081820474805876043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4670517387880316537250695 7005776081820474805876043)
                ·
                  refine ⟨10508664122730712208814065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7005776081820474805876043 10508664122730712208814065)
                  ·
                    refine ⟨7881498092048034156610549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10508664122730712208814065 7881498092048034156610549)
                    ·
                      refine ⟨738890446129503202182239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7881498092048034156610549 738890446129503202182239)
                      ·
                        rfl

theorem cell23_1438984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_1438984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1438984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1438984 prefixEnd_1438984 := by exact prefixLift 1438984
  have htrace : WordTrace (prefixWord ++ tailWord_1438984) baseStart_1438984 baseEnd_1438984 := by
    simpa [prefixWord, tailWord_1438984, baseEnd_1438984] using wordTrace_append hprefix tailTrace_1438984
  have hstable : (prefixWord ++ tailWord_1438984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1438984).length < 2 ^ (prefixWord ++ tailWord_1438984).sum := by decide
  have hdescent : baseEnd_1438984 < baseStart_1438984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1438984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439004 : List Nat := [2, 2, 3, 1, 1, 1, 2, 4, 3, 4]
def baseStart_1439004 : Nat := 118140960795 + 1439004 * 2 ^ 59
def prefixEnd_1439004 : Nat := 4983230072969 + 3 ^ 40 * 1439004 * 2
def baseEnd_1439004 : Nat := 246300238580864374644049

theorem tailTrace_1439004 : CollatzResearch.WordTrace tailWord_1439004 prefixEnd_1439004 246300238580864374644049 := by
  unfold tailWord_1439004
  simp only [CollatzResearch.WordTrace]
  refine ⟨26242393839370872581086033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34989858452494496774781377 26242393839370872581086033)
  ·
    refine ⟨19681795379528154435814525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26242393839370872581086033 19681795379528154435814525)
    ·
      refine ⟨7380673267323057913430447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19681795379528154435814525 7380673267323057913430447)
      ·
        refine ⟨11071009900984586870145671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7380673267323057913430447 11071009900984586870145671)
        ·
          refine ⟨16606514851476880305218507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11071009900984586870145671 16606514851476880305218507)
          ·
            refine ⟨24909772277215320457827761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16606514851476880305218507 24909772277215320457827761)
            ·
              refine ⟨18682329207911490343370821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24909772277215320457827761 18682329207911490343370821)
              ·
                refine ⟨3502936726483404439382029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18682329207911490343370821 3502936726483404439382029)
                ·
                  refine ⟨1313601272431276664768261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3502936726483404439382029 1313601272431276664768261)
                  ·
                    refine ⟨246300238580864374644049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1313601272431276664768261 246300238580864374644049)
                    ·
                      rfl

theorem cell23_1439004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_1439004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439004 prefixEnd_1439004 := by exact prefixLift 1439004
  have htrace : WordTrace (prefixWord ++ tailWord_1439004) baseStart_1439004 baseEnd_1439004 := by
    simpa [prefixWord, tailWord_1439004, baseEnd_1439004] using wordTrace_append hprefix tailTrace_1439004
  have hstable : (prefixWord ++ tailWord_1439004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439004).length < 2 ^ (prefixWord ++ tailWord_1439004).sum := by decide
  have hdescent : baseEnd_1439004 < baseStart_1439004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439034 : List Nat := [3, 1, 1, 1, 4, 1, 4, 2, 6]
def baseStart_1439034 : Nat := 118140960795 + 1439034 * 2 ^ 59
def prefixEnd_1439034 : Nat := 4983230072969 + 3 ^ 40 * 1439034 * 2
def baseEnd_1439034 : Nat := 82101791129136445173001

theorem tailTrace_1439034 : CollatzResearch.WordTrace tailWord_1439034 prefixEnd_1439034 82101791129136445173001 := by
  unfold tailWord_1439034
  simp only [CollatzResearch.WordTrace]
  refine ⟨13121470467158265071441039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34990587912422040190509437 13121470467158265071441039)
  ·
    refine ⟨19682205700737397607161559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13121470467158265071441039 19682205700737397607161559)
    ·
      refine ⟨29523308551106096410742339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19682205700737397607161559 29523308551106096410742339)
      ·
        refine ⟨44284962826659144616113509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29523308551106096410742339 44284962826659144616113509)
        ·
          refine ⟨8303430529998589615521283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44284962826659144616113509 8303430529998589615521283)
          ·
            refine ⟨12455145794997884423281925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8303430529998589615521283 12455145794997884423281925)
            ·
              refine ⟨2335339836562103329365361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12455145794997884423281925 2335339836562103329365361)
              ·
                refine ⟨1751504877421577497024021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2335339836562103329365361 1751504877421577497024021)
                ·
                  refine ⟨82101791129136445173001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1751504877421577497024021 82101791129136445173001)
                  ·
                    rfl

theorem cell23_1439034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 6].length) (baseStart_1439034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439034 prefixEnd_1439034 := by exact prefixLift 1439034
  have htrace : WordTrace (prefixWord ++ tailWord_1439034) baseStart_1439034 baseEnd_1439034 := by
    simpa [prefixWord, tailWord_1439034, baseEnd_1439034] using wordTrace_append hprefix tailTrace_1439034
  have hstable : (prefixWord ++ tailWord_1439034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439034).length < 2 ^ (prefixWord ++ tailWord_1439034).sum := by decide
  have hdescent : baseEnd_1439034 < baseStart_1439034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439038 : List Nat := [4, 2, 1, 2, 1, 1, 3, 4, 1, 4]
def baseStart_1439038 : Nat := 118140960795 + 1439038 * 2 ^ 59
def prefixEnd_1439038 : Nat := 4983230072969 + 3 ^ 40 * 1439038 * 2
def baseEnd_1439038 : Nat := 246306058028281996968997

theorem tailTrace_1439038 : CollatzResearch.WordTrace tailWord_1439038 prefixEnd_1439038 246306058028281996968997 := by
  unfold tailWord_1439038
  simp only [CollatzResearch.WordTrace]
  refine ⟨6560753470077321121113721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34990685173745712645939845 6560753470077321121113721)
  ·
    refine ⟨4920565102557990840835291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6560753470077321121113721 4920565102557990840835291)
    ·
      refine ⟨7380847653836986261252937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4920565102557990840835291 7380847653836986261252937)
      ·
        refine ⟨5535635740377739695939703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7380847653836986261252937 5535635740377739695939703)
        ·
          refine ⟨8303453610566609543909555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5535635740377739695939703 8303453610566609543909555)
          ·
            refine ⟨12455180415849914315864333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8303453610566609543909555 12455180415849914315864333)
            ·
              refine ⟨4670692655943717868449125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12455180415849914315864333 4670692655943717868449125)
              ·
                refine ⟨875754872989447100334211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4670692655943717868449125 875754872989447100334211)
                ·
                  refine ⟨1313632309484170650501317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875754872989447100334211 1313632309484170650501317)
                  ·
                    refine ⟨246306058028281996968997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1313632309484170650501317 246306058028281996968997)
                    ·
                      rfl

theorem cell23_1439038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_1439038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439038 prefixEnd_1439038 := by exact prefixLift 1439038
  have htrace : WordTrace (prefixWord ++ tailWord_1439038) baseStart_1439038 baseEnd_1439038 := by
    simpa [prefixWord, tailWord_1439038, baseEnd_1439038] using wordTrace_append hprefix tailTrace_1439038
  have hstable : (prefixWord ++ tailWord_1439038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439038).length < 2 ^ (prefixWord ++ tailWord_1439038).sum := by decide
  have hdescent : baseEnd_1439038 < baseStart_1439038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439057 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 2, 1, 7]
def baseStart_1439057 : Nat := 118140960795 + 1439057 * 2 ^ 59
def prefixEnd_1439057 : Nat := 4983230072969 + 3 ^ 40 * 1439057 * 2
def baseEnd_1439057 : Nat := 738927930217281416569403

theorem tailTrace_1439057 : CollatzResearch.WordTrace tailWord_1439057 prefixEnd_1439057 738927930217281416569403 := by
  unfold tailWord_1439057
  simp only [CollatzResearch.WordTrace]
  refine ⟨52486720747549735213851425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34991147165033156809234283 52486720747549735213851425)
  ·
    refine ⟨39365040560662301410388569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52486720747549735213851425 39365040560662301410388569)
    ·
      refine ⟨29523780420496726057791427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39365040560662301410388569 29523780420496726057791427)
      ·
        refine ⟨44285670630745089086687141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29523780420496726057791427 44285670630745089086687141)
        ·
          refine ⟨8303563243264704203753839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44285670630745089086687141 8303563243264704203753839)
          ·
            refine ⟨12455344864897056305630759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8303563243264704203753839 12455344864897056305630759)
            ·
              refine ⟨18683017297345584458446139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12455344864897056305630759 18683017297345584458446139)
              ·
                refine ⟨28024525946018376687669209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18683017297345584458446139 28024525946018376687669209)
                ·
                  refine ⟨21018394459513782515751907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28024525946018376687669209 21018394459513782515751907)
                  ·
                    refine ⟨31527591689270673773627861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21018394459513782515751907 31527591689270673773627861)
                    ·
                      refine ⟨738927930217281416569403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31527591689270673773627861 738927930217281416569403)
                      ·
                        rfl

theorem cell23_1439057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_1439057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439057 prefixEnd_1439057 := by exact prefixLift 1439057
  have htrace : WordTrace (prefixWord ++ tailWord_1439057) baseStart_1439057 baseEnd_1439057 := by
    simpa [prefixWord, tailWord_1439057, baseEnd_1439057] using wordTrace_append hprefix tailTrace_1439057
  have hstable : (prefixWord ++ tailWord_1439057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439057).length < 2 ^ (prefixWord ++ tailWord_1439057).sum := by decide
  have hdescent : baseEnd_1439057 < baseStart_1439057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439061 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 5, 1, 3]
def baseStart_1439061 : Nat := 118140960795 + 1439061 * 2 ^ 59
def prefixEnd_1439061 : Nat := 4983230072969 + 3 ^ 40 * 1439061 * 2
def baseEnd_1439061 : Nat := 738929984139899400919385

theorem tailTrace_1439061 : CollatzResearch.WordTrace tailWord_1439061 prefixEnd_1439061 738929984139899400919385 := by
  unfold tailWord_1439061
  simp only [CollatzResearch.WordTrace]
  refine ⟨52486866639535243896997037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34991244426356829264664691 52486866639535243896997037)
  ·
    refine ⟨19682574989825716461373889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52486866639535243896997037 19682574989825716461373889)
    ·
      refine ⟨14761931242369287346030417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19682574989825716461373889 14761931242369287346030417)
      ·
        refine ⟨11071448431776965509522813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14761931242369287346030417 11071448431776965509522813)
        ·
          refine ⟨4151793161916362066071055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11071448431776965509522813 4151793161916362066071055)
          ·
            refine ⟨6227689742874543099106583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4151793161916362066071055 6227689742874543099106583)
            ·
              refine ⟨9341534614311814648659875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6227689742874543099106583 9341534614311814648659875)
              ·
                refine ⟨14012301921467721972989813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9341534614311814648659875 14012301921467721972989813)
                ·
                  refine ⟨1313653305137598934967795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14012301921467721972989813 1313653305137598934967795)
                  ·
                    refine ⟨1970479957706398402451693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1313653305137598934967795 1970479957706398402451693)
                    ·
                      refine ⟨738929984139899400919385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1970479957706398402451693 738929984139899400919385)
                      ·
                        rfl

theorem cell23_1439061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_1439061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439061 prefixEnd_1439061 := by exact prefixLift 1439061
  have htrace : WordTrace (prefixWord ++ tailWord_1439061) baseStart_1439061 baseEnd_1439061 := by
    simpa [prefixWord, tailWord_1439061, baseEnd_1439061] using wordTrace_append hprefix tailTrace_1439061
  have hstable : (prefixWord ++ tailWord_1439061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439061).length < 2 ^ (prefixWord ++ tailWord_1439061).sum := by decide
  have hdescent : baseEnd_1439061 < baseStart_1439061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439064 : List Nat := [2, 1, 2, 2, 1, 1, 4, 4, 1, 5]
def baseStart_1439064 : Nat := 118140960795 + 1439064 * 2 ^ 59
def prefixEnd_1439064 : Nat := 4983230072969 + 3 ^ 40 * 1439064 * 2
def baseEnd_1439064 : Nat := 246310508193954296393957

theorem tailTrace_1439064 : CollatzResearch.WordTrace tailWord_1439064 prefixEnd_1439064 246310508193954296393957 := by
  unfold tailWord_1439064
  simp only [CollatzResearch.WordTrace]
  refine ⟨26243488029262187704678123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34991317372349583606237497 26243488029262187704678123)
  ·
    refine ⟨39365232043893281557017185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26243488029262187704678123 39365232043893281557017185)
    ·
      refine ⟨29523924032919961167762889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39365232043893281557017185 29523924032919961167762889)
      ·
        refine ⟨22142943024689970875822167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29523924032919961167762889 22142943024689970875822167)
        ·
          refine ⟨33214414537034956313733251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22142943024689970875822167 33214414537034956313733251)
          ·
            refine ⟨49821621805552434470599877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33214414537034956313733251 49821621805552434470599877)
            ·
              refine ⟨9341554088541081463237477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49821621805552434470599877 9341554088541081463237477)
              ·
                refine ⟨1751541391601452774357027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9341554088541081463237477 1751541391601452774357027)
                ·
                  refine ⟨2627312087402179161535541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751541391601452774357027 2627312087402179161535541)
                  ·
                    refine ⟨246310508193954296393957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2627312087402179161535541 246310508193954296393957)
                    ·
                      rfl

theorem cell23_1439064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 1, 5].length) (baseStart_1439064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439064 prefixEnd_1439064 := by exact prefixLift 1439064
  have htrace : WordTrace (prefixWord ++ tailWord_1439064) baseStart_1439064 baseEnd_1439064 := by
    simpa [prefixWord, tailWord_1439064, baseEnd_1439064] using wordTrace_append hprefix tailTrace_1439064
  have hstable : (prefixWord ++ tailWord_1439064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439064).length < 2 ^ (prefixWord ++ tailWord_1439064).sum := by decide
  have hdescent : baseEnd_1439064 < baseStart_1439064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439104 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 3]
def baseStart_1439104 : Nat := 118140960795 + 1439104 * 2 ^ 59
def prefixEnd_1439104 : Nat := 4983230072969 + 3 ^ 40 * 1439104 * 2
def baseEnd_1439104 : Nat := 738952063808042732681687

theorem tailTrace_1439104 : CollatzResearch.WordTrace tailWord_1439104 prefixEnd_1439104 738952063808042732681687 := by
  unfold tailWord_1439104
  simp only [CollatzResearch.WordTrace]
  refine ⟨26244217489189731120406183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34992289985586308160541577 26244217489189731120406183)
  ·
    refine ⟨39366326233784596680609275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26244217489189731120406183 39366326233784596680609275)
    ·
      refine ⟨59049489350676895020913913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39366326233784596680609275 59049489350676895020913913)
      ·
        refine ⟨44287117013007671265685435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59049489350676895020913913 44287117013007671265685435)
        ·
          refine ⟨66430675519511506898528153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44287117013007671265685435 66430675519511506898528153)
          ·
            refine ⟨49823006639633630173896115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66430675519511506898528153 49823006639633630173896115)
            ·
              refine ⟨74734509959450445260844173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49823006639633630173896115 74734509959450445260844173)
              ·
                refine ⟨28025441234793916972816565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74734509959450445260844173 28025441234793916972816565)
                ·
                  refine ⟨2627385115761929716201553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28025441234793916972816565 2627385115761929716201553)
                  ·
                    refine ⟨1970538836821447287151165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2627385115761929716201553 1970538836821447287151165)
                    ·
                      refine ⟨738952063808042732681687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1970538836821447287151165 738952063808042732681687)
                      ·
                        rfl

theorem cell23_1439104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_1439104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439104 prefixEnd_1439104 := by exact prefixLift 1439104
  have htrace : WordTrace (prefixWord ++ tailWord_1439104) baseStart_1439104 baseEnd_1439104 := by
    simpa [prefixWord, tailWord_1439104, baseEnd_1439104] using wordTrace_append hprefix tailTrace_1439104
  have hstable : (prefixWord ++ tailWord_1439104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439104).length < 2 ^ (prefixWord ++ tailWord_1439104).sum := by decide
  have hdescent : baseEnd_1439104 < baseStart_1439104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439111 : List Nat := [1, 1, 4, 2, 2, 4, 1, 1, 1, 6]
def baseStart_1439111 : Nat := 118140960795 + 1439111 * 2 ^ 59
def prefixEnd_1439111 : Nat := 4983230072969 + 3 ^ 40 * 1439111 * 2
def baseEnd_1439111 : Nat := 246318552724208068431385

theorem tailTrace_1439111 : CollatzResearch.WordTrace tailWord_1439111 prefixEnd_1439111 246318552724208068431385 := by
  unfold tailWord_1439111
  simp only [CollatzResearch.WordTrace]
  refine ⟨52488690289354102436317187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34992460192902734957544791 52488690289354102436317187)
  ·
    refine ⟨78733035434031153654475781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52488690289354102436317187 78733035434031153654475781)
    ·
      refine ⟨14762444143880841310214209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78733035434031153654475781 14762444143880841310214209)
      ·
        refine ⟨11071833107910630982660657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14762444143880841310214209 11071833107910630982660657)
        ·
          refine ⟨8303874830932973236995493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11071833107910630982660657 8303874830932973236995493)
          ·
            refine ⟨1556976530799932481936655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8303874830932973236995493 1556976530799932481936655)
            ·
              refine ⟨2335464796199898722904983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1556976530799932481936655 2335464796199898722904983)
              ·
                refine ⟨3503197194299848084357475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2335464796199898722904983 3503197194299848084357475)
                ·
                  refine ⟨5254795791449772126536213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3503197194299848084357475 5254795791449772126536213)
                  ·
                    refine ⟨246318552724208068431385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5254795791449772126536213 246318552724208068431385)
                    ·
                      rfl

theorem cell23_1439111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_1439111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439111 prefixEnd_1439111 := by exact prefixLift 1439111
  have htrace : WordTrace (prefixWord ++ tailWord_1439111) baseStart_1439111 baseEnd_1439111 := by
    simpa [prefixWord, tailWord_1439111, baseEnd_1439111] using wordTrace_append hprefix tailTrace_1439111
  have hstable : (prefixWord ++ tailWord_1439111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439111).length < 2 ^ (prefixWord ++ tailWord_1439111).sum := by decide
  have hdescent : baseEnd_1439111 < baseStart_1439111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439138 : List Nat := [3, 3, 1, 2, 1, 2, 2, 3, 1, 2, 3]
def baseStart_1439138 : Nat := 118140960795 + 1439138 * 2 ^ 59
def prefixEnd_1439138 : Nat := 4983230072969 + 3 ^ 40 * 1439138 * 2
def baseEnd_1439138 : Nat := 738969522150295599656531

theorem tailTrace_1439138 : CollatzResearch.WordTrace tailWord_1439138 prefixEnd_1439138 738969522150295599656531 := by
  unfold tailWord_1439138
  simp only [CollatzResearch.WordTrace]
  refine ⟨13122418765064071511887517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34993116706837524031700045 13122418765064071511887517)
  ·
    refine ⟨4920907036899026816957819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13122418765064071511887517 4920907036899026816957819)
    ·
      refine ⟨7381360555348540225436729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4920907036899026816957819 7381360555348540225436729)
      ·
        refine ⟨5536020416511405169077547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7381360555348540225436729 5536020416511405169077547)
        ·
          refine ⟨8304030624767107753616321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5536020416511405169077547 8304030624767107753616321)
          ·
            refine ⟨6228022968575330815212241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8304030624767107753616321 6228022968575330815212241)
            ·
              refine ⟨4671017226431498111409181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6228022968575330815212241 4671017226431498111409181)
              ·
                refine ⟨1751631459911811791778443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4671017226431498111409181 1751631459911811791778443)
                ·
                  refine ⟨2627447189867717687667665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751631459911811791778443 2627447189867717687667665)
                  ·
                    refine ⟨1970585392400788265750749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2627447189867717687667665 1970585392400788265750749)
                    ·
                      refine ⟨738969522150295599656531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1970585392400788265750749 738969522150295599656531)
                      ·
                        rfl

theorem cell23_1439138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_1439138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439138 prefixEnd_1439138 := by exact prefixLift 1439138
  have htrace : WordTrace (prefixWord ++ tailWord_1439138) baseStart_1439138 baseEnd_1439138 := by
    simpa [prefixWord, tailWord_1439138, baseEnd_1439138] using wordTrace_append hprefix tailTrace_1439138
  have hstable : (prefixWord ++ tailWord_1439138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439138).length < 2 ^ (prefixWord ++ tailWord_1439138).sum := by decide
  have hdescent : baseEnd_1439138 < baseStart_1439138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439178 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 3, 3, 2]
def baseStart_1439178 : Nat := 118140960795 + 1439178 * 2 ^ 59
def prefixEnd_1439178 : Nat := 4983230072969 + 3 ^ 40 * 1439178 * 2
def baseEnd_1439178 : Nat := 738990061376475443156347

theorem tailTrace_1439178 : CollatzResearch.WordTrace tailWord_1439178 prefixEnd_1439178 738990061376475443156347 := by
  unfold tailWord_1439178
  simp only [CollatzResearch.WordTrace]
  refine ⟨13122783495027843219751547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34994089320074248586004125 13122783495027843219751547)
  ·
    refine ⟨19684175242541764829627321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13122783495027843219751547 19684175242541764829627321)
    ·
      refine ⟨14763131431906323622220491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19684175242541764829627321 14763131431906323622220491)
      ·
        refine ⟨22144697147859485433330737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14763131431906323622220491 22144697147859485433330737)
        ·
          refine ⟨16608522860894614074998053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22144697147859485433330737 16608522860894614074998053)
          ·
            refine ⟨3114098036417740139062135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16608522860894614074998053 3114098036417740139062135)
            ·
              refine ⟨4671147054626610208593203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3114098036417740139062135 4671147054626610208593203)
              ·
                refine ⟨7006720581939915312889805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4671147054626610208593203 7006720581939915312889805)
                ·
                  refine ⟨2627520218227468242333677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7006720581939915312889805 2627520218227468242333677)
                  ·
                    refine ⟨985320081835300590875129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2627520218227468242333677 985320081835300590875129)
                    ·
                      refine ⟨738990061376475443156347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 985320081835300590875129 738990061376475443156347)
                      ·
                        rfl

theorem cell23_1439178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_1439178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439178 prefixEnd_1439178 := by exact prefixLift 1439178
  have htrace : WordTrace (prefixWord ++ tailWord_1439178) baseStart_1439178 baseEnd_1439178 := by
    simpa [prefixWord, tailWord_1439178, baseEnd_1439178] using wordTrace_append hprefix tailTrace_1439178
  have hstable : (prefixWord ++ tailWord_1439178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439178).length < 2 ^ (prefixWord ++ tailWord_1439178).sum := by decide
  have hdescent : baseEnd_1439178 < baseStart_1439178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439204 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_1439204 : Nat := 118140960795 + 1439204 * 2 ^ 59
def prefixEnd_1439204 : Nat := 4983230072969 + 3 ^ 40 * 1439204 * 2
def baseEnd_1439204 : Nat := 739003411873492341431227

theorem tailTrace_1439204 : CollatzResearch.WordTrace tailWord_1439204 prefixEnd_1439204 739003411873492341431227 := by
  unfold tailWord_1439204
  simp only [CollatzResearch.WordTrace]
  refine ⟨26246041139008589659726333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34994721518678119546301777 26246041139008589659726333)
  ·
    refine ⟨9842265427128221122397375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26246041139008589659726333 9842265427128221122397375)
    ·
      refine ⟨14763398140692331683596063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9842265427128221122397375 14763398140692331683596063)
      ·
        refine ⟨22145097211038497525394095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14763398140692331683596063 22145097211038497525394095)
        ·
          refine ⟨33217645816557746288091143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22145097211038497525394095 33217645816557746288091143)
          ·
            refine ⟨49826468724836619432136715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33217645816557746288091143 49826468724836619432136715)
            ·
              refine ⟨74739703087254929148205073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49826468724836619432136715 74739703087254929148205073)
              ·
                refine ⟨56054777315441196861153805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74739703087254929148205073 56054777315441196861153805)
                ·
                  refine ⟨21020541493290448822932677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56054777315441196861153805 21020541493290448822932677)
                  ·
                    refine ⟨3941351529991959154299877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21020541493290448822932677 3941351529991959154299877)
                    ·
                      refine ⟨739003411873492341431227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3941351529991959154299877 739003411873492341431227)
                      ·
                        rfl

theorem cell23_1439204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_1439204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439204 prefixEnd_1439204 := by exact prefixLift 1439204
  have htrace : WordTrace (prefixWord ++ tailWord_1439204) baseStart_1439204 baseEnd_1439204 := by
    simpa [prefixWord, tailWord_1439204, baseEnd_1439204] using wordTrace_append hprefix tailTrace_1439204
  have hstable : (prefixWord ++ tailWord_1439204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439204).length < 2 ^ (prefixWord ++ tailWord_1439204).sum := by decide
  have hdescent : baseEnd_1439204 < baseStart_1439204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439261 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 4, 5]
def baseStart_1439261 : Nat := 118140960795 + 1439261 * 2 ^ 59
def prefixEnd_1439261 : Nat := 4983230072969 + 3 ^ 40 * 1439261 * 2
def baseEnd_1439261 : Nat := 246344226756932872806155

theorem tailTrace_1439261 : CollatzResearch.WordTrace tailWord_1439261 prefixEnd_1439261 246344226756932872806155 := by
  unfold tailWord_1439261
  simp only [CollatzResearch.WordTrace]
  refine ⟨52494161238810678054277637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34996107492540452036185091 52494161238810678054277637)
  ·
    refine ⟨9842655232277002135177057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52494161238810678054277637 9842655232277002135177057)
    ·
      refine ⟨7381991424207751601382793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9842655232277002135177057 7381991424207751601382793)
      ·
        refine ⟨5536493568155813701037095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7381991424207751601382793 5536493568155813701037095)
        ·
          refine ⟨8304740352233720551555643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5536493568155813701037095 8304740352233720551555643)
          ·
            refine ⟨12457110528350580827333465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8304740352233720551555643 12457110528350580827333465)
            ·
              refine ⟨9342832896262935620500099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12457110528350580827333465 9342832896262935620500099)
              ·
                refine ⟨14014249344394403430750149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9342832896262935620500099 14014249344394403430750149)
                ·
                  refine ⟨2627671752073950643265653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14014249344394403430750149 2627671752073950643265653)
                  ·
                    refine ⟨246344226756932872806155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2627671752073950643265653 246344226756932872806155)
                    ·
                      rfl

theorem cell23_1439261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_1439261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439261 prefixEnd_1439261 := by exact prefixLift 1439261
  have htrace : WordTrace (prefixWord ++ tailWord_1439261) baseStart_1439261 baseEnd_1439261 := by
    simpa [prefixWord, tailWord_1439261, baseEnd_1439261] using wordTrace_append hprefix tailTrace_1439261
  have hstable : (prefixWord ++ tailWord_1439261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439261).length < 2 ^ (prefixWord ++ tailWord_1439261).sum := by decide
  have hdescent : baseEnd_1439261 < baseStart_1439261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439301 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 1, 4, 3]
def baseStart_1439301 : Nat := 118140960795 + 1439301 * 2 ^ 59
def prefixEnd_1439301 : Nat := 4983230072969 + 3 ^ 40 * 1439301 * 2
def baseEnd_1439301 : Nat := 739053219496978461918281

theorem tailTrace_1439301 : CollatzResearch.WordTrace tailWord_1439301 prefixEnd_1439301 739053219496978461918281 := by
  unfold tailWord_1439301
  simp only [CollatzResearch.WordTrace]
  refine ⟨52495620158665764885733757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34997080105777176590489171 52495620158665764885733757)
  ·
    refine ⟨19685857559499661832150159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52495620158665764885733757 19685857559499661832150159)
    ·
      refine ⟨29528786339249492748225239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19685857559499661832150159 29528786339249492748225239)
      ·
        refine ⟨44293179508874239122337859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29528786339249492748225239 44293179508874239122337859)
        ·
          refine ⟨66439769263311358683506789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44293179508874239122337859 66439769263311358683506789)
          ·
            refine ⟨12457456736870879753157523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66439769263311358683506789 12457456736870879753157523)
            ·
              refine ⟨18686185105306319629736285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12457456736870879753157523 18686185105306319629736285)
              ·
                refine ⟨7007319414489869861151107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18686185105306319629736285 7007319414489869861151107)
                ·
                  refine ⟨10510979121734804791726661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7007319414489869861151107 10510979121734804791726661)
                  ·
                    refine ⟨1970808585325275898448749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10510979121734804791726661 1970808585325275898448749)
                    ·
                      refine ⟨739053219496978461918281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1970808585325275898448749 739053219496978461918281)
                      ·
                        rfl

theorem cell23_1439301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_1439301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439301 prefixEnd_1439301 := by exact prefixLift 1439301
  have htrace : WordTrace (prefixWord ++ tailWord_1439301) baseStart_1439301 baseEnd_1439301 := by
    simpa [prefixWord, tailWord_1439301, baseEnd_1439301] using wordTrace_append hprefix tailTrace_1439301
  have hstable : (prefixWord ++ tailWord_1439301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439301).length < 2 ^ (prefixWord ++ tailWord_1439301).sum := by decide
  have hdescent : baseEnd_1439301 < baseStart_1439301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439338 : List Nat := [3, 1, 3, 2, 1, 3, 1, 3, 6]
def baseStart_1439338 : Nat := 118140960795 + 1439338 * 2 ^ 59
def prefixEnd_1439338 : Nat := 4983230072969 + 3 ^ 40 * 1439338 * 2
def baseEnd_1439338 : Nat := 82119135364577201906179

theorem tailTrace_1439338 : CollatzResearch.WordTrace tailWord_1439338 prefixEnd_1439338 82119135364577201906179 := by
  unfold tailWord_1439338
  simp only [CollatzResearch.WordTrace]
  refine ⟨13124242414882930051207667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34997979773021146803220445 13124242414882930051207667)
  ·
    refine ⟨19686363622324395076811501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13124242414882930051207667 19686363622324395076811501)
    ·
      refine ⟨7382386358371648153804313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19686363622324395076811501 7382386358371648153804313)
      ·
        refine ⟨5536789768778736115353235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7382386358371648153804313 5536789768778736115353235)
        ·
          refine ⟨8305184653168104173029853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5536789768778736115353235 8305184653168104173029853)
          ·
            refine ⟨3114444244938039064886195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8305184653168104173029853 3114444244938039064886195)
            ·
              refine ⟨4671666367407058597329293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3114444244938039064886195 4671666367407058597329293)
              ·
                refine ⟨1751874887777646973998485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4671666367407058597329293 1751874887777646973998485)
                ·
                  refine ⟨82119135364577201906179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1751874887777646973998485 82119135364577201906179)
                  ·
                    rfl

theorem cell23_1439338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 6].length) (baseStart_1439338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439338 prefixEnd_1439338 := by exact prefixLift 1439338
  have htrace : WordTrace (prefixWord ++ tailWord_1439338) baseStart_1439338 baseEnd_1439338 := by
    simpa [prefixWord, tailWord_1439338, baseEnd_1439338] using wordTrace_append hprefix tailTrace_1439338
  have hstable : (prefixWord ++ tailWord_1439338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439338).length < 2 ^ (prefixWord ++ tailWord_1439338).sum := by decide
  have hdescent : baseEnd_1439338 < baseStart_1439338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439405 : List Nat := [1, 5, 2, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_1439405 : Nat := 118140960795 + 1439405 * 2 ^ 59
def prefixEnd_1439405 : Nat := 4983230072969 + 3 ^ 40 * 1439405 * 2
def baseEnd_1439405 : Nat := 739106621485046055017803

theorem tailTrace_1439405 : CollatzResearch.WordTrace tailWord_1439405 prefixEnd_1439405 739106621485046055017803 := by
  unfold tailWord_1439405
  simp only [CollatzResearch.WordTrace]
  refine ⟨52499413350288990647519669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34999608900192660431679779 52499413350288990647519669)
  ·
    refine ⟨4921820001589592873204969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52499413350288990647519669 4921820001589592873204969)
    ·
      refine ⟨3691365001192194654903727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4921820001589592873204969 3691365001192194654903727)
      ·
        refine ⟨5537047501788291982355591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3691365001192194654903727 5537047501788291982355591)
        ·
          refine ⟨8305571252682437973533387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5537047501788291982355591 8305571252682437973533387)
          ·
            refine ⟨12458356879023656960300081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8305571252682437973533387 12458356879023656960300081)
            ·
              refine ⟨9343767659267742720225061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12458356879023656960300081 9343767659267742720225061)
              ·
                refine ⟨1751956436112701760042199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9343767659267742720225061 1751956436112701760042199)
                ·
                  refine ⟨2627934654169052640063299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751956436112701760042199 2627934654169052640063299)
                  ·
                    refine ⟨3941901981253578960094949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2627934654169052640063299 3941901981253578960094949)
                    ·
                      refine ⟨739106621485046055017803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3941901981253578960094949 739106621485046055017803)
                      ·
                        rfl

theorem cell23_1439405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_1439405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439405 prefixEnd_1439405 := by exact prefixLift 1439405
  have htrace : WordTrace (prefixWord ++ tailWord_1439405) baseStart_1439405 baseEnd_1439405 := by
    simpa [prefixWord, tailWord_1439405, baseEnd_1439405] using wordTrace_append hprefix tailTrace_1439405
  have hstable : (prefixWord ++ tailWord_1439405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439405).length < 2 ^ (prefixWord ++ tailWord_1439405).sum := by decide
  have hdescent : baseEnd_1439405 < baseStart_1439405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439408 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 3]
def baseStart_1439408 : Nat := 118140960795 + 1439408 * 2 ^ 59
def prefixEnd_1439408 : Nat := 4983230072969 + 3 ^ 40 * 1439408 * 2
def baseEnd_1439408 : Nat := 739108161927009543280289

theorem tailTrace_1439408 : CollatzResearch.WordTrace tailWord_1439408 prefixEnd_1439408 739108161927009543280289 := by
  unfold tailWord_1439408
  simp only [CollatzResearch.WordTrace]
  refine ⟨26249761384639061079939439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34999681846185414773252585 26249761384639061079939439)
  ·
    refine ⟨39374642076958591619909159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26249761384639061079939439 39374642076958591619909159)
    ·
      refine ⟨59061963115437887429863739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39374642076958591619909159 59061963115437887429863739)
      ·
        refine ⟨88592944673156831144795609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59061963115437887429863739 88592944673156831144795609)
        ·
          refine ⟨66444708504867623358596707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88592944673156831144795609 66444708504867623358596707)
          ·
            refine ⟨99667062757301435037895061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66444708504867623358596707 99667062757301435037895061)
            ·
              refine ⟨4671893566748504767401331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99667062757301435037895061 4671893566748504767401331)
              ·
                refine ⟨7007840350122757151101997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4671893566748504767401331 7007840350122757151101997)
                ·
                  refine ⟨2627940131296033931663249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7007840350122757151101997 2627940131296033931663249)
                  ·
                    refine ⟨1970955098472025448747437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2627940131296033931663249 1970955098472025448747437)
                    ·
                      refine ⟨739108161927009543280289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1970955098472025448747437 739108161927009543280289)
                      ·
                        rfl

theorem cell23_1439408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 3].length) (baseStart_1439408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439408 prefixEnd_1439408 := by exact prefixLift 1439408
  have htrace : WordTrace (prefixWord ++ tailWord_1439408) baseStart_1439408 baseEnd_1439408 := by
    simpa [prefixWord, tailWord_1439408, baseEnd_1439408] using wordTrace_append hprefix tailTrace_1439408
  have hstable : (prefixWord ++ tailWord_1439408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439408).length < 2 ^ (prefixWord ++ tailWord_1439408).sum := by decide
  have hdescent : baseEnd_1439408 < baseStart_1439408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439418 : List Nat := [3, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4]
def baseStart_1439418 : Nat := 118140960795 + 1439418 * 2 ^ 59
def prefixEnd_1439418 : Nat := 4983230072969 + 3 ^ 40 * 1439418 * 2
def baseEnd_1439418 : Nat := 739113296733554504155243

theorem tailTrace_1439418 : CollatzResearch.WordTrace tailWord_1439418 prefixEnd_1439418 739113296733554504155243 := by
  unfold tailWord_1439418
  simp only [CollatzResearch.WordTrace]
  refine ⟨13124971874810473466935727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34999924999494595911828605 13124971874810473466935727)
  ·
    refine ⟨19687457812215710200403591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13124971874810473466935727 19687457812215710200403591)
    ·
      refine ⟨29531186718323565300605387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19687457812215710200403591 29531186718323565300605387)
      ·
        refine ⟨44296780077485347950908081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29531186718323565300605387 44296780077485347950908081)
        ·
          refine ⟨33222585058114010963181061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44296780077485347950908081 33222585058114010963181061)
          ·
            refine ⟨6229234698396377055596449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33222585058114010963181061 6229234698396377055596449)
            ·
              refine ⟨4671926023797282791697337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6229234698396377055596449 4671926023797282791697337)
              ·
                refine ⟨3503944517847962093773003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4671926023797282791697337 3503944517847962093773003)
                ·
                  refine ⟨5255916776771943140659505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3503944517847962093773003 5255916776771943140659505)
                  ·
                    refine ⟨3941937582578957355494629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5255916776771943140659505 3941937582578957355494629)
                    ·
                      refine ⟨739113296733554504155243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3941937582578957355494629 739113296733554504155243)
                      ·
                        rfl

theorem cell23_1439418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_1439418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439418 prefixEnd_1439418 := by exact prefixLift 1439418
  have htrace : WordTrace (prefixWord ++ tailWord_1439418) baseStart_1439418 baseEnd_1439418 := by
    simpa [prefixWord, tailWord_1439418, baseEnd_1439418] using wordTrace_append hprefix tailTrace_1439418
  have hstable : (prefixWord ++ tailWord_1439418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439418).length < 2 ^ (prefixWord ++ tailWord_1439418).sum := by decide
  have hdescent : baseEnd_1439418 < baseStart_1439418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439422 : List Nat := [4, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4]
def baseStart_1439422 : Nat := 118140960795 + 1439422 * 2 ^ 59
def prefixEnd_1439422 : Nat := 4983230072969 + 3 ^ 40 * 1439422 * 2
def baseEnd_1439422 : Nat := 739115350656172488505225

theorem tailTrace_1439422 : CollatzResearch.WordTrace tailWord_1439422 prefixEnd_1439422 739115350656172488505225 := by
  unfold tailWord_1439422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6562504173903425318861065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35000022260818268367259013 6562504173903425318861065)
  ·
    refine ⟨4921878130427568989145799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6562504173903425318861065 4921878130427568989145799)
    ·
      refine ⟨7382817195641353483718699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4921878130427568989145799 7382817195641353483718699)
      ·
        refine ⟨11074225793462030225578049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7382817195641353483718699 11074225793462030225578049)
        ·
          refine ⟨8305669345096522669183537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11074225793462030225578049 8305669345096522669183537)
          ·
            refine ⟨6229252008822392001887653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8305669345096522669183537 6229252008822392001887653)
            ·
              refine ⟨1167984751654198500353935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6229252008822392001887653 1167984751654198500353935)
              ·
                refine ⟨1751977127481297750530903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1167984751654198500353935 1751977127481297750530903)
                ·
                  refine ⟨2627965691221946625796355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751977127481297750530903 2627965691221946625796355)
                  ·
                    refine ⟨3941948536832919938694533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2627965691221946625796355 3941948536832919938694533)
                    ·
                      refine ⟨739115350656172488505225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3941948536832919938694533 739115350656172488505225)
                      ·
                        rfl

theorem cell23_1439422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_1439422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439422 prefixEnd_1439422 := by exact prefixLift 1439422
  have htrace : WordTrace (prefixWord ++ tailWord_1439422) baseStart_1439422 baseEnd_1439422 := by
    simpa [prefixWord, tailWord_1439422, baseEnd_1439422] using wordTrace_append hprefix tailTrace_1439422
  have hstable : (prefixWord ++ tailWord_1439422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439422).length < 2 ^ (prefixWord ++ tailWord_1439422).sum := by decide
  have hdescent : baseEnd_1439422 < baseStart_1439422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439506 : List Nat := [3, 2, 4, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_1439506 : Nat := 118140960795 + 1439506 * 2 ^ 59
def prefixEnd_1439506 : Nat := 4983230072969 + 3 ^ 40 * 1439506 * 2
def baseEnd_1439506 : Nat := 739158483031150159854839

theorem tailTrace_1439506 : CollatzResearch.WordTrace tailWord_1439506 prefixEnd_1439506 739158483031150159854839 := by
  unfold tailWord_1439506
  simp only [CollatzResearch.WordTrace]
  refine ⟨13125774280730771224236593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35002064748615389931297581 13125774280730771224236593)
  ·
    refine ⟨9844330710548078418177445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13125774280730771224236593 9844330710548078418177445)
    ·
      refine ⟨1845812008227764703408271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9844330710548078418177445 1845812008227764703408271)
      ·
        refine ⟨2768718012341647055112407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1845812008227764703408271 2768718012341647055112407)
        ·
          refine ⟨4153077018512470582668611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2768718012341647055112407 4153077018512470582668611)
          ·
            refine ⟨6229615527768705874002917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4153077018512470582668611 6229615527768705874002917)
            ·
              refine ⟨1168052911456632351375547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6229615527768705874002917 1168052911456632351375547)
              ·
                refine ⟨1752079367184948527063321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168052911456632351375547 1752079367184948527063321)
                ·
                  refine ⟨1314059525388711395297491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1752079367184948527063321 1314059525388711395297491)
                  ·
                    refine ⟨1971089288083067092946237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1314059525388711395297491 1971089288083067092946237)
                    ·
                      refine ⟨739158483031150159854839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1971089288083067092946237 739158483031150159854839)
                      ·
                        rfl

theorem cell23_1439506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_1439506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439506 prefixEnd_1439506 := by exact prefixLift 1439506
  have htrace : WordTrace (prefixWord ++ tailWord_1439506) baseStart_1439506 baseEnd_1439506 := by
    simpa [prefixWord, tailWord_1439506, baseEnd_1439506] using wordTrace_append hprefix tailTrace_1439506
  have hstable : (prefixWord ++ tailWord_1439506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439506).length < 2 ^ (prefixWord ++ tailWord_1439506).sum := by decide
  have hdescent : baseEnd_1439506 < baseStart_1439506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439555 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 2, 5, 2]
def baseStart_1439555 : Nat := 118140960795 + 1439555 * 2 ^ 59
def prefixEnd_1439555 : Nat := 4983230072969 + 3 ^ 40 * 1439555 * 2
def baseEnd_1439555 : Nat := 739183643583220468142113

theorem tailTrace_1439555 : CollatzResearch.WordTrace tailWord_1439555 prefixEnd_1439555 739183643583220468142113 := by
  unfold tailWord_1439555
  simp only [CollatzResearch.WordTrace]
  refine ⟨52504884299745566265480119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35003256199830377510320079 52504884299745566265480119)
  ·
    refine ⟨78757326449618349398220179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52504884299745566265480119 78757326449618349398220179)
    ·
      refine ⟨118135989674427524097330269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78757326449618349398220179 118135989674427524097330269)
      ·
        refine ⟨44300996127910321536498851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118135989674427524097330269 44300996127910321536498851)
        ·
          refine ⟨66451494191865482304748277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44300996127910321536498851 66451494191865482304748277)
          ·
            refine ⟨6229827580487388966070151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66451494191865482304748277 6229827580487388966070151)
            ·
              refine ⟨9344741370731083449105227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6229827580487388966070151 9344741370731083449105227)
              ·
                refine ⟨14017112056096625173657841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9344741370731083449105227 14017112056096625173657841)
                ·
                  refine ⟨10512834042072468880243381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14017112056096625173657841 10512834042072468880243381)
                  ·
                    refine ⟨985578191444293957522817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10512834042072468880243381 985578191444293957522817)
                    ·
                      refine ⟨739183643583220468142113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 985578191444293957522817 739183643583220468142113)
                      ·
                        rfl

theorem cell23_1439555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 5, 2].length) (baseStart_1439555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439555 prefixEnd_1439555 := by exact prefixLift 1439555
  have htrace : WordTrace (prefixWord ++ tailWord_1439555) baseStart_1439555 baseEnd_1439555 := by
    simpa [prefixWord, tailWord_1439555, baseEnd_1439555] using wordTrace_append hprefix tailTrace_1439555
  have hstable : (prefixWord ++ tailWord_1439555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439555).length < 2 ^ (prefixWord ++ tailWord_1439555).sum := by decide
  have hdescent : baseEnd_1439555 < baseStart_1439555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439568 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 4]
def baseStart_1439568 : Nat := 118140960795 + 1439568 * 2 ^ 59
def prefixEnd_1439568 : Nat := 4983230072969 + 3 ^ 40 * 1439568 * 2
def baseEnd_1439568 : Nat := 739190318831728917279553

theorem tailTrace_1439568 : CollatzResearch.WordTrace tailWord_1439568 prefixEnd_1439568 739190318831728917279553 := by
  unfold tailWord_1439568
  simp only [CollatzResearch.WordTrace]
  refine ⟨26252679224349234742851679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35003572299132312990468905 26252679224349234742851679)
  ·
    refine ⟨39379018836523852114277519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26252679224349234742851679 39379018836523852114277519)
    ·
      refine ⟨59068528254785778171416279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39379018836523852114277519 59068528254785778171416279)
      ·
        refine ⟨88602792382178667257124419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59068528254785778171416279 88602792382178667257124419)
        ·
          refine ⟨132904188573268000885686629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88602792382178667257124419 132904188573268000885686629)
          ·
            refine ⟨24919535357487750166066243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132904188573268000885686629 24919535357487750166066243)
            ·
              refine ⟨37379303036231625249099365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24919535357487750166066243 37379303036231625249099365)
              ·
                refine ⟨7008619319293429734206131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37379303036231625249099365 7008619319293429734206131)
                ·
                  refine ⟨10512928978940144601309197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7008619319293429734206131 10512928978940144601309197)
                  ·
                    refine ⟨3942348367102554225490949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10512928978940144601309197 3942348367102554225490949)
                    ·
                      refine ⟨739190318831728917279553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3942348367102554225490949 739190318831728917279553)
                      ·
                        rfl

theorem cell23_1439568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 4].length) (baseStart_1439568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439568 prefixEnd_1439568 := by exact prefixLift 1439568
  have htrace : WordTrace (prefixWord ++ tailWord_1439568) baseStart_1439568 baseEnd_1439568 := by
    simpa [prefixWord, tailWord_1439568, baseEnd_1439568] using wordTrace_append hprefix tailTrace_1439568
  have hstable : (prefixWord ++ tailWord_1439568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439568).length < 2 ^ (prefixWord ++ tailWord_1439568).sum := by decide
  have hdescent : baseEnd_1439568 < baseStart_1439568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439585 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 1, 6, 2]
def baseStart_1439585 : Nat := 118140960795 + 1439585 * 2 ^ 59
def prefixEnd_1439585 : Nat := 4983230072969 + 3 ^ 40 * 1439585 * 2
def baseEnd_1439585 : Nat := 739199048002855350766975

theorem tailTrace_1439585 : CollatzResearch.WordTrace tailWord_1439585 prefixEnd_1439585 739199048002855350766975 := by
  unfold tailWord_1439585
  simp only [CollatzResearch.WordTrace]
  refine ⟨52505978489636881389072209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35003985659757920926048139 52505978489636881389072209)
  ·
    refine ⟨39379483867227661041804157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52505978489636881389072209 39379483867227661041804157)
    ·
      refine ⟨14767306450210372890676559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39379483867227661041804157 14767306450210372890676559)
      ·
        refine ⟨22150959675315559336014839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14767306450210372890676559 22150959675315559336014839)
        ·
          refine ⟨33226439512973339004022259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22150959675315559336014839 33226439512973339004022259)
          ·
            refine ⟨49839659269460008506033389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33226439512973339004022259 49839659269460008506033389)
            ·
              refine ⟨18689872226047503189762521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49839659269460008506033389 18689872226047503189762521)
              ·
                refine ⟨14017404169535627392321891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18689872226047503189762521 14017404169535627392321891)
                ·
                  refine ⟨21026106254303441088482837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14017404169535627392321891 21026106254303441088482837)
                  ·
                    refine ⟨985598730670473801022633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21026106254303441088482837 985598730670473801022633)
                    ·
                      refine ⟨739199048002855350766975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 985598730670473801022633 739199048002855350766975)
                      ·
                        rfl

theorem cell23_1439585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_1439585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439585 prefixEnd_1439585 := by exact prefixLift 1439585
  have htrace : WordTrace (prefixWord ++ tailWord_1439585) baseStart_1439585 baseEnd_1439585 := by
    simpa [prefixWord, tailWord_1439585, baseEnd_1439585] using wordTrace_append hprefix tailTrace_1439585
  have hstable : (prefixWord ++ tailWord_1439585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439585).length < 2 ^ (prefixWord ++ tailWord_1439585).sum := by decide
  have hdescent : baseEnd_1439585 < baseStart_1439585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439628 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 3, 2, 6]
def baseStart_1439628 : Nat := 118140960795 + 1439628 * 2 ^ 59
def prefixEnd_1439628 : Nat := 4983230072969 + 3 ^ 40 * 1439628 * 2
def baseEnd_1439628 : Nat := 739221127670998682529277

theorem tailTrace_1439628 : CollatzResearch.WordTrace tailWord_1439628 prefixEnd_1439628 739221127670998682529277 := by
  unfold tailWord_1439628
  simp only [CollatzResearch.WordTrace]
  refine ⟨26253773414240549866443769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35005031218987399821925025 26253773414240549866443769)
  ·
    refine ⟨19690330060680412399832827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26253773414240549866443769 19690330060680412399832827)
    ·
      refine ⟨29535495091020618599749241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19690330060680412399832827 29535495091020618599749241)
      ·
        refine ⟨22151621318265463949811931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29535495091020618599749241 22151621318265463949811931)
        ·
          refine ⟨33227431977398195924717897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22151621318265463949811931 33227431977398195924717897)
          ·
            refine ⟨24920573983048646943538423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33227431977398195924717897 24920573983048646943538423)
            ·
              refine ⟨37380860974572970415307635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24920573983048646943538423 37380860974572970415307635)
              ·
                refine ⟨56071291461859455622961453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37380860974572970415307635 56071291461859455622961453)
                ·
                  refine ⟨21026734298197295858610545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56071291461859455622961453 21026734298197295858610545)
                  ·
                    refine ⟨15770050723647971893957909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21026734298197295858610545 15770050723647971893957909)
                    ·
                      refine ⟨739221127670998682529277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15770050723647971893957909 739221127670998682529277)
                      ·
                        rfl

theorem cell23_1439628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_1439628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439628 prefixEnd_1439628 := by exact prefixLift 1439628
  have htrace : WordTrace (prefixWord ++ tailWord_1439628) baseStart_1439628 baseEnd_1439628 := by
    simpa [prefixWord, tailWord_1439628, baseEnd_1439628] using wordTrace_append hprefix tailTrace_1439628
  have hstable : (prefixWord ++ tailWord_1439628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439628).length < 2 ^ (prefixWord ++ tailWord_1439628).sum := by decide
  have hdescent : baseEnd_1439628 < baseStart_1439628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439656 : List Nat := [2, 1, 6, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_1439656 : Nat := 118140960795 + 1439656 * 2 ^ 59
def prefixEnd_1439656 : Nat := 4983230072969 + 3 ^ 40 * 1439656 * 2
def baseEnd_1439656 : Nat := 739235505129324572979149

theorem tailTrace_1439656 : CollatzResearch.WordTrace tailWord_1439656 prefixEnd_1439656 739235505129324572979149 := by
  unfold tailWord_1439656
  simp only [CollatzResearch.WordTrace]
  refine ⟨26254284036189830257453411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35005712048253107009937881 26254284036189830257453411)
  ·
    refine ⟨39381426054284745386180117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26254284036189830257453411 39381426054284745386180117)
    ·
      refine ⟨1846004346294597439977193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39381426054284745386180117 1846004346294597439977193)
      ·
        refine ⟨1384503259720948079982895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1846004346294597439977193 1384503259720948079982895)
        ·
          refine ⟨2076754889581422119974343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1384503259720948079982895 2076754889581422119974343)
          ·
            refine ⟨3115132334372133179961515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2076754889581422119974343 3115132334372133179961515)
            ·
              refine ⟨4672698501558199769942273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3115132334372133179961515 4672698501558199769942273)
              ·
                refine ⟨3504523876168649827456705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4672698501558199769942273 3504523876168649827456705)
                ·
                  refine ⟨2628392907126487370592529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3504523876168649827456705 2628392907126487370592529)
                  ·
                    refine ⟨1971294680344865527944397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2628392907126487370592529 1971294680344865527944397)
                    ·
                      refine ⟨739235505129324572979149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1971294680344865527944397 739235505129324572979149)
                      ·
                        rfl

theorem cell23_1439656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_1439656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439656 prefixEnd_1439656 := by exact prefixLift 1439656
  have htrace : WordTrace (prefixWord ++ tailWord_1439656) baseStart_1439656 baseEnd_1439656 := by
    simpa [prefixWord, tailWord_1439656, baseEnd_1439656] using wordTrace_append hprefix tailTrace_1439656
  have hstable : (prefixWord ++ tailWord_1439656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439656).length < 2 ^ (prefixWord ++ tailWord_1439656).sum := by decide
  have hdescent : baseEnd_1439656 < baseStart_1439656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439669 : List Nat := [1, 3, 3, 2, 1, 2, 3, 1, 3, 1, 3]
def baseStart_1439669 : Nat := 118140960795 + 1439669 * 2 ^ 59
def prefixEnd_1439669 : Nat := 4983230072969 + 3 ^ 40 * 1439669 * 2
def baseEnd_1439669 : Nat := 739242180377833022116589

theorem tailTrace_1439669 : CollatzResearch.WordTrace tailWord_1439669 prefixEnd_1439669 739242180377833022116589 := by
  unfold tailWord_1439669
  simp only [CollatzResearch.WordTrace]
  refine ⟨52509042221332563735130061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35006028147555042490086707 52509042221332563735130061)
  ·
    refine ⟨19690890832999711400673773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52509042221332563735130061 19690890832999711400673773)
    ·
      refine ⟨7384084062374891775252665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19690890832999711400673773 7384084062374891775252665)
      ·
        refine ⟨5538063046781168831439499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7384084062374891775252665 5538063046781168831439499)
        ·
          refine ⟨8307094570171753247159249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5538063046781168831439499 8307094570171753247159249)
          ·
            refine ⟨6230320927628814935369437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8307094570171753247159249 6230320927628814935369437)
            ·
              refine ⟨2336370347860805600763539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6230320927628814935369437 2336370347860805600763539)
              ·
                refine ⟨3504555521791208401145309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2336370347860805600763539 3504555521791208401145309)
                ·
                  refine ⟨1314208320671703150429491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3504555521791208401145309 1314208320671703150429491)
                  ·
                    refine ⟨1971312481007554725644237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1314208320671703150429491 1971312481007554725644237)
                    ·
                      refine ⟨739242180377833022116589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1971312481007554725644237 739242180377833022116589)
                      ·
                        rfl

theorem cell23_1439669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_1439669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439669 prefixEnd_1439669 := by exact prefixLift 1439669
  have htrace : WordTrace (prefixWord ++ tailWord_1439669) baseStart_1439669 baseEnd_1439669 := by
    simpa [prefixWord, tailWord_1439669, baseEnd_1439669] using wordTrace_append hprefix tailTrace_1439669
  have hstable : (prefixWord ++ tailWord_1439669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439669).length < 2 ^ (prefixWord ++ tailWord_1439669).sum := by decide
  have hdescent : baseEnd_1439669 < baseStart_1439669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439676 : List Nat := [2, 2, 2, 5, 1, 2, 2, 1, 6]
def baseStart_1439676 : Nat := 118140960795 + 1439676 * 2 ^ 59
def prefixEnd_1439676 : Nat := 4983230072969 + 3 ^ 40 * 1439676 * 2
def baseEnd_1439676 : Nat := 82138419415823832747673

theorem tailTrace_1439676 : CollatzResearch.WordTrace tailWord_1439676 prefixEnd_1439676 82138419415823832747673 := by
  unfold tailWord_1439676
  simp only [CollatzResearch.WordTrace]
  refine ⟨26254648766153601965317441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35006198354871469287089921 26254648766153601965317441)
  ·
    refine ⟨19690986574615201473988081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26254648766153601965317441 19690986574615201473988081)
    ·
      refine ⟨14768239930961401105491061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19690986574615201473988081 14768239930961401105491061)
      ·
        refine ⟨1384522493527631353639787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14768239930961401105491061 1384522493527631353639787)
        ·
          refine ⟨2076783740291447030459681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1384522493527631353639787 2076783740291447030459681)
          ·
            refine ⟨1557587805218585272844761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2076783740291447030459681 1557587805218585272844761)
            ·
              refine ⟨1168190853913938954633571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1557587805218585272844761 1168190853913938954633571)
              ·
                refine ⟨1752286280870908431950357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168190853913938954633571 1752286280870908431950357)
                ·
                  refine ⟨82138419415823832747673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1752286280870908431950357 82138419415823832747673)
                  ·
                    rfl

theorem cell23_1439676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 6].length) (baseStart_1439676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439676 prefixEnd_1439676 := by exact prefixLift 1439676
  have htrace : WordTrace (prefixWord ++ tailWord_1439676) baseStart_1439676 baseEnd_1439676 := by
    simpa [prefixWord, tailWord_1439676, baseEnd_1439676] using wordTrace_append hprefix tailTrace_1439676
  have hstable : (prefixWord ++ tailWord_1439676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439676).length < 2 ^ (prefixWord ++ tailWord_1439676).sum := by decide
  have hdescent : baseEnd_1439676 < baseStart_1439676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439685 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 6, 4]
def baseStart_1439685 : Nat := 118140960795 + 1439685 * 2 ^ 59
def prefixEnd_1439685 : Nat := 4983230072969 + 3 ^ 40 * 1439685 * 2
def baseEnd_1439685 : Nat := 246416798689434986505505

theorem tailTrace_1439685 : CollatzResearch.WordTrace tailWord_1439685 prefixEnd_1439685 246416798689434986505505 := by
  unfold tailWord_1439685
  simp only [CollatzResearch.WordTrace]
  refine ⟨52509625789274598467712509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35006417192849732311808339 52509625789274598467712509)
  ·
    refine ⟨19691109670977974425392191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52509625789274598467712509 19691109670977974425392191)
    ·
      refine ⟨29536664506466961638088287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19691109670977974425392191 29536664506466961638088287)
      ·
        refine ⟨44304996759700442457132431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29536664506466961638088287 44304996759700442457132431)
        ·
          refine ⟨66457495139550663685698647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44304996759700442457132431 66457495139550663685698647)
          ·
            refine ⟨99686242709325995528547971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66457495139550663685698647 99686242709325995528547971)
            ·
              refine ⟨149529364063988993292821957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99686242709325995528547971 149529364063988993292821957)
              ·
                refine ⟨28036755761997936242404117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149529364063988993292821957 28036755761997936242404117)
                ·
                  refine ⟨1314222926343653261362693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28036755761997936242404117 1314222926343653261362693)
                  ·
                    refine ⟨246416798689434986505505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1314222926343653261362693 246416798689434986505505)
                    ·
                      rfl

theorem cell23_1439685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 4].length) (baseStart_1439685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439685 prefixEnd_1439685 := by exact prefixLift 1439685
  have htrace : WordTrace (prefixWord ++ tailWord_1439685) baseStart_1439685 baseEnd_1439685 := by
    simpa [prefixWord, tailWord_1439685, baseEnd_1439685] using wordTrace_append hprefix tailTrace_1439685
  have hstable : (prefixWord ++ tailWord_1439685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439685).length < 2 ^ (prefixWord ++ tailWord_1439685).sum := by decide
  have hdescent : baseEnd_1439685 < baseStart_1439685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439692 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 3, 1, 4]
def baseStart_1439692 : Nat := 118140960795 + 1439692 * 2 ^ 59
def prefixEnd_1439692 : Nat := 4983230072969 + 3 ^ 40 * 1439692 * 2
def baseEnd_1439692 : Nat := 739253990432886432128983

theorem tailTrace_1439692 : CollatzResearch.WordTrace tailWord_1439692 prefixEnd_1439692 739253990432886432128983 := by
  unfold tailWord_1439692
  simp only [CollatzResearch.WordTrace]
  refine ⟨26254940550124619331608665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35006587400166159108811553 26254940550124619331608665)
  ·
    refine ⟨19691205412593464498706499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26254940550124619331608665 19691205412593464498706499)
    ·
      refine ⟨29536808118890196748059749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19691205412593464498706499 29536808118890196748059749)
      ·
        refine ⟨5538151522291911890261203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29536808118890196748059749 5538151522291911890261203)
        ·
          refine ⟨8307227283437867835391805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5538151522291911890261203 8307227283437867835391805)
          ·
            refine ⟨3115210231289200438271927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8307227283437867835391805 3115210231289200438271927)
            ·
              refine ⟨4672815346933800657407891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3115210231289200438271927 4672815346933800657407891)
              ·
                refine ⟨7009223020400700986111837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4672815346933800657407891 7009223020400700986111837)
                ·
                  refine ⟨2628458632650262869791939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7009223020400700986111837 2628458632650262869791939)
                  ·
                    refine ⟨3942687948975394304687909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2628458632650262869791939 3942687948975394304687909)
                    ·
                      refine ⟨739253990432886432128983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3942687948975394304687909 739253990432886432128983)
                      ·
                        rfl

theorem cell23_1439692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_1439692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439692 prefixEnd_1439692 := by exact prefixLift 1439692
  have htrace : WordTrace (prefixWord ++ tailWord_1439692) baseStart_1439692 baseEnd_1439692 := by
    simpa [prefixWord, tailWord_1439692, baseEnd_1439692] using wordTrace_append hprefix tailTrace_1439692
  have hstable : (prefixWord ++ tailWord_1439692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439692).length < 2 ^ (prefixWord ++ tailWord_1439692).sum := by decide
  have hdescent : baseEnd_1439692 < baseStart_1439692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439712 : List Nat := [2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 3]
def baseStart_1439712 : Nat := 118140960795 + 1439712 * 2 ^ 59
def prefixEnd_1439712 : Nat := 4983230072969 + 3 ^ 40 * 1439712 * 2
def baseEnd_1439712 : Nat := 739264260045976353878891

theorem tailTrace_1439712 : CollatzResearch.WordTrace tailWord_1439712 prefixEnd_1439712 739264260045976353878891 := by
  unfold tailWord_1439712
  simp only [CollatzResearch.WordTrace]
  refine ⟨26255305280088391039472695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35007073706784521385963593 26255305280088391039472695)
  ·
    refine ⟨39382957920132586559209043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26255305280088391039472695 39382957920132586559209043)
    ·
      refine ⟨59074436880198879838813565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39382957920132586559209043 59074436880198879838813565)
      ·
        refine ⟨22152913830074579939555087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59074436880198879838813565 22152913830074579939555087)
        ·
          refine ⟨33229370745111869909332631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22152913830074579939555087 33229370745111869909332631)
          ·
            refine ⟨49844056117667804863998947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33229370745111869909332631 49844056117667804863998947)
            ·
              refine ⟨74766084176501707295998421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49844056117667804863998947 74766084176501707295998421)
              ·
                refine ⟨1752330097886758764749963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 74766084176501707295998421 1752330097886758764749963)
                ·
                  refine ⟨2628495146830138147124945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752330097886758764749963 2628495146830138147124945)
                  ·
                    refine ⟨1971371360122603610343709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2628495146830138147124945 1971371360122603610343709)
                    ·
                      refine ⟨739264260045976353878891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1971371360122603610343709 739264260045976353878891)
                      ·
                        rfl

theorem cell23_1439712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_1439712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439712 prefixEnd_1439712 := by exact prefixLift 1439712
  have htrace : WordTrace (prefixWord ++ tailWord_1439712) baseStart_1439712 baseEnd_1439712 := by
    simpa [prefixWord, tailWord_1439712, baseEnd_1439712] using wordTrace_append hprefix tailTrace_1439712
  have hstable : (prefixWord ++ tailWord_1439712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439712).length < 2 ^ (prefixWord ++ tailWord_1439712).sum := by decide
  have hdescent : baseEnd_1439712 < baseStart_1439712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439745 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 2, 7]
def baseStart_1439745 : Nat := 118140960795 + 1439745 * 2 ^ 59
def prefixEnd_1439745 : Nat := 4983230072969 + 3 ^ 40 * 1439745 * 2
def baseEnd_1439745 : Nat := 246427068302524908255413

theorem tailTrace_1439745 : CollatzResearch.WordTrace tailWord_1439745 prefixEnd_1439745 246427068302524908255413 := by
  unfold tailWord_1439745
  simp only [CollatzResearch.WordTrace]
  refine ⟨52511814169057228714896689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35007876112704819143264459 52511814169057228714896689)
  ·
    refine ⟨39383860626792921536172517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52511814169057228714896689 39383860626792921536172517)
    ·
      refine ⟨7384473867523672788032347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39383860626792921536172517 7384473867523672788032347)
      ·
        refine ⟨11076710801285509182048521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7384473867523672788032347 11076710801285509182048521)
        ·
          refine ⟨8307533100964131886536391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11076710801285509182048521 8307533100964131886536391)
          ·
            refine ⟨12461299651446197829804587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8307533100964131886536391 12461299651446197829804587)
            ·
              refine ⟨18691949477169296744706881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12461299651446197829804587 18691949477169296744706881)
              ·
                refine ⟨14018962107876972558530161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18691949477169296744706881 14018962107876972558530161)
                ·
                  refine ⟨10514221580907729418897621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14018962107876972558530161 10514221580907729418897621)
                  ·
                    refine ⟨246427068302524908255413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10514221580907729418897621 246427068302524908255413)
                    ·
                      rfl

theorem cell23_1439745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_1439745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439745 prefixEnd_1439745 := by exact prefixLift 1439745
  have htrace : WordTrace (prefixWord ++ tailWord_1439745) baseStart_1439745 baseEnd_1439745 := by
    simpa [prefixWord, tailWord_1439745, baseEnd_1439745] using wordTrace_append hprefix tailTrace_1439745
  have hstable : (prefixWord ++ tailWord_1439745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439745).length < 2 ^ (prefixWord ++ tailWord_1439745).sum := by decide
  have hdescent : baseEnd_1439745 < baseStart_1439745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439755 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 5]
def baseStart_1439755 : Nat := 118140960795 + 1439755 * 2 ^ 59
def prefixEnd_1439755 : Nat := 4983230072969 + 3 ^ 40 * 1439755 * 2
def baseEnd_1439755 : Nat := 739286339714119685641193

theorem tailTrace_1439755 : CollatzResearch.WordTrace tailWord_1439755 prefixEnd_1439755 739286339714119685641193 := by
  unfold tailWord_1439755
  simp only [CollatzResearch.WordTrace]
  refine ⟨52512178899021000422760719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35008119266014000281840479 52512178899021000422760719)
  ·
    refine ⟨78768268348531500634141079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52512178899021000422760719 78768268348531500634141079)
    ·
      refine ⟨118152402522797250951211619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78768268348531500634141079 118152402522797250951211619)
      ·
        refine ⟨177228603784195876426817429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118152402522797250951211619 177228603784195876426817429)
        ·
          refine ⟨8307590802384181707507067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 177228603784195876426817429 8307590802384181707507067)
          ·
            refine ⟨12461386203576272561260601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8307590802384181707507067 12461386203576272561260601)
            ·
              refine ⟨9346039652682204420945451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12461386203576272561260601 9346039652682204420945451)
              ·
                refine ⟨14019059479023306631418177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9346039652682204420945451 14019059479023306631418177)
                ·
                  refine ⟨10514294609267479973563633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14019059479023306631418177 10514294609267479973563633)
                  ·
                    refine ⟨7885720956950609980172725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10514294609267479973563633 7885720956950609980172725)
                    ·
                      refine ⟨739286339714119685641193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7885720956950609980172725 739286339714119685641193)
                      ·
                        rfl

theorem cell23_1439755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 5].length) (baseStart_1439755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439755 prefixEnd_1439755 := by exact prefixLift 1439755
  have htrace : WordTrace (prefixWord ++ tailWord_1439755) baseStart_1439755 baseEnd_1439755 := by
    simpa [prefixWord, tailWord_1439755, baseEnd_1439755] using wordTrace_append hprefix tailTrace_1439755
  have hstable : (prefixWord ++ tailWord_1439755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439755).length < 2 ^ (prefixWord ++ tailWord_1439755).sum := by decide
  have hdescent : baseEnd_1439755 < baseStart_1439755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439757 : List Nat := [1, 7, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_1439757 : Nat := 118140960795 + 1439757 * 2 ^ 59
def prefixEnd_1439757 : Nat := 4983230072969 + 3 ^ 40 * 1439757 * 2
def baseEnd_1439757 : Nat := 246429122225142892605395

theorem tailTrace_1439757 : CollatzResearch.WordTrace tailWord_1439757 prefixEnd_1439757 246429122225142892605395 := by
  unfold tailWord_1439757
  simp only [CollatzResearch.WordTrace]
  refine ⟨52512251845013754764333525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35008167896675836509555683 52512251845013754764333525)
  ·
    refine ⟨1230755902617509877289067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 52512251845013754764333525 1230755902617509877289067)
    ·
      refine ⟨1846133853926264815933601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1230755902617509877289067 1846133853926264815933601)
      ·
        refine ⟨1384600390444698611950201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1846133853926264815933601 1384600390444698611950201)
        ·
          refine ⟨1038450292833523958962651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1384600390444698611950201 1038450292833523958962651)
          ·
            refine ⟨1557675439250285938443977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038450292833523958962651 1557675439250285938443977)
            ·
              refine ⟨1168256579437714453832983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1557675439250285938443977 1168256579437714453832983)
              ·
                refine ⟨1752384869156571680749475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168256579437714453832983 1752384869156571680749475)
                ·
                  refine ⟨2628577303734857521124213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752384869156571680749475 2628577303734857521124213)
                  ·
                    refine ⟨246429122225142892605395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2628577303734857521124213 246429122225142892605395)
                    ·
                      rfl

theorem cell23_1439757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_1439757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439757 prefixEnd_1439757 := by exact prefixLift 1439757
  have htrace : WordTrace (prefixWord ++ tailWord_1439757) baseStart_1439757 baseEnd_1439757 := by
    simpa [prefixWord, tailWord_1439757, baseEnd_1439757] using wordTrace_append hprefix tailTrace_1439757
  have hstable : (prefixWord ++ tailWord_1439757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439757).length < 2 ^ (prefixWord ++ tailWord_1439757).sum := by decide
  have hdescent : baseEnd_1439757 < baseStart_1439757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439775 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 4, 6]
def baseStart_1439775 : Nat := 118140960795 + 1439775 * 2 ^ 59
def prefixEnd_1439775 : Nat := 4983230072969 + 3 ^ 40 * 1439775 * 2
def baseEnd_1439775 : Nat := 246432203109069869130367

theorem tailTrace_1439775 : CollatzResearch.WordTrace tailWord_1439775 prefixEnd_1439775 246432203109069869130367 := by
  unfold tailWord_1439775
  simp only [CollatzResearch.WordTrace]
  refine ⟨52512908358948543838488779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35008605572632362558992519 52512908358948543838488779)
  ·
    refine ⟨78769362538422815757733169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52512908358948543838488779 78769362538422815757733169)
    ·
      refine ⟨59077021903817111818299877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78769362538422815757733169 59077021903817111818299877)
      ·
        refine ⟨11076941606965708465931227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59077021903817111818299877 11076941606965708465931227)
        ·
          refine ⟨16615412410448562698896841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11076941606965708465931227 16615412410448562698896841)
          ·
            refine ⟨12461559307836422024172631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16615412410448562698896841 12461559307836422024172631)
            ·
              refine ⟨18692338961754633036258947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12461559307836422024172631 18692338961754633036258947)
              ·
                refine ⟨28038508442631949554388421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18692338961754633036258947 28038508442631949554388421)
                ·
                  refine ⟨5257220332993490541447829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28038508442631949554388421 5257220332993490541447829)
                  ·
                    refine ⟨246432203109069869130367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5257220332993490541447829 246432203109069869130367)
                    ·
                      rfl

theorem cell23_1439775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 6].length) (baseStart_1439775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439775 prefixEnd_1439775 := by exact prefixLift 1439775
  have htrace : WordTrace (prefixWord ++ tailWord_1439775) baseStart_1439775 baseEnd_1439775 := by
    simpa [prefixWord, tailWord_1439775, baseEnd_1439775] using wordTrace_append hprefix tailTrace_1439775
  have hstable : (prefixWord ++ tailWord_1439775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439775).length < 2 ^ (prefixWord ++ tailWord_1439775).sum := by decide
  have hdescent : baseEnd_1439775 < baseStart_1439775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439799 : List Nat := [1, 1, 3, 1, 2, 2, 5, 1, 1, 4, 2]
def baseStart_1439799 : Nat := 118140960795 + 1439799 * 2 ^ 59
def prefixEnd_1439799 : Nat := 4983230072969 + 3 ^ 40 * 1439799 * 2
def baseEnd_1439799 : Nat := 739308932862917513490991

theorem tailTrace_1439799 : CollatzResearch.WordTrace tailWord_1439799 prefixEnd_1439799 739308932862917513490991 := by
  unfold tailWord_1439799
  simp only [CollatzResearch.WordTrace]
  refine ⟨52513783710861595937362451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35009189140574397291574967 52513783710861595937362451)
  ·
    refine ⟨78770675566292393906043677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52513783710861595937362451 78770675566292393906043677)
    ·
      refine ⟨29539003337359647714766379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78770675566292393906043677 29539003337359647714766379)
      ·
        refine ⟨44308505006039471572149569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29539003337359647714766379 44308505006039471572149569)
        ·
          refine ⟨33231378754529603679112177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44308505006039471572149569 33231378754529603679112177)
          ·
            refine ⟨24923534065897202759334133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33231378754529603679112177 24923534065897202759334133)
            ·
              refine ⟨2336581318677862758687575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24923534065897202759334133 2336581318677862758687575)
              ·
                refine ⟨3504871978016794138031363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2336581318677862758687575 3504871978016794138031363)
                ·
                  refine ⟨5257307967025191207047045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3504871978016794138031363 5257307967025191207047045)
                  ·
                    refine ⟨985745243817223351321321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5257307967025191207047045 985745243817223351321321)
                    ·
                      refine ⟨739308932862917513490991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 985745243817223351321321 739308932862917513490991)
                      ·
                        rfl

theorem cell23_1439799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 4, 2].length) (baseStart_1439799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439799 prefixEnd_1439799 := by exact prefixLift 1439799
  have htrace : WordTrace (prefixWord ++ tailWord_1439799) baseStart_1439799 baseEnd_1439799 := by
    simpa [prefixWord, tailWord_1439799, baseEnd_1439799] using wordTrace_append hprefix tailTrace_1439799
  have hstable : (prefixWord ++ tailWord_1439799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439799).length < 2 ^ (prefixWord ++ tailWord_1439799).sum := by decide
  have hdescent : baseEnd_1439799 < baseStart_1439799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439869 : List Nat := [1, 4, 1, 1, 3, 3, 2, 1, 2, 5]
def baseStart_1439869 : Nat := 118140960795 + 1439869 * 2 ^ 59
def prefixEnd_1439869 : Nat := 4983230072969 + 3 ^ 40 * 1439869 * 2
def baseEnd_1439869 : Nat := 246448292169577413205223

theorem tailTrace_1439869 : CollatzResearch.WordTrace tailWord_1439869 prefixEnd_1439869 246448292169577413205223 := by
  unfold tailWord_1439869
  simp only [CollatzResearch.WordTrace]
  refine ⟨52516336820607997892410661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35010891213738665261607107 52516336820607997892410661)
  ·
    refine ⟨9846813153863999604826999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52516336820607997892410661 9846813153863999604826999)
    ·
      refine ⟨14770219730795999407240499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9846813153863999604826999 14770219730795999407240499)
      ·
        refine ⟨22155329596193999110860749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14770219730795999407240499 22155329596193999110860749)
        ·
          refine ⟨8308248598572749666572781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22155329596193999110860749 8308248598572749666572781)
          ·
            refine ⟨3115593224464781124964793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8308248598572749666572781 3115593224464781124964793)
            ·
              refine ⟨2336694918348585843723595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3115593224464781124964793 2336694918348585843723595)
              ·
                refine ⟨3505042377522878765585393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2336694918348585843723595 3505042377522878765585393)
                ·
                  refine ⟨2628781783142159074189045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3505042377522878765585393 2628781783142159074189045)
                  ·
                    refine ⟨246448292169577413205223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2628781783142159074189045 246448292169577413205223)
                    ·
                      rfl

theorem cell23_1439869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_1439869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439869 prefixEnd_1439869 := by exact prefixLift 1439869
  have htrace : WordTrace (prefixWord ++ tailWord_1439869) baseStart_1439869 baseEnd_1439869 := by
    simpa [prefixWord, tailWord_1439869, baseEnd_1439869] using wordTrace_append hprefix tailTrace_1439869
  have hstable : (prefixWord ++ tailWord_1439869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439869).length < 2 ^ (prefixWord ++ tailWord_1439869).sum := by decide
  have hdescent : baseEnd_1439869 < baseStart_1439869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439906 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 1, 6, 2]
def baseStart_1439906 : Nat := 118140960795 + 1439906 * 2 ^ 59
def prefixEnd_1439906 : Nat := 4983230072969 + 3 ^ 40 * 1439906 * 2
def baseEnd_1439906 : Nat := 739363875292948594852999

theorem tailTrace_1439906 : CollatzResearch.WordTrace tailWord_1439906 prefixEnd_1439906 739363875292948594852999 := by
  unfold tailWord_1439906
  simp only [CollatzResearch.WordTrace]
  refine ⟨13129421580368488302876893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35011790880982635474338381 13129421580368488302876893)
  ·
    refine ⟨4923533092638183113578835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13129421580368488302876893 4923533092638183113578835)
    ·
      refine ⟨7385299638957274670368253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4923533092638183113578835 7385299638957274670368253)
      ·
        refine ⟨2769487364608978001388095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7385299638957274670368253 2769487364608978001388095)
        ·
          refine ⟨4154231046913467002082143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2769487364608978001388095 4154231046913467002082143)
          ·
            refine ⟨6231346570370200503123215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4154231046913467002082143 6231346570370200503123215)
            ·
              refine ⟨9347019855555300754684823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6231346570370200503123215 9347019855555300754684823)
              ·
                refine ⟨14020529783332951132027235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9347019855555300754684823 14020529783332951132027235)
                ·
                  refine ⟨21030794674999426698040853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14020529783332951132027235 21030794674999426698040853)
                  ·
                    refine ⟨985818500390598126470665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21030794674999426698040853 985818500390598126470665)
                    ·
                      refine ⟨739363875292948594852999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 985818500390598126470665 739363875292948594852999)
                      ·
                        rfl

theorem cell23_1439906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_1439906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439906 prefixEnd_1439906 := by exact prefixLift 1439906
  have htrace : WordTrace (prefixWord ++ tailWord_1439906) baseStart_1439906 baseEnd_1439906 := by
    simpa [prefixWord, tailWord_1439906, baseEnd_1439906] using wordTrace_append hprefix tailTrace_1439906
  have hstable : (prefixWord ++ tailWord_1439906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439906).length < 2 ^ (prefixWord ++ tailWord_1439906).sum := by decide
  have hdescent : baseEnd_1439906 < baseStart_1439906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439976 : List Nat := [2, 1, 4, 1, 2, 3, 2, 2, 1, 5]
def baseStart_1439976 : Nat := 118140960795 + 1439976 * 2 ^ 59
def prefixEnd_1439976 : Nat := 4983230072969 + 3 ^ 40 * 1439976 * 2
def baseEnd_1439976 : Nat := 246466606312921106992559

theorem tailTrace_1439976 : CollatzResearch.WordTrace tailWord_1439976 prefixEnd_1439976 246466606312921106992559 := by
  unfold tailWord_1439976
  simp only [CollatzResearch.WordTrace]
  refine ⟨26260119715610177583277891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35013492954146903444370521 26260119715610177583277891)
  ·
    refine ⟨39390179573415266374916837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26260119715610177583277891 39390179573415266374916837)
    ·
      refine ⟨7385658670015362445296907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39390179573415266374916837 7385658670015362445296907)
      ·
        refine ⟨11078488005023043667945361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7385658670015362445296907 11078488005023043667945361)
        ·
          refine ⟨8308866003767282750959021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11078488005023043667945361 8308866003767282750959021)
          ·
            refine ⟨3115824751412731031609633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8308866003767282750959021 3115824751412731031609633)
            ·
              refine ⟨2336868563559548273707225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3115824751412731031609633 2336868563559548273707225)
              ·
                refine ⟨1752651422669661205280419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2336868563559548273707225 1752651422669661205280419)
                ·
                  refine ⟨2628977134004491807920629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752651422669661205280419 2628977134004491807920629)
                  ·
                    refine ⟨246466606312921106992559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2628977134004491807920629 246466606312921106992559)
                    ·
                      rfl

theorem cell23_1439976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_1439976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439976 prefixEnd_1439976 := by exact prefixLift 1439976
  have htrace : WordTrace (prefixWord ++ tailWord_1439976) baseStart_1439976 baseEnd_1439976 := by
    simpa [prefixWord, tailWord_1439976, baseEnd_1439976] using wordTrace_append hprefix tailTrace_1439976
  have hstable : (prefixWord ++ tailWord_1439976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439976).length < 2 ^ (prefixWord ++ tailWord_1439976).sum := by decide
  have hdescent : baseEnd_1439976 < baseStart_1439976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439979 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 2, 6, 2]
def baseStart_1439979 : Nat := 118140960795 + 1439979 * 2 ^ 59
def prefixEnd_1439979 : Nat := 4983230072969 + 3 ^ 40 * 1439979 * 2
def baseEnd_1439979 : Nat := 739401359380726809240163

theorem tailTrace_1439979 : CollatzResearch.WordTrace tailWord_1439979 prefixEnd_1439979 739401359380726809240163 := by
  unfold tailWord_1439979
  simp only [CollatzResearch.WordTrace]
  refine ⟨52520348850209486678914991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35013565900139657785943327 52520348850209486678914991)
  ·
    refine ⟨78780523275314230018372487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52520348850209486678914991 78780523275314230018372487)
    ·
      refine ⟨118170784912971345027558731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78780523275314230018372487 118170784912971345027558731)
      ·
        refine ⟨177256177369457017541338097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118170784912971345027558731 177256177369457017541338097)
        ·
          refine ⟨132942133027092763156003573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177256177369457017541338097 132942133027092763156003573)
          ·
            refine ⟨12463324971289946545875335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132942133027092763156003573 12463324971289946545875335)
            ·
              refine ⟨18694987456934919818813003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12463324971289946545875335 18694987456934919818813003)
              ·
                refine ⟨28042481185402379728219505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18694987456934919818813003 28042481185402379728219505)
                ·
                  refine ⟨21031860889051784796164629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28042481185402379728219505 21031860889051784796164629)
                  ·
                    refine ⟨985868479174302412320217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21031860889051784796164629 985868479174302412320217)
                    ·
                      refine ⟨739401359380726809240163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 985868479174302412320217 739401359380726809240163)
                      ·
                        rfl

theorem cell23_1439979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 6, 2].length) (baseStart_1439979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439979 prefixEnd_1439979 := by exact prefixLift 1439979
  have htrace : WordTrace (prefixWord ++ tailWord_1439979) baseStart_1439979 baseEnd_1439979 := by
    simpa [prefixWord, tailWord_1439979, baseEnd_1439979] using wordTrace_append hprefix tailTrace_1439979
  have hstable : (prefixWord ++ tailWord_1439979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439979).length < 2 ^ (prefixWord ++ tailWord_1439979).sum := by decide
  have hdescent : baseEnd_1439979 < baseStart_1439979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439990 : List Nat := [5, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3]
def baseStart_1439990 : Nat := 118140960795 + 1439990 * 2 ^ 59
def prefixEnd_1439990 : Nat := 4983230072969 + 3 ^ 40 * 1439990 * 2
def baseEnd_1439990 : Nat := 739407007667926266202613

theorem tailTrace_1439990 : CollatzResearch.WordTrace tailWord_1439990 prefixEnd_1439990 739407007667926266202613 := by
  unfold tailWord_1439990
  simp only [CollatzResearch.WordTrace]
  refine ⟨3282546878323102222347839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35013833368779757038376949 3282546878323102222347839)
  ·
    refine ⟨4923820317484653333521759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3282546878323102222347839 4923820317484653333521759)
    ·
      refine ⟨7385730476226980000282639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4923820317484653333521759 7385730476226980000282639)
      ·
        refine ⟨11078595714340470000423959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7385730476226980000282639 11078595714340470000423959)
        ·
          refine ⟨16617893571510705000635939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11078595714340470000423959 16617893571510705000635939)
          ·
            refine ⟨24926840357266057500953909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16617893571510705000635939 24926840357266057500953909)
            ·
              refine ⟨2336891283493692890714429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24926840357266057500953909 2336891283493692890714429)
              ·
                refine ⟨876334231310134834017911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2336891283493692890714429 876334231310134834017911)
                ·
                  refine ⟨1314501346965202251026867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876334231310134834017911 1314501346965202251026867)
                  ·
                    refine ⟨1971752020447803376540301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1314501346965202251026867 1971752020447803376540301)
                    ·
                      refine ⟨739407007667926266202613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1971752020447803376540301 739407007667926266202613)
                      ·
                        rfl

theorem cell23_1439990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_1439990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439990 prefixEnd_1439990 := by exact prefixLift 1439990
  have htrace : WordTrace (prefixWord ++ tailWord_1439990) baseStart_1439990 baseEnd_1439990 := by
    simpa [prefixWord, tailWord_1439990, baseEnd_1439990] using wordTrace_append hprefix tailTrace_1439990
  have hstable : (prefixWord ++ tailWord_1439990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439990).length < 2 ^ (prefixWord ++ tailWord_1439990).sum := by decide
  have hdescent : baseEnd_1439990 < baseStart_1439990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439996 : List Nat := [2, 2, 2, 1, 4, 1, 2, 3, 1, 1, 4]
def baseStart_1439996 : Nat := 118140960795 + 1439996 * 2 ^ 59
def prefixEnd_1439996 : Nat := 4983230072969 + 3 ^ 40 * 1439996 * 2
def baseEnd_1439996 : Nat := 739410088551853242727585

theorem tailTrace_1439996 : CollatzResearch.WordTrace tailWord_1439996 prefixEnd_1439996 739410088551853242727585 := by
  unfold tailWord_1439996
  simp only [CollatzResearch.WordTrace]
  refine ⟨26260484445573949291141921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35013979260765265721522561 26260484445573949291141921)
  ·
    refine ⟨19695363334180461968356441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26260484445573949291141921 19695363334180461968356441)
    ·
      refine ⟨14771522500635346476267331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19695363334180461968356441 14771522500635346476267331)
      ·
        refine ⟨22157283750953019714400997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14771522500635346476267331 22157283750953019714400997)
        ·
          refine ⟨4154490703303691196450187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22157283750953019714400997 4154490703303691196450187)
          ·
            refine ⟨6231736054955536794675281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4154490703303691196450187 6231736054955536794675281)
            ·
              refine ⟨4673802041216652596006461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6231736054955536794675281 4673802041216652596006461)
              ·
                refine ⟨1752675765456244723502423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4673802041216652596006461 1752675765456244723502423)
                ·
                  refine ⟨2629013648184367085253635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752675765456244723502423 2629013648184367085253635)
                  ·
                    refine ⟨3943520472276550627880453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2629013648184367085253635 3943520472276550627880453)
                    ·
                      refine ⟨739410088551853242727585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3943520472276550627880453 739410088551853242727585)
                      ·
                        rfl

theorem cell23_1439996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_1439996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439996 prefixEnd_1439996 := by exact prefixLift 1439996
  have htrace : WordTrace (prefixWord ++ tailWord_1439996) baseStart_1439996 baseEnd_1439996 := by
    simpa [prefixWord, tailWord_1439996, baseEnd_1439996] using wordTrace_append hprefix tailTrace_1439996
  have hstable : (prefixWord ++ tailWord_1439996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439996).length < 2 ^ (prefixWord ++ tailWord_1439996).sum := by decide
  have hdescent : baseEnd_1439996 < baseStart_1439996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1439999 : List Nat := [1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 5]
def baseStart_1439999 : Nat := 118140960795 + 1439999 * 2 ^ 59
def prefixEnd_1439999 : Nat := 4983230072969 + 3 ^ 40 * 1439999 * 2
def baseEnd_1439999 : Nat := 739411628993816730990071

theorem tailTrace_1439999 : CollatzResearch.WordTrace tailWord_1439999 prefixEnd_1439999 739411628993816730990071 := by
  unfold tailWord_1439999
  simp only [CollatzResearch.WordTrace]
  refine ⟨52521078310137030094643051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35014052206758020063095367 52521078310137030094643051)
  ·
    refine ⟨78781617465205545141964577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52521078310137030094643051 78781617465205545141964577)
    ·
      refine ⟨59086213098904158856473433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78781617465205545141964577 59086213098904158856473433)
      ·
        refine ⟨44314659824178119142355075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59086213098904158856473433 44314659824178119142355075)
        ·
          refine ⟨66471989736267178713532613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44314659824178119142355075 66471989736267178713532613)
          ·
            refine ⟨12463498075550096008787365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66471989736267178713532613 12463498075550096008787365)
            ·
              refine ⟨2336905889165643001647631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12463498075550096008787365 2336905889165643001647631)
              ·
                refine ⟨3505358833748464502471447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2336905889165643001647631 3505358833748464502471447)
                ·
                  refine ⟨5258038250622696753707171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3505358833748464502471447 5258038250622696753707171)
                  ·
                    refine ⟨7887057375934045130560757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5258038250622696753707171 7887057375934045130560757)
                    ·
                      refine ⟨739411628993816730990071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7887057375934045130560757 739411628993816730990071)
                      ·
                        rfl

theorem cell23_1439999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_1439999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1439999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1439999 prefixEnd_1439999 := by exact prefixLift 1439999
  have htrace : WordTrace (prefixWord ++ tailWord_1439999) baseStart_1439999 baseEnd_1439999 := by
    simpa [prefixWord, tailWord_1439999, baseEnd_1439999] using wordTrace_append hprefix tailTrace_1439999
  have hstable : (prefixWord ++ tailWord_1439999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1439999).length < 2 ^ (prefixWord ++ tailWord_1439999).sum := by decide
  have hdescent : baseEnd_1439999 < baseStart_1439999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1439999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440007 : List Nat := [1, 1, 4, 5, 2, 1, 1, 1, 3, 1, 3]
def baseStart_1440007 : Nat := 118140960795 + 1440007 * 2 ^ 59
def prefixEnd_1440007 : Nat := 4983230072969 + 3 ^ 40 * 1440007 * 2
def baseEnd_1440007 : Nat := 739415736839052699690035

theorem tailTrace_1440007 : CollatzResearch.WordTrace tailWord_1440007 prefixEnd_1440007 739415736839052699690035 := by
  unfold tailWord_1440007
  simp only [CollatzResearch.WordTrace]
  refine ⟨52521370094108047460934275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35014246729405364973956183 52521370094108047460934275)
  ·
    refine ⟨78782055141162071191401413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52521370094108047460934275 78782055141162071191401413)
    ·
      refine ⟨14771635338967888348387765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78782055141162071191401413 14771635338967888348387765)
      ·
        refine ⟨1384840813028239532661353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14771635338967888348387765 1384840813028239532661353)
        ·
          refine ⟨1038630609771179649496015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1384840813028239532661353 1038630609771179649496015)
          ·
            refine ⟨1557945914656769474244023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038630609771179649496015 1557945914656769474244023)
            ·
              refine ⟨2336918871985154211366035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1557945914656769474244023 2336918871985154211366035)
              ·
                refine ⟨3505378307977731317049053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2336918871985154211366035 3505378307977731317049053)
                ·
                  refine ⟨1314516865491649243893395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3505378307977731317049053 1314516865491649243893395)
                  ·
                    refine ⟨1971775298237473865840093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1314516865491649243893395 1971775298237473865840093)
                    ·
                      refine ⟨739415736839052699690035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1971775298237473865840093 739415736839052699690035)
                      ·
                        rfl

theorem cell23_1440007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_1440007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440007 prefixEnd_1440007 := by exact prefixLift 1440007
  have htrace : WordTrace (prefixWord ++ tailWord_1440007) baseStart_1440007 baseEnd_1440007 := by
    simpa [prefixWord, tailWord_1440007, baseEnd_1440007] using wordTrace_append hprefix tailTrace_1440007
  have hstable : (prefixWord ++ tailWord_1440007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440007).length < 2 ^ (prefixWord ++ tailWord_1440007).sum := by decide
  have hdescent : baseEnd_1440007 < baseStart_1440007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440023 : List Nat := [1, 1, 3, 4, 1, 2, 4, 1, 2, 4]
def baseStart_1440023 : Nat := 118140960795 + 1440023 * 2 ^ 59
def prefixEnd_1440023 : Nat := 4983230072969 + 3 ^ 40 * 1440023 * 2
def baseEnd_1440023 : Nat := 246474650843174879029987

theorem tailTrace_1440023 : CollatzResearch.WordTrace tailWord_1440023 prefixEnd_1440023 246474650843174879029987 := by
  unfold tailWord_1440023
  simp only [CollatzResearch.WordTrace]
  refine ⟨52521953662050082193516723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35014635774700054795677815 52521953662050082193516723)
  ·
    refine ⟨78782930493075123290275085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52521953662050082193516723 78782930493075123290275085)
    ·
      refine ⟨29543598934903171233853157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78782930493075123290275085 29543598934903171233853157)
      ·
        refine ⟨5539424800294344606347467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29543598934903171233853157 5539424800294344606347467)
        ·
          refine ⟨8309137200441516909521201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5539424800294344606347467 8309137200441516909521201)
          ·
            refine ⟨6231852900331137682140901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8309137200441516909521201 6231852900331137682140901)
            ·
              refine ⟨1168472418812088315401419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6231852900331137682140901 1168472418812088315401419)
              ·
                refine ⟨1752708628218132473102129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168472418812088315401419 1752708628218132473102129)
                ·
                  refine ⟨1314531471163599354826597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1752708628218132473102129 1314531471163599354826597)
                  ·
                    refine ⟨246474650843174879029987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1314531471163599354826597 246474650843174879029987)
                    ·
                      rfl

theorem cell23_1440023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 2, 4].length) (baseStart_1440023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440023 prefixEnd_1440023 := by exact prefixLift 1440023
  have htrace : WordTrace (prefixWord ++ tailWord_1440023) baseStart_1440023 baseEnd_1440023 := by
    simpa [prefixWord, tailWord_1440023, baseEnd_1440023] using wordTrace_append hprefix tailTrace_1440023
  have hstable : (prefixWord ++ tailWord_1440023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440023).length < 2 ^ (prefixWord ++ tailWord_1440023).sum := by decide
  have hdescent : baseEnd_1440023 < baseStart_1440023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440030 : List Nat := [4, 3, 2, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_1440030 : Nat := 118140960795 + 1440030 * 2 ^ 59
def prefixEnd_1440030 : Nat := 4983230072969 + 3 ^ 40 * 1440030 * 2
def baseEnd_1440030 : Nat := 739427546894106109702429

theorem tailTrace_1440030 : CollatzResearch.WordTrace tailWord_1440030 prefixEnd_1440030 739427546894106109702429 := by
  unfold tailWord_1440030
  simp only [CollatzResearch.WordTrace]
  refine ⟨6565276121628090298627693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35014805982016481592681029 6565276121628090298627693)
  ·
    refine ⟨2461978545610533861985385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6565276121628090298627693 2461978545610533861985385)
    ·
      refine ⟨1846483909207900396489039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2461978545610533861985385 1846483909207900396489039)
      ·
        refine ⟨2769725863811850594733559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1846483909207900396489039 2769725863811850594733559)
        ·
          refine ⟨4154588795717775892100339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2769725863811850594733559 4154588795717775892100339)
          ·
            refine ⟨6231883193576663838150509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4154588795717775892100339 6231883193576663838150509)
            ·
              refine ⟨2336956197591248939306441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6231883193576663838150509 2336956197591248939306441)
              ·
                refine ⟨1752717148193436704479831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2336956197591248939306441 1752717148193436704479831)
                ·
                  refine ⟨2629075722290155056719747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752717148193436704479831 2629075722290155056719747)
                  ·
                    refine ⟨3943613583435232585079621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2629075722290155056719747 3943613583435232585079621)
                    ·
                      refine ⟨739427546894106109702429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3943613583435232585079621 739427546894106109702429)
                      ·
                        rfl

theorem cell23_1440030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_1440030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440030 prefixEnd_1440030 := by exact prefixLift 1440030
  have htrace : WordTrace (prefixWord ++ tailWord_1440030) baseStart_1440030 baseEnd_1440030 := by
    simpa [prefixWord, tailWord_1440030, baseEnd_1440030] using wordTrace_append hprefix tailTrace_1440030
  have hstable : (prefixWord ++ tailWord_1440030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440030).length < 2 ^ (prefixWord ++ tailWord_1440030).sum := by decide
  have hdescent : baseEnd_1440030 < baseStart_1440030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440050 : List Nat := [3, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3]
def baseStart_1440050 : Nat := 118140960795 + 1440050 * 2 ^ 59
def prefixEnd_1440050 : Nat := 4983230072969 + 3 ^ 40 * 1440050 * 2
def baseEnd_1440050 : Nat := 739437816507196031452337

theorem tailTrace_1440050 : CollatzResearch.WordTrace tailWord_1440050 prefixEnd_1440050 739437816507196031452337 := by
  unfold tailWord_1440050
  simp only [CollatzResearch.WordTrace]
  refine ⟨13130734608238066451187401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35015292288634843869833069 13130734608238066451187401)
  ·
    refine ⟨9848050956178549838390551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13130734608238066451187401 9848050956178549838390551)
    ·
      refine ⟨14772076434267824757585827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9848050956178549838390551 14772076434267824757585827)
      ·
        refine ⟨22158114651401737136378741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14772076434267824757585827 22158114651401737136378741)
        ·
          refine ⟨2077323248568912856535507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22158114651401737136378741 2077323248568912856535507)
          ·
            refine ⟨3115984872853369284803261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2077323248568912856535507 3115984872853369284803261)
            ·
              refine ⟨1168494327320013481801223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3115984872853369284803261 1168494327320013481801223)
              ·
                refine ⟨1752741490980020222701835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168494327320013481801223 1752741490980020222701835)
                ·
                  refine ⟨2629112236470030334052753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752741490980020222701835 2629112236470030334052753)
                  ·
                    refine ⟨1971834177352522750539565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2629112236470030334052753 1971834177352522750539565)
                    ·
                      refine ⟨739437816507196031452337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1971834177352522750539565 739437816507196031452337)
                      ·
                        rfl

theorem cell23_1440050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_1440050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440050 prefixEnd_1440050 := by exact prefixLift 1440050
  have htrace : WordTrace (prefixWord ++ tailWord_1440050) baseStart_1440050 baseEnd_1440050 := by
    simpa [prefixWord, tailWord_1440050, baseEnd_1440050] using wordTrace_append hprefix tailTrace_1440050
  have hstable : (prefixWord ++ tailWord_1440050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440050).length < 2 ^ (prefixWord ++ tailWord_1440050).sum := by decide
  have hdescent : baseEnd_1440050 < baseStart_1440050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440063 : List Nat := [1, 1, 2, 2, 4, 1, 4, 2, 2, 1, 3]
def baseStart_1440063 : Nat := 118140960795 + 1440063 * 2 ^ 59
def prefixEnd_1440063 : Nat := 4983230072969 + 3 ^ 40 * 1440063 * 2
def baseEnd_1440063 : Nat := 739444491755704480589777

theorem tailTrace_1440063 : CollatzResearch.WordTrace tailWord_1440063 prefixEnd_1440063 739444491755704480589777 := by
  unfold tailWord_1440063
  simp only [CollatzResearch.WordTrace]
  refine ⟨52523412581905169024972843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35015608387936779349981895 52523412581905169024972843)
  ·
    refine ⟨78785118872857753537459265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52523412581905169024972843 78785118872857753537459265)
    ·
      refine ⟨59088839154643315153094449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78785118872857753537459265 59088839154643315153094449)
      ·
        refine ⟨44316629365982486364820837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59088839154643315153094449 44316629365982486364820837)
        ·
          refine ⟨8309368006121716193403907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44316629365982486364820837 8309368006121716193403907)
          ·
            refine ⟨12464052009182574290105861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8309368006121716193403907 12464052009182574290105861)
            ·
              refine ⟨2337009751721732679394849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12464052009182574290105861 2337009751721732679394849)
              ·
                refine ⟨1752757313791299509546137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2337009751721732679394849 1752757313791299509546137)
                ·
                  refine ⟨1314567985343474632159603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1752757313791299509546137 1314567985343474632159603)
                  ·
                    refine ⟨1971851978015211948239405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1314567985343474632159603 1971851978015211948239405)
                    ·
                      refine ⟨739444491755704480589777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1971851978015211948239405 739444491755704480589777)
                      ·
                        rfl

theorem cell23_1440063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 1, 3].length) (baseStart_1440063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440063 prefixEnd_1440063 := by exact prefixLift 1440063
  have htrace : WordTrace (prefixWord ++ tailWord_1440063) baseStart_1440063 baseEnd_1440063 := by
    simpa [prefixWord, tailWord_1440063, baseEnd_1440063] using wordTrace_append hprefix tailTrace_1440063
  have hstable : (prefixWord ++ tailWord_1440063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440063).length < 2 ^ (prefixWord ++ tailWord_1440063).sum := by decide
  have hdescent : baseEnd_1440063 < baseStart_1440063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440089 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 4, 4, 3]
def baseStart_1440089 : Nat := 118140960795 + 1440089 * 2 ^ 59
def prefixEnd_1440089 : Nat := 4983230072969 + 3 ^ 40 * 1440089 * 2
def baseEnd_1440089 : Nat := 739457842252721378864657

theorem tailTrace_1440089 : CollatzResearch.WordTrace tailWord_1440089 prefixEnd_1440089 739457842252721378864657 := by
  unfold tailWord_1440089
  simp only [CollatzResearch.WordTrace]
  refine ⟨52524360879810975465419321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35016240586540650310279547 52524360879810975465419321)
  ·
    refine ⟨39393270659858231599064491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52524360879810975465419321 39393270659858231599064491)
    ·
      refine ⟨59089905989787347398596737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39393270659858231599064491 59089905989787347398596737)
      ·
        refine ⟨44317429492340510548947553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59089905989787347398596737 44317429492340510548947553)
        ·
          refine ⟨33238072119255382911710665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44317429492340510548947553 33238072119255382911710665)
          ·
            refine ⟨24928554089441537183782999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33238072119255382911710665 24928554089441537183782999)
            ·
              refine ⟨37392831134162305775674499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24928554089441537183782999 37392831134162305775674499)
              ·
                refine ⟨56089246701243458663511749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37392831134162305775674499 56089246701243458663511749)
                ·
                  refine ⟨10516733756483148499408453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56089246701243458663511749 10516733756483148499408453)
                  ·
                    refine ⟨1971887579340590343639085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10516733756483148499408453 1971887579340590343639085)
                    ·
                      refine ⟨739457842252721378864657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1971887579340590343639085 739457842252721378864657)
                      ·
                        rfl

theorem cell23_1440089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_1440089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440089 prefixEnd_1440089 := by exact prefixLift 1440089
  have htrace : WordTrace (prefixWord ++ tailWord_1440089) baseStart_1440089 baseEnd_1440089 := by
    simpa [prefixWord, tailWord_1440089, baseEnd_1440089] using wordTrace_append hprefix tailTrace_1440089
  have hstable : (prefixWord ++ tailWord_1440089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440089).length < 2 ^ (prefixWord ++ tailWord_1440089).sum := by decide
  have hdescent : baseEnd_1440089 < baseStart_1440089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440099 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 4]
def baseStart_1440099 : Nat := 118140960795 + 1440099 * 2 ^ 59
def prefixEnd_1440099 : Nat := 4983230072969 + 3 ^ 40 * 1440099 * 2
def baseEnd_1440099 : Nat := 739462977059266339739611

theorem tailTrace_1440099 : CollatzResearch.WordTrace tailWord_1440099 prefixEnd_1440099 739462977059266339739611 := by
  unfold tailWord_1440099
  simp only [CollatzResearch.WordTrace]
  refine ⟨52524725609774747173283351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35016483739849831448855567 52524725609774747173283351)
  ·
    refine ⟨78787088414662120759925027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52524725609774747173283351 78787088414662120759925027)
    ·
      refine ⟨118180632621993181139887541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78787088414662120759925027 118180632621993181139887541)
      ·
        refine ⟨11079434308311860731864457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118180632621993181139887541 11079434308311860731864457)
        ·
          refine ⟨8309575731233895548898343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11079434308311860731864457 8309575731233895548898343)
          ·
            refine ⟨12464363596850843323347515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8309575731233895548898343 12464363596850843323347515)
            ·
              refine ⟨18696545395276264985021273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12464363596850843323347515 18696545395276264985021273)
              ·
                refine ⟨14022409046457198738765955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18696545395276264985021273 14022409046457198738765955)
                ·
                  refine ⟨21033613569685798108148933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14022409046457198738765955 21033613569685798108148933)
                  ·
                    refine ⟨3943802544316087145277925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21033613569685798108148933 3943802544316087145277925)
                    ·
                      refine ⟨739462977059266339739611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3943802544316087145277925 739462977059266339739611)
                      ·
                        rfl

theorem cell23_1440099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_1440099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440099 prefixEnd_1440099 := by exact prefixLift 1440099
  have htrace : WordTrace (prefixWord ++ tailWord_1440099) baseStart_1440099 baseEnd_1440099 := by
    simpa [prefixWord, tailWord_1440099, baseEnd_1440099] using wordTrace_append hprefix tailTrace_1440099
  have hstable : (prefixWord ++ tailWord_1440099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440099).length < 2 ^ (prefixWord ++ tailWord_1440099).sum := by decide
  have hdescent : baseEnd_1440099 < baseStart_1440099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440103 : List Nat := [1, 1, 5, 1, 3, 1, 2, 2, 1, 4, 2]
def baseStart_1440103 : Nat := 118140960795 + 1440103 * 2 ^ 59
def prefixEnd_1440103 : Nat := 4983230072969 + 3 ^ 40 * 1440103 * 2
def baseEnd_1440103 : Nat := 739465030981884324089593

theorem tailTrace_1440103 : CollatzResearch.WordTrace tailWord_1440103 prefixEnd_1440103 739465030981884324089593 := by
  unfold tailWord_1440103
  simp only [CollatzResearch.WordTrace]
  refine ⟨52524871501760255856428963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35016581001173503904285975 52524871501760255856428963)
  ·
    refine ⟨78787307252640383784643445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52524871501760255856428963 78787307252640383784643445)
    ·
      refine ⟨7386310054935035979810323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78787307252640383784643445 7386310054935035979810323)
      ·
        refine ⟨11079465082402553969715485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7386310054935035979810323 11079465082402553969715485)
        ·
          refine ⟨4154799405900957738643307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11079465082402553969715485 4154799405900957738643307)
          ·
            refine ⟨6232199108851436607964961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4154799405900957738643307 6232199108851436607964961)
            ·
              refine ⟨4674149331638577455973721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6232199108851436607964961 4674149331638577455973721)
              ·
                refine ⟨3505611998728933091980291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4674149331638577455973721 3505611998728933091980291)
                ·
                  refine ⟨5258417998093399637970437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3505611998728933091980291 5258417998093399637970437)
                  ·
                    refine ⟨985953374642512432119457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5258417998093399637970437 985953374642512432119457)
                    ·
                      refine ⟨739465030981884324089593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 985953374642512432119457 739465030981884324089593)
                      ·
                        rfl

theorem cell23_1440103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_1440103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440103 prefixEnd_1440103 := by exact prefixLift 1440103
  have htrace : WordTrace (prefixWord ++ tailWord_1440103) baseStart_1440103 baseEnd_1440103 := by
    simpa [prefixWord, tailWord_1440103, baseEnd_1440103] using wordTrace_append hprefix tailTrace_1440103
  have hstable : (prefixWord ++ tailWord_1440103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440103).length < 2 ^ (prefixWord ++ tailWord_1440103).sum := by decide
  have hdescent : baseEnd_1440103 < baseStart_1440103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440109 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 9]
def baseStart_1440109 : Nat := 118140960795 + 1440109 * 2 ^ 59
def prefixEnd_1440109 : Nat := 4983230072969 + 3 ^ 40 * 1440109 * 2
def baseEnd_1440109 : Nat := 82163123540645700068285

theorem tailTrace_1440109 : CollatzResearch.WordTrace tailWord_1440109 prefixEnd_1440109 82163123540645700068285 := by
  unfold tailWord_1440109
  simp only [CollatzResearch.WordTrace]
  refine ⟨52525090339738518881147381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35016726893159012587431587 52525090339738518881147381)
  ·
    refine ⟨4924227219350486145107567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52525090339738518881147381 4924227219350486145107567)
    ·
      refine ⟨7386340829025729217661351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4924227219350486145107567 7386340829025729217661351)
      ·
        refine ⟨11079511243538593826492027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7386340829025729217661351 11079511243538593826492027)
        ·
          refine ⟨16619266865307890739738041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11079511243538593826492027 16619266865307890739738041)
          ·
            refine ⟨12464450148980918054803531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16619266865307890739738041 12464450148980918054803531)
            ·
              refine ⟨18696675223471377082205297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12464450148980918054803531 18696675223471377082205297)
              ·
                refine ⟨14022506417603532811653973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18696675223471377082205297 14022506417603532811653973)
                ·
                  refine ⟨82163123540645700068285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14022506417603532811653973 82163123540645700068285)
                  ·
                    rfl

theorem cell23_1440109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_1440109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440109 prefixEnd_1440109 := by exact prefixLift 1440109
  have htrace : WordTrace (prefixWord ++ tailWord_1440109) baseStart_1440109 baseEnd_1440109 := by
    simpa [prefixWord, tailWord_1440109, baseEnd_1440109] using wordTrace_append hprefix tailTrace_1440109
  have hstable : (prefixWord ++ tailWord_1440109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440109).length < 2 ^ (prefixWord ++ tailWord_1440109).sum := by decide
  have hdescent : baseEnd_1440109 < baseStart_1440109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440136 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 2, 3, 3]
def baseStart_1440136 : Nat := 118140960795 + 1440136 * 2 ^ 59
def prefixEnd_1440136 : Nat := 4983230072969 + 3 ^ 40 * 1440136 * 2
def baseEnd_1440136 : Nat := 739481975843482694976941

theorem tailTrace_1440136 : CollatzResearch.WordTrace tailWord_1440136 prefixEnd_1440136 739481975843482694976941 := by
  unfold tailWord_1440136
  simp only [CollatzResearch.WordTrace]
  refine ⟨26263037555320351246190131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35017383407093801661586841 26263037555320351246190131)
  ·
    refine ⟨39394556332980526869285197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26263037555320351246190131 39394556332980526869285197)
    ·
      refine ⟨14772958624867697575981949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39394556332980526869285197 14772958624867697575981949)
      ·
        refine ⟨5539859484325386590993231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14772958624867697575981949 5539859484325386590993231)
        ·
          refine ⟨8309789226488079886489847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5539859484325386590993231 8309789226488079886489847)
          ·
            refine ⟨12464683839732119829734771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8309789226488079886489847 12464683839732119829734771)
            ·
              refine ⟨18697025759598179744602157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12464683839732119829734771 18697025759598179744602157)
              ·
                refine ⟨7011384659849317404225809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18697025759598179744602157 7011384659849317404225809)
                ·
                  refine ⟨5258538494886988053169357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7011384659849317404225809 5258538494886988053169357)
                  ·
                    refine ⟨1971951935582620519938509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5258538494886988053169357 1971951935582620519938509)
                    ·
                      refine ⟨739481975843482694976941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1971951935582620519938509 739481975843482694976941)
                      ·
                        rfl

theorem cell23_1440136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_1440136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440136 prefixEnd_1440136 := by exact prefixLift 1440136
  have htrace : WordTrace (prefixWord ++ tailWord_1440136) baseStart_1440136 baseEnd_1440136 := by
    simpa [prefixWord, tailWord_1440136, baseEnd_1440136] using wordTrace_append hprefix tailTrace_1440136
  have hstable : (prefixWord ++ tailWord_1440136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440136).length < 2 ^ (prefixWord ++ tailWord_1440136).sum := by decide
  have hdescent : baseEnd_1440136 < baseStart_1440136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440137 : List Nat := [1, 2, 1, 1, 6, 2, 3, 1, 2, 2, 2]
def baseStart_1440137 : Nat := 118140960795 + 1440137 * 2 ^ 59
def prefixEnd_1440137 : Nat := 4983230072969 + 3 ^ 40 * 1440137 * 2
def baseEnd_1440137 : Nat := 739482489324137191064437

theorem tailTrace_1440137 : CollatzResearch.WordTrace tailWord_1440137 prefixEnd_1440137 739482489324137191064437 := by
  unfold tailWord_1440137
  simp only [CollatzResearch.WordTrace]
  refine ⟨52526111583637079663166665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35017407722424719775444443 52526111583637079663166665)
  ·
    refine ⟨39394583687727809747374999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52526111583637079663166665 39394583687727809747374999)
    ·
      refine ⟨59091875531591714621062499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39394583687727809747374999 59091875531591714621062499)
      ·
        refine ⟨88637813297387571931593749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59091875531591714621062499 88637813297387571931593749)
        ·
          refine ⟨4154897498315042434293457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88637813297387571931593749 4154897498315042434293457)
          ·
            refine ⟨3116173123736281825720093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4154897498315042434293457 3116173123736281825720093)
            ·
              refine ⟨1168564921401105684645035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3116173123736281825720093 1168564921401105684645035)
              ·
                refine ⟨1752847382101658526967553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168564921401105684645035 1752847382101658526967553)
                ·
                  refine ⟨1314635536576243895225665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1752847382101658526967553 1314635536576243895225665)
                  ·
                    refine ⟨985976652432182921419249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1314635536576243895225665 985976652432182921419249)
                    ·
                      refine ⟨739482489324137191064437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 985976652432182921419249 739482489324137191064437)
                      ·
                        rfl

theorem cell23_1440137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 2, 2, 2].length) (baseStart_1440137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440137 prefixEnd_1440137 := by exact prefixLift 1440137
  have htrace : WordTrace (prefixWord ++ tailWord_1440137) baseStart_1440137 baseEnd_1440137 := by
    simpa [prefixWord, tailWord_1440137, baseEnd_1440137] using wordTrace_append hprefix tailTrace_1440137
  have hstable : (prefixWord ++ tailWord_1440137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440137).length < 2 ^ (prefixWord ++ tailWord_1440137).sum := by decide
  have hdescent : baseEnd_1440137 < baseStart_1440137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440139 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 1, 7]
def baseStart_1440139 : Nat := 118140960795 + 1440139 * 2 ^ 59
def prefixEnd_1440139 : Nat := 4983230072969 + 3 ^ 40 * 1440139 * 2
def baseEnd_1440139 : Nat := 246494505428482061079809

theorem tailTrace_1440139 : CollatzResearch.WordTrace tailWord_1440139 prefixEnd_1440139 246494505428482061079809 := by
  unfold tailWord_1440139
  simp only [CollatzResearch.WordTrace]
  refine ⟨52526184529629834004739471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35017456353086556003159647 52526184529629834004739471)
  ·
    refine ⟨78789276794444751007109207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52526184529629834004739471 78789276794444751007109207)
    ·
      refine ⟨118183915191667126510663811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78789276794444751007109207 118183915191667126510663811)
      ·
        refine ⟨177275872787500689765995717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118183915191667126510663811 177275872787500689765995717)
        ·
          refine ⟨33239226147656379331124197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177275872787500689765995717 33239226147656379331124197)
          ·
            refine ⟨6232354902685571124585787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33239226147656379331124197 6232354902685571124585787)
            ·
              refine ⟨9348532354028356686878681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6232354902685571124585787 9348532354028356686878681)
              ·
                refine ⟨7011399265521267515159011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9348532354028356686878681 7011399265521267515159011)
                ·
                  refine ⟨10517098898281901272738517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7011399265521267515159011 10517098898281901272738517)
                  ·
                    refine ⟨246494505428482061079809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10517098898281901272738517 246494505428482061079809)
                    ·
                      rfl

theorem cell23_1440139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 7].length) (baseStart_1440139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440139 prefixEnd_1440139 := by exact prefixLift 1440139
  have htrace : WordTrace (prefixWord ++ tailWord_1440139) baseStart_1440139 baseEnd_1440139 := by
    simpa [prefixWord, tailWord_1440139, baseEnd_1440139] using wordTrace_append hprefix tailTrace_1440139
  have hstable : (prefixWord ++ tailWord_1440139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440139).length < 2 ^ (prefixWord ++ tailWord_1440139).sum := by decide
  have hdescent : baseEnd_1440139 < baseStart_1440139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440149 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_1440149 : Nat := 118140960795 + 1440149 * 2 ^ 59
def prefixEnd_1440149 : Nat := 4983230072969 + 3 ^ 40 * 1440149 * 2
def baseEnd_1440149 : Nat := 739488651091991144114381

theorem tailTrace_1440149 : CollatzResearch.WordTrace tailWord_1440149 prefixEnd_1440149 739488651091991144114381 := by
  unfold tailWord_1440149
  simp only [CollatzResearch.WordTrace]
  refine ⟨52526549259593605712603501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35017699506395737141735667 52526549259593605712603501)
  ·
    refine ⟨19697455972347602142226313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52526549259593605712603501 19697455972347602142226313)
    ·
      refine ⟨14773091979260701606669735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19697455972347602142226313 14773091979260701606669735)
      ·
        refine ⟨22159637968891052410004603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14773091979260701606669735 22159637968891052410004603)
        ·
          refine ⟨33239456953336578615006905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22159637968891052410004603 33239456953336578615006905)
          ·
            refine ⟨24929592715002433961255179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33239456953336578615006905 24929592715002433961255179)
            ·
              refine ⟨37394389072503650941882769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24929592715002433961255179 37394389072503650941882769)
              ·
                refine ⟨28045791804377738206412077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37394389072503650941882769 28045791804377738206412077)
                ·
                  refine ⟨10517171926641651827404529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28045791804377738206412077 10517171926641651827404529)
                  ·
                    refine ⟨7887878944981238870553397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10517171926641651827404529 7887878944981238870553397)
                    ·
                      refine ⟨739488651091991144114381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7887878944981238870553397 739488651091991144114381)
                      ·
                        rfl

theorem cell23_1440149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_1440149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440149 prefixEnd_1440149 := by exact prefixLift 1440149
  have htrace : WordTrace (prefixWord ++ tailWord_1440149) baseStart_1440149 baseEnd_1440149 := by
    simpa [prefixWord, tailWord_1440149, baseEnd_1440149] using wordTrace_append hprefix tailTrace_1440149
  have hstable : (prefixWord ++ tailWord_1440149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440149).length < 2 ^ (prefixWord ++ tailWord_1440149).sum := by decide
  have hdescent : baseEnd_1440149 < baseStart_1440149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440213 : List Nat := [1, 3, 2, 3, 1, 2, 1, 3, 2, 2, 3]
def baseStart_1440213 : Nat := 118140960795 + 1440213 * 2 ^ 59
def prefixEnd_1440213 : Nat := 4983230072969 + 3 ^ 40 * 1440213 * 2
def baseEnd_1440213 : Nat := 739521513853878893714087

theorem tailTrace_1440213 : CollatzResearch.WordTrace tailWord_1440213 prefixEnd_1440213 739521513853878893714087 := by
  unfold tailWord_1440213
  simp only [CollatzResearch.WordTrace]
  refine ⟨52528883531361744642933293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35019255687574496428622195 52528883531361744642933293)
  ·
    refine ⟨19698331324260654241099985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52528883531361744642933293 19698331324260654241099985)
    ·
      refine ⟨14773748493195490680824989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19698331324260654241099985 14773748493195490680824989)
      ·
        refine ⟨5540155684948309005309371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14773748493195490680824989 5540155684948309005309371)
        ·
          refine ⟨8310233527422463507964057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5540155684948309005309371 8310233527422463507964057)
          ·
            refine ⟨6232675145566847630973043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8310233527422463507964057 6232675145566847630973043)
            ·
              refine ⟨9349012718350271446459565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6232675145566847630973043 9349012718350271446459565)
              ·
                refine ⟨3505879769381351792422337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9349012718350271446459565 3505879769381351792422337)
                ·
                  refine ⟨2629409827036013844316753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3505879769381351792422337 2629409827036013844316753)
                  ·
                    refine ⟨1972057370277010383237565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2629409827036013844316753 1972057370277010383237565)
                    ·
                      refine ⟨739521513853878893714087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1972057370277010383237565 739521513853878893714087)
                      ·
                        rfl

theorem cell23_1440213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_1440213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440213 prefixEnd_1440213 := by exact prefixLift 1440213
  have htrace : WordTrace (prefixWord ++ tailWord_1440213) baseStart_1440213 baseEnd_1440213 := by
    simpa [prefixWord, tailWord_1440213, baseEnd_1440213] using wordTrace_append hprefix tailTrace_1440213
  have hstable : (prefixWord ++ tailWord_1440213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440213).length < 2 ^ (prefixWord ++ tailWord_1440213).sum := by decide
  have hdescent : baseEnd_1440213 < baseStart_1440213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440237 : List Nat := [1, 5, 1, 3, 1, 2, 1, 4, 1, 4]
def baseStart_1440237 : Nat := 118140960795 + 1440237 * 2 ^ 59
def prefixEnd_1440237 : Nat := 4983230072969 + 3 ^ 40 * 1440237 * 2
def baseEnd_1440237 : Nat := 246511279129862266604659

theorem tailTrace_1440237 : CollatzResearch.WordTrace tailWord_1440237 prefixEnd_1440237 246511279129862266604659 := by
  unfold tailWord_1440237
  simp only [CollatzResearch.WordTrace]
  refine ⟨52529758883274796741806965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35019839255516531161204643 52529758883274796741806965)
  ·
    refine ⟨4924664895307012194544403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52529758883274796741806965 4924664895307012194544403)
    ·
      refine ⟨7386997342960518291816605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4924664895307012194544403 7386997342960518291816605)
      ·
        refine ⟨2770124003610194359431227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7386997342960518291816605 2770124003610194359431227)
        ·
          refine ⟨4155186005415291539146841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2770124003610194359431227 4155186005415291539146841)
          ·
            refine ⟨3116389504061468654360131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4155186005415291539146841 3116389504061468654360131)
            ·
              refine ⟨4674584256092202981540197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3116389504061468654360131 4674584256092202981540197)
              ·
                refine ⟨876484548017288059038787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4674584256092202981540197 876484548017288059038787)
                ·
                  refine ⟨1314726822025932088558181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876484548017288059038787 1314726822025932088558181)
                  ·
                    refine ⟨246511279129862266604659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1314726822025932088558181 246511279129862266604659)
                    ·
                      rfl

theorem cell23_1440237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_1440237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440237 prefixEnd_1440237 := by exact prefixLift 1440237
  have htrace : WordTrace (prefixWord ++ tailWord_1440237) baseStart_1440237 baseEnd_1440237 := by
    simpa [prefixWord, tailWord_1440237, baseEnd_1440237] using wordTrace_append hprefix tailTrace_1440237
  have hstable : (prefixWord ++ tailWord_1440237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440237).length < 2 ^ (prefixWord ++ tailWord_1440237).sum := by decide
  have hdescent : baseEnd_1440237 < baseStart_1440237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440243 : List Nat := [1, 1, 1, 2, 2, 2, 4, 3, 3, 1, 3]
def baseStart_1440243 : Nat := 118140960795 + 1440243 * 2 ^ 59
def prefixEnd_1440243 : Nat := 4983230072969 + 3 ^ 40 * 1440243 * 2
def baseEnd_1440243 : Nat := 739536918273513776338949

theorem tailTrace_1440243 : CollatzResearch.WordTrace tailWord_1440243 prefixEnd_1440243 739536918273513776338949 := by
  unfold tailWord_1440243
  simp only [CollatzResearch.WordTrace]
  refine ⟨52529977721253059766525383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35019985147502039844350255 52529977721253059766525383)
  ·
    refine ⟨78794966581879589649788075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52529977721253059766525383 78794966581879589649788075)
    ·
      refine ⟨118192449872819384474682113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78794966581879589649788075 118192449872819384474682113)
      ·
        refine ⟨88644337404614538356011585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118192449872819384474682113 88644337404614538356011585)
        ·
          refine ⟨66483253053460903767008689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88644337404614538356011585 66483253053460903767008689)
          ·
            refine ⟨49862439790095677825256517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66483253053460903767008689 49862439790095677825256517)
            ·
              refine ⟨9349207460642939592235597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49862439790095677825256517 9349207460642939592235597)
              ·
                refine ⟨3505952797741102347088349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9349207460642939592235597 3505952797741102347088349)
                ·
                  refine ⟨1314732299152913380158131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3505952797741102347088349 1314732299152913380158131)
                  ·
                    refine ⟨1972098448729370070237197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1314732299152913380158131 1972098448729370070237197)
                    ·
                      refine ⟨739536918273513776338949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1972098448729370070237197 739536918273513776338949)
                      ·
                        rfl

theorem cell23_1440243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 1, 3].length) (baseStart_1440243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440243 prefixEnd_1440243 := by exact prefixLift 1440243
  have htrace : WordTrace (prefixWord ++ tailWord_1440243) baseStart_1440243 baseEnd_1440243 := by
    simpa [prefixWord, tailWord_1440243, baseEnd_1440243] using wordTrace_append hprefix tailTrace_1440243
  have hstable : (prefixWord ++ tailWord_1440243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440243).length < 2 ^ (prefixWord ++ tailWord_1440243).sum := by decide
  have hdescent : baseEnd_1440243 < baseStart_1440243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440253 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 1, 5, 2]
def baseStart_1440253 : Nat := 118140960795 + 1440253 * 2 ^ 59
def prefixEnd_1440253 : Nat := 4983230072969 + 3 ^ 40 * 1440253 * 2
def baseEnd_1440253 : Nat := 739542053080058737213903

theorem tailTrace_1440253 : CollatzResearch.WordTrace tailWord_1440253 prefixEnd_1440253 739542053080058737213903 := by
  unfold tailWord_1440253
  simp only [CollatzResearch.WordTrace]
  refine ⟨52530342451216831474389413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35020228300811220982926275 52530342451216831474389413)
  ·
    refine ⟨9849439209603155901448015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52530342451216831474389413 9849439209603155901448015)
    ·
      refine ⟨14774158814404733852172023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9849439209603155901448015 14774158814404733852172023)
      ·
        refine ⟨22161238221607100778258035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14774158814404733852172023 22161238221607100778258035)
        ·
          refine ⟨33241857332410651167387053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22161238221607100778258035 33241857332410651167387053)
          ·
            refine ⟨12465696499653994187770145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33241857332410651167387053 12465696499653994187770145)
            ·
              refine ⟨9349272374740495640827609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12465696499653994187770145 9349272374740495640827609)
              ·
                refine ⟨7011954281055371730620707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9349272374740495640827609 7011954281055371730620707)
                ·
                  refine ⟨10517931421583057595931061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7011954281055371730620707 10517931421583057595931061)
                  ·
                    refine ⟨986056070773411649618537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10517931421583057595931061 986056070773411649618537)
                    ·
                      refine ⟨739542053080058737213903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 986056070773411649618537 739542053080058737213903)
                      ·
                        rfl

theorem cell23_1440253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_1440253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440253 prefixEnd_1440253 := by exact prefixLift 1440253
  have htrace : WordTrace (prefixWord ++ tailWord_1440253) baseStart_1440253 baseEnd_1440253 := by
    simpa [prefixWord, tailWord_1440253, baseEnd_1440253] using wordTrace_append hprefix tailTrace_1440253
  have hstable : (prefixWord ++ tailWord_1440253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440253).length < 2 ^ (prefixWord ++ tailWord_1440253).sum := by decide
  have hdescent : baseEnd_1440253 < baseStart_1440253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440260 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 5, 1, 3]
def baseStart_1440260 : Nat := 118140960795 + 1440260 * 2 ^ 59
def prefixEnd_1440260 : Nat := 4983230072969 + 3 ^ 40 * 1440260 * 2
def baseEnd_1440260 : Nat := 739545647444640209826371

theorem tailTrace_1440260 : CollatzResearch.WordTrace tailWord_1440260 prefixEnd_1440260 739545647444640209826371 := by
  unfold tailWord_1440260
  simp only [CollatzResearch.WordTrace]
  refine ⟨26265298881095735834947117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35020398508127647779929489 26265298881095735834947117)
  ·
    refine ⟨9849487080410900938105169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26265298881095735834947117 9849487080410900938105169)
    ·
      refine ⟨7387115310308175703578877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9849487080410900938105169 7387115310308175703578877)
      ·
        refine ⟨2770168241365565888842079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7387115310308175703578877 2770168241365565888842079)
        ·
          refine ⟨4155252362048348833263119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2770168241365565888842079 4155252362048348833263119)
          ·
            refine ⟨6232878543072523249894679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4155252362048348833263119 6232878543072523249894679)
            ·
              refine ⟨9349317814608784874842019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6232878543072523249894679 9349317814608784874842019)
              ·
                refine ⟨14023976721913177312263029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9349317814608784874842019 14023976721913177312263029)
                ·
                  refine ⟨1314747817679360373024659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14023976721913177312263029 1314747817679360373024659)
                  ·
                    refine ⟨1972121726519040559536989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1314747817679360373024659 1972121726519040559536989)
                    ·
                      refine ⟨739545647444640209826371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1972121726519040559536989 739545647444640209826371)
                      ·
                        rfl

theorem cell23_1440260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_1440260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440260 prefixEnd_1440260 := by exact prefixLift 1440260
  have htrace : WordTrace (prefixWord ++ tailWord_1440260) baseStart_1440260 baseEnd_1440260 := by
    simpa [prefixWord, tailWord_1440260, baseEnd_1440260] using wordTrace_append hprefix tailTrace_1440260
  have hstable : (prefixWord ++ tailWord_1440260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440260).length < 2 ^ (prefixWord ++ tailWord_1440260).sum := by decide
  have hdescent : baseEnd_1440260 < baseStart_1440260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440270 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2]
def baseStart_1440270 : Nat := 118140960795 + 1440270 * 2 ^ 59
def prefixEnd_1440270 : Nat := 4983230072969 + 3 ^ 40 * 1440270 * 2
def baseEnd_1440270 : Nat := 739550782251185170701325

theorem tailTrace_1440270 : CollatzResearch.WordTrace tailWord_1440270 prefixEnd_1440270 739550782251185170701325 := by
  unfold tailWord_1440270
  simp only [CollatzResearch.WordTrace]
  refine ⟨6566370311519405422219783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35020641661436828918505509 6566370311519405422219783)
  ·
    refine ⟨9849555467279108133329675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6566370311519405422219783 9849555467279108133329675)
    ·
      refine ⟨14774333200918662199994513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9849555467279108133329675 14774333200918662199994513)
      ·
        refine ⟨11080749900688996649995885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14774333200918662199994513 11080749900688996649995885)
        ·
          refine ⟨4155281212758373743748457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11080749900688996649995885 4155281212758373743748457)
          ·
            refine ⟨3116460909568780307811343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4155281212758373743748457 3116460909568780307811343)
            ·
              refine ⟨4674691364353170461717015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3116460909568780307811343 4674691364353170461717015)
              ·
                refine ⟨7012037046529755692575523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4674691364353170461717015 7012037046529755692575523)
                ·
                  refine ⟨10518055569794633538863285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7012037046529755692575523 10518055569794633538863285)
                  ·
                    refine ⟨986067709668246894268433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10518055569794633538863285 986067709668246894268433)
                    ·
                      refine ⟨739550782251185170701325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 986067709668246894268433 739550782251185170701325)
                      ·
                        rfl

theorem cell23_1440270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_1440270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440270 prefixEnd_1440270 := by exact prefixLift 1440270
  have htrace : WordTrace (prefixWord ++ tailWord_1440270) baseStart_1440270 baseEnd_1440270 := by
    simpa [prefixWord, tailWord_1440270, baseEnd_1440270] using wordTrace_append hprefix tailTrace_1440270
  have hstable : (prefixWord ++ tailWord_1440270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440270).length < 2 ^ (prefixWord ++ tailWord_1440270).sum := by decide
  have hdescent : baseEnd_1440270 < baseStart_1440270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440277 : List Nat := [1, 3, 2, 1, 3, 1, 4, 3, 1, 1, 3]
def baseStart_1440277 : Nat := 118140960795 + 1440277 * 2 ^ 59
def prefixEnd_1440277 : Nat := 4983230072969 + 3 ^ 40 * 1440277 * 2
def baseEnd_1440277 : Nat := 739554376615766643313793

theorem tailTrace_1440277 : CollatzResearch.WordTrace tailWord_1440277 prefixEnd_1440277 739554376615766643313793 := by
  unfold tailWord_1440277
  simp only [CollatzResearch.WordTrace]
  refine ⟨52531217803129883573263085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35020811868753255715508723 52531217803129883573263085)
  ·
    refine ⟨19699206676173706339973657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52531217803129883573263085 19699206676173706339973657)
    ·
      refine ⟨14774405007130279754980243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19699206676173706339973657 14774405007130279754980243)
      ·
        refine ⟨22161607510695419632470365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14774405007130279754980243 22161607510695419632470365)
        ·
          refine ⟨8310602816510782362176387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22161607510695419632470365 8310602816510782362176387)
          ·
            refine ⟨12465904224766173543264581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8310602816510782362176387 12465904224766173543264581)
            ·
              refine ⟨2337357042143657539362109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12465904224766173543264581 2337357042143657539362109)
              ·
                refine ⟨876508890803871577260791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2337357042143657539362109 876508890803871577260791)
                ·
                  refine ⟨1314763336205807365891187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876508890803871577260791 1314763336205807365891187)
                  ·
                    refine ⟨1972145004308711048836781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1314763336205807365891187 1972145004308711048836781)
                    ·
                      refine ⟨739554376615766643313793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1972145004308711048836781 739554376615766643313793)
                      ·
                        rfl

theorem cell23_1440277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 1, 1, 3].length) (baseStart_1440277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440277 prefixEnd_1440277 := by exact prefixLift 1440277
  have htrace : WordTrace (prefixWord ++ tailWord_1440277) baseStart_1440277 baseEnd_1440277 := by
    simpa [prefixWord, tailWord_1440277, baseEnd_1440277] using wordTrace_append hprefix tailTrace_1440277
  have hstable : (prefixWord ++ tailWord_1440277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440277).length < 2 ^ (prefixWord ++ tailWord_1440277).sum := by decide
  have hdescent : baseEnd_1440277 < baseStart_1440277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440280 : List Nat := [2, 1, 2, 3, 3, 1, 4, 1, 1, 5]
def baseStart_1440280 : Nat := 118140960795 + 1440280 * 2 ^ 59
def prefixEnd_1440280 : Nat := 4983230072969 + 3 ^ 40 * 1440280 * 2
def baseEnd_1440280 : Nat := 246518639019243377192093

theorem tailTrace_1440280 : CollatzResearch.WordTrace tailWord_1440280 prefixEnd_1440280 246518639019243377192093 := by
  unfold tailWord_1440280
  simp only [CollatzResearch.WordTrace]
  refine ⟨26265663611059507542811147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35020884814746010057081529 26265663611059507542811147)
  ·
    refine ⟨39398495416589261314216721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26265663611059507542811147 39398495416589261314216721)
    ·
      refine ⟨29548871562441945985662541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39398495416589261314216721 29548871562441945985662541)
      ·
        refine ⟨11080826835915729744623453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29548871562441945985662541 11080826835915729744623453)
        ·
          refine ⟨4155310063468398654233795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11080826835915729744623453 4155310063468398654233795)
          ·
            refine ⟨6232965095202597981350693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4155310063468398654233795 6232965095202597981350693)
            ·
              refine ⟨1168680955350487121503255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6232965095202597981350693 1168680955350487121503255)
              ·
                refine ⟨1753021433025730682254883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168680955350487121503255 1753021433025730682254883)
                ·
                  refine ⟨2629532149538596023382325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1753021433025730682254883 2629532149538596023382325)
                  ·
                    refine ⟨246518639019243377192093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2629532149538596023382325 246518639019243377192093)
                    ·
                      rfl

theorem cell23_1440280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 1, 5].length) (baseStart_1440280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440280 prefixEnd_1440280 := by exact prefixLift 1440280
  have htrace : WordTrace (prefixWord ++ tailWord_1440280) baseStart_1440280 baseEnd_1440280 := by
    simpa [prefixWord, tailWord_1440280, baseEnd_1440280] using wordTrace_append hprefix tailTrace_1440280
  have hstable : (prefixWord ++ tailWord_1440280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440280).length < 2 ^ (prefixWord ++ tailWord_1440280).sum := by decide
  have hdescent : baseEnd_1440280 < baseStart_1440280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440310 : List Nat := [5, 1, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_1440310 : Nat := 118140960795 + 1440310 * 2 ^ 59
def prefixEnd_1440310 : Nat := 4983230072969 + 3 ^ 40 * 1440310 * 2
def baseEnd_1440310 : Nat := 246523773825788338067047

theorem tailTrace_1440310 : CollatzResearch.WordTrace tailWord_1440310 prefixEnd_1440310 246523773825788338067047 := by
  unfold tailWord_1440310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3283276338250645638075899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35021614274673553472809589 3283276338250645638075899)
  ·
    refine ⟨4924914507375968457113849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3283276338250645638075899 4924914507375968457113849)
    ·
      refine ⟨3693685880531976342835387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4924914507375968457113849 3693685880531976342835387)
      ·
        refine ⟨5540528820797964514253081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3693685880531976342835387 5540528820797964514253081)
        ·
          refine ⟨4155396615598473385689811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5540528820797964514253081 4155396615598473385689811)
          ·
            refine ⟨6233094923397710078534717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4155396615598473385689811 6233094923397710078534717)
            ·
              refine ⟨2337410596274141279450519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6233094923397710078534717 2337410596274141279450519)
              ·
                refine ⟨3506115894411211919175779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2337410596274141279450519 3506115894411211919175779)
                ·
                  refine ⟨5259173841616817878763669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3506115894411211919175779 5259173841616817878763669)
                  ·
                    refine ⟨246523773825788338067047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5259173841616817878763669 246523773825788338067047)
                    ·
                      rfl

theorem cell23_1440310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_1440310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440310 prefixEnd_1440310 := by exact prefixLift 1440310
  have htrace : WordTrace (prefixWord ++ tailWord_1440310) baseStart_1440310 baseEnd_1440310 := by
    simpa [prefixWord, tailWord_1440310, baseEnd_1440310] using wordTrace_append hprefix tailTrace_1440310
  have hstable : (prefixWord ++ tailWord_1440310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440310).length < 2 ^ (prefixWord ++ tailWord_1440310).sum := by decide
  have hdescent : baseEnd_1440310 < baseStart_1440310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440317 : List Nat := [1, 4, 1, 3, 2, 1, 2, 2, 3, 2, 2]
def baseStart_1440317 : Nat := 118140960795 + 1440317 * 2 ^ 59
def prefixEnd_1440317 : Nat := 4983230072969 + 3 ^ 40 * 1440317 * 2
def baseEnd_1440317 : Nat := 739574915841946486813609

theorem tailTrace_1440317 : CollatzResearch.WordTrace tailWord_1440317 prefixEnd_1440317 739574915841946486813609 := by
  unfold tailWord_1440317
  simp only [CollatzResearch.WordTrace]
  refine ⟨52532676722984970404719205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35021784481989980269812803 52532676722984970404719205)
  ·
    refine ⟨9849876885559681950884851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52532676722984970404719205 9849876885559681950884851)
    ·
      refine ⟨14774815328339522926327277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9849876885559681950884851 14774815328339522926327277)
      ·
        refine ⟨5540555748127321097372729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14774815328339522926327277 5540555748127321097372729)
        ·
          refine ⟨4155416811095490823029547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5540555748127321097372729 4155416811095490823029547)
          ·
            refine ⟨6233125216643236234544321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4155416811095490823029547 6233125216643236234544321)
            ·
              refine ⟨4674843912482427175908241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6233125216643236234544321 4674843912482427175908241)
              ·
                refine ⟨3506132934361820381931181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4674843912482427175908241 3506132934361820381931181)
                ·
                  refine ⟨1314799850385682643224193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3506132934361820381931181 1314799850385682643224193)
                  ·
                    refine ⟨986099887789261982418145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1314799850385682643224193 986099887789261982418145)
                    ·
                      refine ⟨739574915841946486813609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 986099887789261982418145 739574915841946486813609)
                      ·
                        rfl

theorem cell23_1440317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_1440317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440317 prefixEnd_1440317 := by exact prefixLift 1440317
  have htrace : WordTrace (prefixWord ++ tailWord_1440317) baseStart_1440317 baseEnd_1440317 := by
    simpa [prefixWord, tailWord_1440317, baseEnd_1440317] using wordTrace_append hprefix tailTrace_1440317
  have hstable : (prefixWord ++ tailWord_1440317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440317).length < 2 ^ (prefixWord ++ tailWord_1440317).sum := by decide
  have hdescent : baseEnd_1440317 < baseStart_1440317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440334 : List Nat := [4, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2]
def baseStart_1440334 : Nat := 118140960795 + 1440334 * 2 ^ 59
def prefixEnd_1440334 : Nat := 4983230072969 + 3 ^ 40 * 1440334 * 2
def baseEnd_1440334 : Nat := 739583645013072920301031

theorem tailTrace_1440334 : CollatzResearch.WordTrace tailWord_1440334 prefixEnd_1440334 739583645013072920301031 := by
  unfold tailWord_1440334
  simp only [CollatzResearch.WordTrace]
  refine ⟨6566662095490422788511007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35022197842615588205392037 6566662095490422788511007)
  ·
    refine ⟨9849993143235634182766511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6566662095490422788511007 9849993143235634182766511)
    ·
      refine ⟨14774989714853451274149767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9849993143235634182766511 14774989714853451274149767)
      ·
        refine ⟨22162484572280176911224651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14774989714853451274149767 22162484572280176911224651)
        ·
          refine ⟨33243726858420265366836977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22162484572280176911224651 33243726858420265366836977)
          ·
            refine ⟨24932795143815199025127733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33243726858420265366836977 24932795143815199025127733)
            ·
              refine ⟨2337449544732674908605725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24932795143815199025127733 2337449544732674908605725)
              ·
                refine ⟨876543579274753090727147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2337449544732674908605725 876543579274753090727147)
                ·
                  refine ⟨1314815368912129636090721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876543579274753090727147 1314815368912129636090721)
                  ·
                    refine ⟨986111526684097227068041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1314815368912129636090721 986111526684097227068041)
                    ·
                      refine ⟨739583645013072920301031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 986111526684097227068041 739583645013072920301031)
                      ·
                        rfl

theorem cell23_1440334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2].length) (baseStart_1440334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440334 prefixEnd_1440334 := by exact prefixLift 1440334
  have htrace : WordTrace (prefixWord ++ tailWord_1440334) baseStart_1440334 baseEnd_1440334 := by
    simpa [prefixWord, tailWord_1440334, baseEnd_1440334] using wordTrace_append hprefix tailTrace_1440334
  have hstable : (prefixWord ++ tailWord_1440334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440334).length < 2 ^ (prefixWord ++ tailWord_1440334).sum := by decide
  have hdescent : baseEnd_1440334 < baseStart_1440334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440367 : List Nat := [1, 1, 2, 1, 3, 2, 6, 1, 2, 1, 3]
def baseStart_1440367 : Nat := 118140960795 + 1440367 * 2 ^ 59
def prefixEnd_1440367 : Nat := 4983230072969 + 3 ^ 40 * 1440367 * 2
def baseEnd_1440367 : Nat := 739600589874671291188379

theorem tailTrace_1440367 : CollatzResearch.WordTrace tailWord_1440367 prefixEnd_1440367 739600589874671291188379 := by
  unfold tailWord_1440367
  simp only [CollatzResearch.WordTrace]
  refine ⟨52534500372803828944039355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35023000248535885962692903 52534500372803828944039355)
  ·
    refine ⟨78801750559205743416059033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52534500372803828944039355 78801750559205743416059033)
    ·
      refine ⟨59101312919404307562044275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78801750559205743416059033 59101312919404307562044275)
      ·
        refine ⟨88651969379106461343066413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59101312919404307562044275 88651969379106461343066413)
        ·
          refine ⟨33244488517164923003649905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88651969379106461343066413 33244488517164923003649905)
          ·
            refine ⟨24933366387873692252737429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33244488517164923003649905 24933366387873692252737429)
            ·
              refine ⟨1168751549431579324347067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24933366387873692252737429 1168751549431579324347067)
              ·
                refine ⟨1753127324147368986520601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168751549431579324347067 1753127324147368986520601)
                ·
                  refine ⟨1314845493110526739890451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1753127324147368986520601 1314845493110526739890451)
                  ·
                    refine ⟨1972268239665790109835677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1314845493110526739890451 1972268239665790109835677)
                    ·
                      refine ⟨739600589874671291188379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1972268239665790109835677 739600589874671291188379)
                      ·
                        rfl

theorem cell23_1440367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 2, 1, 3].length) (baseStart_1440367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440367 prefixEnd_1440367 := by exact prefixLift 1440367
  have htrace : WordTrace (prefixWord ++ tailWord_1440367) baseStart_1440367 baseEnd_1440367 := by
    simpa [prefixWord, tailWord_1440367, baseEnd_1440367] using wordTrace_append hprefix tailTrace_1440367
  have hstable : (prefixWord ++ tailWord_1440367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440367).length < 2 ^ (prefixWord ++ tailWord_1440367).sum := by decide
  have hdescent : baseEnd_1440367 < baseStart_1440367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440376 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 3, 3, 5]
def baseStart_1440376 : Nat := 118140960795 + 1440376 * 2 ^ 59
def prefixEnd_1440376 : Nat := 4983230072969 + 3 ^ 40 * 1440376 * 2
def baseEnd_1440376 : Nat := 739605211200561755975837

theorem tailTrace_1440376 : CollatzResearch.WordTrace tailWord_1440376 prefixEnd_1440376 739605211200561755975837 := by
  unfold tailWord_1440376
  simp only [CollatzResearch.WordTrace]
  refine ⟨26267414314885611740558491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35023219086514148987411321 26267414314885611740558491)
  ·
    refine ⟨39401121472328417610837737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26267414314885611740558491 39401121472328417610837737)
    ·
      refine ⟨29550841104246313208128303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39401121472328417610837737 29550841104246313208128303)
      ·
        refine ⟨44326261656369469812192455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29550841104246313208128303 44326261656369469812192455)
        ·
          refine ⟨66489392484554204718288683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44326261656369469812192455 66489392484554204718288683)
          ·
            refine ⟨99734088726831307077433025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66489392484554204718288683 99734088726831307077433025)
            ·
              refine ⟨74800566545123480308074769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99734088726831307077433025 74800566545123480308074769)
              ·
                refine ⟨56100424908842610231056077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74800566545123480308074769 56100424908842610231056077)
                ·
                  refine ⟨21037659340815978836646029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56100424908842610231056077 21037659340815978836646029)
                  ·
                    refine ⟨7889122252805992063742261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21037659340815978836646029 7889122252805992063742261)
                    ·
                      refine ⟨739605211200561755975837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7889122252805992063742261 739605211200561755975837)
                      ·
                        rfl

theorem cell23_1440376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_1440376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440376 prefixEnd_1440376 := by exact prefixLift 1440376
  have htrace : WordTrace (prefixWord ++ tailWord_1440376) baseStart_1440376 baseEnd_1440376 := by
    simpa [prefixWord, tailWord_1440376, baseEnd_1440376] using wordTrace_append hprefix tailTrace_1440376
  have hstable : (prefixWord ++ tailWord_1440376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440376).length < 2 ^ (prefixWord ++ tailWord_1440376).sum := by decide
  have hdescent : baseEnd_1440376 < baseStart_1440376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440377 : List Nat := [1, 2, 1, 3, 3, 2, 3, 2, 1, 3, 2]
def baseStart_1440377 : Nat := 118140960795 + 1440377 * 2 ^ 59
def prefixEnd_1440377 : Nat := 4983230072969 + 3 ^ 40 * 1440377 * 2
def baseEnd_1440377 : Nat := 739605724681216252063333

theorem tailTrace_1440377 : CollatzResearch.WordTrace tailWord_1440377 prefixEnd_1440377 739605724681216252063333 := by
  unfold tailWord_1440377
  simp only [CollatzResearch.WordTrace]
  refine ⟨52534865102767600651903385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35023243401845067101268923 52534865102767600651903385)
  ·
    refine ⟨39401148827075700488927539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52534865102767600651903385 39401148827075700488927539)
    ·
      refine ⟨59101723240613550733391309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39401148827075700488927539 59101723240613550733391309)
      ·
        refine ⟨22163146215230081525021741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59101723240613550733391309 22163146215230081525021741)
        ·
          refine ⟨8311179830711280571883153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22163146215230081525021741 8311179830711280571883153)
          ·
            refine ⟨6233384873033460428912365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8311179830711280571883153 6233384873033460428912365)
            ·
              refine ⟨2337519327387547660842137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6233384873033460428912365 2337519327387547660842137)
              ·
                refine ⟨1753139495540660745631603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2337519327387547660842137 1753139495540660745631603)
                ·
                  refine ⟨2629709243310991118447405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1753139495540660745631603 2629709243310991118447405)
                  ·
                    refine ⟨986140966241621669417777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2629709243310991118447405 986140966241621669417777)
                    ·
                      refine ⟨739605724681216252063333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 986140966241621669417777 739605724681216252063333)
                      ·
                        rfl

theorem cell23_1440377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_1440377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440377 prefixEnd_1440377 := by exact prefixLift 1440377
  have htrace : WordTrace (prefixWord ++ tailWord_1440377) baseStart_1440377 baseEnd_1440377 := by
    simpa [prefixWord, tailWord_1440377, baseEnd_1440377] using wordTrace_append hprefix tailTrace_1440377
  have hstable : (prefixWord ++ tailWord_1440377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440377).length < 2 ^ (prefixWord ++ tailWord_1440377).sum := by decide
  have hdescent : baseEnd_1440377 < baseStart_1440377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440396 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 11]
def baseStart_1440396 : Nat := 118140960795 + 1440396 * 2 ^ 59
def prefixEnd_1440396 : Nat := 4983230072969 + 3 ^ 40 * 1440396 * 2
def baseEnd_1440396 : Nat := 82179497868183519747305

theorem tailTrace_1440396 : CollatzResearch.WordTrace tailWord_1440396 prefixEnd_1440396 82179497868183519747305 := by
  unfold tailWord_1440396
  simp only [CollatzResearch.WordTrace]
  refine ⟨26267779044849383448422521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35023705393132511264563361 26267779044849383448422521)
  ·
    refine ⟨19700834283637037586316891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26267779044849383448422521 19700834283637037586316891)
    ·
      refine ⟨29551251425455556379475337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19700834283637037586316891 29551251425455556379475337)
      ·
        refine ⟨22163438569091667284606503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29551251425455556379475337 22163438569091667284606503)
        ·
          refine ⟨33245157853637500926909755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22163438569091667284606503 33245157853637500926909755)
          ·
            refine ⟨49867736780456251390364633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33245157853637500926909755 49867736780456251390364633)
            ·
              refine ⟨37400802585342188542773475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49867736780456251390364633 37400802585342188542773475)
              ·
                refine ⟨56101203878013282814160213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37400802585342188542773475 56101203878013282814160213)
                ·
                  refine ⟨82179497868183519747305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 56101203878013282814160213 82179497868183519747305)
                  ·
                    rfl

theorem cell23_1440396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 11].length) (baseStart_1440396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440396 prefixEnd_1440396 := by exact prefixLift 1440396
  have htrace : WordTrace (prefixWord ++ tailWord_1440396) baseStart_1440396 baseEnd_1440396 := by
    simpa [prefixWord, tailWord_1440396, baseEnd_1440396] using wordTrace_append hprefix tailTrace_1440396
  have hstable : (prefixWord ++ tailWord_1440396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440396).length < 2 ^ (prefixWord ++ tailWord_1440396).sum := by decide
  have hdescent : baseEnd_1440396 < baseStart_1440396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440430 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 9]
def baseStart_1440430 : Nat := 118140960795 + 1440430 * 2 ^ 59
def prefixEnd_1440430 : Nat := 4983230072969 + 3 ^ 40 * 1440430 * 2
def baseEnd_1440430 : Nat := 82181437683989393855621

theorem tailTrace_1440430 : CollatzResearch.WordTrace tailWord_1440430 prefixEnd_1440430 82181437683989393855621 := by
  unfold tailWord_1440430
  simp only [CollatzResearch.WordTrace]
  refine ⟨6567099771446948837947843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35024532114383727135721829 6567099771446948837947843)
  ·
    refine ⟨9850649657170423256921765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6567099771446948837947843 9850649657170423256921765)
    ·
      refine ⟨1846996810719454360672831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9850649657170423256921765 1846996810719454360672831)
      ·
        refine ⟨2770495216079181541009247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1846996810719454360672831 2770495216079181541009247)
        ·
          refine ⟨4155742824118772311513871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2770495216079181541009247 4155742824118772311513871)
          ·
            refine ⟨6233614236178158467270807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4155742824118772311513871 6233614236178158467270807)
            ·
              refine ⟨9350421354267237700906211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6233614236178158467270807 9350421354267237700906211)
              ·
                refine ⟨14025632031400856551359317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9350421354267237700906211 14025632031400856551359317)
                ·
                  refine ⟨82181437683989393855621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14025632031400856551359317 82181437683989393855621)
                  ·
                    rfl

theorem cell23_1440430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_1440430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440430 prefixEnd_1440430 := by exact prefixLift 1440430
  have htrace : WordTrace (prefixWord ++ tailWord_1440430) baseStart_1440430 baseEnd_1440430 := by
    simpa [prefixWord, tailWord_1440430, baseEnd_1440430] using wordTrace_append hprefix tailTrace_1440430
  have hstable : (prefixWord ++ tailWord_1440430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440430).length < 2 ^ (prefixWord ++ tailWord_1440430).sum := by decide
  have hdescent : baseEnd_1440430 < baseStart_1440430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440553 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 2, 5, 4]
def baseStart_1440553 : Nat := 118140960795 + 1440553 * 2 ^ 59
def prefixEnd_1440553 : Nat := 4983230072969 + 3 ^ 40 * 1440553 * 2
def baseEnd_1440553 : Nat := 739696097276407563462523

theorem tailTrace_1440553 : CollatzResearch.WordTrace tailWord_1440553 prefixEnd_1440553 739696097276407563462523 := by
  unfold tailWord_1440553
  simp only [CollatzResearch.WordTrace]
  refine ⟨52541284350129982710310313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35027522900086655140206875 52541284350129982710310313)
  ·
    refine ⟨39405963262597487032732735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52541284350129982710310313 39405963262597487032732735)
    ·
      refine ⟨59108944893896230549099103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39405963262597487032732735 59108944893896230549099103)
      ·
        refine ⟨88663417340844345823648655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59108944893896230549099103 88663417340844345823648655)
        ·
          refine ⟨132995126011266518735472983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88663417340844345823648655 132995126011266518735472983)
          ·
            refine ⟨199492689016899778103209475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132995126011266518735472983 199492689016899778103209475)
            ·
              refine ⟨299239033525349667154814213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199492689016899778103209475 299239033525349667154814213)
              ·
                refine ⟨56107318786003062591527665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 299239033525349667154814213 56107318786003062591527665)
                ·
                  refine ⟨42080489089502296943645749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56107318786003062591527665 42080489089502296943645749)
                  ·
                    refine ⟨3945045852140840338466789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42080489089502296943645749 3945045852140840338466789)
                    ·
                      refine ⟨739696097276407563462523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3945045852140840338466789 739696097276407563462523)
                      ·
                        rfl

theorem cell23_1440553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 5, 4].length) (baseStart_1440553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440553 prefixEnd_1440553 := by exact prefixLift 1440553
  have htrace : WordTrace (prefixWord ++ tailWord_1440553) baseStart_1440553 baseEnd_1440553 := by
    simpa [prefixWord, tailWord_1440553, baseEnd_1440553] using wordTrace_append hprefix tailTrace_1440553
  have hstable : (prefixWord ++ tailWord_1440553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440553).length < 2 ^ (prefixWord ++ tailWord_1440553).sum := by decide
  have hdescent : baseEnd_1440553 < baseStart_1440553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440567 : List Nat := [1, 1, 3, 1, 2, 1, 7, 1, 1, 5]
def baseStart_1440567 : Nat := 118140960795 + 1440567 * 2 ^ 59
def prefixEnd_1440567 : Nat := 4983230072969 + 3 ^ 40 * 1440567 * 2
def baseEnd_1440567 : Nat := 246567762001856836229153

theorem tailTrace_1440567 : CollatzResearch.WordTrace tailWord_1440567 prefixEnd_1440567 246567762001856836229153 := by
  unfold tailWord_1440567
  simp only [CollatzResearch.WordTrace]
  refine ⟨52541794972079263101319955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35027863314719508734213303 52541794972079263101319955)
  ·
    refine ⟨78812692458118894651979933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52541794972079263101319955 78812692458118894651979933)
    ·
      refine ⟨29554759671794585494492475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78812692458118894651979933 29554759671794585494492475)
      ·
        refine ⟨44332139507691878241738713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29554759671794585494492475 44332139507691878241738713)
        ·
          refine ⟨33249104630768908681304035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44332139507691878241738713 33249104630768908681304035)
          ·
            refine ⟨49873656946153363021956053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33249104630768908681304035 49873656946153363021956053)
            ·
              refine ⟨1168913834675469445827095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 49873656946153363021956053 1168913834675469445827095)
              ·
                refine ⟨1753370752013204168740643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168913834675469445827095 1753370752013204168740643)
                ·
                  refine ⟨2630056128019806253110965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1753370752013204168740643 2630056128019806253110965)
                  ·
                    refine ⟨246567762001856836229153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2630056128019806253110965 246567762001856836229153)
                    ·
                      rfl

theorem cell23_1440567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 1, 5].length) (baseStart_1440567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440567 prefixEnd_1440567 := by exact prefixLift 1440567
  have htrace : WordTrace (prefixWord ++ tailWord_1440567) baseStart_1440567 baseEnd_1440567 := by
    simpa [prefixWord, tailWord_1440567, baseEnd_1440567] using wordTrace_append hprefix tailTrace_1440567
  have hstable : (prefixWord ++ tailWord_1440567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440567).length < 2 ^ (prefixWord ++ tailWord_1440567).sum := by decide
  have hdescent : baseEnd_1440567 < baseStart_1440567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440587 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 9, 2, 2]
def baseStart_1440587 : Nat := 118140960795 + 1440587 * 2 ^ 59
def prefixEnd_1440587 : Nat := 4983230072969 + 3 ^ 40 * 1440587 * 2
def baseEnd_1440587 : Nat := 739713555618660430437367

theorem tailTrace_1440587 : CollatzResearch.WordTrace tailWord_1440587 prefixEnd_1440587 739713555618660430437367 := by
  unfold tailWord_1440587
  simp only [CollatzResearch.WordTrace]
  refine ⟨52542524432006806517048015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35028349621337871011365343 52542524432006806517048015)
  ·
    refine ⟨78813786648010209775572023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52542524432006806517048015 78813786648010209775572023)
    ·
      refine ⟨118220679972015314663358035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78813786648010209775572023 118220679972015314663358035)
      ·
        refine ⟨177331019958022971995037053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118220679972015314663358035 177331019958022971995037053)
        ·
          refine ⟨66499132484258614498138895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177331019958022971995037053 66499132484258614498138895)
          ·
            refine ⟨99748698726387921747208343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66499132484258614498138895 99748698726387921747208343)
            ·
              refine ⟨149623048089581882620812515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99748698726387921747208343 149623048089581882620812515)
              ·
                refine ⟨224434572134372823931218773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149623048089581882620812515 224434572134372823931218773)
                ·
                  refine ⟨1315046321099840765221985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 224434572134372823931218773 1315046321099840765221985)
                  ·
                    refine ⟨986284740824880573916489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1315046321099840765221985 986284740824880573916489)
                    ·
                      refine ⟨739713555618660430437367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 986284740824880573916489 739713555618660430437367)
                      ·
                        rfl

theorem cell23_1440587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 2, 2].length) (baseStart_1440587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440587 prefixEnd_1440587 := by exact prefixLift 1440587
  have htrace : WordTrace (prefixWord ++ tailWord_1440587) baseStart_1440587 baseEnd_1440587 := by
    simpa [prefixWord, tailWord_1440587, baseEnd_1440587] using wordTrace_append hprefix tailTrace_1440587
  have hstable : (prefixWord ++ tailWord_1440587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440587).length < 2 ^ (prefixWord ++ tailWord_1440587).sum := by decide
  have hdescent : baseEnd_1440587 < baseStart_1440587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440590 : List Nat := [4, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5]
def baseStart_1440590 : Nat := 118140960795 + 1440590 * 2 ^ 59
def prefixEnd_1440590 : Nat := 4983230072969 + 3 ^ 40 * 1440590 * 2
def baseEnd_1440590 : Nat := 739715096060623918699853

theorem tailTrace_1440590 : CollatzResearch.WordTrace tailWord_1440590 prefixEnd_1440590 739715096060623918699853 := by
  unfold tailWord_1440590
  simp only [CollatzResearch.WordTrace]
  refine ⟨6567829231374492253675903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35028422567330625352938149 6567829231374492253675903)
  ·
    refine ⟨9851743847061738380513855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6567829231374492253675903 9851743847061738380513855)
    ·
      refine ⟨14777615770592607570770783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9851743847061738380513855 14777615770592607570770783)
      ·
        refine ⟨22166423655888911356156175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14777615770592607570770783 22166423655888911356156175)
        ·
          refine ⟨33249635483833367034234263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22166423655888911356156175 33249635483833367034234263)
          ·
            refine ⟨49874453225750050551351395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33249635483833367034234263 49874453225750050551351395)
            ·
              refine ⟨74811679838625075827027093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49874453225750050551351395 74811679838625075827027093)
              ·
                refine ⟨3506797492435550429391895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74811679838625075827027093 3506797492435550429391895)
                ·
                  refine ⟨5260196238653325644087843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3506797492435550429391895 5260196238653325644087843)
                  ·
                    refine ⟨7890294357979988466131765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5260196238653325644087843 7890294357979988466131765)
                    ·
                      refine ⟨739715096060623918699853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7890294357979988466131765 739715096060623918699853)
                      ·
                        rfl

theorem cell23_1440590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_1440590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440590 prefixEnd_1440590 := by exact prefixLift 1440590
  have htrace : WordTrace (prefixWord ++ tailWord_1440590) baseStart_1440590 baseEnd_1440590 := by
    simpa [prefixWord, tailWord_1440590, baseEnd_1440590] using wordTrace_append hprefix tailTrace_1440590
  have hstable : (prefixWord ++ tailWord_1440590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440590).length < 2 ^ (prefixWord ++ tailWord_1440590).sum := by decide
  have hdescent : baseEnd_1440590 < baseStart_1440590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440597 : List Nat := [1, 3, 2, 2, 2, 1, 1, 5, 2, 4]
def baseStart_1440597 : Nat := 118140960795 + 1440597 * 2 ^ 59
def prefixEnd_1440597 : Nat := 4983230072969 + 3 ^ 40 * 1440597 * 2
def baseEnd_1440597 : Nat := 246572896808401797104107

theorem tailTrace_1440597 : CollatzResearch.WordTrace tailWord_1440597 prefixEnd_1440597 246572896808401797104107 := by
  unfold tailWord_1440597
  simp only [CollatzResearch.WordTrace]
  refine ⟨52542889161970578224912045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35028592774647052149941363 52542889161970578224912045)
  ·
    refine ⟨19703583435738966834342017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52542889161970578224912045 19703583435738966834342017)
    ·
      refine ⟨14777687576804225125756513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19703583435738966834342017 14777687576804225125756513)
      ·
        refine ⟨11083265682603168844317385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14777687576804225125756513 11083265682603168844317385)
        ·
          refine ⟨8312449261952376633238039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11083265682603168844317385 8312449261952376633238039)
          ·
            refine ⟨12468673892928564949857059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8312449261952376633238039 12468673892928564949857059)
            ·
              refine ⟨18703010839392847424785589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12468673892928564949857059 18703010839392847424785589)
              ·
                refine ⟨1753407266193079446073649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18703010839392847424785589 1753407266193079446073649)
                ·
                  refine ⟨1315055449644809584555237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1753407266193079446073649 1315055449644809584555237)
                  ·
                    refine ⟨246572896808401797104107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1315055449644809584555237 246572896808401797104107)
                    ·
                      rfl

theorem cell23_1440597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_1440597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440597 prefixEnd_1440597 := by exact prefixLift 1440597
  have htrace : WordTrace (prefixWord ++ tailWord_1440597) baseStart_1440597 baseEnd_1440597 := by
    simpa [prefixWord, tailWord_1440597, baseEnd_1440597] using wordTrace_append hprefix tailTrace_1440597
  have hstable : (prefixWord ++ tailWord_1440597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440597).length < 2 ^ (prefixWord ++ tailWord_1440597).sum := by decide
  have hdescent : baseEnd_1440597 < baseStart_1440597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440607 : List Nat := [1, 1, 2, 3, 1, 3, 2, 4, 1, 2, 3]
def baseStart_1440607 : Nat := 118140960795 + 1440607 * 2 ^ 59
def prefixEnd_1440607 : Nat := 4983230072969 + 3 ^ 40 * 1440607 * 2
def baseEnd_1440607 : Nat := 739723825231750352187275

theorem tailTrace_1440607 : CollatzResearch.WordTrace tailWord_1440607 prefixEnd_1440607 739723825231750352187275 := by
  unfold tailWord_1440607
  simp only [CollatzResearch.WordTrace]
  refine ⟨52543253891934349932776075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35028835927956233288517383 52543253891934349932776075)
  ·
    refine ⟨78814880837901524899164113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52543253891934349932776075 78814880837901524899164113)
    ·
      refine ⟨59111160628426143674373085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78814880837901524899164113 59111160628426143674373085)
      ·
        refine ⟨22166685235659803877889907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59111160628426143674373085 22166685235659803877889907)
        ·
          refine ⟨33250027853489705816834861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22166685235659803877889907 33250027853489705816834861)
          ·
            refine ⟨12468760445058639681313073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33250027853489705816834861 12468760445058639681313073)
            ·
              refine ⟨9351570333793979760984805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12468760445058639681313073 9351570333793979760984805)
              ·
                refine ⟨1753419437586371205184651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9351570333793979760984805 1753419437586371205184651)
                ·
                  refine ⟨2630129156379556807776977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1753419437586371205184651 2630129156379556807776977)
                  ·
                    refine ⟨1972596867284667605832733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2630129156379556807776977 1972596867284667605832733)
                    ·
                      refine ⟨739723825231750352187275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1972596867284667605832733 739723825231750352187275)
                      ·
                        rfl

theorem cell23_1440607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_1440607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440607 prefixEnd_1440607 := by exact prefixLift 1440607
  have htrace : WordTrace (prefixWord ++ tailWord_1440607) baseStart_1440607 baseEnd_1440607 := by
    simpa [prefixWord, tailWord_1440607, baseEnd_1440607] using wordTrace_append hprefix tailTrace_1440607
  have hstable : (prefixWord ++ tailWord_1440607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440607).length < 2 ^ (prefixWord ++ tailWord_1440607).sum := by decide
  have hdescent : baseEnd_1440607 < baseStart_1440607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440624 : List Nat := [2, 1, 1, 1, 4, 1, 6, 1, 1, 2, 3]
def baseStart_1440624 : Nat := 118140960795 + 1440624 * 2 ^ 59
def prefixEnd_1440624 : Nat := 4983230072969 + 3 ^ 40 * 1440624 * 2
def baseEnd_1440624 : Nat := 739732554402876785674697

theorem tailTrace_1440624 : CollatzResearch.WordTrace tailWord_1440624 prefixEnd_1440624 739732554402876785674697 := by
  unfold tailWord_1440624
  simp only [CollatzResearch.WordTrace]
  refine ⟨26271936966436380918072463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35029249288581841224096617 26271936966436380918072463)
  ·
    refine ⟨39407905449654571377108695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26271936966436380918072463 39407905449654571377108695)
    ·
      refine ⟨59111858174481857065663043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39407905449654571377108695 59111858174481857065663043)
      ·
        refine ⟨88667787261722785598494565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59111858174481857065663043 88667787261722785598494565)
        ·
          refine ⟨16625210111573022299717731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88667787261722785598494565 16625210111573022299717731)
          ·
            refine ⟨24937815167359533449576597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16625210111573022299717731 24937815167359533449576597)
            ·
              refine ⟨1168960085969978130448903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24937815167359533449576597 1168960085969978130448903)
              ·
                refine ⟨1753440128954967195673355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168960085969978130448903 1753440128954967195673355)
                ·
                  refine ⟨2630160193432450793510033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1753440128954967195673355 2630160193432450793510033)
                  ·
                    refine ⟨1972620145074338095132525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2630160193432450793510033 1972620145074338095132525)
                    ·
                      refine ⟨739732554402876785674697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1972620145074338095132525 739732554402876785674697)
                      ·
                        rfl

theorem cell23_1440624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 1, 2, 3].length) (baseStart_1440624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440624 prefixEnd_1440624 := by exact prefixLift 1440624
  have htrace : WordTrace (prefixWord ++ tailWord_1440624) baseStart_1440624 baseEnd_1440624 := by
    simpa [prefixWord, tailWord_1440624, baseEnd_1440624] using wordTrace_append hprefix tailTrace_1440624
  have hstable : (prefixWord ++ tailWord_1440624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440624).length < 2 ^ (prefixWord ++ tailWord_1440624).sum := by decide
  have hdescent : baseEnd_1440624 < baseStart_1440624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440751 : List Nat := [1, 1, 2, 1, 4, 5, 2, 2, 5]
def baseStart_1440751 : Nat := 118140960795 + 1440751 * 2 ^ 59
def prefixEnd_1440751 : Nat := 4983230072969 + 3 ^ 40 * 1440751 * 2
def baseEnd_1440751 : Nat := 82199751827333087642957

theorem tailTrace_1440751 : CollatzResearch.WordTrace tailWord_1440751 prefixEnd_1440751 82199751827333087642957 := by
  unfold tailWord_1440751
  simp only [CollatzResearch.WordTrace]
  refine ⟨52548506003412662526018107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35032337335608441684012071 52548506003412662526018107)
  ·
    refine ⟨78822759005118993789027161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52548506003412662526018107 78822759005118993789027161)
    ·
      refine ⟨59117069253839245341770371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78822759005118993789027161 59117069253839245341770371)
      ·
        refine ⟨88675603880758868012655557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59117069253839245341770371 88675603880758868012655557)
        ·
          refine ⟨16626675727642287752372917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88675603880758868012655557 16626675727642287752372917)
          ·
            refine ⟨1558750849466464476784961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16626675727642287752372917 1558750849466464476784961)
            ·
              refine ⟨1169063137099848357588721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1558750849466464476784961 1169063137099848357588721)
              ·
                refine ⟨876797352824886268191541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1169063137099848357588721 876797352824886268191541)
                ·
                  refine ⟨82199751827333087642957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 876797352824886268191541 82199751827333087642957)
                  ·
                    rfl

theorem cell23_1440751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 5].length) (baseStart_1440751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440751 prefixEnd_1440751 := by exact prefixLift 1440751
  have htrace : WordTrace (prefixWord ++ tailWord_1440751) baseStart_1440751 baseEnd_1440751 := by
    simpa [prefixWord, tailWord_1440751, baseEnd_1440751] using wordTrace_append hprefix tailTrace_1440751
  have hstable : (prefixWord ++ tailWord_1440751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440751).length < 2 ^ (prefixWord ++ tailWord_1440751).sum := by decide
  have hdescent : baseEnd_1440751 < baseStart_1440751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440760 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 2, 8]
def baseStart_1440760 : Nat := 118140960795 + 1440760 * 2 ^ 59
def prefixEnd_1440760 : Nat := 4983230072969 + 3 ^ 40 * 1440760 * 2
def baseEnd_1440760 : Nat := 246600795923962751191357

theorem tailTrace_1440760 : CollatzResearch.WordTrace tailWord_1440760 prefixEnd_1440760 246600795923962751191357 := by
  unfold tailWord_1440760
  simp only [CollatzResearch.WordTrace]
  refine ⟨26274417130190028531547867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35032556173586704708730489 26274417130190028531547867)
  ·
    refine ⟨39411625695285042797321801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26274417130190028531547867 39411625695285042797321801)
    ·
      refine ⟨29558719271463782097991351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39411625695285042797321801 29558719271463782097991351)
      ·
        refine ⟨44338078907195673146987027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29558719271463782097991351 44338078907195673146987027)
        ·
          refine ⟨66507118360793509720480541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44338078907195673146987027 66507118360793509720480541)
          ·
            refine ⟨24940169385297566145180203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66507118360793509720480541 24940169385297566145180203)
            ·
              refine ⟨37410254077946349217770305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24940169385297566145180203 37410254077946349217770305)
              ·
                refine ⟨28057690558459761913327729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37410254077946349217770305 28057690558459761913327729)
                ·
                  refine ⟨21043267918844821434995797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28057690558459761913327729 21043267918844821434995797)
                  ·
                    refine ⟨246600795923962751191357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21043267918844821434995797 246600795923962751191357)
                    ·
                      rfl

theorem cell23_1440760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_1440760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440760 prefixEnd_1440760 := by exact prefixLift 1440760
  have htrace : WordTrace (prefixWord ++ tailWord_1440760) baseStart_1440760 baseEnd_1440760 := by
    simpa [prefixWord, tailWord_1440760, baseEnd_1440760] using wordTrace_append hprefix tailTrace_1440760
  have hstable : (prefixWord ++ tailWord_1440760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440760).length < 2 ^ (prefixWord ++ tailWord_1440760).sum := by decide
  have hdescent : baseEnd_1440760 < baseStart_1440760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440837 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 3, 5]
def baseStart_1440837 : Nat := 118140960795 + 1440837 * 2 ^ 59
def prefixEnd_1440837 : Nat := 4983230072969 + 3 ^ 40 * 1440837 * 2
def baseEnd_1440837 : Nat := 246613975260761484103739

theorem tailTrace_1440837 : CollatzResearch.WordTrace tailWord_1440837 prefixEnd_1440837 246613975260761484103739 := by
  unfold tailWord_1440837
  simp only [CollatzResearch.WordTrace]
  refine ⟨52551642681101099213648765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35034428454067399475765843 52551642681101099213648765)
  ·
    refine ⟨19706866005412912205118287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52551642681101099213648765 19706866005412912205118287)
    ·
      refine ⟨29560299008119368307677431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19706866005412912205118287 29560299008119368307677431)
      ·
        refine ⟨44340448512179052461516147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29560299008119368307677431 44340448512179052461516147)
        ·
          refine ⟨66510672768268578692274221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44340448512179052461516147 66510672768268578692274221)
          ·
            refine ⟨24941502288100717009602833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66510672768268578692274221 24941502288100717009602833)
            ·
              refine ⟨18706126716075537757202125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24941502288100717009602833 18706126716075537757202125)
              ·
                refine ⟨7014797518528326658950797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18706126716075537757202125 7014797518528326658950797)
                ·
                  refine ⟨2630549069448122497106549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7014797518528326658950797 2630549069448122497106549)
                  ·
                    refine ⟨246613975260761484103739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2630549069448122497106549 246613975260761484103739)
                    ·
                      rfl

theorem cell23_1440837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_1440837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440837 prefixEnd_1440837 := by exact prefixLift 1440837
  have htrace : WordTrace (prefixWord ++ tailWord_1440837) baseStart_1440837 baseEnd_1440837 := by
    simpa [prefixWord, tailWord_1440837, baseEnd_1440837] using wordTrace_append hprefix tailTrace_1440837
  have hstable : (prefixWord ++ tailWord_1440837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440837).length < 2 ^ (prefixWord ++ tailWord_1440837).sum := by decide
  have hdescent : baseEnd_1440837 < baseStart_1440837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440845 : List Nat := [1, 6, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_1440845 : Nat := 118140960795 + 1440845 * 2 ^ 59
def prefixEnd_1440845 : Nat := 4983230072969 + 3 ^ 40 * 1440845 * 2
def baseEnd_1440845 : Nat := 246615344542506807003727

theorem tailTrace_1440845 : CollatzResearch.WordTrace tailWord_1440845 prefixEnd_1440845 246615344542506807003727 := by
  unfold tailWord_1440845
  simp only [CollatzResearch.WordTrace]
  refine ⟨52551934465072116579939989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35034622976714744386626659 52551934465072116579939989)
  ·
    refine ⟨2463371928050255464684687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52551934465072116579939989 2463371928050255464684687)
    ·
      refine ⟨3695057892075383197027031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2463371928050255464684687 3695057892075383197027031)
      ·
        refine ⟨5542586838113074795540547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3695057892075383197027031 5542586838113074795540547)
        ·
          refine ⟨8313880257169612193310821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5542586838113074795540547 8313880257169612193310821)
          ·
            refine ⟨1558852548219302286245779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8313880257169612193310821 1558852548219302286245779)
            ·
              refine ⟨2338278822328953429368669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1558852548219302286245779 2338278822328953429368669)
              ·
                refine ⟨876854558373357536013251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2338278822328953429368669 876854558373357536013251)
                ·
                  refine ⟨1315281837560036304019877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876854558373357536013251 1315281837560036304019877)
                  ·
                    refine ⟨246615344542506807003727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1315281837560036304019877 246615344542506807003727)
                    ·
                      rfl

theorem cell23_1440845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_1440845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440845 prefixEnd_1440845 := by exact prefixLift 1440845
  have htrace : WordTrace (prefixWord ++ tailWord_1440845) baseStart_1440845 baseEnd_1440845 := by
    simpa [prefixWord, tailWord_1440845, baseEnd_1440845] using wordTrace_append hprefix tailTrace_1440845
  have hstable : (prefixWord ++ tailWord_1440845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440845).length < 2 ^ (prefixWord ++ tailWord_1440845).sum := by decide
  have hdescent : baseEnd_1440845 < baseStart_1440845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440887 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 6]
def baseStart_1440887 : Nat := 118140960795 + 1440887 * 2 ^ 59
def prefixEnd_1440887 : Nat := 4983230072969 + 3 ^ 40 * 1440887 * 2
def baseEnd_1440887 : Nat := 739867599815009256685987

theorem tailTrace_1440887 : CollatzResearch.WordTrace tailWord_1440887 prefixEnd_1440887 739867599815009256685987 := by
  unfold tailWord_1440887
  simp only [CollatzResearch.WordTrace]
  refine ⟨52553466330919957752968915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35035644220613305168645943 52553466330919957752968915)
  ·
    refine ⟨78830199496379936629453373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52553466330919957752968915 78830199496379936629453373)
    ·
      refine ⟨29561324811142476236045015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78830199496379936629453373 29561324811142476236045015)
      ·
        refine ⟨44341987216713714354067523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29561324811142476236045015 44341987216713714354067523)
        ·
          refine ⟨66512980825070571531101285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44341987216713714354067523 66512980825070571531101285)
          ·
            refine ⟨12471183904700732162081491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66512980825070571531101285 12471183904700732162081491)
            ·
              refine ⟨18706775857051098243122237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12471183904700732162081491 18706775857051098243122237)
              ·
                refine ⟨7015040946394161841170839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18706775857051098243122237 7015040946394161841170839)
                ·
                  refine ⟨10522561419591242761756259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7015040946394161841170839 10522561419591242761756259)
                  ·
                    refine ⟨15783842129386864142634389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10522561419591242761756259 15783842129386864142634389)
                    ·
                      refine ⟨739867599815009256685987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15783842129386864142634389 739867599815009256685987)
                      ·
                        rfl

theorem cell23_1440887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_1440887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440887 prefixEnd_1440887 := by exact prefixLift 1440887
  have htrace : WordTrace (prefixWord ++ tailWord_1440887) baseStart_1440887 baseEnd_1440887 := by
    simpa [prefixWord, tailWord_1440887, baseEnd_1440887] using wordTrace_append hprefix tailTrace_1440887
  have hstable : (prefixWord ++ tailWord_1440887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440887).length < 2 ^ (prefixWord ++ tailWord_1440887).sum := by decide
  have hdescent : baseEnd_1440887 < baseStart_1440887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440891 : List Nat := [1, 1, 1, 1, 1, 4, 1, 6, 3, 2, 2]
def baseStart_1440891 : Nat := 118140960795 + 1440891 * 2 ^ 59
def prefixEnd_1440891 : Nat := 4983230072969 + 3 ^ 40 * 1440891 * 2
def baseEnd_1440891 : Nat := 739869653737627241035969

theorem tailTrace_1440891 : CollatzResearch.WordTrace tailWord_1440891 prefixEnd_1440891 739869653737627241035969 := by
  unfold tailWord_1440891
  simp only [CollatzResearch.WordTrace]
  refine ⟨52553612222905466436114527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35035741481936977624076351 52553612222905466436114527)
  ·
    refine ⟨78830418334358199654171791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52553612222905466436114527 78830418334358199654171791)
    ·
      refine ⟨118245627501537299481257687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78830418334358199654171791 118245627501537299481257687)
      ·
        refine ⟨177368441252305949221886531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118245627501537299481257687 177368441252305949221886531)
        ·
          refine ⟨266052661878458923832829797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177368441252305949221886531 266052661878458923832829797)
          ·
            refine ⟨49884874102211048218655587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 266052661878458923832829797 49884874102211048218655587)
            ·
              refine ⟨74827311153316572327983381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49884874102211048218655587 74827311153316572327983381)
              ·
                refine ⟨3507530210311714327874221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74827311153316572327983381 3507530210311714327874221)
                ·
                  refine ⟨1315323828866892872952833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3507530210311714327874221 1315323828866892872952833)
                  ·
                    refine ⟨986492871650169654714625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1315323828866892872952833 986492871650169654714625)
                    ·
                      refine ⟨739869653737627241035969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 986492871650169654714625 739869653737627241035969)
                      ·
                        rfl

theorem cell23_1440891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 2, 2].length) (baseStart_1440891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440891 prefixEnd_1440891 := by exact prefixLift 1440891
  have htrace : WordTrace (prefixWord ++ tailWord_1440891) baseStart_1440891 baseEnd_1440891 := by
    simpa [prefixWord, tailWord_1440891, baseEnd_1440891] using wordTrace_append hprefix tailTrace_1440891
  have hstable : (prefixWord ++ tailWord_1440891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440891).length < 2 ^ (prefixWord ++ tailWord_1440891).sum := by decide
  have hdescent : baseEnd_1440891 < baseStart_1440891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440917 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_1440917 : Nat := 118140960795 + 1440917 * 2 ^ 59
def prefixEnd_1440917 : Nat := 4983230072969 + 3 ^ 40 * 1440917 * 2
def baseEnd_1440917 : Nat := 739883004234644139310849

theorem tailTrace_1440917 : CollatzResearch.WordTrace tailWord_1440917 prefixEnd_1440917 739883004234644139310849 := by
  unfold tailWord_1440917
  simp only [CollatzResearch.WordTrace]
  refine ⟨52554560520811272876561005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35036373680540848584374003 52554560520811272876561005)
  ·
    refine ⟨19707960195304227328710377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52554560520811272876561005 19707960195304227328710377)
    ·
      refine ⟨14780970146478170496532783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19707960195304227328710377 14780970146478170496532783)
      ·
        refine ⟨22171455219717255744799175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14780970146478170496532783 22171455219717255744799175)
        ·
          refine ⟨33257182829575883617198763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22171455219717255744799175 33257182829575883617198763)
          ·
            refine ⟨49885774244363825425798145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33257182829575883617198763 49885774244363825425798145)
            ·
              refine ⟨37414330683272869069348609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49885774244363825425798145 37414330683272869069348609)
              ·
                refine ⟨28060748012454651802011457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37414330683272869069348609 28060748012454651802011457)
                ·
                  refine ⟨21045561009340988851508593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28060748012454651802011457 21045561009340988851508593)
                  ·
                    refine ⟨15784170757005741638631445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21045561009340988851508593 15784170757005741638631445)
                    ·
                      refine ⟨739883004234644139310849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15784170757005741638631445 739883004234644139310849)
                      ·
                        rfl

theorem cell23_1440917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_1440917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440917 prefixEnd_1440917 := by exact prefixLift 1440917
  have htrace : WordTrace (prefixWord ++ tailWord_1440917) baseStart_1440917 baseEnd_1440917 := by
    simpa [prefixWord, tailWord_1440917, baseEnd_1440917] using wordTrace_append hprefix tailTrace_1440917
  have hstable : (prefixWord ++ tailWord_1440917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440917).length < 2 ^ (prefixWord ++ tailWord_1440917).sum := by decide
  have hdescent : baseEnd_1440917 < baseStart_1440917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440925 : List Nat := [1, 4, 2, 1, 1, 2, 3, 4, 1, 2, 2]
def baseStart_1440925 : Nat := 118140960795 + 1440925 * 2 ^ 59
def prefixEnd_1440925 : Nat := 4983230072969 + 3 ^ 40 * 1440925 * 2
def baseEnd_1440925 : Nat := 739887112079880108010813

theorem tailTrace_1440925 : CollatzResearch.WordTrace tailWord_1440925 prefixEnd_1440925 739887112079880108010813 := by
  unfold tailWord_1440925
  simp only [CollatzResearch.WordTrace]
  refine ⟨52554852304782290242852229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35036568203188193495234819 52554852304782290242852229)
  ·
    refine ⟨9854034807146679420534793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52554852304782290242852229 9854034807146679420534793)
    ·
      refine ⟨7390526105360009565401095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9854034807146679420534793 7390526105360009565401095)
      ·
        refine ⟨11085789158040014348101643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7390526105360009565401095 11085789158040014348101643)
        ·
          refine ⟨16628683737060021522152465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11085789158040014348101643 16628683737060021522152465)
          ·
            refine ⟨12471512802795016141614349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16628683737060021522152465 12471512802795016141614349)
            ·
              refine ⟨4676817301048131053105381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12471512802795016141614349 4676817301048131053105381)
              ·
                refine ⟨876903243946524572457259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4676817301048131053105381 876903243946524572457259)
                ·
                  refine ⟨1315354865919786858685889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876903243946524572457259 1315354865919786858685889)
                  ·
                    refine ⟨986516149439840144014417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1315354865919786858685889 986516149439840144014417)
                    ·
                      refine ⟨739887112079880108010813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 986516149439840144014417 739887112079880108010813)
                      ·
                        rfl

theorem cell23_1440925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_1440925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440925 prefixEnd_1440925 := by exact prefixLift 1440925
  have htrace : WordTrace (prefixWord ++ tailWord_1440925) baseStart_1440925 baseEnd_1440925 := by
    simpa [prefixWord, tailWord_1440925, baseEnd_1440925] using wordTrace_append hprefix tailTrace_1440925
  have hstable : (prefixWord ++ tailWord_1440925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440925).length < 2 ^ (prefixWord ++ tailWord_1440925).sum := by decide
  have hdescent : baseEnd_1440925 < baseStart_1440925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440937 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 6, 2, 5]
def baseStart_1440937 : Nat := 118140960795 + 1440937 * 2 ^ 59
def prefixEnd_1440937 : Nat := 4983230072969 + 3 ^ 40 * 1440937 * 2
def baseEnd_1440937 : Nat := 739893273847734061060757

theorem tailTrace_1440937 : CollatzResearch.WordTrace tailWord_1440937 prefixEnd_1440937 739893273847734061060757 := by
  unfold tailWord_1440937
  simp only [CollatzResearch.WordTrace]
  refine ⟨52555289980738816292289065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35036859987159210861526043 52555289980738816292289065)
  ·
    refine ⟨39416467485554112219216799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52555289980738816292289065 39416467485554112219216799)
    ·
      refine ⟨59124701228331168328825199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39416467485554112219216799 59124701228331168328825199)
      ·
        refine ⟨88687051842496752493237799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59124701228331168328825199 88687051842496752493237799)
        ·
          refine ⟨133030577763745128739856699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88687051842496752493237799 133030577763745128739856699)
          ·
            refine ⟨199545866645617693109785049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133030577763745128739856699 199545866645617693109785049)
            ·
              refine ⟨149659399984213269832338787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199545866645617693109785049 149659399984213269832338787)
              ·
                refine ⟨224489099976319904748508181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149659399984213269832338787 224489099976319904748508181)
                ·
                  refine ⟨10522926561389995535086321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 224489099976319904748508181 10522926561389995535086321)
                  ·
                    refine ⟨7892194921042496651314741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10522926561389995535086321 7892194921042496651314741)
                    ·
                      refine ⟨739893273847734061060757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7892194921042496651314741 739893273847734061060757)
                      ·
                        rfl

theorem cell23_1440937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_1440937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440937 prefixEnd_1440937 := by exact prefixLift 1440937
  have htrace : WordTrace (prefixWord ++ tailWord_1440937) baseStart_1440937 baseEnd_1440937 := by
    simpa [prefixWord, tailWord_1440937, baseEnd_1440937] using wordTrace_append hprefix tailTrace_1440937
  have hstable : (prefixWord ++ tailWord_1440937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440937).length < 2 ^ (prefixWord ++ tailWord_1440937).sum := by decide
  have hdescent : baseEnd_1440937 < baseStart_1440937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440938 : List Nat := [3, 1, 5, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1440938 : Nat := 118140960795 + 1440938 * 2 ^ 59
def prefixEnd_1440938 : Nat := 4983230072969 + 3 ^ 40 * 1440938 * 2
def baseEnd_1440938 : Nat := 739893787328388557148253

theorem tailTrace_1440938 : CollatzResearch.WordTrace tailWord_1440938 prefixEnd_1440938 739893787328388557148253 := by
  unfold tailWord_1440938
  simp only [CollatzResearch.WordTrace]
  refine ⟨13138831613433798365768867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35036884302490128975383645 13138831613433798365768867)
  ·
    refine ⟨19708247420150697548653301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13138831613433798365768867 19708247420150697548653301)
    ·
      refine ⟨1847648195639127895186247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19708247420150697548653301 1847648195639127895186247)
      ·
        refine ⟨2771472293458691842779371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1847648195639127895186247 2771472293458691842779371)
        ·
          refine ⟨4157208440188037764169057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2771472293458691842779371 4157208440188037764169057)
          ·
            refine ⟨3117906330141028323126793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4157208440188037764169057 3117906330141028323126793)
            ·
              refine ⟨2338429747605771242345095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3117906330141028323126793 2338429747605771242345095)
              ·
                refine ⟨3507644621408656863517643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2338429747605771242345095 3507644621408656863517643)
                ·
                  refine ⟨5261466932112985295276465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3507644621408656863517643 5261466932112985295276465)
                  ·
                    refine ⟨3946100199084738971457349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5261466932112985295276465 3946100199084738971457349)
                    ·
                      refine ⟨739893787328388557148253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3946100199084738971457349 739893787328388557148253)
                      ·
                        rfl

theorem cell23_1440938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1440938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440938 prefixEnd_1440938 := by exact prefixLift 1440938
  have htrace : WordTrace (prefixWord ++ tailWord_1440938) baseStart_1440938 baseEnd_1440938 := by
    simpa [prefixWord, tailWord_1440938, baseEnd_1440938] using wordTrace_append hprefix tailTrace_1440938
  have hstable : (prefixWord ++ tailWord_1440938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440938).length < 2 ^ (prefixWord ++ tailWord_1440938).sum := by decide
  have hdescent : baseEnd_1440938 < baseStart_1440938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440951 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 3, 3, 2]
def baseStart_1440951 : Nat := 118140960795 + 1440951 * 2 ^ 59
def prefixEnd_1440951 : Nat := 4983230072969 + 3 ^ 40 * 1440951 * 2
def baseEnd_1440951 : Nat := 739900462576897006285693

theorem tailTrace_1440951 : CollatzResearch.WordTrace tailWord_1440951 prefixEnd_1440951 739900462576897006285693 := by
  unfold tailWord_1440951
  simp only [CollatzResearch.WordTrace]
  refine ⟨52555800602688096683298707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35037200401792064455532471 52555800602688096683298707)
  ·
    refine ⟨78833700904032145024948061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52555800602688096683298707 78833700904032145024948061)
    ·
      refine ⟨29562637839012054384355523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78833700904032145024948061 29562637839012054384355523)
      ·
        refine ⟨44343956758518081576533285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29562637839012054384355523 44343956758518081576533285)
        ·
          refine ⟨8314491892222140295599991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44343956758518081576533285 8314491892222140295599991)
          ·
            refine ⟨12471737838333210443399987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8314491892222140295599991 12471737838333210443399987)
            ·
              refine ⟨18707606757499815665099981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12471737838333210443399987 18707606757499815665099981)
              ·
                refine ⟨7015352534062430874412493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18707606757499815665099981 7015352534062430874412493)
                ·
                  refine ⟨2630757200273411577904685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7015352534062430874412493 2630757200273411577904685)
                  ·
                    refine ⟨986533950102529341714257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2630757200273411577904685 986533950102529341714257)
                    ·
                      refine ⟨739900462576897006285693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 986533950102529341714257 739900462576897006285693)
                      ·
                        rfl

theorem cell23_1440951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 3, 2].length) (baseStart_1440951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440951 prefixEnd_1440951 := by exact prefixLift 1440951
  have htrace : WordTrace (prefixWord ++ tailWord_1440951) baseStart_1440951 baseEnd_1440951 := by
    simpa [prefixWord, tailWord_1440951, baseEnd_1440951] using wordTrace_append hprefix tailTrace_1440951
  have hstable : (prefixWord ++ tailWord_1440951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440951).length < 2 ^ (prefixWord ++ tailWord_1440951).sum := by decide
  have hdescent : baseEnd_1440951 < baseStart_1440951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1440962 : List Nat := [3, 5, 1, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_1440962 : Nat := 118140960795 + 1440962 * 2 ^ 59
def prefixEnd_1440962 : Nat := 4983230072969 + 3 ^ 40 * 1440962 * 2
def baseEnd_1440962 : Nat := 739906110864096463248143

theorem tailTrace_1440962 : CollatzResearch.WordTrace tailWord_1440962 prefixEnd_1440962 739906110864096463248143 := by
  unfold tailWord_1440962
  simp only [CollatzResearch.WordTrace]
  refine ⟨13139050451412061390487285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35037467870432163707966093 13139050451412061390487285)
  ·
    refine ⟨1231785979819880755358183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13139050451412061390487285 1231785979819880755358183)
    ·
      refine ⟨1847678969729821133037275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1231785979819880755358183 1847678969729821133037275)
      ·
        refine ⟨2771518454594731699555913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1847678969729821133037275 2771518454594731699555913)
        ·
          refine ⟨2078638840946048774666935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2771518454594731699555913 2078638840946048774666935)
          ·
            refine ⟨3117958261419073162000403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2078638840946048774666935 3117958261419073162000403)
            ·
              refine ⟨4676937392128609743000605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3117958261419073162000403 4676937392128609743000605)
              ·
                refine ⟨1753851522048228653625227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4676937392128609743000605 1753851522048228653625227)
                ·
                  refine ⟨2630777283072342980437841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1753851522048228653625227 2630777283072342980437841)
                  ·
                    refine ⟨1973082962304257235328381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2630777283072342980437841 1973082962304257235328381)
                    ·
                      refine ⟨739906110864096463248143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1973082962304257235328381 739906110864096463248143)
                      ·
                        rfl

theorem cell23_1440962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_1440962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1440962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1440962 prefixEnd_1440962 := by exact prefixLift 1440962
  have htrace : WordTrace (prefixWord ++ tailWord_1440962) baseStart_1440962 baseEnd_1440962 := by
    simpa [prefixWord, tailWord_1440962, baseEnd_1440962] using wordTrace_append hprefix tailTrace_1440962
  have hstable : (prefixWord ++ tailWord_1440962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1440962).length < 2 ^ (prefixWord ++ tailWord_1440962).sum := by decide
  have hdescent : baseEnd_1440962 < baseStart_1440962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1440962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441004 : List Nat := [2, 2, 1, 1, 2, 4, 2, 2, 7]
def baseStart_1441004 : Nat := 118140960795 + 1441004 * 2 ^ 59
def prefixEnd_1441004 : Nat := 4983230072969 + 3 ^ 40 * 1441004 * 2
def baseEnd_1441004 : Nat := 82214186339065033213661

theorem tailTrace_1441004 : CollatzResearch.WordTrace tailWord_1441004 prefixEnd_1441004 82214186339065033213661 := by
  unfold tailWord_1441004
  simp only [CollatzResearch.WordTrace]
  refine ⟨26278866835748043367489033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35038489114330724489985377 26278866835748043367489033)
  ·
    refine ⟨19709150126811032525616775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26278866835748043367489033 19709150126811032525616775)
    ·
      refine ⟨29563725190216548788425163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19709150126811032525616775 29563725190216548788425163)
      ·
        refine ⟨44345587785324823182637745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29563725190216548788425163 44345587785324823182637745)
        ·
          refine ⟨33259190838993617386978309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44345587785324823182637745 33259190838993617386978309)
          ·
            refine ⟨6236098282311303260058433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33259190838993617386978309 6236098282311303260058433)
            ·
              refine ⟨4677073711733477445043825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6236098282311303260058433 4677073711733477445043825)
              ·
                refine ⟨3507805283800108083782869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4677073711733477445043825 3507805283800108083782869)
                ·
                  refine ⟨82214186339065033213661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3507805283800108083782869 82214186339065033213661)
                  ·
                    rfl

theorem cell23_1441004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 7].length) (baseStart_1441004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441004 prefixEnd_1441004 := by exact prefixLift 1441004
  have htrace : WordTrace (prefixWord ++ tailWord_1441004) baseStart_1441004 baseEnd_1441004 := by
    simpa [prefixWord, tailWord_1441004, baseEnd_1441004] using wordTrace_append hprefix tailTrace_1441004
  have hstable : (prefixWord ++ tailWord_1441004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441004).length < 2 ^ (prefixWord ++ tailWord_1441004).sum := by decide
  have hdescent : baseEnd_1441004 < baseStart_1441004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441041 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 2, 5, 2]
def baseStart_1441041 : Nat := 118140960795 + 1441041 * 2 ^ 59
def prefixEnd_1441041 : Nat := 4983230072969 + 3 ^ 40 * 1441041 * 2
def baseEnd_1441041 : Nat := 739946675835801654160279

theorem tailTrace_1441041 : CollatzResearch.WordTrace tailWord_1441041 prefixEnd_1441041 739946675835801654160279 := by
  unfold tailWord_1441041
  simp only [CollatzResearch.WordTrace]
  refine ⟨52559083172362042054074977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35039388781574694702716651 52559083172362042054074977)
  ·
    refine ⟨39419312379271531540556233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52559083172362042054074977 39419312379271531540556233)
    ·
      refine ⟨29564484284453648655417175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39419312379271531540556233 29564484284453648655417175)
      ·
        refine ⟨44346726426680472983125763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29564484284453648655417175 44346726426680472983125763)
        ·
          refine ⟨66520089640020709474688645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44346726426680472983125763 66520089640020709474688645)
          ·
            refine ⟨12472516807503883026504121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66520089640020709474688645 12472516807503883026504121)
            ·
              refine ⟨9354387605627912269878091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12472516807503883026504121 9354387605627912269878091)
              ·
                refine ⟨14031581408441868404817137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9354387605627912269878091 14031581408441868404817137)
                ·
                  refine ⟨10523686056331401303612853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14031581408441868404817137 10523686056331401303612853)
                  ·
                    refine ⟨986595567781068872213705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10523686056331401303612853 986595567781068872213705)
                    ·
                      refine ⟨739946675835801654160279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 986595567781068872213705 739946675835801654160279)
                      ·
                        rfl

theorem cell23_1441041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 5, 2].length) (baseStart_1441041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441041 prefixEnd_1441041 := by exact prefixLift 1441041
  have htrace : WordTrace (prefixWord ++ tailWord_1441041) baseStart_1441041 baseEnd_1441041 := by
    simpa [prefixWord, tailWord_1441041, baseEnd_1441041] using wordTrace_append hprefix tailTrace_1441041
  have hstable : (prefixWord ++ tailWord_1441041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441041).length < 2 ^ (prefixWord ++ tailWord_1441041).sum := by decide
  have hdescent : baseEnd_1441041 < baseStart_1441041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441071 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 4, 4, 2]
def baseStart_1441071 : Nat := 118140960795 + 1441071 * 2 ^ 59
def prefixEnd_1441071 : Nat := 4983230072969 + 3 ^ 40 * 1441071 * 2
def baseEnd_1441071 : Nat := 739962080255436536785141

theorem tailTrace_1441071 : CollatzResearch.WordTrace tailWord_1441071 prefixEnd_1441071 739962080255436536785141 := by
  unfold tailWord_1441071
  simp only [CollatzResearch.WordTrace]
  refine ⟨52560177362253357177667067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35040118241502238118444711 52560177362253357177667067)
  ·
    refine ⟨78840266043380035766500601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52560177362253357177667067 78840266043380035766500601)
    ·
      refine ⟨59130199532535026824875451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78840266043380035766500601 59130199532535026824875451)
      ·
        refine ⟨88695299298802540237313177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59130199532535026824875451 88695299298802540237313177)
        ·
          refine ⟨66521474474101905177984883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88695299298802540237313177 66521474474101905177984883)
          ·
            refine ⟨99782211711152857766977325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66521474474101905177984883 99782211711152857766977325)
            ·
              refine ⟨37418329391682321662616497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99782211711152857766977325 37418329391682321662616497)
              ·
                refine ⟨28063747043761741246962373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37418329391682321662616497 28063747043761741246962373)
                ·
                  refine ⟨5261952570705326483805445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28063747043761741246962373 5261952570705326483805445)
                  ·
                    refine ⟨986616107007248715713521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5261952570705326483805445 986616107007248715713521)
                    ·
                      refine ⟨739962080255436536785141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 986616107007248715713521 739962080255436536785141)
                      ·
                        rfl

theorem cell23_1441071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 4, 2].length) (baseStart_1441071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441071 prefixEnd_1441071 := by exact prefixLift 1441071
  have htrace : WordTrace (prefixWord ++ tailWord_1441071) baseStart_1441071 baseEnd_1441071 := by
    simpa [prefixWord, tailWord_1441071, baseEnd_1441071] using wordTrace_append hprefix tailTrace_1441071
  have hstable : (prefixWord ++ tailWord_1441071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441071).length < 2 ^ (prefixWord ++ tailWord_1441071).sum := by decide
  have hdescent : baseEnd_1441071 < baseStart_1441071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441111 : List Nat := [1, 1, 3, 2, 3, 2, 2, 3, 6]
def baseStart_1441111 : Nat := 118140960795 + 1441111 * 2 ^ 59
def prefixEnd_1441111 : Nat := 4983230072969 + 3 ^ 40 * 1441111 * 2
def baseEnd_1441111 : Nat := 82220291053512931142773

theorem tailTrace_1441111 : CollatzResearch.WordTrace tailWord_1441111 prefixEnd_1441111 82220291053512931142773 := by
  unfold tailWord_1441111
  simp only [CollatzResearch.WordTrace]
  refine ⟨52561636282108444009123187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35041090854738962672748791 52561636282108444009123187)
  ·
    refine ⟨78842454423162666013684781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52561636282108444009123187 78842454423162666013684781)
    ·
      refine ⟨29565920408685999755131793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78842454423162666013684781 29565920408685999755131793)
      ·
        refine ⟨22174440306514499816348845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29565920408685999755131793 22174440306514499816348845)
        ·
          refine ⟨8315415114942937431130817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22174440306514499816348845 8315415114942937431130817)
          ·
            refine ⟨6236561336207203073348113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8315415114942937431130817 6236561336207203073348113)
            ·
              refine ⟨4677421002155402305011085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6236561336207203073348113 4677421002155402305011085)
              ·
                refine ⟨1754032875808275864379157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4677421002155402305011085 1754032875808275864379157)
                ·
                  refine ⟨82220291053512931142773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1754032875808275864379157 82220291053512931142773)
                  ·
                    rfl

theorem cell23_1441111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 6].length) (baseStart_1441111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441111 prefixEnd_1441111 := by exact prefixLift 1441111
  have htrace : WordTrace (prefixWord ++ tailWord_1441111) baseStart_1441111 baseEnd_1441111 := by
    simpa [prefixWord, tailWord_1441111, baseEnd_1441111] using wordTrace_append hprefix tailTrace_1441111
  have hstable : (prefixWord ++ tailWord_1441111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441111).length < 2 ^ (prefixWord ++ tailWord_1441111).sum := by decide
  have hdescent : baseEnd_1441111 < baseStart_1441111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441138 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 5, 1, 3]
def baseStart_1441138 : Nat := 118140960795 + 1441138 * 2 ^ 59
def prefixEnd_1441138 : Nat := 4983230072969 + 3 ^ 40 * 1441138 * 2
def baseEnd_1441138 : Nat := 739996483459287774647333

theorem tailTrace_1441138 : CollatzResearch.WordTrace tailWord_1441138 prefixEnd_1441138 739996483459287774647333 := by
  unfold tailWord_1441138
  simp only [CollatzResearch.WordTrace]
  refine ⟨13140655263252656905089017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35041747368673751746904045 13140655263252656905089017)
  ·
    refine ⟨9855491447439492678816763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13140655263252656905089017 9855491447439492678816763)
    ·
      refine ⟨14783237171159239018225145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9855491447439492678816763 14783237171159239018225145)
      ·
        refine ⟨11087427878369429263668859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14783237171159239018225145 11087427878369429263668859)
        ·
          refine ⟨16631141817554143895503289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11087427878369429263668859 16631141817554143895503289)
          ·
            refine ⟨12473356363165607921627467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16631141817554143895503289 12473356363165607921627467)
            ·
              refine ⟨18710034544748411882441201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12473356363165607921627467 18710034544748411882441201)
              ·
                refine ⟨14032525908561308911830901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18710034544748411882441201 14032525908561308911830901)
                ·
                  refine ⟨1315549303927622710484147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14032525908561308911830901 1315549303927622710484147)
                  ·
                    refine ⟨1973323955891434065726221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1315549303927622710484147 1973323955891434065726221)
                    ·
                      refine ⟨739996483459287774647333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1973323955891434065726221 739996483459287774647333)
                      ·
                        rfl

theorem cell23_1441138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_1441138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441138 prefixEnd_1441138 := by exact prefixLift 1441138
  have htrace : WordTrace (prefixWord ++ tailWord_1441138) baseStart_1441138 baseEnd_1441138 := by
    simpa [prefixWord, tailWord_1441138, baseEnd_1441138] using wordTrace_append hprefix tailTrace_1441138
  have hstable : (prefixWord ++ tailWord_1441138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441138).length < 2 ^ (prefixWord ++ tailWord_1441138).sum := by decide
  have hdescent : baseEnd_1441138 < baseStart_1441138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441148 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 4, 3, 2]
def baseStart_1441148 : Nat := 118140960795 + 1441148 * 2 ^ 59
def prefixEnd_1441148 : Nat := 4983230072969 + 3 ^ 40 * 1441148 * 2
def baseEnd_1441148 : Nat := 740001618265832735522287

theorem tailTrace_1441148 : CollatzResearch.WordTrace tailWord_1441148 prefixEnd_1441148 740001618265832735522287 := by
  unfold tailWord_1441148
  simp only [CollatzResearch.WordTrace]
  refine ⟨26281492891487199664110049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35041990521982932885480065 26281492891487199664110049)
  ·
    refine ⟨19711119668615399748082537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26281492891487199664110049 19711119668615399748082537)
    ·
      refine ⟨14783339751461549811061903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19711119668615399748082537 14783339751461549811061903)
      ·
        refine ⟨22175009627192324716592855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14783339751461549811061903 22175009627192324716592855)
        ·
          refine ⟨33262514440788487074889283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22175009627192324716592855 33262514440788487074889283)
          ·
            refine ⟨49893771661182730612333925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33262514440788487074889283 49893771661182730612333925)
            ·
              refine ⟨9355082186471761989812611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49893771661182730612333925 9355082186471761989812611)
              ·
                refine ⟨14032623279707642984718917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9355082186471761989812611 14032623279707642984718917)
                ·
                  refine ⟨2631116864945183059634797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14032623279707642984718917 2631116864945183059634797)
                  ·
                    refine ⟨986668824354443647363049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2631116864945183059634797 986668824354443647363049)
                    ·
                      refine ⟨740001618265832735522287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 986668824354443647363049 740001618265832735522287)
                      ·
                        rfl

theorem cell23_1441148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_1441148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441148 prefixEnd_1441148 := by exact prefixLift 1441148
  have htrace : WordTrace (prefixWord ++ tailWord_1441148) baseStart_1441148 baseEnd_1441148 := by
    simpa [prefixWord, tailWord_1441148, baseEnd_1441148] using wordTrace_append hprefix tailTrace_1441148
  have hstable : (prefixWord ++ tailWord_1441148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441148).length < 2 ^ (prefixWord ++ tailWord_1441148).sum := by decide
  have hdescent : baseEnd_1441148 < baseStart_1441148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441155 : List Nat := [1, 1, 1, 3, 5, 2, 2, 1, 3, 1, 3]
def baseStart_1441155 : Nat := 118140960795 + 1441155 * 2 ^ 59
def prefixEnd_1441155 : Nat := 4983230072969 + 3 ^ 40 * 1441155 * 2
def baseEnd_1441155 : Nat := 740005212630414208134755

theorem tailTrace_1441155 : CollatzResearch.WordTrace tailWord_1441155 prefixEnd_1441155 740005212630414208134755 := by
  unfold tailWord_1441155
  simp only [CollatzResearch.WordTrace]
  refine ⟨52563241093949039523724919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35042160729299359682483279 52563241093949039523724919)
  ·
    refine ⟨78844861640923559285587379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52563241093949039523724919 78844861640923559285587379)
    ·
      refine ⟨118267292461385338928381069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78844861640923559285587379 118267292461385338928381069)
      ·
        refine ⟨44350234673019502098142901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118267292461385338928381069 44350234673019502098142901)
        ·
          refine ⟨4157834500595578321700897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44350234673019502098142901 4157834500595578321700897)
          ·
            refine ⟨3118375875446683741275673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4157834500595578321700897 3118375875446683741275673)
            ·
              refine ⟨2338781906585012805956755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3118375875446683741275673 2338781906585012805956755)
              ·
                refine ⟨3508172859877519208935133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2338781906585012805956755 3508172859877519208935133)
                ·
                  refine ⟨1315564822454069703350675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3508172859877519208935133 1315564822454069703350675)
                  ·
                    refine ⟨1973347233681104555026013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1315564822454069703350675 1973347233681104555026013)
                    ·
                      refine ⟨740005212630414208134755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1973347233681104555026013 740005212630414208134755)
                      ·
                        rfl

theorem cell23_1441155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 1, 3].length) (baseStart_1441155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441155 prefixEnd_1441155 := by exact prefixLift 1441155
  have htrace : WordTrace (prefixWord ++ tailWord_1441155) baseStart_1441155 baseEnd_1441155 := by
    simpa [prefixWord, tailWord_1441155, baseEnd_1441155] using wordTrace_append hprefix tailTrace_1441155
  have hstable : (prefixWord ++ tailWord_1441155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441155).length < 2 ^ (prefixWord ++ tailWord_1441155).sum := by decide
  have hdescent : baseEnd_1441155 < baseStart_1441155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441178 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2]
def baseStart_1441178 : Nat := 118140960795 + 1441178 * 2 ^ 59
def prefixEnd_1441178 : Nat := 4983230072969 + 3 ^ 40 * 1441178 * 2
def baseEnd_1441178 : Nat := 740017022685467618147149

theorem tailTrace_1441178 : CollatzResearch.WordTrace tailWord_1441178 prefixEnd_1441178 740017022685467618147149 := by
  unfold tailWord_1441178
  simp only [CollatzResearch.WordTrace]
  refine ⟨13141019993216428612953047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35042719981910476301208125 13141019993216428612953047)
  ·
    refine ⟨19711529989824642919429571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13141019993216428612953047 19711529989824642919429571)
    ·
      refine ⟨29567294984736964379144357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19711529989824642919429571 29567294984736964379144357)
      ·
        refine ⟨5543867809638180821089567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29567294984736964379144357 5543867809638180821089567)
        ·
          refine ⟨8315801714457271231634351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5543867809638180821089567 8315801714457271231634351)
          ·
            refine ⟨12473702571685906847451527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8315801714457271231634351 12473702571685906847451527)
            ·
              refine ⟨18710553857528860271177291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12473702571685906847451527 18710553857528860271177291)
              ·
                refine ⟨28065830786293290406765937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18710553857528860271177291 28065830786293290406765937)
                ·
                  refine ⟨21049373089719967805074453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28065830786293290406765937 21049373089719967805074453)
                  ·
                    refine ⟨986689363580623490862865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21049373089719967805074453 986689363580623490862865)
                    ·
                      refine ⟨740017022685467618147149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 986689363580623490862865 740017022685467618147149)
                      ·
                        rfl

theorem cell23_1441178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_1441178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441178 prefixEnd_1441178 := by exact prefixLift 1441178
  have htrace : WordTrace (prefixWord ++ tailWord_1441178) baseStart_1441178 baseEnd_1441178 := by
    simpa [prefixWord, tailWord_1441178, baseEnd_1441178] using wordTrace_append hprefix tailTrace_1441178
  have hstable : (prefixWord ++ tailWord_1441178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441178).length < 2 ^ (prefixWord ++ tailWord_1441178).sum := by decide
  have hdescent : baseEnd_1441178 < baseStart_1441178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441245 : List Nat := [1, 4, 3, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_1441245 : Nat := 118140960795 + 1441245 * 2 ^ 59
def prefixEnd_1441245 : Nat := 4983230072969 + 3 ^ 40 * 1441245 * 2
def baseEnd_1441245 : Nat := 740051425889318856009341

theorem tailTrace_1441245 : CollatzResearch.WordTrace tailWord_1441245 prefixEnd_1441245 740051425889318856009341 := by
  unfold tailWord_1441245
  simp only [CollatzResearch.WordTrace]
  refine ⟨52566523663622984894501189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35044349109081989929667459 52566523663622984894501189)
  ·
    refine ⟨9856223186929309667718973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52566523663622984894501189 9856223186929309667718973)
    ·
      refine ⟨3696083695098491125394615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9856223186929309667718973 3696083695098491125394615)
      ·
        refine ⟨5544125542647736688091923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3696083695098491125394615 5544125542647736688091923)
        ·
          refine ⟨8316188313971605032137885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5544125542647736688091923 8316188313971605032137885)
          ·
            refine ⟨3118570617739351887051707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8316188313971605032137885 3118570617739351887051707)
            ·
              refine ⟨4677855926609027830577561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3118570617739351887051707 4677855926609027830577561)
              ·
                refine ⟨3508391944956770872933171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4677855926609027830577561 3508391944956770872933171)
                ·
                  refine ⟨5262587917435156309399757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3508391944956770872933171 5262587917435156309399757)
                  ·
                    refine ⟨1973470469038183616024909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5262587917435156309399757 1973470469038183616024909)
                    ·
                      refine ⟨740051425889318856009341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1973470469038183616024909 740051425889318856009341)
                      ·
                        rfl

theorem cell23_1441245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_1441245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441245 prefixEnd_1441245 := by exact prefixLift 1441245
  have htrace : WordTrace (prefixWord ++ tailWord_1441245) baseStart_1441245 baseEnd_1441245 := by
    simpa [prefixWord, tailWord_1441245, baseEnd_1441245] using wordTrace_append hprefix tailTrace_1441245
  have hstable : (prefixWord ++ tailWord_1441245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441245).length < 2 ^ (prefixWord ++ tailWord_1441245).sum := by decide
  have hdescent : baseEnd_1441245 < baseStart_1441245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441262 : List Nat := [4, 1, 2, 1, 2, 1, 4, 2, 2, 1, 3]
def baseStart_1441262 : Nat := 118140960795 + 1441262 * 2 ^ 59
def prefixEnd_1441262 : Nat := 4983230072969 + 3 ^ 40 * 1441262 * 2
def baseEnd_1441262 : Nat := 740060155060445289496763

theorem tailTrace_1441262 : CollatzResearch.WordTrace tailWord_1441262 prefixEnd_1441262 740060155060445289496763 := by
  unfold tailWord_1441262
  simp only [CollatzResearch.WordTrace]
  refine ⟨6570892963070174599733755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35044762469707597865246693 6570892963070174599733755)
  ·
    refine ⟨9856339444605261899600633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6570892963070174599733755 9856339444605261899600633)
    ·
      refine ⟨7392254583453946424700475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9856339444605261899600633 7392254583453946424700475)
      ·
        refine ⟨11088381875180919637050713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7392254583453946424700475 11088381875180919637050713)
        ·
          refine ⟨8316286406385689727788035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11088381875180919637050713 8316286406385689727788035)
          ·
            refine ⟨12474429609578534591682053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8316286406385689727788035 12474429609578534591682053)
            ·
              refine ⟨2338955551795975235940385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12474429609578534591682053 2338955551795975235940385)
              ·
                refine ⟨1754216663846981426955289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2338955551795975235940385 1754216663846981426955289)
                ·
                  refine ⟨1315662497885236070216467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1754216663846981426955289 1315662497885236070216467)
                  ·
                    refine ⟨1973493746827854105324701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1315662497885236070216467 1973493746827854105324701)
                    ·
                      refine ⟨740060155060445289496763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1973493746827854105324701 740060155060445289496763)
                      ·
                        rfl

theorem cell23_1441262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_1441262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441262 prefixEnd_1441262 := by exact prefixLift 1441262
  have htrace : WordTrace (prefixWord ++ tailWord_1441262) baseStart_1441262 baseEnd_1441262 := by
    simpa [prefixWord, tailWord_1441262, baseEnd_1441262] using wordTrace_append hprefix tailTrace_1441262
  have hstable : (prefixWord ++ tailWord_1441262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441262).length < 2 ^ (prefixWord ++ tailWord_1441262).sum := by decide
  have hdescent : baseEnd_1441262 < baseStart_1441262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441271 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 5]
def baseStart_1441271 : Nat := 118140960795 + 1441271 * 2 ^ 59
def prefixEnd_1441271 : Nat := 4983230072969 + 3 ^ 40 * 1441271 * 2
def baseEnd_1441271 : Nat := 740064776386335754284221

theorem tailTrace_1441271 : CollatzResearch.WordTrace tailWord_1441271 prefixEnd_1441271 740064776386335754284221 := by
  unfold tailWord_1441271
  simp only [CollatzResearch.WordTrace]
  refine ⟨52567471961528791334947667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35044981307685860889965111 52567471961528791334947667)
  ·
    refine ⟨78851207942293187002421501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52567471961528791334947667 78851207942293187002421501)
    ·
      refine ⟨29569202978359945125908063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78851207942293187002421501 29569202978359945125908063)
      ·
        refine ⟨44353804467539917688862095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29569202978359945125908063 44353804467539917688862095)
        ·
          refine ⟨66530706701309876533293143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44353804467539917688862095 66530706701309876533293143)
          ·
            refine ⟨99796060051964814799939715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66530706701309876533293143 99796060051964814799939715)
            ·
              refine ⟨149694090077947222199909573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99796060051964814799939715 149694090077947222199909573)
              ·
                refine ⟨28067641889615104162483045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149694090077947222199909573 28067641889615104162483045)
                ·
                  refine ⟨5262682854302832030465571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28067641889615104162483045 5262682854302832030465571)
                  ·
                    refine ⟨7894024281454248045698357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5262682854302832030465571 7894024281454248045698357)
                    ·
                      refine ⟨740064776386335754284221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7894024281454248045698357 740064776386335754284221)
                      ·
                        rfl

theorem cell23_1441271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_1441271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441271 prefixEnd_1441271 := by exact prefixLift 1441271
  have htrace : WordTrace (prefixWord ++ tailWord_1441271) baseStart_1441271 baseEnd_1441271 := by
    simpa [prefixWord, tailWord_1441271, baseEnd_1441271] using wordTrace_append hprefix tailTrace_1441271
  have hstable : (prefixWord ++ tailWord_1441271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441271).length < 2 ^ (prefixWord ++ tailWord_1441271).sum := by decide
  have hdescent : baseEnd_1441271 < baseStart_1441271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441285 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 6, 2, 2]
def baseStart_1441285 : Nat := 118140960795 + 1441285 * 2 ^ 59
def prefixEnd_1441285 : Nat := 4983230072969 + 3 ^ 40 * 1441285 * 2
def baseEnd_1441285 : Nat := 740071965115498699509157

theorem tailTrace_1441285 : CollatzResearch.WordTrace tailWord_1441285 prefixEnd_1441285 740071965115498699509157 := by
  unfold tailWord_1441285
  simp only [CollatzResearch.WordTrace]
  refine ⟨52567982583478071725957309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35045321722318714483971539 52567982583478071725957309)
  ·
    refine ⟨19712993468804276897233991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52567982583478071725957309 19712993468804276897233991)
    ·
      refine ⟨29569490203206415345850987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19712993468804276897233991 29569490203206415345850987)
      ·
        refine ⟨44354235304809623018776481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29569490203206415345850987 44354235304809623018776481)
        ·
          refine ⟨33265676478607217264082361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44354235304809623018776481 33265676478607217264082361)
          ·
            refine ⟨24949257358955412948061771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33265676478607217264082361 24949257358955412948061771)
            ·
              refine ⟨37423886038433119422092657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24949257358955412948061771 37423886038433119422092657)
              ·
                refine ⟨28067914528824839566569493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37423886038433119422092657 28067914528824839566569493)
                ·
                  refine ⟨1315683493538664354682945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28067914528824839566569493 1315683493538664354682945)
                  ·
                    refine ⟨986762620153998266012209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1315683493538664354682945 986762620153998266012209)
                    ·
                      refine ⟨740071965115498699509157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 986762620153998266012209 740071965115498699509157)
                      ·
                        rfl

theorem cell23_1441285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 2, 2].length) (baseStart_1441285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441285 prefixEnd_1441285 := by exact prefixLift 1441285
  have htrace : WordTrace (prefixWord ++ tailWord_1441285) baseStart_1441285 baseEnd_1441285 := by
    simpa [prefixWord, tailWord_1441285, baseEnd_1441285] using wordTrace_append hprefix tailTrace_1441285
  have hstable : (prefixWord ++ tailWord_1441285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441285).length < 2 ^ (prefixWord ++ tailWord_1441285).sum := by decide
  have hdescent : baseEnd_1441285 < baseStart_1441285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441385 : List Nat := [1, 2, 1, 1, 1, 4, 5, 1, 3, 4]
def baseStart_1441385 : Nat := 118140960795 + 1441385 * 2 ^ 59
def prefixEnd_1441385 : Nat := 4983230072969 + 3 ^ 40 * 1441385 * 2
def baseEnd_1441385 : Nat := 246707771060316102752899

theorem tailTrace_1441385 : CollatzResearch.WordTrace tailWord_1441385 prefixEnd_1441385 246707771060316102752899 := by
  unfold tailWord_1441385
  simp only [CollatzResearch.WordTrace]
  refine ⟨52571629883115788804597609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35047753255410525869731739 52571629883115788804597609)
  ·
    refine ⟨39428722412336841603448207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52571629883115788804597609 39428722412336841603448207)
    ·
      refine ⟨59143083618505262405172311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39428722412336841603448207 59143083618505262405172311)
      ·
        refine ⟨88714625427757893607758467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59143083618505262405172311 88714625427757893607758467)
        ·
          refine ⟨133071938141636840411637701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88714625427757893607758467 133071938141636840411637701)
          ·
            refine ⟨24950988401556907577182069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133071938141636840411637701 24950988401556907577182069)
            ·
              refine ⟨2339155162645960085360819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24950988401556907577182069 2339155162645960085360819)
              ·
                refine ⟨3508732743968940128041229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2339155162645960085360819 3508732743968940128041229)
                ·
                  refine ⟨1315774778988352548015461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3508732743968940128041229 1315774778988352548015461)
                  ·
                    refine ⟨246707771060316102752899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1315774778988352548015461 246707771060316102752899)
                    ·
                      rfl

theorem cell23_1441385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 4].length) (baseStart_1441385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441385 prefixEnd_1441385 := by exact prefixLift 1441385
  have htrace : WordTrace (prefixWord ++ tailWord_1441385) baseStart_1441385 baseEnd_1441385 := by
    simpa [prefixWord, tailWord_1441385, baseEnd_1441385] using wordTrace_append hprefix tailTrace_1441385
  have hstable : (prefixWord ++ tailWord_1441385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441385).length < 2 ^ (prefixWord ++ tailWord_1441385).sum := by decide
  have hdescent : baseEnd_1441385 < baseStart_1441385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441425 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 7, 1, 3]
def baseStart_1441425 : Nat := 118140960795 + 1441425 * 2 ^ 59
def prefixEnd_1441425 : Nat := 4983230072969 + 3 ^ 40 * 1441425 * 2
def baseEnd_1441425 : Nat := 740143852407128151758513

theorem tailTrace_1441425 : CollatzResearch.WordTrace tailWord_1441425 prefixEnd_1441425 740143852407128151758513 := by
  unfold tailWord_1441425
  simp only [CollatzResearch.WordTrace]
  refine ⟨52573088802970875636053729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35048725868647250424035819 52573088802970875636053729)
  ·
    refine ⟨39429816602228156727040297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52573088802970875636053729 39429816602228156727040297)
    ·
      refine ⟨29572362451671117545280223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39429816602228156727040297 29572362451671117545280223)
      ·
        refine ⟨44358543677506676317920335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29572362451671117545280223 44358543677506676317920335)
        ·
          refine ⟨66537815516260014476880503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44358543677506676317920335 66537815516260014476880503)
          ·
            refine ⟨99806723274390021715320755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66537815516260014476880503 99806723274390021715320755)
            ·
              refine ⟨149710084911585032572981133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99806723274390021715320755 149710084911585032572981133)
              ·
                refine ⟨56141281841844387214867925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149710084911585032572981133 56141281841844387214867925)
                ·
                  refine ⟨1315811293168227825348467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 56141281841844387214867925 1315811293168227825348467)
                  ·
                    refine ⟨1973716939752341738022701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1315811293168227825348467 1973716939752341738022701)
                    ·
                      refine ⟨740143852407128151758513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1973716939752341738022701 740143852407128151758513)
                      ·
                        rfl

theorem cell23_1441425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 1, 3].length) (baseStart_1441425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441425 prefixEnd_1441425 := by exact prefixLift 1441425
  have htrace : WordTrace (prefixWord ++ tailWord_1441425) baseStart_1441425 baseEnd_1441425 := by
    simpa [prefixWord, tailWord_1441425, baseEnd_1441425] using wordTrace_append hprefix tailTrace_1441425
  have hstable : (prefixWord ++ tailWord_1441425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441425).length < 2 ^ (prefixWord ++ tailWord_1441425).sum := by decide
  have hdescent : baseEnd_1441425 < baseStart_1441425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441465 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 3, 1, 4]
def baseStart_1441465 : Nat := 118140960795 + 1441465 * 2 ^ 59
def prefixEnd_1441465 : Nat := 4983230072969 + 3 ^ 40 * 1441465 * 2
def baseEnd_1441465 : Nat := 740164391633307995258329

theorem tailTrace_1441465 : CollatzResearch.WordTrace tailWord_1441465 prefixEnd_1441465 740164391633307995258329 := by
  unfold tailWord_1441465
  simp only [CollatzResearch.WordTrace]
  refine ⟨52574547722825962467509849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35049698481883974978339899 52574547722825962467509849)
  ·
    refine ⟨39430910792119471850632387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52574547722825962467509849 39430910792119471850632387)
    ·
      refine ⟨59146366188179207775948581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39430910792119471850632387 59146366188179207775948581)
      ·
        refine ⟨11089943660283601457990359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59146366188179207775948581 11089943660283601457990359)
        ·
          refine ⟨16634915490425402186985539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11089943660283601457990359 16634915490425402186985539)
          ·
            refine ⟨24952373235638103280478309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16634915490425402186985539 24952373235638103280478309)
            ·
              refine ⟨4678569981682144365089683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24952373235638103280478309 4678569981682144365089683)
              ·
                refine ⟨7017854972523216547634525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4678569981682144365089683 7017854972523216547634525)
                ·
                  refine ⟨2631695614696206205362947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7017854972523216547634525 2631695614696206205362947)
                  ·
                    refine ⟨3947543422044309308044421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2631695614696206205362947 3947543422044309308044421)
                    ·
                      refine ⟨740164391633307995258329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3947543422044309308044421 740164391633307995258329)
                      ·
                        rfl

theorem cell23_1441465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_1441465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441465 prefixEnd_1441465 := by exact prefixLift 1441465
  have htrace : WordTrace (prefixWord ++ tailWord_1441465) baseStart_1441465 baseEnd_1441465 := by
    simpa [prefixWord, tailWord_1441465, baseEnd_1441465] using wordTrace_append hprefix tailTrace_1441465
  have hstable : (prefixWord ++ tailWord_1441465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441465).length < 2 ^ (prefixWord ++ tailWord_1441465).sum := by decide
  have hdescent : baseEnd_1441465 < baseStart_1441465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441476 : List Nat := [2, 3, 3, 1, 1, 1, 4, 3, 1, 1, 3]
def baseStart_1441476 : Nat := 118140960795 + 1441476 * 2 ^ 59
def prefixEnd_1441476 : Nat := 4983230072969 + 3 ^ 40 * 1441476 * 2
def baseEnd_1441476 : Nat := 740170039920507452220779

theorem tailTrace_1441476 : CollatzResearch.WordTrace tailWord_1441476 prefixEnd_1441476 740170039920507452220779 := by
  unfold tailWord_1441476
  simp only [CollatzResearch.WordTrace]
  refine ⟨26287474462893055673080141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35049965950524074230773521 26287474462893055673080141)
  ·
    refine ⟨9857802923584895877405053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26287474462893055673080141 9857802923584895877405053)
    ·
      refine ⟨3696676096344335954026895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9857802923584895877405053 3696676096344335954026895)
      ·
        refine ⟨5545014144516503931040343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3696676096344335954026895 5545014144516503931040343)
        ·
          refine ⟨8317521216774755896560515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5545014144516503931040343 8317521216774755896560515)
          ·
            refine ⟨12476281825162133844840773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8317521216774755896560515 12476281825162133844840773)
            ·
              refine ⟨2339302842217900095907645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12476281825162133844840773 2339302842217900095907645)
              ·
                refine ⟨877238565831712535965367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2339302842217900095907645 877238565831712535965367)
                ·
                  refine ⟨1315857848747568803948051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 877238565831712535965367 1315857848747568803948051)
                  ·
                    refine ⟨1973786773121353205922077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1315857848747568803948051 1973786773121353205922077)
                    ·
                      refine ⟨740170039920507452220779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1973786773121353205922077 740170039920507452220779)
                      ·
                        rfl

theorem cell23_1441476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_1441476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441476 prefixEnd_1441476 := by exact prefixLift 1441476
  have htrace : WordTrace (prefixWord ++ tailWord_1441476) baseStart_1441476 baseEnd_1441476 := by
    simpa [prefixWord, tailWord_1441476, baseEnd_1441476] using wordTrace_append hprefix tailTrace_1441476
  have hstable : (prefixWord ++ tailWord_1441476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441476).length < 2 ^ (prefixWord ++ tailWord_1441476).sum := by decide
  have hdescent : baseEnd_1441476 < baseStart_1441476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441509 : List Nat := [1, 3, 1, 4, 1, 1, 5, 1, 2, 4]
def baseStart_1441509 : Nat := 118140960795 + 1441509 * 2 ^ 59
def prefixEnd_1441509 : Nat := 4983230072969 + 3 ^ 40 * 1441509 * 2
def baseEnd_1441509 : Nat := 246728994927368607702709

theorem tailTrace_1441509 : CollatzResearch.WordTrace tailWord_1441509 prefixEnd_1441509 246728994927368607702709 := by
  unfold tailWord_1441509
  simp only [CollatzResearch.WordTrace]
  refine ⟨52576152534666557982111581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35050768356444371988074387 52576152534666557982111581)
  ·
    refine ⟨19716057200499959243291843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52576152534666557982111581 19716057200499959243291843)
    ·
      refine ⟨29574085800749938864937765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19716057200499959243291843 29574085800749938864937765)
      ·
        refine ⟨5545141087640613537175831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29574085800749938864937765 5545141087640613537175831)
        ·
          refine ⟨8317711631460920305763747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5545141087640613537175831 8317711631460920305763747)
          ·
            refine ⟨12476567447191380458645621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8317711631460920305763747 12476567447191380458645621)
            ·
              refine ⟨1169678198174191917998027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12476567447191380458645621 1169678198174191917998027)
              ·
                refine ⟨1754517297261287876997041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1169678198174191917998027 1754517297261287876997041)
                ·
                  refine ⟨1315887972945965907747781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1754517297261287876997041 1315887972945965907747781)
                  ·
                    refine ⟨246728994927368607702709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1315887972945965907747781 246728994927368607702709)
                    ·
                      rfl

theorem cell23_1441509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 2, 4].length) (baseStart_1441509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441509 prefixEnd_1441509 := by exact prefixLift 1441509
  have htrace : WordTrace (prefixWord ++ tailWord_1441509) baseStart_1441509 baseEnd_1441509 := by
    simpa [prefixWord, tailWord_1441509, baseEnd_1441509] using wordTrace_append hprefix tailTrace_1441509
  have hstable : (prefixWord ++ tailWord_1441509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441509).length < 2 ^ (prefixWord ++ tailWord_1441509).sum := by decide
  have hdescent : baseEnd_1441509 < baseStart_1441509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441512 : List Nat := [2, 1, 4, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_1441512 : Nat := 118140960795 + 1441512 * 2 ^ 59
def prefixEnd_1441512 : Nat := 4983230072969 + 3 ^ 40 * 1441512 * 2
def baseEnd_1441512 : Nat := 740188525224069311370613

theorem tailTrace_1441512 : CollatzResearch.WordTrace tailWord_1441512 prefixEnd_1441512 740188525224069311370613 := by
  unfold tailWord_1441512
  simp only [CollatzResearch.WordTrace]
  refine ⟨26288130976827844747235395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35050841302437126329647193 26288130976827844747235395)
  ·
    refine ⟨39432196465241767120853093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26288130976827844747235395 39432196465241767120853093)
    ·
      refine ⟨7393536837232831335159955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39432196465241767120853093 7393536837232831335159955)
      ·
        refine ⟨11090305255849247002739933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7393536837232831335159955 11090305255849247002739933)
        ·
          refine ⟨4158864470943467626027475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11090305255849247002739933 4158864470943467626027475)
          ·
            refine ⟨6238296706415201439041213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4158864470943467626027475 6238296706415201439041213)
            ·
              refine ⟨2339361264905700539640455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6238296706415201439041213 2339361264905700539640455)
              ·
                refine ⟨3509041897358550809460683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2339361264905700539640455 3509041897358550809460683)
                ·
                  refine ⟨5263562846037826214191025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3509041897358550809460683 5263562846037826214191025)
                  ·
                    refine ⟨3947672134528369660643269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5263562846037826214191025 3947672134528369660643269)
                    ·
                      refine ⟨740188525224069311370613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3947672134528369660643269 740188525224069311370613)
                      ·
                        rfl

theorem cell23_1441512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_1441512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441512 prefixEnd_1441512 := by exact prefixLift 1441512
  have htrace : WordTrace (prefixWord ++ tailWord_1441512) baseStart_1441512 baseEnd_1441512 := by
    simpa [prefixWord, tailWord_1441512, baseEnd_1441512] using wordTrace_append hprefix tailTrace_1441512
  have hstable : (prefixWord ++ tailWord_1441512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441512).length < 2 ^ (prefixWord ++ tailWord_1441512).sum := by decide
  have hdescent : baseEnd_1441512 < baseStart_1441512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441532 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 6, 1, 3]
def baseStart_1441532 : Nat := 118140960795 + 1441532 * 2 ^ 59
def prefixEnd_1441532 : Nat := 4983230072969 + 3 ^ 40 * 1441532 * 2
def baseEnd_1441532 : Nat := 740198794837159233120521

theorem tailTrace_1441532 : CollatzResearch.WordTrace tailWord_1441532 prefixEnd_1441532 740198794837159233120521 := by
  unfold tailWord_1441532
  simp only [CollatzResearch.WordTrace]
  refine ⟨26288495706791616455099425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35051327609055488606799233 26288495706791616455099425)
  ·
    refine ⟨19716371780093712341324569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26288495706791616455099425 19716371780093712341324569)
    ·
      refine ⟨14787278835070284255993427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19716371780093712341324569 14787278835070284255993427)
      ·
        refine ⟨22180918252605426383990141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14787278835070284255993427 22180918252605426383990141)
        ·
          refine ⟨8317844344727034893996303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22180918252605426383990141 8317844344727034893996303)
          ·
            refine ⟨12476766517090552340994455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8317844344727034893996303 12476766517090552340994455)
            ·
              refine ⟨18715149775635828511491683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12476766517090552340994455 18715149775635828511491683)
              ·
                refine ⟨28072724663453742767237525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18715149775635828511491683 28072724663453742767237525)
                ·
                  refine ⟨1315908968599394192214259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28072724663453742767237525 1315908968599394192214259)
                  ·
                    refine ⟨1973863452899091288321389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1315908968599394192214259 1973863452899091288321389)
                    ·
                      refine ⟨740198794837159233120521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1973863452899091288321389 740198794837159233120521)
                      ·
                        rfl

theorem cell23_1441532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_1441532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441532 prefixEnd_1441532 := by exact prefixLift 1441532
  have htrace : WordTrace (prefixWord ++ tailWord_1441532) baseStart_1441532 baseEnd_1441532 := by
    simpa [prefixWord, tailWord_1441532, baseEnd_1441532] using wordTrace_append hprefix tailTrace_1441532
  have hstable : (prefixWord ++ tailWord_1441532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441532).length < 2 ^ (prefixWord ++ tailWord_1441532).sum := by decide
  have hdescent : baseEnd_1441532 < baseStart_1441532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441556 : List Nat := [2, 4, 4, 1, 1, 1, 2, 8]
def baseStart_1441556 : Nat := 118140960795 + 1441556 * 2 ^ 59
def prefixEnd_1441556 : Nat := 4983230072969 + 3 ^ 40 * 1441556 * 2
def baseEnd_1441556 : Nat := 27415226606402486637793

theorem tailTrace_1441556 : CollatzResearch.WordTrace tailWord_1441556 prefixEnd_1441556 27415226606402486637793 := by
  unfold tailWord_1441556
  simp only [CollatzResearch.WordTrace]
  refine ⟨26288933382748142504536261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35051911176997523339381681 26288933382748142504536261)
  ·
    refine ⟨4929175009265276719600549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26288933382748142504536261 4929175009265276719600549)
    ·
      refine ⟨924220314237239384925103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4929175009265276719600549 924220314237239384925103)
      ·
        refine ⟨1386330471355859077387655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 924220314237239384925103 1386330471355859077387655)
        ·
          refine ⟨2079495707033788616081483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1386330471355859077387655 2079495707033788616081483)
          ·
            refine ⟨3119243560550682924122225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2079495707033788616081483 3119243560550682924122225)
            ·
              refine ⟨2339432670413012193091669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3119243560550682924122225 2339432670413012193091669)
              ·
                refine ⟨27415226606402486637793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2339432670413012193091669 27415226606402486637793)
                ·
                  rfl

theorem cell23_1441556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 8].length) (baseStart_1441556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441556 prefixEnd_1441556 := by exact prefixLift 1441556
  have htrace : WordTrace (prefixWord ++ tailWord_1441556) baseStart_1441556 baseEnd_1441556 := by
    simpa [prefixWord, tailWord_1441556, baseEnd_1441556] using wordTrace_append hprefix tailTrace_1441556
  have hstable : (prefixWord ++ tailWord_1441556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441556).length < 2 ^ (prefixWord ++ tailWord_1441556).sum := by decide
  have hdescent : baseEnd_1441556 < baseStart_1441556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441576 : List Nat := [2, 1, 5, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_1441576 : Nat := 118140960795 + 1441576 * 2 ^ 59
def prefixEnd_1441576 : Nat := 4983230072969 + 3 ^ 40 * 1441576 * 2
def baseEnd_1441576 : Nat := 740221387985957060970319

theorem tailTrace_1441576 : CollatzResearch.WordTrace tailWord_1441576 prefixEnd_1441576 740221387985957060970319 := by
  unfold tailWord_1441576
  simp only [CollatzResearch.WordTrace]
  refine ⟨26289298112711914212400291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35052397483615885616533721 26289298112711914212400291)
  ·
    refine ⟨39433947169067871318600437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26289298112711914212400291 39433947169067871318600437)
    ·
      refine ⟨3696932547100112936118791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39433947169067871318600437 3696932547100112936118791)
      ·
        refine ⟨5545398820650169404178187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3696932547100112936118791 5545398820650169404178187)
        ·
          refine ⟨8318098230975254106267281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5545398820650169404178187 8318098230975254106267281)
          ·
            refine ⟨6238573673231440579700461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8318098230975254106267281 6238573673231440579700461)
            ·
              refine ⟨2339465127461790217387673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6238573673231440579700461 2339465127461790217387673)
              ·
                refine ⟨1754598845596342663040755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2339465127461790217387673 1754598845596342663040755)
                ·
                  refine ⟨2631898268394513994561133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1754598845596342663040755 2631898268394513994561133)
                  ·
                    refine ⟨986961850647942747960425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2631898268394513994561133 986961850647942747960425)
                    ·
                      refine ⟨740221387985957060970319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 986961850647942747960425 740221387985957060970319)
                      ·
                        rfl

theorem cell23_1441576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_1441576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441576 prefixEnd_1441576 := by exact prefixLift 1441576
  have htrace : WordTrace (prefixWord ++ tailWord_1441576) baseStart_1441576 baseEnd_1441576 := by
    simpa [prefixWord, tailWord_1441576, baseEnd_1441576] using wordTrace_append hprefix tailTrace_1441576
  have hstable : (prefixWord ++ tailWord_1441576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441576).length < 2 ^ (prefixWord ++ tailWord_1441576).sum := by decide
  have hdescent : baseEnd_1441576 < baseStart_1441576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441625 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 1, 7]
def baseStart_1441625 : Nat := 118140960795 + 1441625 * 2 ^ 59
def prefixEnd_1441625 : Nat := 4983230072969 + 3 ^ 40 * 1441625 * 2
def baseEnd_1441625 : Nat := 246748849512675789752531

theorem tailTrace_1441625 : CollatzResearch.WordTrace tailWord_1441625 prefixEnd_1441625 246748849512675789752531 := by
  unfold tailWord_1441625
  simp only [CollatzResearch.WordTrace]
  refine ⟨52580383402246309793334329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35053588934830873195556219 52580383402246309793334329)
  ·
    refine ⟨39435287551684732345000747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52580383402246309793334329 39435287551684732345000747)
    ·
      refine ⟨59152931327527098517501121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39435287551684732345000747 59152931327527098517501121)
      ·
        refine ⟨44364698495645323888125841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59152931327527098517501121 44364698495645323888125841)
        ·
          refine ⟨33273523871733992916094381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44364698495645323888125841 33273523871733992916094381)
          ·
            refine ⟨12477571451900247343535393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33273523871733992916094381 12477571451900247343535393)
            ·
              refine ⟨9358178588925185507651545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12477571451900247343535393 9358178588925185507651545)
              ·
                refine ⟨7018633941693889130738659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9358178588925185507651545 7018633941693889130738659)
                ·
                  refine ⟨10527950912540833696107989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7018633941693889130738659 10527950912540833696107989)
                  ·
                    refine ⟨246748849512675789752531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10527950912540833696107989 246748849512675789752531)
                    ·
                      rfl

theorem cell23_1441625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 7].length) (baseStart_1441625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441625 prefixEnd_1441625 := by exact prefixLift 1441625
  have htrace : WordTrace (prefixWord ++ tailWord_1441625) baseStart_1441625 baseEnd_1441625 := by
    simpa [prefixWord, tailWord_1441625, baseEnd_1441625] using wordTrace_append hprefix tailTrace_1441625
  have hstable : (prefixWord ++ tailWord_1441625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441625).length < 2 ^ (prefixWord ++ tailWord_1441625).sum := by decide
  have hdescent : baseEnd_1441625 < baseStart_1441625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441646 : List Nat := [4, 1, 2, 3, 1, 2, 2, 3, 5]
def baseStart_1441646 : Nat := 118140960795 + 1441646 * 2 ^ 59
def prefixEnd_1441646 : Nat := 4983230072969 + 3 ^ 40 * 1441646 * 2
def baseEnd_1441646 : Nat := 82250814625752420788333

theorem tailTrace_1441646 : CollatzResearch.WordTrace tailWord_1441646 prefixEnd_1441646 82250814625752420788333 := by
  unfold tailWord_1441646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6572643666896278797481099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35054099556780153586565861 6572643666896278797481099)
  ·
    refine ⟨9858965500344418196221649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6572643666896278797481099 9858965500344418196221649)
    ·
      refine ⟨7394224125258313647166237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9858965500344418196221649 7394224125258313647166237)
      ·
        refine ⟨2772834046971867617687339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7394224125258313647166237 2772834046971867617687339)
        ·
          refine ⟨4159251070457801426531009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2772834046971867617687339 4159251070457801426531009)
          ·
            refine ⟨3119438302843351069898257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4159251070457801426531009 3119438302843351069898257)
            ·
              refine ⟨2339578727132513302423693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3119438302843351069898257 2339578727132513302423693)
              ·
                refine ⟨877342022674692488408885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2339578727132513302423693 877342022674692488408885)
                ·
                  refine ⟨82250814625752420788333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 877342022674692488408885 82250814625752420788333)
                  ·
                    rfl

theorem cell23_1441646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_1441646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441646 prefixEnd_1441646 := by exact prefixLift 1441646
  have htrace : WordTrace (prefixWord ++ tailWord_1441646) baseStart_1441646 baseEnd_1441646 := by
    simpa [prefixWord, tailWord_1441646, baseEnd_1441646] using wordTrace_append hprefix tailTrace_1441646
  have hstable : (prefixWord ++ tailWord_1441646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441646).length < 2 ^ (prefixWord ++ tailWord_1441646).sum := by decide
  have hdescent : baseEnd_1441646 < baseStart_1441646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441675 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 6]
def baseStart_1441675 : Nat := 118140960795 + 1441675 * 2 ^ 59
def prefixEnd_1441675 : Nat := 4983230072969 + 3 ^ 40 * 1441675 * 2
def baseEnd_1441675 : Nat := 740272222570752173632363

theorem tailTrace_1441675 : CollatzResearch.WordTrace tailWord_1441675 prefixEnd_1441675 740272222570752173632363 := by
  unfold tailWord_1441675
  simp only [CollatzResearch.WordTrace]
  refine ⟨52582207052065168332654479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35054804701376778888436319 52582207052065168332654479)
  ·
    refine ⟨78873310578097752498981719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52582207052065168332654479 78873310578097752498981719)
    ·
      refine ⟨118309965867146628748472579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78873310578097752498981719 118309965867146628748472579)
      ·
        refine ⟨177464948800719943122708869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118309965867146628748472579 177464948800719943122708869)
        ·
          refine ⟨33274677900134989335507913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177464948800719943122708869 33274677900134989335507913)
          ·
            refine ⟨24956008425101242001630935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33274677900134989335507913 24956008425101242001630935)
            ·
              refine ⟨37434012637651863002446403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24956008425101242001630935 37434012637651863002446403)
              ·
                refine ⟨56151018956477794503669605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37434012637651863002446403 56151018956477794503669605)
                ·
                  refine ⟨10528316054339586469438051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56151018956477794503669605 10528316054339586469438051)
                  ·
                    refine ⟨15792474081509379704157077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10528316054339586469438051 15792474081509379704157077)
                    ·
                      refine ⟨740272222570752173632363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15792474081509379704157077 740272222570752173632363)
                      ·
                        rfl

theorem cell23_1441675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 6].length) (baseStart_1441675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441675 prefixEnd_1441675 := by exact prefixLift 1441675
  have htrace : WordTrace (prefixWord ++ tailWord_1441675) baseStart_1441675 baseEnd_1441675 := by
    simpa [prefixWord, tailWord_1441675, baseEnd_1441675] using wordTrace_append hprefix tailTrace_1441675
  have hstable : (prefixWord ++ tailWord_1441675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441675).length < 2 ^ (prefixWord ++ tailWord_1441675).sum := by decide
  have hdescent : baseEnd_1441675 < baseStart_1441675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441705 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 8]
def baseStart_1441705 : Nat := 118140960795 + 1441705 * 2 ^ 59
def prefixEnd_1441705 : Nat := 4983230072969 + 3 ^ 40 * 1441705 * 2
def baseEnd_1441705 : Nat := 740287626990387056257225

theorem tailTrace_1441705 : CollatzResearch.WordTrace tailWord_1441705 prefixEnd_1441705 740287626990387056257225 := by
  unfold tailWord_1441705
  simp only [CollatzResearch.WordTrace]
  refine ⟨52583301241956483456246569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35055534161304322304164379 52583301241956483456246569)
  ·
    refine ⟨39437475931467362592184927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52583301241956483456246569 39437475931467362592184927)
    ·
      refine ⟨59156213897201043888277391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39437475931467362592184927 59156213897201043888277391)
      ·
        refine ⟨88734320845801565832416087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59156213897201043888277391 88734320845801565832416087)
        ·
          refine ⟨133101481268702348748624131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88734320845801565832416087 133101481268702348748624131)
          ·
            refine ⟨199652221903053523122936197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133101481268702348748624131 199652221903053523122936197)
            ·
              refine ⟨37434791606822535585550537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 199652221903053523122936197 37434791606822535585550537)
              ·
                refine ⟨28076093705116901689162903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37434791606822535585550537 28076093705116901689162903)
                ·
                  refine ⟨42114140557675352533744355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28076093705116901689162903 42114140557675352533744355)
                  ·
                    refine ⟨63171210836513028800616533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42114140557675352533744355 63171210836513028800616533)
                    ·
                      refine ⟨740287626990387056257225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 63171210836513028800616533 740287626990387056257225)
                      ·
                        rfl

theorem cell23_1441705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_1441705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441705 prefixEnd_1441705 := by exact prefixLift 1441705
  have htrace : WordTrace (prefixWord ++ tailWord_1441705) baseStart_1441705 baseEnd_1441705 := by
    simpa [prefixWord, tailWord_1441705, baseEnd_1441705] using wordTrace_append hprefix tailTrace_1441705
  have hstable : (prefixWord ++ tailWord_1441705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441705).length < 2 ^ (prefixWord ++ tailWord_1441705).sum := by decide
  have hdescent : baseEnd_1441705 < baseStart_1441705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441736 : List Nat := [2, 1, 3, 1, 4, 3, 2, 1, 6]
def baseStart_1441736 : Nat := 118140960795 + 1441736 * 2 ^ 59
def prefixEnd_1441736 : Nat := 4983230072969 + 3 ^ 40 * 1441736 * 2
def baseEnd_1441736 : Nat := 82255949432297381663287

theorem tailTrace_1441736 : CollatzResearch.WordTrace tailWord_1441736 prefixEnd_1441736 82255949432297381663287 := by
  unfold tailWord_1441736
  simp only [CollatzResearch.WordTrace]
  refine ⟨26292215952422087875312531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35056287936562783833750041 26292215952422087875312531)
  ·
    refine ⟨39438323928633131812968797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26292215952422087875312531 39438323928633131812968797)
    ·
      refine ⟨14789371473237424429863299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39438323928633131812968797 14789371473237424429863299)
      ·
        refine ⟨22184057209856136644794949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14789371473237424429863299 22184057209856136644794949)
        ·
          refine ⟨4159510726848025620899053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22184057209856136644794949 4159510726848025620899053)
          ·
            refine ⟨1559816522568009607837145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4159510726848025620899053 1559816522568009607837145)
            ·
              refine ⟨1169862391926007205877859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1559816522568009607837145 1169862391926007205877859)
              ·
                refine ⟨1754793587889010808816789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1169862391926007205877859 1754793587889010808816789)
                ·
                  refine ⟨82255949432297381663287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1754793587889010808816789 82255949432297381663287)
                  ·
                    rfl

theorem cell23_1441736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 6].length) (baseStart_1441736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441736 prefixEnd_1441736 := by exact prefixLift 1441736
  have htrace : WordTrace (prefixWord ++ tailWord_1441736) baseStart_1441736 baseEnd_1441736 := by
    simpa [prefixWord, tailWord_1441736, baseEnd_1441736] using wordTrace_append hprefix tailTrace_1441736
  have hstable : (prefixWord ++ tailWord_1441736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441736).length < 2 ^ (prefixWord ++ tailWord_1441736).sum := by decide
  have hdescent : baseEnd_1441736 < baseStart_1441736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441739 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 4, 3, 2]
def baseStart_1441739 : Nat := 118140960795 + 1441739 * 2 ^ 59
def prefixEnd_1441739 : Nat := 4983230072969 + 3 ^ 40 * 1441739 * 2
def baseEnd_1441739 : Nat := 740305085332639923232069

theorem tailTrace_1441739 : CollatzResearch.WordTrace tailWord_1441739 prefixEnd_1441739 740305085332639923232069 := by
  unfold tailWord_1441739
  simp only [CollatzResearch.WordTrace]
  refine ⟨52584541323833307262984271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35056360882555538175322847 52584541323833307262984271)
  ·
    refine ⟨78876811985749960894476407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52584541323833307262984271 78876811985749960894476407)
    ·
      refine ⟨118315217978624941341714611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78876811985749960894476407 118315217978624941341714611)
      ·
        refine ⟨177472826967937412012571917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118315217978624941341714611 177472826967937412012571917)
        ·
          refine ⟨66552310112976529504714469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177472826967937412012571917 66552310112976529504714469)
          ·
            refine ⟨12478558146183099282133963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66552310112976529504714469 12478558146183099282133963)
            ·
              refine ⟨18717837219274648923200945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12478558146183099282133963 18717837219274648923200945)
              ·
                refine ⟨14038377914455986692400709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18717837219274648923200945 14038377914455986692400709)
                ·
                  refine ⟨2632195858960497504825133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14038377914455986692400709 2632195858960497504825133)
                  ·
                    refine ⟨987073447110186564309425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2632195858960497504825133 987073447110186564309425)
                    ·
                      refine ⟨740305085332639923232069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 987073447110186564309425 740305085332639923232069)
                      ·
                        rfl

theorem cell23_1441739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 3, 2].length) (baseStart_1441739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441739 prefixEnd_1441739 := by exact prefixLift 1441739
  have htrace : WordTrace (prefixWord ++ tailWord_1441739) baseStart_1441739 baseEnd_1441739 := by
    simpa [prefixWord, tailWord_1441739, baseEnd_1441739] using wordTrace_append hprefix tailTrace_1441739
  have hstable : (prefixWord ++ tailWord_1441739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441739).length < 2 ^ (prefixWord ++ tailWord_1441739).sum := by decide
  have hdescent : baseEnd_1441739 < baseStart_1441739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441749 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 3, 5]
def baseStart_1441749 : Nat := 118140960795 + 1441749 * 2 ^ 59
def prefixEnd_1441749 : Nat := 4983230072969 + 3 ^ 40 * 1441749 * 2
def baseEnd_1441749 : Nat := 246770073379728294702341

theorem tailTrace_1441749 : CollatzResearch.WordTrace tailWord_1441749 prefixEnd_1441749 246770073379728294702341 := by
  unfold tailWord_1441749
  simp only [CollatzResearch.WordTrace]
  refine ⟨52584906053797078970848301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35056604035864719313898867 52584906053797078970848301)
  ·
    refine ⟨19719339770173904614068113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52584906053797078970848301 19719339770173904614068113)
    ·
      refine ⟨14789504827630428460551085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19719339770173904614068113 14789504827630428460551085)
      ·
        refine ⟨5546064310361410672706657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14789504827630428460551085 5546064310361410672706657)
        ·
          refine ⟨4159548232771058004529993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5546064310361410672706657 4159548232771058004529993)
          ·
            refine ⟨3119661174578293503397495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4159548232771058004529993 3119661174578293503397495)
            ·
              refine ⟨4679491761867440255096243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3119661174578293503397495 4679491761867440255096243)
              ·
                refine ⟨7019237642801160382644365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4679491761867440255096243 7019237642801160382644365)
                ·
                  refine ⟨2632214116050435143491637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7019237642801160382644365 2632214116050435143491637)
                  ·
                    refine ⟨246770073379728294702341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2632214116050435143491637 246770073379728294702341)
                    ·
                      rfl

theorem cell23_1441749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_1441749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441749 prefixEnd_1441749 := by exact prefixLift 1441749
  have htrace : WordTrace (prefixWord ++ tailWord_1441749) baseStart_1441749 baseEnd_1441749 := by
    simpa [prefixWord, tailWord_1441749, baseEnd_1441749] using wordTrace_append hprefix tailTrace_1441749
  have hstable : (prefixWord ++ tailWord_1441749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441749).length < 2 ^ (prefixWord ++ tailWord_1441749).sum := by decide
  have hdescent : baseEnd_1441749 < baseStart_1441749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441789 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 3, 2, 3]
def baseStart_1441789 : Nat := 118140960795 + 1441789 * 2 ^ 59
def prefixEnd_1441789 : Nat := 4983230072969 + 3 ^ 40 * 1441789 * 2
def baseEnd_1441789 : Nat := 740330759365364727606839

theorem tailTrace_1441789 : CollatzResearch.WordTrace tailWord_1441789 prefixEnd_1441789 740330759365364727606839 := by
  unfold tailWord_1441789
  simp only [CollatzResearch.WordTrace]
  refine ⟨52586364973652165802304421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35057576649101443868202947 52586364973652165802304421)
  ·
    refine ⟨9859943432559781087932079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52586364973652165802304421 9859943432559781087932079)
    ·
      refine ⟨14789915148839671631898119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9859943432559781087932079 14789915148839671631898119)
      ·
        refine ⟨22184872723259507447847179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14789915148839671631898119 22184872723259507447847179)
        ·
          refine ⟨33277309084889261171770769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22184872723259507447847179 33277309084889261171770769)
          ·
            refine ⟨24957981813666945878828077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33277309084889261171770769 24957981813666945878828077)
            ·
              refine ⟨9359243180125104704560529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24957981813666945878828077 9359243180125104704560529)
              ·
                refine ⟨7019432385093828528420397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9359243180125104704560529 7019432385093828528420397)
                ·
                  refine ⟨2632287144410185698157649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7019432385093828528420397 2632287144410185698157649)
                  ·
                    refine ⟨1974215358307639273618237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2632287144410185698157649 1974215358307639273618237)
                    ·
                      refine ⟨740330759365364727606839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1974215358307639273618237 740330759365364727606839)
                      ·
                        rfl

theorem cell23_1441789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_1441789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441789 prefixEnd_1441789 := by exact prefixLift 1441789
  have htrace : WordTrace (prefixWord ++ tailWord_1441789) baseStart_1441789 baseEnd_1441789 := by
    simpa [prefixWord, tailWord_1441789, baseEnd_1441789] using wordTrace_append hprefix tailTrace_1441789
  have hstable : (prefixWord ++ tailWord_1441789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441789).length < 2 ^ (prefixWord ++ tailWord_1441789).sum := by decide
  have hdescent : baseEnd_1441789 < baseStart_1441789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441799 : List Nat := [1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 4]
def baseStart_1441799 : Nat := 118140960795 + 1441799 * 2 ^ 59
def prefixEnd_1441799 : Nat := 4983230072969 + 3 ^ 40 * 1441799 * 2
def baseEnd_1441799 : Nat := 740335894171909688481793

theorem tailTrace_1441799 : CollatzResearch.WordTrace tailWord_1441799 prefixEnd_1441799 740335894171909688481793 := by
  unfold tailWord_1441799
  simp only [CollatzResearch.WordTrace]
  refine ⟨52586729703615937510168451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35057819802410625006778967 52586729703615937510168451)
  ·
    refine ⟨78880094555423906265252677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52586729703615937510168451 78880094555423906265252677)
    ·
      refine ⟨14790017729141982424734877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78880094555423906265252677 14790017729141982424734877)
      ·
        refine ⟨5546256648428243409275579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14790017729141982424734877 5546256648428243409275579)
        ·
          refine ⟨8319384972642365113913369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5546256648428243409275579 8319384972642365113913369)
          ·
            refine ⟨6239538729481773835435027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8319384972642365113913369 6239538729481773835435027)
            ·
              refine ⟨9359308094222660753152541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6239538729481773835435027 9359308094222660753152541)
              ·
                refine ⟨3509740535333497782432203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9359308094222660753152541 3509740535333497782432203)
                ·
                  refine ⟨5264610803000246673648305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3509740535333497782432203 5264610803000246673648305)
                  ·
                    refine ⟨3948458102250185005236229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5264610803000246673648305 3948458102250185005236229)
                    ·
                      refine ⟨740335894171909688481793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3948458102250185005236229 740335894171909688481793)
                      ·
                        rfl

theorem cell23_1441799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_1441799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441799 prefixEnd_1441799 := by exact prefixLift 1441799
  have htrace : WordTrace (prefixWord ++ tailWord_1441799) baseStart_1441799 baseEnd_1441799 := by
    simpa [prefixWord, tailWord_1441799, baseEnd_1441799] using wordTrace_append hprefix tailTrace_1441799
  have hstable : (prefixWord ++ tailWord_1441799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441799).length < 2 ^ (prefixWord ++ tailWord_1441799).sum := by decide
  have hdescent : baseEnd_1441799 < baseStart_1441799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441806 : List Nat := [4, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3]
def baseStart_1441806 : Nat := 118140960795 + 1441806 * 2 ^ 59
def prefixEnd_1441806 : Nat := 4983230072969 + 3 ^ 40 * 1441806 * 2
def baseEnd_1441806 : Nat := 740339488536491161094261

theorem tailTrace_1441806 : CollatzResearch.WordTrace tailWord_1441806 prefixEnd_1441806 740339488536491161094261 := by
  unfold tailWord_1441806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6573373126823822213209159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35057990009727051803782181 6573373126823822213209159)
  ·
    refine ⟨9860059690235733319813739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6573373126823822213209159 9860059690235733319813739)
    ·
      refine ⟨14790089535353599979720609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9860059690235733319813739 14790089535353599979720609)
      ·
        refine ⟨11092567151515199984790457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14790089535353599979720609 11092567151515199984790457)
        ·
          refine ⟨8319425363636399988592843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11092567151515199984790457 8319425363636399988592843)
          ·
            refine ⟨12479138045454599982889265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8319425363636399988592843 12479138045454599982889265)
            ·
              refine ⟨9359353534090949987166949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12479138045454599982889265 9359353534090949987166949)
              ·
                refine ⟨1754878787642053122593803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9359353534090949987166949 1754878787642053122593803)
                ·
                  refine ⟨2632318181463079683890705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1754878787642053122593803 2632318181463079683890705)
                  ·
                    refine ⟨1974238636097309762918029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2632318181463079683890705 1974238636097309762918029)
                    ·
                      refine ⟨740339488536491161094261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1974238636097309762918029 740339488536491161094261)
                      ·
                        rfl

theorem cell23_1441806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_1441806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441806 prefixEnd_1441806 := by exact prefixLift 1441806
  have htrace : WordTrace (prefixWord ++ tailWord_1441806) baseStart_1441806 baseEnd_1441806 := by
    simpa [prefixWord, tailWord_1441806, baseEnd_1441806] using wordTrace_append hprefix tailTrace_1441806
  have hstable : (prefixWord ++ tailWord_1441806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441806).length < 2 ^ (prefixWord ++ tailWord_1441806).sum := by decide
  have hdescent : baseEnd_1441806 < baseStart_1441806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441820 : List Nat := [2, 2, 3, 1, 3, 1, 1, 5, 1, 2, 2]
def baseStart_1441820 : Nat := 118140960795 + 1441820 * 2 ^ 59
def prefixEnd_1441820 : Nat := 4983230072969 + 3 ^ 40 * 1441820 * 2
def baseEnd_1441820 : Nat := 740346677265654106319197

theorem tailTrace_1441820 : CollatzResearch.WordTrace tailWord_1441820 prefixEnd_1441820 740346677265654106319197 := by
  unfold tailWord_1441820
  simp only [CollatzResearch.WordTrace]
  refine ⟨26293747818269929048341457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35058330424359905397788609 26293747818269929048341457)
  ·
    refine ⟨19720310863702446786256093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26293747818269929048341457 19720310863702446786256093)
    ·
      refine ⟨7395116573888417544846035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19720310863702446786256093 7395116573888417544846035)
      ·
        refine ⟨11092674860832626317269053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7395116573888417544846035 11092674860832626317269053)
        ·
          refine ⟨4159753072812234868975895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11092674860832626317269053 4159753072812234868975895)
          ·
            refine ⟨6239629609218352303463843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4159753072812234868975895 6239629609218352303463843)
            ·
              refine ⟨9359444413827528455195765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6239629609218352303463843 9359444413827528455195765)
              ·
                refine ⟨877447913796330792674603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9359444413827528455195765 877447913796330792674603)
                ·
                  refine ⟨1316171870694496189011905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 877447913796330792674603 1316171870694496189011905)
                  ·
                    refine ⟨987128903020872141758929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1316171870694496189011905 987128903020872141758929)
                    ·
                      refine ⟨740346677265654106319197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 987128903020872141758929 740346677265654106319197)
                      ·
                        rfl

theorem cell23_1441820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_1441820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441820 prefixEnd_1441820 := by exact prefixLift 1441820
  have htrace : WordTrace (prefixWord ++ tailWord_1441820) baseStart_1441820 baseEnd_1441820 := by
    simpa [prefixWord, tailWord_1441820, baseEnd_1441820] using wordTrace_append hprefix tailTrace_1441820
  have hstable : (prefixWord ++ tailWord_1441820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441820).length < 2 ^ (prefixWord ++ tailWord_1441820).sum := by decide
  have hdescent : baseEnd_1441820 < baseStart_1441820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441836 : List Nat := [2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 3]
def baseStart_1441836 : Nat := 118140960795 + 1441836 * 2 ^ 59
def prefixEnd_1441836 : Nat := 4983230072969 + 3 ^ 40 * 1441836 * 2
def baseEnd_1441836 : Nat := 740354892956126043719123

theorem tailTrace_1441836 : CollatzResearch.WordTrace tailWord_1441836 prefixEnd_1441836 740354892956126043719123 := by
  unfold tailWord_1441836
  simp only [CollatzResearch.WordTrace]
  refine ⟨26294039602240946414632681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35058719469654595219510241 26294039602240946414632681)
  ·
    refine ⟨19720529701680709810974511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26294039602240946414632681 19720529701680709810974511)
    ·
      refine ⟨29580794552521064716461767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19720529701680709810974511 29580794552521064716461767)
      ·
        refine ⟨44371191828781597074692651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29580794552521064716461767 44371191828781597074692651)
        ·
          refine ⟨66556787743172395612038977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44371191828781597074692651 66556787743172395612038977)
          ·
            refine ⟨49917590807379296709029233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66556787743172395612038977 49917590807379296709029233)
            ·
              refine ⟨37438193105534472531771925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49917590807379296709029233 37438193105534472531771925)
              ·
                refine ⟨1754915301821928399926809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37438193105534472531771925 1754915301821928399926809)
                ·
                  refine ⟨1316186476366446299945107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1754915301821928399926809 1316186476366446299945107)
                  ·
                    refine ⟨1974279714549669449917661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1316186476366446299945107 1974279714549669449917661)
                    ·
                      refine ⟨740354892956126043719123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1974279714549669449917661 740354892956126043719123)
                      ·
                        rfl

theorem cell23_1441836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 3].length) (baseStart_1441836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441836 prefixEnd_1441836 := by exact prefixLift 1441836
  have htrace : WordTrace (prefixWord ++ tailWord_1441836) baseStart_1441836 baseEnd_1441836 := by
    simpa [prefixWord, tailWord_1441836, baseEnd_1441836] using wordTrace_append hprefix tailTrace_1441836
  have hstable : (prefixWord ++ tailWord_1441836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441836).length < 2 ^ (prefixWord ++ tailWord_1441836).sum := by decide
  have hdescent : baseEnd_1441836 < baseStart_1441836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441863 : List Nat := [1, 1, 4, 1, 3, 1, 4, 2, 1, 3, 2]
def baseStart_1441863 : Nat := 118140960795 + 1441863 * 2 ^ 59
def prefixEnd_1441863 : Nat := 4983230072969 + 3 ^ 40 * 1441863 * 2
def baseEnd_1441863 : Nat := 740368756933797438081499

theorem tailTrace_1441863 : CollatzResearch.WordTrace tailWord_1441863 prefixEnd_1441863 740368756933797438081499 := by
  unfold tailWord_1441863
  simp only [CollatzResearch.WordTrace]
  refine ⟨52589063975384076440498243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35059375983589384293665495 52589063975384076440498243)
  ·
    refine ⟨78883595963076114660747365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52589063975384076440498243 78883595963076114660747365)
    ·
      refine ⟨14790674243076771498890131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78883595963076114660747365 14790674243076771498890131)
      ·
        refine ⟨22186011364615157248335197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14790674243076771498890131 22186011364615157248335197)
        ·
          refine ⟨8319754261730683968125699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22186011364615157248335197 8319754261730683968125699)
          ·
            refine ⟨12479631392596025952188549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8319754261730683968125699 12479631392596025952188549)
            ·
              refine ⟨2339930886111754866035353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12479631392596025952188549 2339930886111754866035353)
              ·
                refine ⟨1754948164583816149526515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2339930886111754866035353 1754948164583816149526515)
                ·
                  refine ⟨2632422246875724224289773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1754948164583816149526515 2632422246875724224289773)
                  ·
                    refine ⟨987158342578396584108665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2632422246875724224289773 987158342578396584108665)
                    ·
                      refine ⟨740368756933797438081499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 987158342578396584108665 740368756933797438081499)
                      ·
                        rfl

theorem cell23_1441863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_1441863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441863 prefixEnd_1441863 := by exact prefixLift 1441863
  have htrace : WordTrace (prefixWord ++ tailWord_1441863) baseStart_1441863 baseEnd_1441863 := by
    simpa [prefixWord, tailWord_1441863, baseEnd_1441863] using wordTrace_append hprefix tailTrace_1441863
  have hstable : (prefixWord ++ tailWord_1441863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441863).length < 2 ^ (prefixWord ++ tailWord_1441863).sum := by decide
  have hdescent : baseEnd_1441863 < baseStart_1441863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441876 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 3, 4, 2]
def baseStart_1441876 : Nat := 118140960795 + 1441876 * 2 ^ 59
def prefixEnd_1441876 : Nat := 4983230072969 + 3 ^ 40 * 1441876 * 2
def baseEnd_1441876 : Nat := 740375432182305887218939

theorem tailTrace_1441876 : CollatzResearch.WordTrace tailWord_1441876 prefixEnd_1441876 740375432182305887218939 := by
  unfold tailWord_1441876
  simp only [CollatzResearch.WordTrace]
  refine ⟨26294769062168489830360741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35059692082891319773814321 26294769062168489830360741)
  ·
    refine ⟨4930269199156591843192639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26294769062168489830360741 4930269199156591843192639)
    ·
      refine ⟨7395403798734887764788959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4930269199156591843192639 7395403798734887764788959)
      ·
        refine ⟨11093105698102331647183439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7395403798734887764788959 11093105698102331647183439)
        ·
          refine ⟨16639658547153497470775159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11093105698102331647183439 16639658547153497470775159)
          ·
            refine ⟨24959487820730246206162739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16639658547153497470775159 24959487820730246206162739)
            ·
              refine ⟨37439231731095369309244109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24959487820730246206162739 37439231731095369309244109)
              ·
                refine ⟨14039711899160763490966541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37439231731095369309244109 14039711899160763490966541)
                ·
                  refine ⟨5264891962185286309112453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14039711899160763490966541 5264891962185286309112453)
                  ·
                    refine ⟨987167242909741182958585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5264891962185286309112453 987167242909741182958585)
                    ·
                      refine ⟨740375432182305887218939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 987167242909741182958585 740375432182305887218939)
                      ·
                        rfl

theorem cell23_1441876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_1441876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441876 prefixEnd_1441876 := by exact prefixLift 1441876
  have htrace : WordTrace (prefixWord ++ tailWord_1441876) baseStart_1441876 baseEnd_1441876 := by
    simpa [prefixWord, tailWord_1441876, baseEnd_1441876] using wordTrace_append hprefix tailTrace_1441876
  have hstable : (prefixWord ++ tailWord_1441876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441876).length < 2 ^ (prefixWord ++ tailWord_1441876).sum := by decide
  have hdescent : baseEnd_1441876 < baseStart_1441876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441893 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 4, 2, 2]
def baseStart_1441893 : Nat := 118140960795 + 1441893 * 2 ^ 59
def prefixEnd_1441893 : Nat := 4983230072969 + 3 ^ 40 * 1441893 * 2
def baseEnd_1441893 : Nat := 740384161353432320706361

theorem tailTrace_1441893 : CollatzResearch.WordTrace tailWord_1441893 prefixEnd_1441893 740384161353432320706361 := by
  unfold tailWord_1441893
  simp only [CollatzResearch.WordTrace]
  refine ⟨52590158165275391564090333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35060105443516927709393555 52590158165275391564090333)
  ·
    refine ⟨19721309311978271836533875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52590158165275391564090333 19721309311978271836533875)
    ·
      refine ⟨29581963967967407754800813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19721309311978271836533875 29581963967967407754800813)
      ·
        refine ⟨11093236487987777908050305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29581963967967407754800813 11093236487987777908050305)
        ·
          refine ⟨8319927365990833431037729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11093236487987777908050305 8319927365990833431037729)
          ·
            refine ⟨6239945524493125073278297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8319927365990833431037729 6239945524493125073278297)
            ·
              refine ⟨4679959143369843804958723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6239945524493125073278297 4679959143369843804958723)
              ·
                refine ⟨7019938715054765707438085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4679959143369843804958723 7019938715054765707438085)
                ·
                  refine ⟨1316238509072768570144641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7019938715054765707438085 1316238509072768570144641)
                  ·
                    refine ⟨987178881804576427608481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1316238509072768570144641 987178881804576427608481)
                    ·
                      refine ⟨740384161353432320706361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 987178881804576427608481 740384161353432320706361)
                      ·
                        rfl

theorem cell23_1441893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_1441893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441893 prefixEnd_1441893 := by exact prefixLift 1441893
  have htrace : WordTrace (prefixWord ++ tailWord_1441893) baseStart_1441893 baseEnd_1441893 := by
    simpa [prefixWord, tailWord_1441893, baseEnd_1441893] using wordTrace_append hprefix tailTrace_1441893
  have hstable : (prefixWord ++ tailWord_1441893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441893).length < 2 ^ (prefixWord ++ tailWord_1441893).sum := by decide
  have hdescent : baseEnd_1441893 < baseStart_1441893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441950 : List Nat := [4, 3, 1, 1, 3, 1, 1, 4, 5]
def baseStart_1441950 : Nat := 118140960795 + 1441950 * 2 ^ 59
def prefixEnd_1441950 : Nat := 4983230072969 + 3 ^ 40 * 1441950 * 2
def baseEnd_1441950 : Nat := 82268158861193177521511

theorem tailTrace_1441950 : CollatzResearch.WordTrace tailWord_1441950 prefixEnd_1441950 82268158861193177521511 := by
  unfold tailWord_1441950
  simp only [CollatzResearch.WordTrace]
  refine ⟨6574029640758611287364413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35061491417379260199276869 6574029640758611287364413)
  ·
    refine ⟨2465261115284479232761655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6574029640758611287364413 2465261115284479232761655)
    ·
      refine ⟨3697891672926718849142483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2465261115284479232761655 3697891672926718849142483)
      ·
        refine ⟨5546837509390078273713725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3697891672926718849142483 5546837509390078273713725)
        ·
          refine ⟨2080064066021279352642647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5546837509390078273713725 2080064066021279352642647)
          ·
            refine ⟨3120096099031919028963971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080064066021279352642647 3120096099031919028963971)
            ·
              refine ⟨4680144148547878543445957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3120096099031919028963971 4680144148547878543445957)
              ·
                refine ⟨877527027852727226896117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4680144148547878543445957 877527027852727226896117)
                ·
                  refine ⟨82268158861193177521511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 877527027852727226896117 82268158861193177521511)
                  ·
                    rfl

theorem cell23_1441950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_1441950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441950 prefixEnd_1441950 := by exact prefixLift 1441950
  have htrace : WordTrace (prefixWord ++ tailWord_1441950) baseStart_1441950 baseEnd_1441950 := by
    simpa [prefixWord, tailWord_1441950, baseEnd_1441950] using wordTrace_append hprefix tailTrace_1441950
  have hstable : (prefixWord ++ tailWord_1441950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441950).length < 2 ^ (prefixWord ++ tailWord_1441950).sum := by decide
  have hdescent : baseEnd_1441950 < baseStart_1441950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441976 : List Nat := [2, 1, 2, 1, 2, 1, 5, 2, 3, 4]
def baseStart_1441976 : Nat := 118140960795 + 1441976 * 2 ^ 59
def prefixEnd_1441976 : Nat := 4983230072969 + 3 ^ 40 * 1441976 * 2
def baseEnd_1441976 : Nat := 246808926749251831989493

theorem tailTrace_1441976 : CollatzResearch.WordTrace tailWord_1441976 prefixEnd_1441976 246808926749251831989493 := by
  unfold tailWord_1441976
  simp only [CollatzResearch.WordTrace]
  refine ⟨26296592711987348369680891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35062123615983131159574521 26296592711987348369680891)
  ·
    refine ⟨39444889067981022554521337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26296592711987348369680891 39444889067981022554521337)
    ·
      refine ⟨29583666800985766915891003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39444889067981022554521337 29583666800985766915891003)
      ·
        refine ⟨44375500201478650373836505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29583666800985766915891003 44375500201478650373836505)
        ·
          refine ⟨33281625151108987780377379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44375500201478650373836505 33281625151108987780377379)
          ·
            refine ⟨49922437726663481670566069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33281625151108987780377379 49922437726663481670566069)
            ·
              refine ⟨4680228536874701406615569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49922437726663481670566069 4680228536874701406615569)
              ·
                refine ⟨3510171402656026054961677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4680228536874701406615569 3510171402656026054961677)
                ·
                  refine ⟨1316314275996009770610629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3510171402656026054961677 1316314275996009770610629)
                  ·
                    refine ⟨246808926749251831989493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1316314275996009770610629 246808926749251831989493)
                    ·
                      rfl

theorem cell23_1441976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 3, 4].length) (baseStart_1441976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441976 prefixEnd_1441976 := by exact prefixLift 1441976
  have htrace : WordTrace (prefixWord ++ tailWord_1441976) baseStart_1441976 baseEnd_1441976 := by
    simpa [prefixWord, tailWord_1441976, baseEnd_1441976] using wordTrace_append hprefix tailTrace_1441976
  have hstable : (prefixWord ++ tailWord_1441976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441976).length < 2 ^ (prefixWord ++ tailWord_1441976).sum := by decide
  have hdescent : baseEnd_1441976 < baseStart_1441976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1441980 : List Nat := [2, 2, 2, 3, 4, 1, 1, 1, 2, 5]
def baseStart_1441980 : Nat := 118140960795 + 1441980 * 2 ^ 59
def prefixEnd_1441980 : Nat := 4983230072969 + 3 ^ 40 * 1441980 * 2
def baseEnd_1441980 : Nat := 246809611390124493439487

theorem tailTrace_1441980 : CollatzResearch.WordTrace tailWord_1441980 prefixEnd_1441980 246809611390124493439487 := by
  unfold tailWord_1441980
  simp only [CollatzResearch.WordTrace]
  refine ⟨26296665657980102711253697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35062220877306803615004929 26296665657980102711253697)
  ·
    refine ⟨19722499243485077033440273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26296665657980102711253697 19722499243485077033440273)
    ·
      refine ⟨14791874432613807775080205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19722499243485077033440273 14791874432613807775080205)
      ·
        refine ⟨5546952912230177915655077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14791874432613807775080205 5546952912230177915655077)
        ·
          refine ⟨1040053671043158359185327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5546952912230177915655077 1040053671043158359185327)
          ·
            refine ⟨1560080506564737538777991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040053671043158359185327 1560080506564737538777991)
            ·
              refine ⟨2340120759847106308166987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1560080506564737538777991 2340120759847106308166987)
              ·
                refine ⟨3510181139770659462250481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2340120759847106308166987 3510181139770659462250481)
                ·
                  refine ⟨2632635854827994596687861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3510181139770659462250481 2632635854827994596687861)
                  ·
                    refine ⟨246809611390124493439487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2632635854827994596687861 246809611390124493439487)
                    ·
                      rfl

theorem cell23_1441980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_1441980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1441980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1441980 prefixEnd_1441980 := by exact prefixLift 1441980
  have htrace : WordTrace (prefixWord ++ tailWord_1441980) baseStart_1441980 baseEnd_1441980 := by
    simpa [prefixWord, tailWord_1441980, baseEnd_1441980] using wordTrace_append hprefix tailTrace_1441980
  have hstable : (prefixWord ++ tailWord_1441980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1441980).length < 2 ^ (prefixWord ++ tailWord_1441980).sum := by decide
  have hdescent : baseEnd_1441980 < baseStart_1441980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1441980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442009 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 1, 2, 6]
def baseStart_1442009 : Nat := 118140960795 + 1442009 * 2 ^ 59
def prefixEnd_1442009 : Nat := 4983230072969 + 3 ^ 40 * 1442009 * 2
def baseEnd_1442009 : Nat := 740443725109353866855827

theorem tailTrace_1442009 : CollatzResearch.WordTrace tailWord_1442009 prefixEnd_1442009 740443725109353866855827 := by
  unfold tailWord_1442009
  simp only [CollatzResearch.WordTrace]
  refine ⟨52594389032855143375313081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35062926021903428916875387 52594389032855143375313081)
  ·
    refine ⟨39445791774641357531484811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52594389032855143375313081 39445791774641357531484811)
    ·
      refine ⟨59168687661962036297227217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39445791774641357531484811 59168687661962036297227217)
      ·
        refine ⟨44376515746471527222920413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59168687661962036297227217 44376515746471527222920413)
        ·
          refine ⟨16641193404926822708595155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44376515746471527222920413 16641193404926822708595155)
          ·
            refine ⟨24961790107390234062892733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16641193404926822708595155 24961790107390234062892733)
            ·
              refine ⟨9360671290271337773584775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24961790107390234062892733 9360671290271337773584775)
              ·
                refine ⟨14041006935407006660377163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9360671290271337773584775 14041006935407006660377163)
                ·
                  refine ⟨21061510403110509990565745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14041006935407006660377163 21061510403110509990565745)
                  ·
                    refine ⟨15796132802332882492924309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21061510403110509990565745 15796132802332882492924309)
                    ·
                      refine ⟨740443725109353866855827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15796132802332882492924309 740443725109353866855827)
                      ·
                        rfl

theorem cell23_1442009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_1442009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442009 prefixEnd_1442009 := by exact prefixLift 1442009
  have htrace : WordTrace (prefixWord ++ tailWord_1442009) baseStart_1442009 baseEnd_1442009 := by
    simpa [prefixWord, tailWord_1442009, baseEnd_1442009] using wordTrace_append hprefix tailTrace_1442009
  have hstable : (prefixWord ++ tailWord_1442009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442009).length < 2 ^ (prefixWord ++ tailWord_1442009).sum := by decide
  have hdescent : baseEnd_1442009 < baseStart_1442009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442033 : List Nat := [1, 2, 2, 2, 2, 1, 4, 2, 3, 1, 3]
def baseStart_1442033 : Nat := 118140960795 + 1442033 * 2 ^ 59
def prefixEnd_1442033 : Nat := 4983230072969 + 3 ^ 40 * 1442033 * 2
def baseEnd_1442033 : Nat := 740456048645061772955717

theorem tailTrace_1442033 : CollatzResearch.WordTrace tailWord_1442033 prefixEnd_1442033 740456048645061772955717 := by
  unfold tailWord_1442033
  simp only [CollatzResearch.WordTrace]
  refine ⟨52595264384768195474186753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35063509589845463649457835 52595264384768195474186753)
  ·
    refine ⟨39446448288576146605640065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52595264384768195474186753 39446448288576146605640065)
    ·
      refine ⟨29584836216432109954230049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39446448288576146605640065 29584836216432109954230049)
      ·
        refine ⟨22188627162324082465672537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29584836216432109954230049 22188627162324082465672537)
        ·
          refine ⟨16641470371743061849254403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22188627162324082465672537 16641470371743061849254403)
          ·
            refine ⟨24962205557614592773881605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16641470371743061849254403 24962205557614592773881605)
            ·
              refine ⟨4680413542052736145102801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24962205557614592773881605 4680413542052736145102801)
              ·
                refine ⟨3510310156539552108827101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4680413542052736145102801 3510310156539552108827101)
                ·
                  refine ⟨1316366308702332040810163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3510310156539552108827101 1316366308702332040810163)
                  ·
                    refine ⟨1974549463053498061215245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1316366308702332040810163 1974549463053498061215245)
                    ·
                      refine ⟨740456048645061772955717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1974549463053498061215245 740456048645061772955717)
                      ·
                        rfl

theorem cell23_1442033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_1442033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442033 prefixEnd_1442033 := by exact prefixLift 1442033
  have htrace : WordTrace (prefixWord ++ tailWord_1442033) baseStart_1442033 baseEnd_1442033 := by
    simpa [prefixWord, tailWord_1442033, baseEnd_1442033] using wordTrace_append hprefix tailTrace_1442033
  have hstable : (prefixWord ++ tailWord_1442033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442033).length < 2 ^ (prefixWord ++ tailWord_1442033).sum := by decide
  have hdescent : baseEnd_1442033 < baseStart_1442033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442076 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_1442076 : Nat := 118140960795 + 1442076 * 2 ^ 59
def prefixEnd_1442076 : Nat := 4983230072969 + 3 ^ 40 * 1442076 * 2
def baseEnd_1442076 : Nat := 740478128313205104718019

theorem tailTrace_1442076 : CollatzResearch.WordTrace tailWord_1442076 prefixEnd_1442076 740478128313205104718019 := by
  unfold tailWord_1442076
  simp only [CollatzResearch.WordTrace]
  refine ⟨26298416361806206909001041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35064555149074942545334721 26298416361806206909001041)
  ·
    refine ⟨19723812271354655181750781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26298416361806206909001041 19723812271354655181750781)
    ·
      refine ⟨7396429601757995693156543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19723812271354655181750781 7396429601757995693156543)
      ·
        refine ⟨11094644402636993539734815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7396429601757995693156543 11094644402636993539734815)
        ·
          refine ⟨16641966603955490309602223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11094644402636993539734815 16641966603955490309602223)
          ·
            refine ⟨24962949905933235464403335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16641966603955490309602223 24962949905933235464403335)
            ·
              refine ⟨37444424858899853196605003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24962949905933235464403335 37444424858899853196605003)
              ·
                refine ⟨56166637288349779794907505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37444424858899853196605003 56166637288349779794907505)
                ·
                  refine ⟨42124977966262334846180629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56166637288349779794907505 42124977966262334846180629)
                  ·
                    refine ⟨1974608342168546945914717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42124977966262334846180629 1974608342168546945914717)
                    ·
                      refine ⟨740478128313205104718019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1974608342168546945914717 740478128313205104718019)
                      ·
                        rfl

theorem cell23_1442076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_1442076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442076 prefixEnd_1442076 := by exact prefixLift 1442076
  have htrace : WordTrace (prefixWord ++ tailWord_1442076) baseStart_1442076 baseEnd_1442076 := by
    simpa [prefixWord, tailWord_1442076, baseEnd_1442076] using wordTrace_append hprefix tailTrace_1442076
  have hstable : (prefixWord ++ tailWord_1442076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442076).length < 2 ^ (prefixWord ++ tailWord_1442076).sum := by decide
  have hdescent : baseEnd_1442076 < baseStart_1442076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442083 : List Nat := [1, 1, 1, 4, 2, 2, 3, 3, 2, 4]
def baseStart_1442083 : Nat := 118140960795 + 1442083 * 2 ^ 59
def prefixEnd_1442083 : Nat := 4983230072969 + 3 ^ 40 * 1442083 * 2
def baseEnd_1442083 : Nat := 246827240892595525776829

theorem tailTrace_1442083 : CollatzResearch.WordTrace tailWord_1442083 prefixEnd_1442083 246827240892595525776829 := by
  unfold tailWord_1442083
  simp only [CollatzResearch.WordTrace]
  refine ⟨52597088034587054013506903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35064725356391369342337935 52597088034587054013506903)
  ·
    refine ⟨78895632051880581020260355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52597088034587054013506903 78895632051880581020260355)
    ·
      refine ⟨118343448077820871530390533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78895632051880581020260355 118343448077820871530390533)
      ·
        refine ⟨22189396514591413411948225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118343448077820871530390533 22189396514591413411948225)
        ·
          refine ⟨16642047385943560058961169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22189396514591413411948225 16642047385943560058961169)
          ·
            refine ⟨12481535539457670044220877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16642047385943560058961169 12481535539457670044220877)
            ·
              refine ⟨4680575827296626266582829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12481535539457670044220877 4680575827296626266582829)
              ·
                refine ⟨1755215935236234849968561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4680575827296626266582829 1755215935236234849968561)
                ·
                  refine ⟨1316411951427176137476421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1755215935236234849968561 1316411951427176137476421)
                  ·
                    refine ⟨246827240892595525776829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1316411951427176137476421 246827240892595525776829)
                    ·
                      rfl

theorem cell23_1442083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 4].length) (baseStart_1442083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442083 prefixEnd_1442083 := by exact prefixLift 1442083
  have htrace : WordTrace (prefixWord ++ tailWord_1442083) baseStart_1442083 baseEnd_1442083 := by
    simpa [prefixWord, tailWord_1442083, baseEnd_1442083] using wordTrace_append hprefix tailTrace_1442083
  have hstable : (prefixWord ++ tailWord_1442083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442083).length < 2 ^ (prefixWord ++ tailWord_1442083).sum := by decide
  have hdescent : baseEnd_1442083 < baseStart_1442083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442087 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1442087 : Nat := 118140960795 + 1442087 * 2 ^ 59
def prefixEnd_1442087 : Nat := 4983230072969 + 3 ^ 40 * 1442087 * 2
def baseEnd_1442087 : Nat := 246827925533468187226823

theorem tailTrace_1442087 : CollatzResearch.WordTrace tailWord_1442087 prefixEnd_1442087 246827925533468187226823 := by
  unfold tailWord_1442087
  simp only [CollatzResearch.WordTrace]
  refine ⟨52597233926572562696652515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35064822617715041797768343 52597233926572562696652515)
  ·
    refine ⟨78895850889858844044978773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52597233926572562696652515 78895850889858844044978773)
    ·
      refine ⟨924560752615533328652095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 78895850889858844044978773 924560752615533328652095)
      ·
        refine ⟨1386841128923299992978143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 924560752615533328652095 1386841128923299992978143)
        ·
          refine ⟨2080261693384949989467215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1386841128923299992978143 2080261693384949989467215)
          ·
            refine ⟨3120392540077424984200823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080261693384949989467215 3120392540077424984200823)
            ·
              refine ⟨4680588810116137476301235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3120392540077424984200823 4680588810116137476301235)
              ·
                refine ⟨7020883215174206214451853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4680588810116137476301235 7020883215174206214451853)
                ·
                  refine ⟨2632831205690327330419445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7020883215174206214451853 2632831205690327330419445)
                  ·
                    refine ⟨246827925533468187226823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2632831205690327330419445 246827925533468187226823)
                    ·
                      rfl

theorem cell23_1442087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1442087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442087 prefixEnd_1442087 := by exact prefixLift 1442087
  have htrace : WordTrace (prefixWord ++ tailWord_1442087) baseStart_1442087 baseEnd_1442087 := by
    simpa [prefixWord, tailWord_1442087, baseEnd_1442087] using wordTrace_append hprefix tailTrace_1442087
  have hstable : (prefixWord ++ tailWord_1442087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442087).length < 2 ^ (prefixWord ++ tailWord_1442087).sum := by decide
  have hdescent : baseEnd_1442087 < baseStart_1442087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442090 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_1442090 : Nat := 118140960795 + 1442090 * 2 ^ 59
def prefixEnd_1442090 : Nat := 4983230072969 + 3 ^ 40 * 1442090 * 2
def baseEnd_1442090 : Nat := 740485317042368049942955

theorem tailTrace_1442090 : CollatzResearch.WordTrace tailWord_1442090 prefixEnd_1442090 740485317042368049942955 := by
  unfold tailWord_1442090
  simp only [CollatzResearch.WordTrace]
  refine ⟨13149335836390423552252931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35064895563707796139341149 13149335836390423552252931)
  ·
    refine ⟨19724003754585635328379397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13149335836390423552252931 19724003754585635328379397)
    ·
      refine ⟨3698250703984806624071137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19724003754585635328379397 3698250703984806624071137)
      ·
        refine ⟨2773688027988604968053353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3698250703984806624071137 2773688027988604968053353)
        ·
          refine ⟨2080266020991453726040015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2773688027988604968053353 2080266020991453726040015)
          ·
            refine ⟨3120399031487180589060023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080266020991453726040015 3120399031487180589060023)
            ·
              refine ⟨4680598547230770883590035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3120399031487180589060023 4680598547230770883590035)
              ·
                refine ⟨7020897820846156325385053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4680598547230770883590035 7020897820846156325385053)
                ·
                  refine ⟨2632836682817308622019395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7020897820846156325385053 2632836682817308622019395)
                  ·
                    refine ⟨3949255024225962933029093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2632836682817308622019395 3949255024225962933029093)
                    ·
                      refine ⟨740485317042368049942955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3949255024225962933029093 740485317042368049942955)
                      ·
                        rfl

theorem cell23_1442090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_1442090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442090 prefixEnd_1442090 := by exact prefixLift 1442090
  have htrace : WordTrace (prefixWord ++ tailWord_1442090) baseStart_1442090 baseEnd_1442090 := by
    simpa [prefixWord, tailWord_1442090, baseEnd_1442090] using wordTrace_append hprefix tailTrace_1442090
  have hstable : (prefixWord ++ tailWord_1442090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442090).length < 2 ^ (prefixWord ++ tailWord_1442090).sum := by decide
  have hdescent : baseEnd_1442090 < baseStart_1442090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442094 : List Nat := [4, 1, 3, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_1442094 : Nat := 118140960795 + 1442094 * 2 ^ 59
def prefixEnd_1442094 : Nat := 4983230072969 + 3 ^ 40 * 1442094 * 2
def baseEnd_1442094 : Nat := 740487370964986034292937

theorem tailTrace_1442094 : CollatzResearch.WordTrace tailWord_1442094 prefixEnd_1442094 740487370964986034292937 := by
  unfold tailWord_1442094
  simp only [CollatzResearch.WordTrace]
  refine ⟨6574686154693400361519667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35064992825031468594771557 6574686154693400361519667)
  ·
    refine ⟨9862029232040100542279501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6574686154693400361519667 9862029232040100542279501)
    ·
      refine ⟨3698260962015037703354813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9862029232040100542279501 3698260962015037703354813)
      ·
        refine ⟨1386847860755639138758055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3698260962015037703354813 1386847860755639138758055)
        ·
          refine ⟨2080271791133458708137083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1386847860755639138758055 2080271791133458708137083)
          ·
            refine ⟨3120407686700188062205625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080271791133458708137083 3120407686700188062205625)
            ·
              refine ⟨2340305765025141046654219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3120407686700188062205625 2340305765025141046654219)
              ·
                refine ⟨3510458647537711569981329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2340305765025141046654219 3510458647537711569981329)
                ·
                  refine ⟨2632843985653283677485997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3510458647537711569981329 2632843985653283677485997)
                  ·
                    refine ⟨987316494619981379057249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2632843985653283677485997 987316494619981379057249)
                    ·
                      refine ⟨740487370964986034292937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 987316494619981379057249 740487370964986034292937)
                      ·
                        rfl

theorem cell23_1442094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_1442094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442094 prefixEnd_1442094 := by exact prefixLift 1442094
  have htrace : WordTrace (prefixWord ++ tailWord_1442094) baseStart_1442094 baseEnd_1442094 := by
    simpa [prefixWord, tailWord_1442094, baseEnd_1442094] using wordTrace_append hprefix tailTrace_1442094
  have hstable : (prefixWord ++ tailWord_1442094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442094).length < 2 ^ (prefixWord ++ tailWord_1442094).sum := by decide
  have hdescent : baseEnd_1442094 < baseStart_1442094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442110 : List Nat := [4, 2, 1, 2, 1, 4, 1, 1, 1, 1, 5]
def baseStart_1442110 : Nat := 118140960795 + 1442110 * 2 ^ 59
def prefixEnd_1442110 : Nat := 4983230072969 + 3 ^ 40 * 1442110 * 2
def baseEnd_1442110 : Nat := 740495586655457971692863

theorem tailTrace_1442110 : CollatzResearch.WordTrace tailWord_1442110 prefixEnd_1442110 740495586655457971692863 := by
  unfold tailWord_1442110
  simp only [CollatzResearch.WordTrace]
  refine ⟨6574759100686154703092473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35065381870326158416493189 6574759100686154703092473)
  ·
    refine ⟨4931069325514616027319355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6574759100686154703092473 4931069325514616027319355)
    ·
      refine ⟨7396603988271924040979033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4931069325514616027319355 7396603988271924040979033)
      ·
        refine ⟨5547452991203943030734275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7396603988271924040979033 5547452991203943030734275)
        ·
          refine ⟨8321179486805914546101413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5547452991203943030734275 8321179486805914546101413)
          ·
            refine ⟨1560221153776108977394015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8321179486805914546101413 1560221153776108977394015)
            ·
              refine ⟨2340331730664163466091023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1560221153776108977394015 2340331730664163466091023)
              ·
                refine ⟨3510497595996245199136535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2340331730664163466091023 3510497595996245199136535)
                ·
                  refine ⟨5265746393994367798704803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3510497595996245199136535 5265746393994367798704803)
                  ·
                    refine ⟨7898619590991551698057205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5265746393994367798704803 7898619590991551698057205)
                    ·
                      refine ⟨740495586655457971692863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7898619590991551698057205 740495586655457971692863)
                      ·
                        rfl

theorem cell23_1442110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_1442110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442110 prefixEnd_1442110 := by exact prefixLift 1442110
  have htrace : WordTrace (prefixWord ++ tailWord_1442110) baseStart_1442110 baseEnd_1442110 := by
    simpa [prefixWord, tailWord_1442110, baseEnd_1442110] using wordTrace_append hprefix tailTrace_1442110
  have hstable : (prefixWord ++ tailWord_1442110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442110).length < 2 ^ (prefixWord ++ tailWord_1442110).sum := by decide
  have hdescent : baseEnd_1442110 < baseStart_1442110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442113 : List Nat := [1, 2, 5, 2, 3, 10]
def baseStart_1442113 : Nat := 118140960795 + 1442113 * 2 ^ 59
def prefixEnd_1442113 : Nat := 4983230072969 + 3 ^ 40 * 1442113 * 2
def baseEnd_1442113 : Nat := 3047313280236302304343

theorem tailTrace_1442113 : CollatzResearch.WordTrace tailWord_1442113 prefixEnd_1442113 3047313280236302304343 := by
  unfold tailWord_1442113
  simp only [CollatzResearch.WordTrace]
  refine ⟨52598182224478369137098993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35065454816318912758065995 52598182224478369137098993)
  ·
    refine ⟨39448636668358776852824245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52598182224478369137098993 39448636668358776852824245)
    ·
      refine ⟨3698309687658635329952273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39448636668358776852824245 3698309687658635329952273)
      ·
        refine ⟨2773732265743976497464205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3698309687658635329952273 2773732265743976497464205)
        ·
          refine ⟨1040149599653991186549077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2773732265743976497464205 1040149599653991186549077)
          ·
            refine ⟨3047313280236302304343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1040149599653991186549077 3047313280236302304343)
            ·
              rfl

theorem cell23_1442113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 10].length) (baseStart_1442113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442113 prefixEnd_1442113 := by exact prefixLift 1442113
  have htrace : WordTrace (prefixWord ++ tailWord_1442113) baseStart_1442113 baseEnd_1442113 := by
    simpa [prefixWord, tailWord_1442113, baseEnd_1442113] using wordTrace_append hprefix tailTrace_1442113
  have hstable : (prefixWord ++ tailWord_1442113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442113).length < 2 ^ (prefixWord ++ tailWord_1442113).sum := by decide
  have hdescent : baseEnd_1442113 < baseStart_1442113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442223 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 3, 7, 2]
def baseStart_1442223 : Nat := 118140960795 + 1442223 * 2 ^ 59
def prefixEnd_1442223 : Nat := 4983230072969 + 3 ^ 40 * 1442223 * 2
def baseEnd_1442223 : Nat := 740553609969416029579843

theorem tailTrace_1442223 : CollatzResearch.WordTrace tailWord_1442223 prefixEnd_1442223 740553609969416029579843 := by
  unfold tailWord_1442223
  simp only [CollatzResearch.WordTrace]
  refine ⟨52602194254079857923603323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35068129502719905282402215 52602194254079857923603323)
  ·
    refine ⟨78903291381119786885404985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52602194254079857923603323 78903291381119786885404985)
    ·
      refine ⟨59177468535839840164053739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78903291381119786885404985 59177468535839840164053739)
      ·
        refine ⟨88766202803759760246080609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59177468535839840164053739 88766202803759760246080609)
        ·
          refine ⟨66574652102819820184560457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88766202803759760246080609 66574652102819820184560457)
          ·
            refine ⟨49930989077114865138420343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66574652102819820184560457 49930989077114865138420343)
            ·
              refine ⟨74896483615672297707630515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49930989077114865138420343 74896483615672297707630515)
              ·
                refine ⟨112344725423508446561445773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74896483615672297707630515 112344725423508446561445773)
                ·
                  refine ⟨42129272033815667460542165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112344725423508446561445773 42129272033815667460542165)
                  ·
                    refine ⟨987404813292554706106457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42129272033815667460542165 987404813292554706106457)
                    ·
                      refine ⟨740553609969416029579843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 987404813292554706106457 740553609969416029579843)
                      ·
                        rfl

theorem cell23_1442223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 7, 2].length) (baseStart_1442223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442223 prefixEnd_1442223 := by exact prefixLift 1442223
  have htrace : WordTrace (prefixWord ++ tailWord_1442223) baseStart_1442223 baseEnd_1442223 := by
    simpa [prefixWord, tailWord_1442223, baseEnd_1442223] using wordTrace_append hprefix tailTrace_1442223
  have hstable : (prefixWord ++ tailWord_1442223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442223).length < 2 ^ (prefixWord ++ tailWord_1442223).sum := by decide
  have hdescent : baseEnd_1442223 < baseStart_1442223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442233 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 4, 5]
def baseStart_1442233 : Nat := 118140960795 + 1442233 * 2 ^ 59
def prefixEnd_1442233 : Nat := 4983230072969 + 3 ^ 40 * 1442233 * 2
def baseEnd_1442233 : Nat := 246852914925320330151599

theorem tailTrace_1442233 : CollatzResearch.WordTrace tailWord_1442233 prefixEnd_1442233 246852914925320330151599 := by
  unfold tailWord_1442233
  simp only [CollatzResearch.WordTrace]
  refine ⟨52602558984043629631467353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35068372656029086420978235 52602558984043629631467353)
  ·
    refine ⟨39451919238032722223600515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52602558984043629631467353 39451919238032722223600515)
    ·
      refine ⟨59177878857049083335400773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39451919238032722223600515 59177878857049083335400773)
      ·
        refine ⟨11095852285696703125387645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59177878857049083335400773 11095852285696703125387645)
        ·
          refine ⟨4160944607136263672020367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11095852285696703125387645 4160944607136263672020367)
          ·
            refine ⟨6241416910704395508030551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4160944607136263672020367 6241416910704395508030551)
            ·
              refine ⟨9362125366056593262045827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6241416910704395508030551 9362125366056593262045827)
              ·
                refine ⟨14043188049084889893068741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9362125366056593262045827 14043188049084889893068741)
                ·
                  refine ⟨2633097759203416854950389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14043188049084889893068741 2633097759203416854950389)
                  ·
                    refine ⟨246852914925320330151599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2633097759203416854950389 246852914925320330151599)
                    ·
                      rfl

theorem cell23_1442233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 5].length) (baseStart_1442233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442233 prefixEnd_1442233 := by exact prefixLift 1442233
  have htrace : WordTrace (prefixWord ++ tailWord_1442233) baseStart_1442233 baseEnd_1442233 := by
    simpa [prefixWord, tailWord_1442233, baseEnd_1442233] using wordTrace_append hprefix tailTrace_1442233
  have hstable : (prefixWord ++ tailWord_1442233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442233).length < 2 ^ (prefixWord ++ tailWord_1442233).sum := by decide
  have hdescent : baseEnd_1442233 < baseStart_1442233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442237 : List Nat := [1, 4, 1, 2, 2, 3, 3, 2, 5]
def baseStart_1442237 : Nat := 118140960795 + 1442237 * 2 ^ 59
def prefixEnd_1442237 : Nat := 4983230072969 + 3 ^ 40 * 1442237 * 2
def baseEnd_1442237 : Nat := 82284533188730997200531

theorem tailTrace_1442237 : CollatzResearch.WordTrace tailWord_1442237 prefixEnd_1442237 82284533188730997200531 := by
  unfold tailWord_1442237
  simp only [CollatzResearch.WordTrace]
  refine ⟨52602704876029138314612965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35068469917352758876408643 52602704876029138314612965)
  ·
    refine ⟨9863007164255463433989931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52602704876029138314612965 9863007164255463433989931)
    ·
      refine ⟨14794510746383195150984897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9863007164255463433989931 14794510746383195150984897)
      ·
        refine ⟨11095883059787396363238673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14794510746383195150984897 11095883059787396363238673)
        ·
          refine ⟨8321912294840547272429005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11095883059787396363238673 8321912294840547272429005)
          ·
            refine ⟨3120717110565205227160877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8321912294840547272429005 3120717110565205227160877)
            ·
              refine ⟨1170268916461951960185329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3120717110565205227160877 1170268916461951960185329)
              ·
                refine ⟨877701687346463970138997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1170268916461951960185329 877701687346463970138997)
                ·
                  refine ⟨82284533188730997200531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 877701687346463970138997 82284533188730997200531)
                  ·
                    rfl

theorem cell23_1442237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_1442237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442237 prefixEnd_1442237 := by exact prefixLift 1442237
  have htrace : WordTrace (prefixWord ++ tailWord_1442237) baseStart_1442237 baseEnd_1442237 := by
    simpa [prefixWord, tailWord_1442237, baseEnd_1442237] using wordTrace_append hprefix tailTrace_1442237
  have hstable : (prefixWord ++ tailWord_1442237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442237).length < 2 ^ (prefixWord ++ tailWord_1442237).sum := by decide
  have hdescent : baseEnd_1442237 < baseStart_1442237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442323 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 3, 5]
def baseStart_1442323 : Nat := 118140960795 + 1442323 * 2 ^ 59
def prefixEnd_1442323 : Nat := 4983230072969 + 3 ^ 40 * 1442323 * 2
def baseEnd_1442323 : Nat := 246868319344955212776461

theorem tailTrace_1442323 : CollatzResearch.WordTrace tailWord_1442323 prefixEnd_1442323 246868319344955212776461 := by
  unfold tailWord_1442323
  simp only [CollatzResearch.WordTrace]
  refine ⟨52605841553717575002243623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35070561035811716668162415 52605841553717575002243623)
  ·
    refine ⟨78908762330576362503365435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52605841553717575002243623 78908762330576362503365435)
    ·
      refine ⟨118363143495864543755048153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78908762330576362503365435 118363143495864543755048153)
      ·
        refine ⟨88772357621898407816286115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118363143495864543755048153 88772357621898407816286115)
        ·
          refine ⟨133158536432847611724429173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88772357621898407816286115 133158536432847611724429173)
          ·
            refine ⟨12483612790579463599165235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133158536432847611724429173 12483612790579463599165235)
            ·
              refine ⟨18725419185869195398747853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12483612790579463599165235 18725419185869195398747853)
              ·
                refine ⟨7022032194700948274530445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18725419185869195398747853 7022032194700948274530445)
                ·
                  refine ⟨2633262073012855602948917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7022032194700948274530445 2633262073012855602948917)
                  ·
                    refine ⟨246868319344955212776461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2633262073012855602948917 246868319344955212776461)
                    ·
                      rfl

theorem cell23_1442323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 5].length) (baseStart_1442323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442323 prefixEnd_1442323 := by exact prefixLift 1442323
  have htrace : WordTrace (prefixWord ++ tailWord_1442323) baseStart_1442323 baseEnd_1442323 := by
    simpa [prefixWord, tailWord_1442323, baseEnd_1442323] using wordTrace_append hprefix tailTrace_1442323
  have hstable : (prefixWord ++ tailWord_1442323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442323).length < 2 ^ (prefixWord ++ tailWord_1442323).sum := by decide
  have hdescent : baseEnd_1442323 < baseStart_1442323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442324 : List Nat := [2, 4, 3, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_1442324 : Nat := 118140960795 + 1442324 * 2 ^ 59
def prefixEnd_1442324 : Nat := 4983230072969 + 3 ^ 40 * 1442324 * 2
def baseEnd_1442324 : Nat := 740605471515520134416879

theorem tailTrace_1442324 : CollatzResearch.WordTrace tailWord_1442324 prefixEnd_1442324 740605471515520134416879 := by
  unfold tailWord_1442324
  simp only [CollatzResearch.WordTrace]
  refine ⟨26302939013356976086515013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35070585351142634782020017 26302939013356976086515013)
  ·
    refine ⟨4931801065004433016221565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26302939013356976086515013 4931801065004433016221565)
    ·
      refine ⟨1849425399376662381083087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4931801065004433016221565 1849425399376662381083087)
      ·
        refine ⟨2774138099064993571624631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1849425399376662381083087 2774138099064993571624631)
        ·
          refine ⟨4161207148597490357436947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2774138099064993571624631 4161207148597490357436947)
          ·
            refine ⟨6241810722896235536155421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4161207148597490357436947 6241810722896235536155421)
            ·
              refine ⟨2340679021086088326058283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6241810722896235536155421 2340679021086088326058283)
              ·
                refine ⟨3511018531629132489087425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2340679021086088326058283 3511018531629132489087425)
                ·
                  refine ⟨2633263898721849366815569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3511018531629132489087425 2633263898721849366815569)
                  ·
                    refine ⟨1974947924041387025111677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2633263898721849366815569 1974947924041387025111677)
                    ·
                      refine ⟨740605471515520134416879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1974947924041387025111677 740605471515520134416879)
                      ·
                        rfl

theorem cell23_1442324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_1442324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442324 prefixEnd_1442324 := by exact prefixLift 1442324
  have htrace : WordTrace (prefixWord ++ tailWord_1442324) baseStart_1442324 baseEnd_1442324 := by
    simpa [prefixWord, tailWord_1442324, baseEnd_1442324] using wordTrace_append hprefix tailTrace_1442324
  have hstable : (prefixWord ++ tailWord_1442324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442324).length < 2 ^ (prefixWord ++ tailWord_1442324).sum := by decide
  have hdescent : baseEnd_1442324 < baseStart_1442324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442353 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 3, 6]
def baseStart_1442353 : Nat := 118140960795 + 1442353 * 2 ^ 59
def prefixEnd_1442353 : Nat := 4983230072969 + 3 ^ 40 * 1442353 * 2
def baseEnd_1442353 : Nat := 246873454151500173651415

theorem tailTrace_1442353 : CollatzResearch.WordTrace tailWord_1442353 prefixEnd_1442353 246873454151500173651415 := by
  unfold tailWord_1442353
  simp only [CollatzResearch.WordTrace]
  refine ⟨52606935743608890125835713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35071290495739260083890475 52606935743608890125835713)
  ·
    refine ⟨39455201807706667594376785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52606935743608890125835713 39455201807706667594376785)
    ·
      refine ⟨29591401355780000695782589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39455201807706667594376785 29591401355780000695782589)
      ·
        refine ⟨11096775508417500260918471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29591401355780000695782589 11096775508417500260918471)
        ·
          refine ⟨16645163262626250391377707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11096775508417500260918471 16645163262626250391377707)
          ·
            refine ⟨24967744893939375587066561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16645163262626250391377707 24967744893939375587066561)
            ·
              refine ⟨18725808670454531690299921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24967744893939375587066561 18725808670454531690299921)
              ·
                refine ⟨14044356502840898767724941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18725808670454531690299921 14044356502840898767724941)
                ·
                  refine ⟨5266633688565337037896853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14044356502840898767724941 5266633688565337037896853)
                  ·
                    refine ⟨246873454151500173651415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5266633688565337037896853 246873454151500173651415)
                    ·
                      rfl

theorem cell23_1442353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_1442353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442353 prefixEnd_1442353 := by exact prefixLift 1442353
  have htrace : WordTrace (prefixWord ++ tailWord_1442353) baseStart_1442353 baseEnd_1442353 := by
    simpa [prefixWord, tailWord_1442353, baseEnd_1442353] using wordTrace_append hprefix tailTrace_1442353
  have hstable : (prefixWord ++ tailWord_1442353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442353).length < 2 ^ (prefixWord ++ tailWord_1442353).sum := by decide
  have hdescent : baseEnd_1442353 < baseStart_1442353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442354 : List Nat := [3, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3]
def baseStart_1442354 : Nat := 118140960795 + 1442354 * 2 ^ 59
def prefixEnd_1442354 : Nat := 4983230072969 + 3 ^ 40 * 1442354 * 2
def baseEnd_1442354 : Nat := 740620875935155017041741

theorem tailTrace_1442354 : CollatzResearch.WordTrace tailWord_1442354 prefixEnd_1442354 740620875935155017041741 := by
  unfold tailWord_1442354
  simp only [CollatzResearch.WordTrace]
  refine ⟨13151743054151316824155529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35071314811070178197748077 13151743054151316824155529)
  ·
    refine ⟨9863807290613487618116647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13151743054151316824155529 9863807290613487618116647)
    ·
      refine ⟨14795710935920231427174971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9863807290613487618116647 14795710935920231427174971)
      ·
        refine ⟨22193566403880347140762457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14795710935920231427174971 22193566403880347140762457)
        ·
          refine ⟨16645174802910260355571843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22193566403880347140762457 16645174802910260355571843)
          ·
            refine ⟨24967762204365390533357765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16645174802910260355571843 24967762204365390533357765)
            ·
              refine ⟨4681455413318510725004581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24967762204365390533357765 4681455413318510725004581)
              ·
                refine ⟨877772889997220760938359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4681455413318510725004581 877772889997220760938359)
                ·
                  refine ⟨1316659334995831141407539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 877772889997220760938359 1316659334995831141407539)
                  ·
                    refine ⟨1974989002493746712111309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1316659334995831141407539 1974989002493746712111309)
                    ·
                      refine ⟨740620875935155017041741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1974989002493746712111309 740620875935155017041741)
                      ·
                        rfl

theorem cell23_1442354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3].length) (baseStart_1442354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442354 prefixEnd_1442354 := by exact prefixLift 1442354
  have htrace : WordTrace (prefixWord ++ tailWord_1442354) baseStart_1442354 baseEnd_1442354 := by
    simpa [prefixWord, tailWord_1442354, baseEnd_1442354] using wordTrace_append hprefix tailTrace_1442354
  have hstable : (prefixWord ++ tailWord_1442354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442354).length < 2 ^ (prefixWord ++ tailWord_1442354).sum := by decide
  have hdescent : baseEnd_1442354 < baseStart_1442354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442374 : List Nat := [6, 1, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_1442374 : Nat := 118140960795 + 1442374 * 2 ^ 59
def prefixEnd_1442374 : Nat := 4983230072969 + 3 ^ 40 * 1442374 * 2
def baseEnd_1442374 : Nat := 246877048516081646263883

theorem tailTrace_1442374 : CollatzResearch.WordTrace tailWord_1442374 prefixEnd_1442374 246877048516081646263883 := by
  unfold tailWord_1442374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1643990677391650334760943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35071801117688540474900117 1643990677391650334760943)
  ·
    refine ⟨2465986016087475502141415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1643990677391650334760943 2465986016087475502141415)
    ·
      refine ⟨3698979024131213253212123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2465986016087475502141415 3698979024131213253212123)
      ·
        refine ⟨5548468536196819879818185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3698979024131213253212123 5548468536196819879818185)
        ·
          refine ⟨4161351402147614909863639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5548468536196819879818185 4161351402147614909863639)
          ·
            refine ⟨6242027103221422364795459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4161351402147614909863639 6242027103221422364795459)
            ·
              refine ⟨9363040654832133547193189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6242027103221422364795459 9363040654832133547193189)
              ·
                refine ⟨1755570122781025040098723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9363040654832133547193189 1755570122781025040098723)
                ·
                  refine ⟨2633355184171537560148085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1755570122781025040098723 2633355184171537560148085)
                  ·
                    refine ⟨246877048516081646263883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2633355184171537560148085 246877048516081646263883)
                    ·
                      rfl

theorem cell23_1442374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_1442374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442374 prefixEnd_1442374 := by exact prefixLift 1442374
  have htrace : WordTrace (prefixWord ++ tailWord_1442374) baseStart_1442374 baseEnd_1442374 := by
    simpa [prefixWord, tailWord_1442374, baseEnd_1442374] using wordTrace_append hprefix tailTrace_1442374
  have hstable : (prefixWord ++ tailWord_1442374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442374).length < 2 ^ (prefixWord ++ tailWord_1442374).sum := by decide
  have hdescent : baseEnd_1442374 < baseStart_1442374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442443 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 3, 8]
def baseStart_1442443 : Nat := 118140960795 + 1442443 * 2 ^ 59
def prefixEnd_1442443 : Nat := 4983230072969 + 3 ^ 40 * 1442443 * 2
def baseEnd_1442443 : Nat := 246888858571135056276277

theorem tailTrace_1442443 : CollatzResearch.WordTrace tailWord_1442443 prefixEnd_1442443 246888858571135056276277 := by
  unfold tailWord_1442443
  simp only [CollatzResearch.WordTrace]
  refine ⟨52610218313282835496611983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35073478875521890331074655 52610218313282835496611983)
  ·
    refine ⟨78915327469924253244917975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52610218313282835496611983 78915327469924253244917975)
    ·
      refine ⟨118372991204886379867376963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78915327469924253244917975 118372991204886379867376963)
      ·
        refine ⟨177559486807329569801065445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118372991204886379867376963 177559486807329569801065445)
        ·
          refine ⟨33292403776374294337699771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177559486807329569801065445 33292403776374294337699771)
          ·
            refine ⟨49938605664561441506549657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33292403776374294337699771 49938605664561441506549657)
            ·
              refine ⟨37453954248421081129912243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49938605664561441506549657 37453954248421081129912243)
              ·
                refine ⟨56180931372631621694868365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37453954248421081129912243 56180931372631621694868365)
                ·
                  refine ⟨21067849264736858135575637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56180931372631621694868365 21067849264736858135575637)
                  ·
                    refine ⟨246888858571135056276277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21067849264736858135575637 246888858571135056276277)
                    ·
                      rfl

theorem cell23_1442443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 8].length) (baseStart_1442443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442443 prefixEnd_1442443 := by exact prefixLift 1442443
  have htrace : WordTrace (prefixWord ++ tailWord_1442443) baseStart_1442443 baseEnd_1442443 := by
    simpa [prefixWord, tailWord_1442443, baseEnd_1442443] using wordTrace_append hprefix tailTrace_1442443
  have hstable : (prefixWord ++ tailWord_1442443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442443).length < 2 ^ (prefixWord ++ tailWord_1442443).sum := by decide
  have hdescent : baseEnd_1442443 < baseStart_1442443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442477 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_1442477 : Nat := 118140960795 + 1442477 * 2 ^ 59
def prefixEnd_1442477 : Nat := 4983230072969 + 3 ^ 40 * 1442477 * 2
def baseEnd_1442477 : Nat := 246894678018552678601225

theorem tailTrace_1442477 : CollatzResearch.WordTrace tailWord_1442477 prefixEnd_1442477 246894678018552678601225 := by
  unfold tailWord_1442477
  simp only [CollatzResearch.WordTrace]
  refine ⟨52611458395159659303349685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35074305596773106202233123 52611458395159659303349685)
  ·
    refine ⟨4932324224546218059689033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52611458395159659303349685 4932324224546218059689033)
    ·
      refine ⟨3699243168409663544766775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4932324224546218059689033 3699243168409663544766775)
      ·
        refine ⟨5548864752614495317150163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3699243168409663544766775 5548864752614495317150163)
        ·
          refine ⟨8323297128921742975725245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5548864752614495317150163 8323297128921742975725245)
          ·
            refine ⟨3121236423345653615896967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8323297128921742975725245 3121236423345653615896967)
            ·
              refine ⟨4681854635018480423845451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3121236423345653615896967 4681854635018480423845451)
              ·
                refine ⟨7022781952527720635768177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4681854635018480423845451 7022781952527720635768177)
                ·
                  refine ⟨5267086464395790476826133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7022781952527720635768177 5267086464395790476826133)
                  ·
                    refine ⟨246894678018552678601225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5267086464395790476826133 246894678018552678601225)
                    ·
                      rfl

theorem cell23_1442477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_1442477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442477 prefixEnd_1442477 := by exact prefixLift 1442477
  have htrace : WordTrace (prefixWord ++ tailWord_1442477) baseStart_1442477 baseEnd_1442477 := by
    simpa [prefixWord, tailWord_1442477, baseEnd_1442477] using wordTrace_append hprefix tailTrace_1442477
  have hstable : (prefixWord ++ tailWord_1442477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442477).length < 2 ^ (prefixWord ++ tailWord_1442477).sum := by decide
  have hdescent : baseEnd_1442477 < baseStart_1442477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442490 : List Nat := [3, 1, 1, 1, 2, 3, 3, 2, 7]
def baseStart_1442490 : Nat := 118140960795 + 1442490 * 2 ^ 59
def prefixEnd_1442490 : Nat := 4983230072969 + 3 ^ 40 * 1442490 * 2
def baseEnd_1442490 : Nat := 82298967700462942771235

theorem tailTrace_1442490 : CollatzResearch.WordTrace tailWord_1442490 prefixEnd_1442490 82298967700462942771235 := by
  unfold tailWord_1442490
  simp only [CollatzResearch.WordTrace]
  refine ⟨13152983136028140630893231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35074621696075041682381949 13152983136028140630893231)
  ·
    refine ⟨19729474704042210946339847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13152983136028140630893231 19729474704042210946339847)
    ·
      refine ⟨29594212056063316419509771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19729474704042210946339847 29594212056063316419509771)
      ·
        refine ⟨44391318084094974629264657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29594212056063316419509771 44391318084094974629264657)
        ·
          refine ⟨33293488563071230971948493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44391318084094974629264657 33293488563071230971948493)
          ·
            refine ⟨12485058211151711614480685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33293488563071230971948493 12485058211151711614480685)
            ·
              refine ⟨4681896829181891855430257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12485058211151711614480685 4681896829181891855430257)
              ·
                refine ⟨3511422621886418891572693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4681896829181891855430257 3511422621886418891572693)
                ·
                  refine ⟨82298967700462942771235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3511422621886418891572693 82298967700462942771235)
                  ·
                    rfl

theorem cell23_1442490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 7].length) (baseStart_1442490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442490 prefixEnd_1442490 := by exact prefixLift 1442490
  have htrace : WordTrace (prefixWord ++ tailWord_1442490) baseStart_1442490 baseEnd_1442490 := by
    simpa [prefixWord, tailWord_1442490, baseEnd_1442490] using wordTrace_append hprefix tailTrace_1442490
  have hstable : (prefixWord ++ tailWord_1442490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442490).length < 2 ^ (prefixWord ++ tailWord_1442490).sum := by decide
  have hdescent : baseEnd_1442490 < baseStart_1442490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442524 : List Nat := [2, 2, 5, 1, 1, 2, 2, 1, 7]
def baseStart_1442524 : Nat := 118140960795 + 1442524 * 2 ^ 59
def prefixEnd_1442524 : Nat := 4983230072969 + 3 ^ 40 * 1442524 * 2
def baseEnd_1442524 : Nat := 82300907516268816879551

theorem tailTrace_1442524 : CollatzResearch.WordTrace tailWord_1442524 prefixEnd_1442524 82300907516268816879551 := by
  unfold tailWord_1442524
  simp only [CollatzResearch.WordTrace]
  refine ⟨26306586312994693165155313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35075448417326257553540417 26306586312994693165155313)
  ·
    refine ⟨19729939734746019873866485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26306586312994693165155313 19729939734746019873866485)
    ·
      refine ⟨1849681850132439363174983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19729939734746019873866485 1849681850132439363174983)
      ·
        refine ⟨2774522775198659044762475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1849681850132439363174983 2774522775198659044762475)
        ·
          refine ⟨4161784162797988567143713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2774522775198659044762475 4161784162797988567143713)
          ·
            refine ⟨3121338122098491425357785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4161784162797988567143713 3121338122098491425357785)
            ·
              refine ⟨2341003591573868569018339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3121338122098491425357785 2341003591573868569018339)
              ·
                refine ⟨3511505387360802853527509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2341003591573868569018339 3511505387360802853527509)
                ·
                  refine ⟨82300907516268816879551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3511505387360802853527509 82300907516268816879551)
                  ·
                    rfl

theorem cell23_1442524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 7].length) (baseStart_1442524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442524 prefixEnd_1442524 := by exact prefixLift 1442524
  have htrace : WordTrace (prefixWord ++ tailWord_1442524) baseStart_1442524 baseEnd_1442524 := by
    simpa [prefixWord, tailWord_1442524, baseEnd_1442524] using wordTrace_append hprefix tailTrace_1442524
  have hstable : (prefixWord ++ tailWord_1442524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442524).length < 2 ^ (prefixWord ++ tailWord_1442524).sum := by decide
  have hdescent : baseEnd_1442524 < baseStart_1442524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442557 : List Nat := [1, 4, 1, 1, 1, 1, 4, 3, 2, 1, 4]
def baseStart_1442557 : Nat := 118140960795 + 1442557 * 2 ^ 59
def prefixEnd_1442557 : Nat := 4983230072969 + 3 ^ 40 * 1442557 * 2
def baseEnd_1442557 : Nat := 740725112508017722803307

theorem tailTrace_1442557 : CollatzResearch.WordTrace tailWord_1442557 prefixEnd_1442557 740725112508017722803307 := by
  unfold tailWord_1442557
  simp only [CollatzResearch.WordTrace]
  refine ⟨52614376234869832966261925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35076250823246555310841283 52614376234869832966261925)
  ·
    refine ⟨9865195544038093681174111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52614376234869832966261925 9865195544038093681174111)
    ·
      refine ⟨14797793316057140521761167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9865195544038093681174111 14797793316057140521761167)
      ·
        refine ⟨22196689974085710782641751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14797793316057140521761167 22196689974085710782641751)
        ·
          refine ⟨33295034961128566173962627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22196689974085710782641751 33295034961128566173962627)
          ·
            refine ⟨49942552441692849260943941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33295034961128566173962627 49942552441692849260943941)
            ·
              refine ⟨9364228582817409236426989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49942552441692849260943941 9364228582817409236426989)
              ·
                refine ⟨3511585718556528463660121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9364228582817409236426989 3511585718556528463660121)
                ·
                  refine ⟨2633689288917396347745091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3511585718556528463660121 2633689288917396347745091)
                  ·
                    refine ⟨3950533933376094521617637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2633689288917396347745091 3950533933376094521617637)
                    ·
                      refine ⟨740725112508017722803307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3950533933376094521617637 740725112508017722803307)
                      ·
                        rfl

theorem cell23_1442557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_1442557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442557 prefixEnd_1442557 := by exact prefixLift 1442557
  have htrace : WordTrace (prefixWord ++ tailWord_1442557) baseStart_1442557 baseEnd_1442557 := by
    simpa [prefixWord, tailWord_1442557, baseEnd_1442557] using wordTrace_append hprefix tailTrace_1442557
  have hstable : (prefixWord ++ tailWord_1442557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442557).length < 2 ^ (prefixWord ++ tailWord_1442557).sum := by decide
  have hdescent : baseEnd_1442557 < baseStart_1442557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442577 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 3]
def baseStart_1442577 : Nat := 118140960795 + 1442577 * 2 ^ 59
def prefixEnd_1442577 : Nat := 4983230072969 + 3 ^ 40 * 1442577 * 2
def baseEnd_1442577 : Nat := 740735382121107644553215

theorem tailTrace_1442577 : CollatzResearch.WordTrace tailWord_1442577 prefixEnd_1442577 740735382121107644553215 := by
  unfold tailWord_1442577
  simp only [CollatzResearch.WordTrace]
  refine ⟨52615105694797376381989985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35076737129864917587993323 52615105694797376381989985)
  ·
    refine ⟨39461329271098032286492489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52615105694797376381989985 39461329271098032286492489)
    ·
      refine ⟨29595996953323524214869367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39461329271098032286492489 29595996953323524214869367)
      ·
        refine ⟨44393995429985286322304051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29595996953323524214869367 44393995429985286322304051)
        ·
          refine ⟨66590993144977929483456077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44393995429985286322304051 66590993144977929483456077)
          ·
            refine ⟨24971622429366723556296029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66590993144977929483456077 24971622429366723556296029)
            ·
              refine ⟨9364358411012521333611011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24971622429366723556296029 9364358411012521333611011)
              ·
                refine ⟨14046537616518782000416517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9364358411012521333611011 14046537616518782000416517)
                ·
                  refine ⟨2633725803097271625078097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14046537616518782000416517 2633725803097271625078097)
                  ·
                    refine ⟨1975294352322953718808573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2633725803097271625078097 1975294352322953718808573)
                    ·
                      refine ⟨740735382121107644553215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1975294352322953718808573 740735382121107644553215)
                      ·
                        rfl

theorem cell23_1442577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_1442577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442577 prefixEnd_1442577 := by exact prefixLift 1442577
  have htrace : WordTrace (prefixWord ++ tailWord_1442577) baseStart_1442577 baseEnd_1442577 := by
    simpa [prefixWord, tailWord_1442577, baseEnd_1442577] using wordTrace_append hprefix tailTrace_1442577
  have hstable : (prefixWord ++ tailWord_1442577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442577).length < 2 ^ (prefixWord ++ tailWord_1442577).sum := by decide
  have hdescent : baseEnd_1442577 < baseStart_1442577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442597 : List Nat := [1, 3, 1, 2, 3, 1, 3, 3, 6]
def baseStart_1442597 : Nat := 118140960795 + 1442597 * 2 ^ 59
def prefixEnd_1442597 : Nat := 4983230072969 + 3 ^ 40 * 1442597 * 2
def baseEnd_1442597 : Nat := 82305072414910840700347

theorem tailTrace_1442597 : CollatzResearch.WordTrace tailWord_1442597 prefixEnd_1442597 82305072414910840700347 := by
  unfold tailWord_1442597
  simp only [CollatzResearch.WordTrace]
  refine ⟨52615835154724919797718045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35077223436483279865145363 52615835154724919797718045)
  ·
    refine ⟨19730938183021844924144267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52615835154724919797718045 19730938183021844924144267)
    ·
      refine ⟨29596407274532767386216401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19730938183021844924144267 29596407274532767386216401)
      ·
        refine ⟨22197305455899575539662301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29596407274532767386216401 22197305455899575539662301)
        ·
          refine ⟨8323989545962340827373363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22197305455899575539662301 8323989545962340827373363)
          ·
            refine ⟨12485984318943511241060045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8323989545962340827373363 12485984318943511241060045)
            ·
              refine ⟨4682244119603816715397517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12485984318943511241060045 4682244119603816715397517)
              ·
                refine ⟨1755841544851431268274069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4682244119603816715397517 1755841544851431268274069)
                ·
                  refine ⟨82305072414910840700347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1755841544851431268274069 82305072414910840700347)
                  ·
                    rfl

theorem cell23_1442597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 6].length) (baseStart_1442597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442597 prefixEnd_1442597 := by exact prefixLift 1442597
  have htrace : WordTrace (prefixWord ++ tailWord_1442597) baseStart_1442597 baseEnd_1442597 := by
    simpa [prefixWord, tailWord_1442597, baseEnd_1442597] using wordTrace_append hprefix tailTrace_1442597
  have hstable : (prefixWord ++ tailWord_1442597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442597).length < 2 ^ (prefixWord ++ tailWord_1442597).sum := by decide
  have hdescent : baseEnd_1442597 < baseStart_1442597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442634 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 4, 3, 2]
def baseStart_1442634 : Nat := 118140960795 + 1442634 * 2 ^ 59
def prefixEnd_1442634 : Nat := 4983230072969 + 3 ^ 40 * 1442634 * 2
def baseEnd_1442634 : Nat := 740764650518413921540453

theorem tailTrace_1442634 : CollatzResearch.WordTrace tailWord_1442634 prefixEnd_1442634 740764650518413921540453 := by
  unfold tailWord_1442634
  simp only [CollatzResearch.WordTrace]
  refine ⟨13154296163897718779203739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35078123103727250077876637 13154296163897718779203739)
  ·
    refine ⟨19731444245846578168805609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13154296163897718779203739 19731444245846578168805609)
    ·
      refine ⟨14798583184384933626604207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19731444245846578168805609 14798583184384933626604207)
      ·
        refine ⟨22197874776577400439906311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14798583184384933626604207 22197874776577400439906311)
        ·
          refine ⟨33296812164866100659859467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22197874776577400439906311 33296812164866100659859467)
          ·
            refine ⟨49945218247299150989789201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33296812164866100659859467 49945218247299150989789201)
            ·
              refine ⟨37458913685474363242341901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49945218247299150989789201 37458913685474363242341901)
              ·
                refine ⟨14047092632052886215878213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37458913685474363242341901 14047092632052886215878213)
                ·
                  refine ⟨2633829868509916165477165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14047092632052886215878213 2633829868509916165477165)
                  ·
                    refine ⟨987686200691218562053937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2633829868509916165477165 987686200691218562053937)
                    ·
                      refine ⟨740764650518413921540453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 987686200691218562053937 740764650518413921540453)
                      ·
                        rfl

theorem cell23_1442634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_1442634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442634 prefixEnd_1442634 := by exact prefixLift 1442634
  have htrace : WordTrace (prefixWord ++ tailWord_1442634) baseStart_1442634 baseEnd_1442634 := by
    simpa [prefixWord, tailWord_1442634, baseEnd_1442634] using wordTrace_append hprefix tailTrace_1442634
  have hstable : (prefixWord ++ tailWord_1442634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442634).length < 2 ^ (prefixWord ++ tailWord_1442634).sum := by decide
  have hdescent : baseEnd_1442634 < baseStart_1442634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442658 : List Nat := [3, 3, 2, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_1442658 : Nat := 118140960795 + 1442658 * 2 ^ 59
def prefixEnd_1442658 : Nat := 4983230072969 + 3 ^ 40 * 1442658 * 2
def baseEnd_1442658 : Nat := 740776974054121827640343

theorem tailTrace_1442658 : CollatzResearch.WordTrace tailWord_1442658 prefixEnd_1442658 740776974054121827640343 := by
  unfold tailWord_1442658
  simp only [CollatzResearch.WordTrace]
  refine ⟨13154515001875981803922157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35078706671669284810459085 13154515001875981803922157)
  ·
    refine ⟨4932943125703493176470809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13154515001875981803922157 4932943125703493176470809)
    ·
      refine ⟨3699707344277619882353107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4932943125703493176470809 3699707344277619882353107)
      ·
        refine ⟨5549561016416429823529661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3699707344277619882353107 5549561016416429823529661)
        ·
          refine ⟨2081085381156161183823623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5549561016416429823529661 2081085381156161183823623)
          ·
            refine ⟨3121628071734241775735435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2081085381156161183823623 3121628071734241775735435)
            ·
              refine ⟨4682442107601362663603153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3121628071734241775735435 4682442107601362663603153)
              ·
                refine ⟨3511831580701021997702365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4682442107601362663603153 3511831580701021997702365)
                ·
                  refine ⟨1316936842762883249138387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3511831580701021997702365 1316936842762883249138387)
                  ·
                    refine ⟨1975405264144324873707581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1316936842762883249138387 1975405264144324873707581)
                    ·
                      refine ⟨740776974054121827640343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1975405264144324873707581 740776974054121827640343)
                      ·
                        rfl

theorem cell23_1442658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_1442658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442658 prefixEnd_1442658 := by exact prefixLift 1442658
  have htrace : WordTrace (prefixWord ++ tailWord_1442658) baseStart_1442658 baseEnd_1442658 := by
    simpa [prefixWord, tailWord_1442658, baseEnd_1442658] using wordTrace_append hprefix tailTrace_1442658
  have hstable : (prefixWord ++ tailWord_1442658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442658).length < 2 ^ (prefixWord ++ tailWord_1442658).sum := by decide
  have hdescent : baseEnd_1442658 < baseStart_1442658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442664 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_1442664 : Nat := 118140960795 + 1442664 * 2 ^ 59
def prefixEnd_1442664 : Nat := 4983230072969 + 3 ^ 40 * 1442664 * 2
def baseEnd_1442664 : Nat := 740780054938048804165315

theorem tailTrace_1442664 : CollatzResearch.WordTrace tailWord_1442664 prefixEnd_1442664 740780054938048804165315 := by
  unfold tailWord_1442664
  simp only [CollatzResearch.WordTrace]
  refine ⟨26309139422741095120203523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35078852563654793493604697 26309139422741095120203523)
  ·
    refine ⟨39463709134111642680305285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26309139422741095120203523 39463709134111642680305285)
    ·
      refine ⟨7399445462645933002557241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39463709134111642680305285 7399445462645933002557241)
      ·
        refine ⟨5549584096984449751917931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7399445462645933002557241 5549584096984449751917931)
        ·
          refine ⟨8324376145476674627876897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5549584096984449751917931 8324376145476674627876897)
          ·
            refine ⟨6243282109107505970907673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8324376145476674627876897 6243282109107505970907673)
            ·
              refine ⟨4682461581830629478180755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6243282109107505970907673 4682461581830629478180755)
              ·
                refine ⟨7023692372745944217271133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4682461581830629478180755 7023692372745944217271133)
                ·
                  refine ⟨2633884639779729081476675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7023692372745944217271133 2633884639779729081476675)
                  ·
                    refine ⟨3950826959669593622215013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2633884639779729081476675 3950826959669593622215013)
                    ·
                      refine ⟨740780054938048804165315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3950826959669593622215013 740780054938048804165315)
                      ·
                        rfl

theorem cell23_1442664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_1442664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442664 prefixEnd_1442664 := by exact prefixLift 1442664
  have htrace : WordTrace (prefixWord ++ tailWord_1442664) baseStart_1442664 baseEnd_1442664 := by
    simpa [prefixWord, tailWord_1442664, baseEnd_1442664] using wordTrace_append hprefix tailTrace_1442664
  have hstable : (prefixWord ++ tailWord_1442664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442664).length < 2 ^ (prefixWord ++ tailWord_1442664).sum := by decide
  have hdescent : baseEnd_1442664 < baseStart_1442664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442678 : List Nat := [5, 1, 1, 3, 1, 1, 4, 1, 1, 5]
def baseStart_1442678 : Nat := 118140960795 + 1442678 * 2 ^ 59
def prefixEnd_1442678 : Nat := 4983230072969 + 3 ^ 40 * 1442678 * 2
def baseEnd_1442678 : Nat := 246929081222403916463417

theorem tailTrace_1442678 : CollatzResearch.WordTrace tailWord_1442678 prefixEnd_1442678 246929081222403916463417 := by
  unfold tailWord_1442678
  simp only [CollatzResearch.WordTrace]
  refine ⟨3288674341714466914463543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35079192978287647087611125 3288674341714466914463543)
  ·
    refine ⟨4933011512571700371695315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3288674341714466914463543 4933011512571700371695315)
    ·
      refine ⟨7399517268857550557542973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4933011512571700371695315 7399517268857550557542973)
      ·
        refine ⟨2774818975821581459078615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7399517268857550557542973 2774818975821581459078615)
        ·
          refine ⟨4162228463732372188617923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2774818975821581459078615 4162228463732372188617923)
          ·
            refine ⟨6243342695598558282926885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4162228463732372188617923 6243342695598558282926885)
            ·
              refine ⟨1170626755424729678048791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6243342695598558282926885 1170626755424729678048791)
              ·
                refine ⟨1755940133137094517073187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1170626755424729678048791 1755940133137094517073187)
                ·
                  refine ⟨2633910199705641775609781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1755940133137094517073187 2633910199705641775609781)
                  ·
                    refine ⟨246929081222403916463417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2633910199705641775609781 246929081222403916463417)
                    ·
                      rfl

theorem cell23_1442678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_1442678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442678 prefixEnd_1442678 := by exact prefixLift 1442678
  have htrace : WordTrace (prefixWord ++ tailWord_1442678) baseStart_1442678 baseEnd_1442678 := by
    simpa [prefixWord, tailWord_1442678, baseEnd_1442678] using wordTrace_append hprefix tailTrace_1442678
  have hstable : (prefixWord ++ tailWord_1442678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442678).length < 2 ^ (prefixWord ++ tailWord_1442678).sum := by decide
  have hdescent : baseEnd_1442678 < baseStart_1442678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442681 : List Nat := [1, 2, 1, 3, 2, 3, 4, 1, 1, 1, 4]
def baseStart_1442681 : Nat := 118140960795 + 1442681 * 2 ^ 59
def prefixEnd_1442681 : Nat := 4983230072969 + 3 ^ 40 * 1442681 * 2
def baseEnd_1442681 : Nat := 740788784109175237652737

theorem tailTrace_1442681 : CollatzResearch.WordTrace tailWord_1442681 prefixEnd_1442681 740788784109175237652737 := by
  unfold tailWord_1442681
  simp only [CollatzResearch.WordTrace]
  refine ⟨52618898886420602143775897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35079265924280401429183931 52618898886420602143775897)
  ·
    refine ⟨39464174164815451607831923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52618898886420602143775897 39464174164815451607831923)
    ·
      refine ⟨59196261247223177411747885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39464174164815451607831923 59196261247223177411747885)
      ·
        refine ⟨22198597967708691529405457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59196261247223177411747885 22198597967708691529405457)
        ·
          refine ⟨16648948475781518647054093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22198597967708691529405457 16648948475781518647054093)
          ·
            refine ⟨6243355678418069492645285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16648948475781518647054093 6243355678418069492645285)
            ·
              refine ⟨1170629189703388029870991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6243355678418069492645285 1170629189703388029870991)
              ·
                refine ⟨1755943784555082044806487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1170629189703388029870991 1755943784555082044806487)
                ·
                  refine ⟨2633915676832623067209731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1755943784555082044806487 2633915676832623067209731)
                  ·
                    refine ⟨3950873515248934600814597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2633915676832623067209731 3950873515248934600814597)
                    ·
                      refine ⟨740788784109175237652737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3950873515248934600814597 740788784109175237652737)
                      ·
                        rfl

theorem cell23_1442681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_1442681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442681 prefixEnd_1442681 := by exact prefixLift 1442681
  have htrace : WordTrace (prefixWord ++ tailWord_1442681) baseStart_1442681 baseEnd_1442681 := by
    simpa [prefixWord, tailWord_1442681, baseEnd_1442681] using wordTrace_append hprefix tailTrace_1442681
  have hstable : (prefixWord ++ tailWord_1442681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442681).length < 2 ^ (prefixWord ++ tailWord_1442681).sum := by decide
  have hdescent : baseEnd_1442681 < baseStart_1442681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442698 : List Nat := [3, 1, 2, 4, 1, 1, 1, 3, 3, 2, 2]
def baseStart_1442698 : Nat := 118140960795 + 1442698 * 2 ^ 59
def prefixEnd_1442698 : Nat := 4983230072969 + 3 ^ 40 * 1442698 * 2
def baseEnd_1442698 : Nat := 740797513280301671140159

theorem tailTrace_1442698 : CollatzResearch.WordTrace tailWord_1442698 prefixEnd_1442698 740797513280301671140159 := by
  unfold tailWord_1442698
  simp only [CollatzResearch.WordTrace]
  refine ⟨13154879731839753511786187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35079679284906009364763165 13154879731839753511786187)
  ·
    refine ⟨19732319597759630267679281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13154879731839753511786187 19732319597759630267679281)
    ·
      refine ⟨14799239698319722700759461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19732319597759630267679281 14799239698319722700759461)
      ·
        refine ⟨2774857443434948006392399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14799239698319722700759461 2774857443434948006392399)
        ·
          refine ⟨4162286165152422009588599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2774857443434948006392399 4162286165152422009588599)
          ·
            refine ⟨6243429247728633014382899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4162286165152422009588599 6243429247728633014382899)
            ·
              refine ⟨9365143871592949521574349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6243429247728633014382899 9365143871592949521574349)
              ·
                refine ⟨3511928951847356070590381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9365143871592949521574349 3511928951847356070590381)
                ·
                  refine ⟨1316973356942758526471393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3511928951847356070590381 1316973356942758526471393)
                  ·
                    refine ⟨987730017707068894853545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1316973356942758526471393 987730017707068894853545)
                    ·
                      refine ⟨740797513280301671140159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 987730017707068894853545 740797513280301671140159)
                      ·
                        rfl

theorem cell23_1442698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_1442698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442698 prefixEnd_1442698 := by exact prefixLift 1442698
  have htrace : WordTrace (prefixWord ++ tailWord_1442698) baseStart_1442698 baseEnd_1442698 := by
    simpa [prefixWord, tailWord_1442698, baseEnd_1442698] using wordTrace_append hprefix tailTrace_1442698
  have hstable : (prefixWord ++ tailWord_1442698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442698).length < 2 ^ (prefixWord ++ tailWord_1442698).sum := by decide
  have hdescent : baseEnd_1442698 < baseStart_1442698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442708 : List Nat := [2, 4, 2, 1, 1, 1, 5, 1, 2, 4]
def baseStart_1442708 : Nat := 118140960795 + 1442708 * 2 ^ 59
def prefixEnd_1442708 : Nat := 4983230072969 + 3 ^ 40 * 1442708 * 2
def baseEnd_1442708 : Nat := 246934216028948877338371

theorem tailTrace_1442708 : CollatzResearch.WordTrace tailWord_1442708 prefixEnd_1442708 246934216028948877338371 := by
  unfold tailWord_1442708
  simp only [CollatzResearch.WordTrace]
  refine ⟨26309941828661392877504389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35079922438215190503339185 26309941828661392877504389)
  ·
    refine ⟨4933114092874011164532073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26309941828661392877504389 4933114092874011164532073)
    ·
      refine ⟨3699835569655508373399055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4933114092874011164532073 3699835569655508373399055)
      ·
        refine ⟨5549753354483262560098583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3699835569655508373399055 5549753354483262560098583)
        ·
          refine ⟨8324630031724893840147875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5549753354483262560098583 8324630031724893840147875)
          ·
            refine ⟨12486945047587340760221813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8324630031724893840147875 12486945047587340760221813)
            ·
              refine ⟨1170651098211313196270795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12486945047587340760221813 1170651098211313196270795)
              ·
                refine ⟨1755976647316969794406193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1170651098211313196270795 1755976647316969794406193)
                ·
                  refine ⟨1316982485487727345804645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1755976647316969794406193 1316982485487727345804645)
                  ·
                    refine ⟨246934216028948877338371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1316982485487727345804645 246934216028948877338371)
                    ·
                      rfl

theorem cell23_1442708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_1442708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442708 prefixEnd_1442708 := by exact prefixLift 1442708
  have htrace : WordTrace (prefixWord ++ tailWord_1442708) baseStart_1442708 baseEnd_1442708 := by
    simpa [prefixWord, tailWord_1442708, baseEnd_1442708] using wordTrace_append hprefix tailTrace_1442708
  have hstable : (prefixWord ++ tailWord_1442708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442708).length < 2 ^ (prefixWord ++ tailWord_1442708).sum := by decide
  have hdescent : baseEnd_1442708 < baseStart_1442708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442721 : List Nat := [1, 2, 3, 4, 1, 3, 2, 7]
def baseStart_1442721 : Nat := 118140960795 + 1442721 * 2 ^ 59
def prefixEnd_1442721 : Nat := 4983230072969 + 3 ^ 40 * 1442721 * 2
def baseEnd_1442721 : Nat := 27437382345753891894539

theorem tailTrace_1442721 : CollatzResearch.WordTrace tailWord_1442721 prefixEnd_1442721 27437382345753891894539 := by
  unfold tailWord_1442721
  simp only [CollatzResearch.WordTrace]
  refine ⟨52620357806275688975232017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35080238537517125983488011 52620357806275688975232017)
  ·
    refine ⟨39465268354706766731424013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52620357806275688975232017 39465268354706766731424013)
    ·
      refine ⟨14799475633015037524284005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39465268354706766731424013 14799475633015037524284005)
      ·
        refine ⟨2774901681190319535803251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14799475633015037524284005 2774901681190319535803251)
        ·
          refine ⟨4162352521785479303704877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2774901681190319535803251 4162352521785479303704877)
          ·
            refine ⟨1560882195669554738889329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4162352521785479303704877 1560882195669554738889329)
            ·
              refine ⟨1170661646752166054166997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1560882195669554738889329 1170661646752166054166997)
              ·
                refine ⟨27437382345753891894539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1170661646752166054166997 27437382345753891894539)
                ·
                  rfl

theorem cell23_1442721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 7].length) (baseStart_1442721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442721 prefixEnd_1442721 := by exact prefixLift 1442721
  have htrace : WordTrace (prefixWord ++ tailWord_1442721) baseStart_1442721 baseEnd_1442721 := by
    simpa [prefixWord, tailWord_1442721, baseEnd_1442721] using wordTrace_append hprefix tailTrace_1442721
  have hstable : (prefixWord ++ tailWord_1442721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442721).length < 2 ^ (prefixWord ++ tailWord_1442721).sum := by decide
  have hdescent : baseEnd_1442721 < baseStart_1442721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442922 : List Nat := [3, 1, 3, 2, 2, 2, 3, 2, 1, 4]
def baseStart_1442922 : Nat := 118140960795 + 1442922 * 2 ^ 59
def prefixEnd_1442922 : Nat := 4983230072969 + 3 ^ 40 * 1442922 * 2
def baseEnd_1442922 : Nat := 246970844315636264913043

theorem tailTrace_1442922 : CollatzResearch.WordTrace tailWord_1442922 prefixEnd_1442922 246970844315636264913043 := by
  unfold tailWord_1442922
  simp only [CollatzResearch.WordTrace]
  refine ⟨13156922219636875075824755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35085125919031666868866013 13156922219636875075824755)
  ·
    refine ⟨19735383329455312613737133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13156922219636875075824755 19735383329455312613737133)
    ·
      refine ⟨7400768748545742230151425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19735383329455312613737133 7400768748545742230151425)
      ·
        refine ⟨5550576561409306672613569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7400768748545742230151425 5550576561409306672613569)
        ·
          refine ⟨4162932421056980004460177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5550576561409306672613569 4162932421056980004460177)
          ·
            refine ⟨3122199315792735003345133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4162932421056980004460177 3122199315792735003345133)
            ·
              refine ⟨1170824743422275626254425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3122199315792735003345133 1170824743422275626254425)
              ·
                refine ⟨878118557566706719690819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1170824743422275626254425 878118557566706719690819)
                ·
                  refine ⟨1317177836350060079536229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 878118557566706719690819 1317177836350060079536229)
                  ·
                    refine ⟨246970844315636264913043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1317177836350060079536229 246970844315636264913043)
                    ·
                      rfl

theorem cell23_1442922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_1442922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442922 prefixEnd_1442922 := by exact prefixLift 1442922
  have htrace : WordTrace (prefixWord ++ tailWord_1442922) baseStart_1442922 baseEnd_1442922 := by
    simpa [prefixWord, tailWord_1442922, baseEnd_1442922] using wordTrace_append hprefix tailTrace_1442922
  have hstable : (prefixWord ++ tailWord_1442922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442922).length < 2 ^ (prefixWord ++ tailWord_1442922).sum := by decide
  have hdescent : baseEnd_1442922 < baseStart_1442922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1442948 : List Nat := [2, 3, 2, 1, 2, 2, 3, 2, 1, 5]
def baseStart_1442948 : Nat := 118140960795 + 1442948 * 2 ^ 59
def prefixEnd_1442948 : Nat := 4983230072969 + 3 ^ 40 * 1442948 * 2
def baseEnd_1442948 : Nat := 246975294481308564338003

theorem tailTrace_1442948 : CollatzResearch.WordTrace tailWord_1442948 prefixEnd_1442948 246975294481308564338003 := by
  unfold tailWord_1442948
  simp only [CollatzResearch.WordTrace]
  refine ⟨26314318588226653371872749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35085758117635537829163665 26314318588226653371872749)
  ·
    refine ⟨9867869470584995014452281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26314318588226653371872749 9867869470584995014452281)
    ·
      refine ⟨7400902102938746260839211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9867869470584995014452281 7400902102938746260839211)
      ·
        refine ⟨11101353154408119391258817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7400902102938746260839211 11101353154408119391258817)
        ·
          refine ⟨8326014865806089543444113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11101353154408119391258817 8326014865806089543444113)
          ·
            refine ⟨6244511149354567157583085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8326014865806089543444113 6244511149354567157583085)
            ·
              refine ⟨2341691681007962684093657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6244511149354567157583085 2341691681007962684093657)
              ·
                refine ⟨1756268760755972013070243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2341691681007962684093657 1756268760755972013070243)
                ·
                  refine ⟨2634403141133958019605365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1756268760755972013070243 2634403141133958019605365)
                  ·
                    refine ⟨246975294481308564338003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2634403141133958019605365 246975294481308564338003)
                    ·
                      rfl

theorem cell23_1442948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_1442948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1442948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1442948 prefixEnd_1442948 := by exact prefixLift 1442948
  have htrace : WordTrace (prefixWord ++ tailWord_1442948) baseStart_1442948 baseEnd_1442948 := by
    simpa [prefixWord, tailWord_1442948, baseEnd_1442948] using wordTrace_append hprefix tailTrace_1442948
  have hstable : (prefixWord ++ tailWord_1442948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1442948).length < 2 ^ (prefixWord ++ tailWord_1442948).sum := by decide
  have hdescent : baseEnd_1442948 < baseStart_1442948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1442948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443008 : List Nat := [2, 1, 1, 2, 6, 1, 3, 7]
def baseStart_1443008 : Nat := 118140960795 + 1443008 * 2 ^ 59
def prefixEnd_1443008 : Nat := 4983230072969 + 3 ^ 40 * 1443008 * 2
def baseEnd_1443008 : Nat := 27442840454933165120879

theorem tailTrace_1443008 : CollatzResearch.WordTrace tailWord_1443008 prefixEnd_1443008 27442840454933165120879 := by
  unfold tailWord_1443008
  simp only [CollatzResearch.WordTrace]
  refine ⟨26315412778117968495464839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35087217037490624660619785 26315412778117968495464839)
  ·
    refine ⟨39473119167176952743197259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26315412778117968495464839 39473119167176952743197259)
    ·
      refine ⟨59209678750765429114795889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39473119167176952743197259 59209678750765429114795889)
      ·
        refine ⟨44407259063074071836096917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59209678750765429114795889 44407259063074071836096917)
        ·
          refine ⟨2081590268581597117317043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44407259063074071836096917 2081590268581597117317043)
          ·
            refine ⟨3122385402872395675975565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2081590268581597117317043 3122385402872395675975565)
            ·
              refine ⟨1170894526077148378490837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3122385402872395675975565 1170894526077148378490837)
              ·
                refine ⟨27442840454933165120879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1170894526077148378490837 27442840454933165120879)
                ·
                  rfl

theorem cell23_1443008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 7].length) (baseStart_1443008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443008 prefixEnd_1443008 := by exact prefixLift 1443008
  have htrace : WordTrace (prefixWord ++ tailWord_1443008) baseStart_1443008 baseEnd_1443008 := by
    simpa [prefixWord, tailWord_1443008, baseEnd_1443008] using wordTrace_append hprefix tailTrace_1443008
  have hstable : (prefixWord ++ tailWord_1443008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443008).length < 2 ^ (prefixWord ++ tailWord_1443008).sum := by decide
  have hdescent : baseEnd_1443008 < baseStart_1443008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443018 : List Nat := [3, 1, 2, 1, 3, 2, 2, 2, 1, 3, 3]
def baseStart_1443018 : Nat := 118140960795 + 1443018 * 2 ^ 59
def prefixEnd_1443018 : Nat := 4983230072969 + 3 ^ 40 * 1443018 * 2
def baseEnd_1443018 : Nat := 740961827089740419138687

theorem tailTrace_1443018 : CollatzResearch.WordTrace tailWord_1443018 prefixEnd_1443018 740961827089740419138687 := by
  unfold tailWord_1443018
  simp only [CollatzResearch.WordTrace]
  refine ⟨13157797571549927174698427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35087460190799805799195805 13157797571549927174698427)
  ·
    refine ⟨19736696357324890762047641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13157797571549927174698427 19736696357324890762047641)
    ·
      refine ⟨14802522267993668071535731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19736696357324890762047641 14802522267993668071535731)
      ·
        refine ⟨22203783401990502107303597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14802522267993668071535731 22203783401990502107303597)
        ·
          refine ⟨8326418775746438290238849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22203783401990502107303597 8326418775746438290238849)
          ·
            refine ⟨6244814081809828717679137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8326418775746438290238849 6244814081809828717679137)
            ·
              refine ⟨4683610561357371538259353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6244814081809828717679137 4683610561357371538259353)
              ·
                refine ⟨3512707921018028653694515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4683610561357371538259353 3512707921018028653694515)
                ·
                  refine ⟨5269061881527042980541773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3512707921018028653694515 5269061881527042980541773)
                  ·
                    refine ⟨1975898205572641117703165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5269061881527042980541773 1975898205572641117703165)
                    ·
                      refine ⟨740961827089740419138687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1975898205572641117703165 740961827089740419138687)
                      ·
                        rfl

theorem cell23_1443018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_1443018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443018 prefixEnd_1443018 := by exact prefixLift 1443018
  have htrace : WordTrace (prefixWord ++ tailWord_1443018) baseStart_1443018 baseEnd_1443018 := by
    simpa [prefixWord, tailWord_1443018, baseEnd_1443018] using wordTrace_append hprefix tailTrace_1443018
  have hstable : (prefixWord ++ tailWord_1443018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443018).length < 2 ^ (prefixWord ++ tailWord_1443018).sum := by decide
  have hdescent : baseEnd_1443018 < baseStart_1443018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443051 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 2, 6]
def baseStart_1443051 : Nat := 118140960795 + 1443051 * 2 ^ 59
def prefixEnd_1443051 : Nat := 4983230072969 + 3 ^ 40 * 1443051 * 2
def baseEnd_1443051 : Nat := 246992923983779596675345

theorem tailTrace_1443051 : CollatzResearch.WordTrace tailWord_1443051 prefixEnd_1443051 246992923983779596675345 := by
  unfold tailWord_1443051
  simp only [CollatzResearch.WordTrace]
  refine ⟨52632393895080155334745007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35088262596720103556496671 52632393895080155334745007)
  ·
    refine ⟨78948590842620233002117511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52632393895080155334745007 78948590842620233002117511)
    ·
      refine ⟨118422886263930349503176267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78948590842620233002117511 118422886263930349503176267)
      ·
        refine ⟨177634329395895524254764401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118422886263930349503176267 177634329395895524254764401)
        ·
          refine ⟨133225747046921643191073301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177634329395895524254764401 133225747046921643191073301)
          ·
            refine ⟨6244956892824452024581561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 133225747046921643191073301 6244956892824452024581561)
            ·
              refine ⟨4683717669618339018436171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6244956892824452024581561 4683717669618339018436171)
              ·
                refine ⟨7025576504427508527654257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4683717669618339018436171 7025576504427508527654257)
                ·
                  refine ⟨5269182378320631395740693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7025576504427508527654257 5269182378320631395740693)
                  ·
                    refine ⟨246992923983779596675345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5269182378320631395740693 246992923983779596675345)
                    ·
                      rfl

theorem cell23_1443051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 6].length) (baseStart_1443051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443051 prefixEnd_1443051 := by exact prefixLift 1443051
  have htrace : WordTrace (prefixWord ++ tailWord_1443051) baseStart_1443051 baseEnd_1443051 := by
    simpa [prefixWord, tailWord_1443051, baseEnd_1443051] using wordTrace_append hprefix tailTrace_1443051
  have hstable : (prefixWord ++ tailWord_1443051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443051).length < 2 ^ (prefixWord ++ tailWord_1443051).sum := by decide
  have hdescent : baseEnd_1443051 < baseStart_1443051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443052 : List Nat := [2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 3]
def baseStart_1443052 : Nat := 118140960795 + 1443052 * 2 ^ 59
def prefixEnd_1443052 : Nat := 4983230072969 + 3 ^ 40 * 1443052 * 2
def baseEnd_1443052 : Nat := 740979285431993286113531

theorem tailTrace_1443052 : CollatzResearch.WordTrace tailWord_1443052 prefixEnd_1443052 740979285431993286113531 := by
  unfold tailWord_1443052
  simp only [CollatzResearch.WordTrace]
  refine ⟨26316215184038266252765705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35088286912051021670354273 26316215184038266252765705)
  ·
    refine ⟨19737161388028699689574279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26316215184038266252765705 19737161388028699689574279)
    ·
      refine ⟨29605742082043049534361419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19737161388028699689574279 29605742082043049534361419)
      ·
        refine ⟨44408613123064574301542129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29605742082043049534361419 44408613123064574301542129)
        ·
          refine ⟨33306459842298430726156597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44408613123064574301542129 33306459842298430726156597)
          ·
            refine ⟨3122480610215477880577181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33306459842298430726156597 3122480610215477880577181)
            ·
              refine ⟨1170930228830804205216443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3122480610215477880577181 1170930228830804205216443)
              ·
                refine ⟨1756395343246206307824665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1170930228830804205216443 1756395343246206307824665)
                ·
                  refine ⟨1317296507434654730868499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1756395343246206307824665 1317296507434654730868499)
                  ·
                    refine ⟨1975944761151982096302749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1317296507434654730868499 1975944761151982096302749)
                    ·
                      refine ⟨740979285431993286113531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1975944761151982096302749 740979285431993286113531)
                      ·
                        rfl

theorem cell23_1443052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 3].length) (baseStart_1443052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443052 prefixEnd_1443052 := by exact prefixLift 1443052
  have htrace : WordTrace (prefixWord ++ tailWord_1443052) baseStart_1443052 baseEnd_1443052 := by
    simpa [prefixWord, tailWord_1443052, baseEnd_1443052] using wordTrace_append hprefix tailTrace_1443052
  have hstable : (prefixWord ++ tailWord_1443052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443052).length < 2 ^ (prefixWord ++ tailWord_1443052).sum := by decide
  have hdescent : baseEnd_1443052 < baseStart_1443052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443075 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 4, 2, 2]
def baseStart_1443075 : Nat := 118140960795 + 1443075 * 2 ^ 59
def prefixEnd_1443075 : Nat := 4983230072969 + 3 ^ 40 * 1443075 * 2
def baseEnd_1443075 : Nat := 740991095487046696125925

theorem tailTrace_1443075 : CollatzResearch.WordTrace tailWord_1443075 prefixEnd_1443075 740991095487046696125925 := by
  unfold tailWord_1443075
  simp only [CollatzResearch.WordTrace]
  refine ⟨52633269246993207433618679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35088846164662138289079119 52633269246993207433618679)
  ·
    refine ⟨78949903870489811150428019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52633269246993207433618679 78949903870489811150428019)
    ·
      refine ⟨118424855805734716725642029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78949903870489811150428019 118424855805734716725642029)
      ·
        refine ⟨44409320927150518772115761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118424855805734716725642029 44409320927150518772115761)
        ·
          refine ⟨33306990695362889079086821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44409320927150518772115761 33306990695362889079086821)
          ·
            refine ⟨6245060755380541702328779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33306990695362889079086821 6245060755380541702328779)
            ·
              refine ⟨9367591133070812553493169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6245060755380541702328779 9367591133070812553493169)
              ·
                refine ⟨7025693349803109415119877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9367591133070812553493169 7025693349803109415119877)
                ·
                  refine ⟨1317317503088083015334977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7025693349803109415119877 1317317503088083015334977)
                  ·
                    refine ⟨987988127316062261501233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1317317503088083015334977 987988127316062261501233)
                    ·
                      refine ⟨740991095487046696125925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 987988127316062261501233 740991095487046696125925)
                      ·
                        rfl

theorem cell23_1443075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 2, 2].length) (baseStart_1443075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443075 prefixEnd_1443075 := by exact prefixLift 1443075
  have htrace : WordTrace (prefixWord ++ tailWord_1443075) baseStart_1443075 baseEnd_1443075 := by
    simpa [prefixWord, tailWord_1443075, baseEnd_1443075] using wordTrace_append hprefix tailTrace_1443075
  have hstable : (prefixWord ++ tailWord_1443075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443075).length < 2 ^ (prefixWord ++ tailWord_1443075).sum := by decide
  have hdescent : baseEnd_1443075 < baseStart_1443075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443098 : List Nat := [3, 1, 1, 3, 3, 1, 3, 1, 7]
def baseStart_1443098 : Nat := 118140960795 + 1443098 * 2 ^ 59
def prefixEnd_1443098 : Nat := 4983230072969 + 3 ^ 40 * 1443098 * 2
def baseEnd_1443098 : Nat := 82333656171344456237591

theorem tailTrace_1443098 : CollatzResearch.WordTrace tailWord_1443098 prefixEnd_1443098 82333656171344456237591 := by
  unfold tailWord_1443098
  simp only [CollatzResearch.WordTrace]
  refine ⟨13158527031477470590426487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35089405417273254907803965 13158527031477470590426487)
  ·
    refine ⟨19737790547216205885639731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13158527031477470590426487 19737790547216205885639731)
    ·
      refine ⟨29606685820824308828459597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19737790547216205885639731 29606685820824308828459597)
      ·
        refine ⟨11102507182809115810672349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29606685820824308828459597 11102507182809115810672349)
        ·
          refine ⟨4163440193553418429002131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11102507182809115810672349 4163440193553418429002131)
          ·
            refine ⟨6245160290330127643503197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4163440193553418429002131 6245160290330127643503197)
            ·
              refine ⟨2341935108873797866313699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6245160290330127643503197 2341935108873797866313699)
              ·
                refine ⟨3512902663310696799470549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2341935108873797866313699 3512902663310696799470549)
                ·
                  refine ⟨82333656171344456237591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3512902663310696799470549 82333656171344456237591)
                  ·
                    rfl

theorem cell23_1443098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 7].length) (baseStart_1443098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443098 prefixEnd_1443098 := by exact prefixLift 1443098
  have htrace : WordTrace (prefixWord ++ tailWord_1443098) baseStart_1443098 baseEnd_1443098 := by
    simpa [prefixWord, tailWord_1443098, baseEnd_1443098] using wordTrace_append hprefix tailTrace_1443098
  have hstable : (prefixWord ++ tailWord_1443098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443098).length < 2 ^ (prefixWord ++ tailWord_1443098).sum := by decide
  have hdescent : baseEnd_1443098 < baseStart_1443098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443108 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 1, 5, 3]
def baseStart_1443108 : Nat := 118140960795 + 1443108 * 2 ^ 59
def prefixEnd_1443108 : Nat := 4983230072969 + 3 ^ 40 * 1443108 * 2
def baseEnd_1443108 : Nat := 741008040348645067013273

theorem tailTrace_1443108 : CollatzResearch.WordTrace tailWord_1443108 prefixEnd_1443108 741008040348645067013273 := by
  unfold tailWord_1443108
  simp only [CollatzResearch.WordTrace]
  refine ⟨26317236427936827034784989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35089648570582436046379985 26317236427936827034784989)
  ·
    refine ⟨9868963660476310138044371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26317236427936827034784989 9868963660476310138044371)
    ·
      refine ⟨14803445490714465207066557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9868963660476310138044371 14803445490714465207066557)
      ·
        refine ⟨5551292059017924452649959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14803445490714465207066557 5551292059017924452649959)
        ·
          refine ⟨8326938088526886678974939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5551292059017924452649959 8326938088526886678974939)
          ·
            refine ⟨12490407132790330018462409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8326938088526886678974939 12490407132790330018462409)
            ·
              refine ⟨9367805349592747513846807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12490407132790330018462409 9367805349592747513846807)
              ·
                refine ⟨14051708024389121270770211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9367805349592747513846807 14051708024389121270770211)
                ·
                  refine ⟨21077562036583681906155317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14051708024389121270770211 21077562036583681906155317)
                  ·
                    refine ⟨1976021440929720178702061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21077562036583681906155317 1976021440929720178702061)
                    ·
                      refine ⟨741008040348645067013273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1976021440929720178702061 741008040348645067013273)
                      ·
                        rfl

theorem cell23_1443108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_1443108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443108 prefixEnd_1443108 := by exact prefixLift 1443108
  have htrace : WordTrace (prefixWord ++ tailWord_1443108) baseStart_1443108 baseEnd_1443108 := by
    simpa [prefixWord, tailWord_1443108, baseEnd_1443108] using wordTrace_append hprefix tailTrace_1443108
  have hstable : (prefixWord ++ tailWord_1443108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443108).length < 2 ^ (prefixWord ++ tailWord_1443108).sum := by decide
  have hdescent : baseEnd_1443108 < baseStart_1443108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443109 : List Nat := [1, 3, 1, 2, 4, 1, 4, 1, 2, 2, 2]
def baseStart_1443109 : Nat := 118140960795 + 1443109 * 2 ^ 59
def prefixEnd_1443109 : Nat := 4983230072969 + 3 ^ 40 * 1443109 * 2
def baseEnd_1443109 : Nat := 741008553829299563100769

theorem tailTrace_1443109 : CollatzResearch.WordTrace tailWord_1443109 prefixEnd_1443109 741008553829299563100769 := by
  unfold tailWord_1443109
  simp only [CollatzResearch.WordTrace]
  refine ⟨52634509328870031240356381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35089672885913354160237587 52634509328870031240356381)
  ·
    refine ⟨19737940998326261715133643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52634509328870031240356381 19737940998326261715133643)
    ·
      refine ⟨29606911497489392572700465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19737940998326261715133643 29606911497489392572700465)
      ·
        refine ⟨22205183623117044429525349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29606911497489392572700465 22205183623117044429525349)
        ·
          refine ⟨4163471929334445830536003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22205183623117044429525349 4163471929334445830536003)
          ·
            refine ⟨6245207894001668745804005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4163471929334445830536003 6245207894001668745804005)
            ·
              refine ⟨1170976480125312889838251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6245207894001668745804005 1170976480125312889838251)
              ·
                refine ⟨1756464720187969334757377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1170976480125312889838251 1756464720187969334757377)
                ·
                  refine ⟨1317348540140977001068033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1756464720187969334757377 1317348540140977001068033)
                  ·
                    refine ⟨988011405105732750801025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1317348540140977001068033 988011405105732750801025)
                    ·
                      refine ⟨741008553829299563100769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 988011405105732750801025 741008553829299563100769)
                      ·
                        rfl

theorem cell23_1443109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_1443109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443109 prefixEnd_1443109 := by exact prefixLift 1443109
  have htrace : WordTrace (prefixWord ++ tailWord_1443109) baseStart_1443109 baseEnd_1443109 := by
    simpa [prefixWord, tailWord_1443109, baseEnd_1443109] using wordTrace_append hprefix tailTrace_1443109
  have hstable : (prefixWord ++ tailWord_1443109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443109).length < 2 ^ (prefixWord ++ tailWord_1443109).sum := by decide
  have hdescent : baseEnd_1443109 < baseStart_1443109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443131 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 4]
def baseStart_1443131 : Nat := 118140960795 + 1443131 * 2 ^ 59
def prefixEnd_1443131 : Nat := 4983230072969 + 3 ^ 40 * 1443131 * 2
def baseEnd_1443131 : Nat := 741019850403698477025667

theorem tailTrace_1443131 : CollatzResearch.WordTrace tailWord_1443131 prefixEnd_1443131 741019850403698477025667 := by
  unfold tailWord_1443131
  simp only [CollatzResearch.WordTrace]
  refine ⟨52635311734790328997657247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35090207823193552665104831 52635311734790328997657247)
  ·
    refine ⟨78952967602185493496485871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52635311734790328997657247 78952967602185493496485871)
    ·
      refine ⟨118429451403278240244728807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78952967602185493496485871 118429451403278240244728807)
      ·
        refine ⟨177644177104917360367093211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118429451403278240244728807 177644177104917360367093211)
        ·
          refine ⟨266466265657376040550639817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177644177104917360367093211 266466265657376040550639817)
          ·
            refine ⟨199849699243032030412979863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266466265657376040550639817 199849699243032030412979863)
            ·
              refine ⟨299774548864548045619469795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199849699243032030412979863 299774548864548045619469795)
              ·
                refine ⟨449661823296822068429204693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299774548864548045619469795 449661823296822068429204693)
                ·
                  refine ⟨10538948983519267228809485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 449661823296822068429204693 10538948983519267228809485)
                  ·
                    refine ⟨3952105868819725210803557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10538948983519267228809485 3952105868819725210803557)
                    ·
                      refine ⟨741019850403698477025667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3952105868819725210803557 741019850403698477025667)
                      ·
                        rfl

theorem cell23_1443131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 4].length) (baseStart_1443131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443131 prefixEnd_1443131 := by exact prefixLift 1443131
  have htrace : WordTrace (prefixWord ++ tailWord_1443131) baseStart_1443131 baseEnd_1443131 := by
    simpa [prefixWord, tailWord_1443131, baseEnd_1443131] using wordTrace_append hprefix tailTrace_1443131
  have hstable : (prefixWord ++ tailWord_1443131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443131).length < 2 ^ (prefixWord ++ tailWord_1443131).sum := by decide
  have hdescent : baseEnd_1443131 < baseStart_1443131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443149 : List Nat := [1, 6, 1, 3, 1, 1, 1, 4, 5]
def baseStart_1443149 : Nat := 118140960795 + 1443149 * 2 ^ 59
def prefixEnd_1443149 : Nat := 4983230072969 + 3 ^ 40 * 1443149 * 2
def baseEnd_1443149 : Nat := 82336565895053267400065

theorem tailTrace_1443149 : CollatzResearch.WordTrace tailWord_1443149 prefixEnd_1443149 82336565895053267400065 := by
  unfold tailWord_1443149
  simp only [CollatzResearch.WordTrace]
  refine ⟨52635968248725118071812501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35090645499150078714541667 52635968248725118071812501)
  ·
    refine ⟨2467311011658989909616211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52635968248725118071812501 2467311011658989909616211)
    ·
      refine ⟨3700966517488484864424317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2467311011658989909616211 3700966517488484864424317)
      ·
        refine ⟨1387862444058181824159119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3700966517488484864424317 1387862444058181824159119)
        ·
          refine ⟨2081793666087272736238679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1387862444058181824159119 2081793666087272736238679)
          ·
            refine ⟨3122690499130909104358019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2081793666087272736238679 3122690499130909104358019)
            ·
              refine ⟨4684035748696363656537029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3122690499130909104358019 4684035748696363656537029)
              ·
                refine ⟨878256702880568185600693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4684035748696363656537029 878256702880568185600693)
                ·
                  refine ⟨82336565895053267400065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 878256702880568185600693 82336565895053267400065)
                  ·
                    rfl

theorem cell23_1443149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_1443149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443149 prefixEnd_1443149 := by exact prefixLift 1443149
  have htrace : WordTrace (prefixWord ++ tailWord_1443149) baseStart_1443149 baseEnd_1443149 := by
    simpa [prefixWord, tailWord_1443149, baseEnd_1443149] using wordTrace_append hprefix tailTrace_1443149
  have hstable : (prefixWord ++ tailWord_1443149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443149).length < 2 ^ (prefixWord ++ tailWord_1443149).sum := by decide
  have hdescent : baseEnd_1443149 < baseStart_1443149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443182 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 1, 3, 4]
def baseStart_1443182 : Nat := 118140960795 + 1443182 * 2 ^ 59
def prefixEnd_1443182 : Nat := 4983230072969 + 3 ^ 40 * 1443182 * 2
def baseEnd_1443182 : Nat := 741046037917077777487933

theorem tailTrace_1443182 : CollatzResearch.WordTrace tailWord_1443182 prefixEnd_1443182 741046037917077777487933 := by
  unfold tailWord_1443182
  simp only [CollatzResearch.WordTrace]
  refine ⟨6579646482200695588470475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35091447905070376471842533 6579646482200695588470475)
  ·
    refine ⟨9869469723301043382705713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6579646482200695588470475 9869469723301043382705713)
    ·
      refine ⟨7402102292475782537029285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9869469723301043382705713 7402102292475782537029285)
      ·
        refine ⟨1387894179839209225692991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7402102292475782537029285 1387894179839209225692991)
        ·
          refine ⟨2081841269758813838539487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1387894179839209225692991 2081841269758813838539487)
          ·
            refine ⟨3122761904638220757809231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2081841269758813838539487 3122761904638220757809231)
            ·
              refine ⟨4684142856957331136713847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3122761904638220757809231 4684142856957331136713847)
              ·
                refine ⟨7026214285435996705070771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4684142856957331136713847 7026214285435996705070771)
                ·
                  refine ⟨10539321428153995057606157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7026214285435996705070771 10539321428153995057606157)
                  ·
                    refine ⟨3952245535557748146602309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10539321428153995057606157 3952245535557748146602309)
                    ·
                      refine ⟨741046037917077777487933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3952245535557748146602309 741046037917077777487933)
                      ·
                        rfl

theorem cell23_1443182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_1443182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443182 prefixEnd_1443182 := by exact prefixLift 1443182
  have htrace : WordTrace (prefixWord ++ tailWord_1443182) baseStart_1443182 baseEnd_1443182 := by
    simpa [prefixWord, tailWord_1443182, baseEnd_1443182] using wordTrace_append hprefix tailTrace_1443182
  have hstable : (prefixWord ++ tailWord_1443182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443182).length < 2 ^ (prefixWord ++ tailWord_1443182).sum := by decide
  have hdescent : baseEnd_1443182 < baseStart_1443182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443185 : List Nat := [1, 2, 2, 2, 1, 2, 5, 1, 2, 2, 3]
def baseStart_1443185 : Nat := 118140960795 + 1443185 * 2 ^ 59
def prefixEnd_1443185 : Nat := 4983230072969 + 3 ^ 40 * 1443185 * 2
def baseEnd_1443185 : Nat := 741047578359041265750419

theorem tailTrace_1443185 : CollatzResearch.WordTrace tailWord_1443185 prefixEnd_1443185 741047578359041265750419 := by
  unfold tailWord_1443185
  simp only [CollatzResearch.WordTrace]
  refine ⟨52637281276594696220123009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35091520851063130813415339 52637281276594696220123009)
  ·
    refine ⟨39477960957446022165092257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52637281276594696220123009 39477960957446022165092257)
    ·
      refine ⟨29608470718084516623819193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39477960957446022165092257 29608470718084516623819193)
      ·
        refine ⟨22206353038563387467864395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29608470718084516623819193 22206353038563387467864395)
        ·
          refine ⟨33309529557845081201796593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22206353038563387467864395 33309529557845081201796593)
          ·
            refine ⟨24982147168383810901347445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33309529557845081201796593 24982147168383810901347445)
            ·
              refine ⟨2342076297035982272001323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24982147168383810901347445 2342076297035982272001323)
              ·
                refine ⟨3513114445553973408001985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342076297035982272001323 3513114445553973408001985)
                ·
                  refine ⟨2634835834165480056001489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3513114445553973408001985 2634835834165480056001489)
                  ·
                    refine ⟨1976126875624110042001117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2634835834165480056001489 1976126875624110042001117)
                    ·
                      refine ⟨741047578359041265750419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1976126875624110042001117 741047578359041265750419)
                      ·
                        rfl

theorem cell23_1443185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_1443185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443185 prefixEnd_1443185 := by exact prefixLift 1443185
  have htrace : WordTrace (prefixWord ++ tailWord_1443185) baseStart_1443185 baseEnd_1443185 := by
    simpa [prefixWord, tailWord_1443185, baseEnd_1443185] using wordTrace_append hprefix tailTrace_1443185
  have hstable : (prefixWord ++ tailWord_1443185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443185).length < 2 ^ (prefixWord ++ tailWord_1443185).sum := by decide
  have hdescent : baseEnd_1443185 < baseStart_1443185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443208 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_1443208 : Nat := 118140960795 + 1443208 * 2 ^ 59
def prefixEnd_1443208 : Nat := 4983230072969 + 3 ^ 40 * 1443208 * 2
def baseEnd_1443208 : Nat := 741059388414094675762813

theorem tailTrace_1443208 : CollatzResearch.WordTrace tailWord_1443208 prefixEnd_1443208 741059388414094675762813 := by
  unfold tailWord_1443208
  simp only [CollatzResearch.WordTrace]
  refine ⟨26319060077755685574105139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35092080103674247432140185 26319060077755685574105139)
  ·
    refine ⟨39478590116633528361157709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26319060077755685574105139 39478590116633528361157709)
    ·
      refine ⟨14804471293737573135434141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39478590116633528361157709 14804471293737573135434141)
      ·
        refine ⟨5551676735151589925787803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14804471293737573135434141 5551676735151589925787803)
        ·
          refine ⟨8327515102727384888681705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5551676735151589925787803 8327515102727384888681705)
          ·
            refine ⟨6245636327045538666511279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8327515102727384888681705 6245636327045538666511279)
            ·
              refine ⟨9368454490568307999766919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6245636327045538666511279 9368454490568307999766919)
              ·
                refine ⟨14052681735852461999650379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9368454490568307999766919 14052681735852461999650379)
                ·
                  refine ⟨21079022603778692999475569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14052681735852461999650379 21079022603778692999475569)
                  ·
                    refine ⟨15809266952834019749606677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21079022603778692999475569 15809266952834019749606677)
                    ·
                      refine ⟨741059388414094675762813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15809266952834019749606677 741059388414094675762813)
                      ·
                        rfl

theorem cell23_1443208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_1443208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443208 prefixEnd_1443208 := by exact prefixLift 1443208
  have htrace : WordTrace (prefixWord ++ tailWord_1443208) baseStart_1443208 baseEnd_1443208 := by
    simpa [prefixWord, tailWord_1443208, baseEnd_1443208] using wordTrace_append hprefix tailTrace_1443208
  have hstable : (prefixWord ++ tailWord_1443208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443208).length < 2 ^ (prefixWord ++ tailWord_1443208).sum := by decide
  have hdescent : baseEnd_1443208 < baseStart_1443208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443225 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 1, 5, 2]
def baseStart_1443225 : Nat := 118140960795 + 1443225 * 2 ^ 59
def prefixEnd_1443225 : Nat := 4983230072969 + 3 ^ 40 * 1443225 * 2
def baseEnd_1443225 : Nat := 741068117585221109250235

theorem tailTrace_1443225 : CollatzResearch.WordTrace tailWord_1443225 prefixEnd_1443225 741068117585221109250235 := by
  unfold tailWord_1443225
  simp only [CollatzResearch.WordTrace]
  refine ⟨52638740196449783051579129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35092493464299855367719419 52638740196449783051579129)
  ·
    refine ⟨39479055147337337288684347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52638740196449783051579129 39479055147337337288684347)
    ·
      refine ⟨59218582721006005933026521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39479055147337337288684347 59218582721006005933026521)
      ·
        refine ⟨44413937040754504449769891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59218582721006005933026521 44413937040754504449769891)
        ·
          refine ⟨66620905561131756674654837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44413937040754504449769891 66620905561131756674654837)
          ·
            refine ⟨6245709896356102188248891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66620905561131756674654837 6245709896356102188248891)
            ·
              refine ⟨9368564844534153282373337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6245709896356102188248891 9368564844534153282373337)
              ·
                refine ⟨7026423633400614961780003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9368564844534153282373337 7026423633400614961780003)
                ·
                  refine ⟨10539635450100922442670005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7026423633400614961780003 10539635450100922442670005)
                  ·
                    refine ⟨988090823446961479000313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10539635450100922442670005 988090823446961479000313)
                    ·
                      refine ⟨741068117585221109250235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 988090823446961479000313 741068117585221109250235)
                      ·
                        rfl

theorem cell23_1443225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 5, 2].length) (baseStart_1443225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443225 prefixEnd_1443225 := by exact prefixLift 1443225
  have htrace : WordTrace (prefixWord ++ tailWord_1443225) baseStart_1443225 baseEnd_1443225 := by
    simpa [prefixWord, tailWord_1443225, baseEnd_1443225] using wordTrace_append hprefix tailTrace_1443225
  have hstable : (prefixWord ++ tailWord_1443225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443225).length < 2 ^ (prefixWord ++ tailWord_1443225).sum := by decide
  have hdescent : baseEnd_1443225 < baseStart_1443225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443235 : List Nat := [1, 1, 1, 4, 1, 3, 4, 2, 1, 5]
def baseStart_1443235 : Nat := 118140960795 + 1443235 * 2 ^ 59
def prefixEnd_1443235 : Nat := 4983230072969 + 3 ^ 40 * 1443235 * 2
def baseEnd_1443235 : Nat := 247024417463922023375063

theorem tailTrace_1443235 : CollatzResearch.WordTrace tailWord_1443235 prefixEnd_1443235 247024417463922023375063 := by
  unfold tailWord_1443235
  simp only [CollatzResearch.WordTrace]
  refine ⟨52639104926413554759443159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35092736617609036506295439 52639104926413554759443159)
  ·
    refine ⟨78958657389620332139164739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52639104926413554759443159 78958657389620332139164739)
    ·
      refine ⟨118437986084430498208747109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78958657389620332139164739 118437986084430498208747109)
      ·
        refine ⟨22207122390830718414140083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118437986084430498208747109 22207122390830718414140083)
        ·
          refine ⟨33310683586246077621210125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22207122390830718414140083 33310683586246077621210125)
          ·
            refine ⟨12491506344842279107953797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33310683586246077621210125 12491506344842279107953797)
            ·
              refine ⟨2342157439657927332741337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12491506344842279107953797 2342157439657927332741337)
              ·
                refine ⟨1756618079743445499556003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2342157439657927332741337 1756618079743445499556003)
                ·
                  refine ⟨2634927119615168249334005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1756618079743445499556003 2634927119615168249334005)
                  ·
                    refine ⟨247024417463922023375063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2634927119615168249334005 247024417463922023375063)
                    ·
                      rfl

theorem cell23_1443235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 5].length) (baseStart_1443235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443235 prefixEnd_1443235 := by exact prefixLift 1443235
  have htrace : WordTrace (prefixWord ++ tailWord_1443235) baseStart_1443235 baseEnd_1443235 := by
    simpa [prefixWord, tailWord_1443235, baseEnd_1443235] using wordTrace_append hprefix tailTrace_1443235
  have hstable : (prefixWord ++ tailWord_1443235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443235).length < 2 ^ (prefixWord ++ tailWord_1443235).sum := by decide
  have hdescent : baseEnd_1443235 < baseStart_1443235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443255 : List Nat := [1, 1, 3, 1, 3, 2, 1, 5, 1, 1, 4]
def baseStart_1443255 : Nat := 118140960795 + 1443255 * 2 ^ 59
def prefixEnd_1443255 : Nat := 4983230072969 + 3 ^ 40 * 1443255 * 2
def baseEnd_1443255 : Nat := 741083522004855991875097

theorem tailTrace_1443255 : CollatzResearch.WordTrace tailWord_1443255 prefixEnd_1443255 741083522004855991875097 := by
  unfold tailWord_1443255
  simp only [CollatzResearch.WordTrace]
  refine ⟨52639834386341098175171219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35093222924227398783447479 52639834386341098175171219)
  ·
    refine ⟨78959751579511647262756829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52639834386341098175171219 78959751579511647262756829)
    ·
      refine ⟨29609906842316867723533811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78959751579511647262756829 29609906842316867723533811)
      ·
        refine ⟨44414860263475301585300717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29609906842316867723533811 44414860263475301585300717)
        ·
          refine ⟨16655572598803238094487769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44414860263475301585300717 16655572598803238094487769)
          ·
            refine ⟨12491679449102428570865827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16655572598803238094487769 12491679449102428570865827)
            ·
              refine ⟨18737519173653642856298741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12491679449102428570865827 18737519173653642856298741)
              ·
                refine ⟨1756642422530029017778007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18737519173653642856298741 1756642422530029017778007)
                ·
                  refine ⟨2634963633795043526667011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1756642422530029017778007 2634963633795043526667011)
                  ·
                    refine ⟨3952445450692565290000517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2634963633795043526667011 3952445450692565290000517)
                    ·
                      refine ⟨741083522004855991875097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3952445450692565290000517 741083522004855991875097)
                      ·
                        rfl

theorem cell23_1443255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 1, 4].length) (baseStart_1443255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443255 prefixEnd_1443255 := by exact prefixLift 1443255
  have htrace : WordTrace (prefixWord ++ tailWord_1443255) baseStart_1443255 baseEnd_1443255 := by
    simpa [prefixWord, tailWord_1443255, baseEnd_1443255] using wordTrace_append hprefix tailTrace_1443255
  have hstable : (prefixWord ++ tailWord_1443255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443255).length < 2 ^ (prefixWord ++ tailWord_1443255).sum := by decide
  have hdescent : baseEnd_1443255 < baseStart_1443255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443278 : List Nat := [4, 1, 1, 1, 2, 1, 3, 10]
def baseStart_1443278 : Nat := 118140960795 + 1443278 * 2 ^ 59
def prefixEnd_1443278 : Nat := 4983230072969 + 3 ^ 40 * 1443278 * 2
def baseEnd_1443278 : Nat := 27447975261478125995833

theorem tailTrace_1443278 : CollatzResearch.WordTrace tailWord_1443278 prefixEnd_1443278 27447975261478125995833 := by
  unfold tailWord_1443278
  simp only [CollatzResearch.WordTrace]
  refine ⟨6580084158157221637907311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35093782176838515402172325 6580084158157221637907311)
  ·
    refine ⟨9870126237235832456860967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6580084158157221637907311 9870126237235832456860967)
    ·
      refine ⟨14805189355853748685291451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9870126237235832456860967 14805189355853748685291451)
      ·
        refine ⟨22207784033780623027937177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14805189355853748685291451 22207784033780623027937177)
        ·
          refine ⟨16655838025335467270952883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22207784033780623027937177 16655838025335467270952883)
          ·
            refine ⟨24983757038003200906429325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16655838025335467270952883 24983757038003200906429325)
            ·
              refine ⟨9368908889251200339910997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24983757038003200906429325 9368908889251200339910997)
              ·
                refine ⟨27447975261478125995833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9368908889251200339910997 27447975261478125995833)
                ·
                  rfl

theorem cell23_1443278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 10].length) (baseStart_1443278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443278 prefixEnd_1443278 := by exact prefixLift 1443278
  have htrace : WordTrace (prefixWord ++ tailWord_1443278) baseStart_1443278 baseEnd_1443278 := by
    simpa [prefixWord, tailWord_1443278, baseEnd_1443278] using wordTrace_append hprefix tailTrace_1443278
  have hstable : (prefixWord ++ tailWord_1443278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443278).length < 2 ^ (prefixWord ++ tailWord_1443278).sum := by decide
  have hdescent : baseEnd_1443278 < baseStart_1443278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443285 : List Nat := [1, 3, 2, 3, 1, 1, 2, 3, 1, 2, 4]
def baseStart_1443285 : Nat := 118140960795 + 1443285 * 2 ^ 59
def prefixEnd_1443285 : Nat := 4983230072969 + 3 ^ 40 * 1443285 * 2
def baseEnd_1443285 : Nat := 741098926424490874499959

theorem tailTrace_1443285 : CollatzResearch.WordTrace tailWord_1443285 prefixEnd_1443285 741098926424490874499959 := by
  unfold tailWord_1443285
  simp only [CollatzResearch.WordTrace]
  refine ⟨52640928576232413298763309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35093952384154942199175539 52640928576232413298763309)
  ·
    refine ⟨19740348216087154987036241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52640928576232413298763309 19740348216087154987036241)
    ·
      refine ⟨14805261162065366240277181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19740348216087154987036241 14805261162065366240277181)
      ·
        refine ⟨5551972935774512340103943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14805261162065366240277181 5551972935774512340103943)
        ·
          refine ⟨8327959403661768510155915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5551972935774512340103943 8327959403661768510155915)
          ·
            refine ⟨12491939105492652765233873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8327959403661768510155915 12491939105492652765233873)
            ·
              refine ⟨9368954329119489573925405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12491939105492652765233873 9368954329119489573925405)
              ·
                refine ⟨3513357873419808590222027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9368954329119489573925405 3513357873419808590222027)
                ·
                  refine ⟨5270036810129712885333041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3513357873419808590222027 5270036810129712885333041)
                  ·
                    refine ⟨3952527607597284663999781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5270036810129712885333041 3952527607597284663999781)
                    ·
                      refine ⟨741098926424490874499959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3952527607597284663999781 741098926424490874499959)
                      ·
                        rfl

theorem cell23_1443285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_1443285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443285 prefixEnd_1443285 := by exact prefixLift 1443285
  have htrace : WordTrace (prefixWord ++ tailWord_1443285) baseStart_1443285 baseEnd_1443285 := by
    simpa [prefixWord, tailWord_1443285, baseEnd_1443285] using wordTrace_append hprefix tailTrace_1443285
  have hstable : (prefixWord ++ tailWord_1443285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443285).length < 2 ^ (prefixWord ++ tailWord_1443285).sum := by decide
  have hdescent : baseEnd_1443285 < baseStart_1443285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443309 : List Nat := [1, 5, 1, 3, 2, 2, 1, 1, 1, 1, 5]
def baseStart_1443309 : Nat := 118140960795 + 1443309 * 2 ^ 59
def prefixEnd_1443309 : Nat := 4983230072969 + 3 ^ 40 * 1443309 * 2
def baseEnd_1443309 : Nat := 741111249960198780599849

theorem tailTrace_1443309 : CollatzResearch.WordTrace tailWord_1443309 prefixEnd_1443309 741111249960198780599849 := by
  unfold tailWord_1443309
  simp only [CollatzResearch.WordTrace]
  refine ⟨52641803928145465397636981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35094535952096976931757987 52641803928145465397636981)
  ·
    refine ⟨4935169118263637381028467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52641803928145465397636981 4935169118263637381028467)
    ·
      refine ⟨7402753677395456071542701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4935169118263637381028467 7402753677395456071542701)
      ·
        refine ⟨2776032629023296026828513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7402753677395456071542701 2776032629023296026828513)
        ·
          refine ⟨2082024471767472020121385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2776032629023296026828513 2082024471767472020121385)
          ·
            refine ⟨1561518353825604015091039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2082024471767472020121385 1561518353825604015091039)
            ·
              refine ⟨2342277530738406022636559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561518353825604015091039 2342277530738406022636559)
              ·
                refine ⟨3513416296107609033954839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342277530738406022636559 3513416296107609033954839)
                ·
                  refine ⟨5270124444161413550932259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3513416296107609033954839 5270124444161413550932259)
                  ·
                    refine ⟨7905186666242120326398389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5270124444161413550932259 7905186666242120326398389)
                    ·
                      refine ⟨741111249960198780599849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7905186666242120326398389 741111249960198780599849)
                      ·
                        rfl

theorem cell23_1443309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_1443309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443309 prefixEnd_1443309 := by exact prefixLift 1443309
  have htrace : WordTrace (prefixWord ++ tailWord_1443309) baseStart_1443309 baseEnd_1443309 := by
    simpa [prefixWord, tailWord_1443309, baseEnd_1443309] using wordTrace_append hprefix tailTrace_1443309
  have hstable : (prefixWord ++ tailWord_1443309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443309).length < 2 ^ (prefixWord ++ tailWord_1443309).sum := by decide
  have hdescent : baseEnd_1443309 < baseStart_1443309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443379 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 4, 2, 2]
def baseStart_1443379 : Nat := 118140960795 + 1443379 * 2 ^ 59
def prefixEnd_1443379 : Nat := 4983230072969 + 3 ^ 40 * 1443379 * 2
def baseEnd_1443379 : Nat := 741147193606013506724527

theorem tailTrace_1443379 : CollatzResearch.WordTrace tailWord_1443379 prefixEnd_1443379 741147193606013506724527 := by
  unfold tailWord_1443379
  simp only [CollatzResearch.WordTrace]
  refine ⟨52644357037891867352685191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35096238025261244901790127 52644357037891867352685191)
  ·
    refine ⟨78966535556837801029027787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52644357037891867352685191 78966535556837801029027787)
    ·
      refine ⟨118449803335256701543541681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78966535556837801029027787 118449803335256701543541681)
      ·
        refine ⟨88837352501442526157656261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118449803335256701543541681 88837352501442526157656261)
        ·
          refine ⟨16657003594020473654560549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88837352501442526157656261 16657003594020473654560549)
          ·
            refine ⟨3123188173878838810230103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16657003594020473654560549 3123188173878838810230103)
            ·
              refine ⟨4684782260818258215345155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3123188173878838810230103 4684782260818258215345155)
              ·
                refine ⟨7027173391227387323017733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4684782260818258215345155 7027173391227387323017733)
                ·
                  refine ⟨1317595010855135123065825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7027173391227387323017733 1317595010855135123065825)
                  ·
                    refine ⟨988196258141351342299369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1317595010855135123065825 988196258141351342299369)
                    ·
                      refine ⟨741147193606013506724527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 988196258141351342299369 741147193606013506724527)
                      ·
                        rfl

theorem cell23_1443379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 2, 2].length) (baseStart_1443379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443379 prefixEnd_1443379 := by exact prefixLift 1443379
  have htrace : WordTrace (prefixWord ++ tailWord_1443379) baseStart_1443379 baseEnd_1443379 := by
    simpa [prefixWord, tailWord_1443379, baseEnd_1443379] using wordTrace_append hprefix tailTrace_1443379
  have hstable : (prefixWord ++ tailWord_1443379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443379).length < 2 ^ (prefixWord ++ tailWord_1443379).sum := by decide
  have hdescent : baseEnd_1443379 < baseStart_1443379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443385 : List Nat := [1, 2, 1, 5, 1, 2, 1, 3, 7]
def baseStart_1443385 : Nat := 118140960795 + 1443385 * 2 ^ 59
def prefixEnd_1443385 : Nat := 4983230072969 + 3 ^ 40 * 1443385 * 2
def baseEnd_1443385 : Nat := 82350030498882275916611

theorem tailTrace_1443385 : CollatzResearch.WordTrace tailWord_1443385 prefixEnd_1443385 82350030498882275916611 := by
  unfold tailWord_1443385
  simp only [CollatzResearch.WordTrace]
  refine ⟨52644575875870130377403609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35096383917246753584935739 52644575875870130377403609)
  ·
    refine ⟨39483431906902597783052707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52644575875870130377403609 39483431906902597783052707)
    ·
      refine ⟨59225147860353896674579061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39483431906902597783052707 59225147860353896674579061)
      ·
        refine ⟨5552357611908177813241787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59225147860353896674579061 5552357611908177813241787)
        ·
          refine ⟨8328536417862266719862681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5552357611908177813241787 8328536417862266719862681)
          ·
            refine ⟨6246402313396700039897011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8328536417862266719862681 6246402313396700039897011)
            ·
              refine ⟨9369603470095050059845517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6246402313396700039897011 9369603470095050059845517)
              ·
                refine ⟨3513601301285643772442069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9369603470095050059845517 3513601301285643772442069)
                ·
                  refine ⟨82350030498882275916611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3513601301285643772442069 82350030498882275916611)
                  ·
                    rfl

theorem cell23_1443385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 7].length) (baseStart_1443385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443385 prefixEnd_1443385 := by exact prefixLift 1443385
  have htrace : WordTrace (prefixWord ++ tailWord_1443385) baseStart_1443385 baseEnd_1443385 := by
    simpa [prefixWord, tailWord_1443385, baseEnd_1443385] using wordTrace_append hprefix tailTrace_1443385
  have hstable : (prefixWord ++ tailWord_1443385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443385).length < 2 ^ (prefixWord ++ tailWord_1443385).sum := by decide
  have hdescent : baseEnd_1443385 < baseStart_1443385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443415 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 1, 7]
def baseStart_1443415 : Nat := 118140960795 + 1443415 * 2 ^ 59
def prefixEnd_1443415 : Nat := 4983230072969 + 3 ^ 40 * 1443415 * 2
def baseEnd_1443415 : Nat := 247055226303191788624787

theorem tailTrace_1443415 : CollatzResearch.WordTrace tailWord_1443415 prefixEnd_1443415 247055226303191788624787 := by
  unfold tailWord_1443415
  simp only [CollatzResearch.WordTrace]
  refine ⟨52645670065761445500995699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35097113377174297000663799 52645670065761445500995699)
  ·
    refine ⟨78968505098642168251493549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52645670065761445500995699 78968505098642168251493549)
    ·
      refine ⟨29613189411990813094310081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78968505098642168251493549 29613189411990813094310081)
      ·
        refine ⟨22209892058993109820732561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29613189411990813094310081 22209892058993109820732561)
        ·
          refine ⟨16657419044244832365549421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22209892058993109820732561 16657419044244832365549421)
          ·
            refine ⟨6246532141591812137081033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16657419044244832365549421 6246532141591812137081033)
            ·
              refine ⟨4684899106193859102810775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6246532141591812137081033 4684899106193859102810775)
              ·
                refine ⟨7027348659290788654216163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4684899106193859102810775 7027348659290788654216163)
                ·
                  refine ⟨10541022988936182981324245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7027348659290788654216163 10541022988936182981324245)
                  ·
                    refine ⟨247055226303191788624787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10541022988936182981324245 247055226303191788624787)
                    ·
                      rfl

theorem cell23_1443415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_1443415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443415 prefixEnd_1443415 := by exact prefixLift 1443415
  have htrace : WordTrace (prefixWord ++ tailWord_1443415) baseStart_1443415 baseEnd_1443415 := by
    simpa [prefixWord, tailWord_1443415, baseEnd_1443415] using wordTrace_append hprefix tailTrace_1443415
  have hstable : (prefixWord ++ tailWord_1443415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443415).length < 2 ^ (prefixWord ++ tailWord_1443415).sum := by decide
  have hdescent : baseEnd_1443415 < baseStart_1443415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443425 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_1443425 : Nat := 118140960795 + 1443425 * 2 ^ 59
def prefixEnd_1443425 : Nat := 4983230072969 + 3 ^ 40 * 1443425 * 2
def baseEnd_1443425 : Nat := 741170813716120326749315

theorem tailTrace_1443425 : CollatzResearch.WordTrace tailWord_1443425 prefixEnd_1443425 741170813716120326749315 := by
  unfold tailWord_1443425
  simp only [CollatzResearch.WordTrace]
  refine ⟨52646034795725217208859729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35097356530483478139239819 52646034795725217208859729)
  ·
    refine ⟨39484526096793912906644797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52646034795725217208859729 39484526096793912906644797)
    ·
      refine ⟨14806697286297717339991799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39484526096793912906644797 14806697286297717339991799)
      ·
        refine ⟨22210045929446576009987699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14806697286297717339991799 22210045929446576009987699)
        ·
          refine ⟨33315068894169864014981549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22210045929446576009987699 33315068894169864014981549)
          ·
            refine ⟨12493150835313699005618081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33315068894169864014981549 12493150835313699005618081)
            ·
              refine ⟨9369863126485274254213561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12493150835313699005618081 9369863126485274254213561)
              ·
                refine ⟨7027397344863955690660171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9369863126485274254213561 7027397344863955690660171)
                ·
                  refine ⟨10541096017295933535990257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7027397344863955690660171 10541096017295933535990257)
                  ·
                    refine ⟨7905822012971950151992693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10541096017295933535990257 7905822012971950151992693)
                    ·
                      refine ⟨741170813716120326749315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7905822012971950151992693 741170813716120326749315)
                      ·
                        rfl

theorem cell23_1443425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_1443425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443425 prefixEnd_1443425 := by exact prefixLift 1443425
  have htrace : WordTrace (prefixWord ++ tailWord_1443425) baseStart_1443425 baseEnd_1443425 := by
    simpa [prefixWord, tailWord_1443425, baseEnd_1443425] using wordTrace_append hprefix tailTrace_1443425
  have hstable : (prefixWord ++ tailWord_1443425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443425).length < 2 ^ (prefixWord ++ tailWord_1443425).sum := by decide
  have hdescent : baseEnd_1443425 < baseStart_1443425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443432 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 4, 5]
def baseStart_1443432 : Nat := 118140960795 + 1443432 * 2 ^ 59
def prefixEnd_1443432 : Nat := 4983230072969 + 3 ^ 40 * 1443432 * 2
def baseEnd_1443432 : Nat := 247058136026900599787261

theorem tailTrace_1443432 : CollatzResearch.WordTrace tailWord_1443432 prefixEnd_1443432 247058136026900599787261 := by
  unfold tailWord_1443432
  simp only [CollatzResearch.WordTrace]
  refine ⟨26323145053349928702182275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35097526737799904936243033 26323145053349928702182275)
  ·
    refine ⟨39484717580024893053273413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26323145053349928702182275 39484717580024893053273413)
    ·
      refine ⟨7403384546254667447488765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39484717580024893053273413 7403384546254667447488765)
      ·
        refine ⟨2776269204845500292808287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7403384546254667447488765 2776269204845500292808287)
        ·
          refine ⟨4164403807268250439212431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2776269204845500292808287 4164403807268250439212431)
          ·
            refine ⟨6246605710902375658818647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4164403807268250439212431 6246605710902375658818647)
            ·
              refine ⟨9369908566353563488227971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6246605710902375658818647 9369908566353563488227971)
              ·
                refine ⟨14054862849530345232341957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9369908566353563488227971 14054862849530345232341957)
                ·
                  refine ⟨2635286784286939731064117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14054862849530345232341957 2635286784286939731064117)
                  ·
                    refine ⟨247058136026900599787261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2635286784286939731064117 247058136026900599787261)
                    ·
                      rfl

theorem cell23_1443432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_1443432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443432 prefixEnd_1443432 := by exact prefixLift 1443432
  have htrace : WordTrace (prefixWord ++ tailWord_1443432) baseStart_1443432 baseEnd_1443432 := by
    simpa [prefixWord, tailWord_1443432, baseEnd_1443432] using wordTrace_append hprefix tailTrace_1443432
  have hstable : (prefixWord ++ tailWord_1443432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443432).length < 2 ^ (prefixWord ++ tailWord_1443432).sum := by decide
  have hdescent : baseEnd_1443432 < baseStart_1443432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443442 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 1, 2, 5]
def baseStart_1443442 : Nat := 118140960795 + 1443442 * 2 ^ 59
def prefixEnd_1443442 : Nat := 4983230072969 + 3 ^ 40 * 1443442 * 2
def baseEnd_1443442 : Nat := 741179542887246760236737

theorem tailTrace_1443442 : CollatzResearch.WordTrace tailWord_1443442 prefixEnd_1443442 741179542887246760236737 := by
  unfold tailWord_1443442
  simp only [CollatzResearch.WordTrace]
  refine ⟨13161663709165907278057145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35097769891109086074819053 13161663709165907278057145)
  ·
    refine ⟨9871247781874430458542859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13161663709165907278057145 9871247781874430458542859)
    ·
      refine ⟨14806871672811645687814289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9871247781874430458542859 14806871672811645687814289)
      ·
        refine ⟨11105153754608734265860717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14806871672811645687814289 11105153754608734265860717)
        ·
          refine ⟨4164432657978275349697769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11105153754608734265860717 4164432657978275349697769)
          ·
            refine ⟨3123324493483706512273327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4164432657978275349697769 3123324493483706512273327)
            ·
              refine ⟨4684986740225559768409991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3123324493483706512273327 4684986740225559768409991)
              ·
                refine ⟨7027480110338339652614987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4684986740225559768409991 7027480110338339652614987)
                ·
                  refine ⟨10541220165507509478922481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7027480110338339652614987 10541220165507509478922481)
                  ·
                    refine ⟨7905915124130632109191861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10541220165507509478922481 7905915124130632109191861)
                    ·
                      refine ⟨741179542887246760236737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7905915124130632109191861 741179542887246760236737)
                      ·
                        rfl

theorem cell23_1443442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_1443442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443442 prefixEnd_1443442 := by exact prefixLift 1443442
  have htrace : WordTrace (prefixWord ++ tailWord_1443442) baseStart_1443442 baseEnd_1443442 := by
    simpa [prefixWord, tailWord_1443442, baseEnd_1443442] using wordTrace_append hprefix tailTrace_1443442
  have hstable : (prefixWord ++ tailWord_1443442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443442).length < 2 ^ (prefixWord ++ tailWord_1443442).sum := by decide
  have hdescent : baseEnd_1443442 < baseStart_1443442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443452 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 1, 6, 2]
def baseStart_1443452 : Nat := 118140960795 + 1443452 * 2 ^ 59
def prefixEnd_1443452 : Nat := 4983230072969 + 3 ^ 40 * 1443452 * 2
def baseEnd_1443452 : Nat := 741184677693791721111691

theorem tailTrace_1443452 : CollatzResearch.WordTrace tailWord_1443452 prefixEnd_1443452 741184677693791721111691 := by
  unfold tailWord_1443452
  simp only [CollatzResearch.WordTrace]
  refine ⟨26323509783313700410046305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35098013044418267213395073 26323509783313700410046305)
  ·
    refine ⟨19742632337485275307534729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26323509783313700410046305 19742632337485275307534729)
    ·
      refine ⟨14806974253113956480651047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19742632337485275307534729 14806974253113956480651047)
      ·
        refine ⟨22210461379670934720976571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14806974253113956480651047 22210461379670934720976571)
        ·
          refine ⟨33315692069506402081464857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22210461379670934720976571 33315692069506402081464857)
          ·
            refine ⟨24986769052129801561098643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33315692069506402081464857 24986769052129801561098643)
            ·
              refine ⟨37480153578194702341647965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24986769052129801561098643 37480153578194702341647965)
              ·
                refine ⟨14055057591823013378117987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37480153578194702341647965 14055057591823013378117987)
                ·
                  refine ⟨21082586387734520067176981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14055057591823013378117987 21082586387734520067176981)
                  ·
                    refine ⟨988246236925055628148921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21082586387734520067176981 988246236925055628148921)
                    ·
                      refine ⟨741184677693791721111691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 988246236925055628148921 741184677693791721111691)
                      ·
                        rfl

theorem cell23_1443452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_1443452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443452 prefixEnd_1443452 := by exact prefixLift 1443452
  have htrace : WordTrace (prefixWord ++ tailWord_1443452) baseStart_1443452 baseEnd_1443452 := by
    simpa [prefixWord, tailWord_1443452, baseEnd_1443452] using wordTrace_append hprefix tailTrace_1443452
  have hstable : (prefixWord ++ tailWord_1443452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443452).length < 2 ^ (prefixWord ++ tailWord_1443452).sum := by decide
  have hdescent : baseEnd_1443452 < baseStart_1443452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443465 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 2, 4, 4]
def baseStart_1443465 : Nat := 118140960795 + 1443465 * 2 ^ 59
def prefixEnd_1443465 : Nat := 4983230072969 + 3 ^ 40 * 1443465 * 2
def baseEnd_1443465 : Nat := 741191352942300170249131

theorem tailTrace_1443465 : CollatzResearch.WordTrace tailWord_1443465 prefixEnd_1443465 741191352942300170249131 := by
  unfold tailWord_1443465
  simp only [CollatzResearch.WordTrace]
  refine ⟨52647493715580304040315849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35098329143720202693543899 52647493715580304040315849)
  ·
    refine ⟨39485620286685228030236887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52647493715580304040315849 39485620286685228030236887)
    ·
      refine ⟨59228430430027842045355331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39485620286685228030236887 59228430430027842045355331)
      ·
        refine ⟨88842645645041763068032997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59228430430027842045355331 88842645645041763068032997)
        ·
          refine ⟨16657996058445330575256187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88842645645041763068032997 16657996058445330575256187)
          ·
            refine ⟨24986994087667995862884281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16657996058445330575256187 24986994087667995862884281)
            ·
              refine ⟨18740245565750996897163211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24986994087667995862884281 18740245565750996897163211)
              ·
                refine ⟨28110368348626495345744817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18740245565750996897163211 28110368348626495345744817)
                ·
                  refine ⟨21082776261469871509308613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28110368348626495345744817 21082776261469871509308613)
                  ·
                    refine ⟨3953020549025600907995365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21082776261469871509308613 3953020549025600907995365)
                    ·
                      refine ⟨741191352942300170249131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3953020549025600907995365 741191352942300170249131)
                      ·
                        rfl

theorem cell23_1443465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 4, 4].length) (baseStart_1443465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443465 prefixEnd_1443465 := by exact prefixLift 1443465
  have htrace : WordTrace (prefixWord ++ tailWord_1443465) baseStart_1443465 baseEnd_1443465 := by
    simpa [prefixWord, tailWord_1443465, baseEnd_1443465] using wordTrace_append hprefix tailTrace_1443465
  have hstable : (prefixWord ++ tailWord_1443465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443465).length < 2 ^ (prefixWord ++ tailWord_1443465).sum := by decide
  have hdescent : baseEnd_1443465 < baseStart_1443465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443489 : List Nat := [1, 2, 3, 3, 2, 1, 2, 2, 2, 2, 3]
def baseStart_1443489 : Nat := 118140960795 + 1443489 * 2 ^ 59
def prefixEnd_1443489 : Nat := 4983230072969 + 3 ^ 40 * 1443489 * 2
def baseEnd_1443489 : Nat := 741203676478008076349021

theorem tailTrace_1443489 : CollatzResearch.WordTrace tailWord_1443489 prefixEnd_1443489 741203676478008076349021 := by
  unfold tailWord_1443489
  simp only [CollatzResearch.WordTrace]
  refine ⟨52648369067493356139189521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35098912711662237426126347 52648369067493356139189521)
  ·
    refine ⟨39486276800620017104392141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52648369067493356139189521 39486276800620017104392141)
    ·
      refine ⟨14807353800232506414147053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39486276800620017104392141 14807353800232506414147053)
      ·
        refine ⟨5552757675087189905305145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14807353800232506414147053 5552757675087189905305145)
        ·
          refine ⟨4164568256315392428978859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5552757675087189905305145 4164568256315392428978859)
          ·
            refine ⟨6246852384473088643468289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4164568256315392428978859 6246852384473088643468289)
            ·
              refine ⟨4685139288354816482601217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6246852384473088643468289 4685139288354816482601217)
              ·
                refine ⟨3513854466266112361950913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4685139288354816482601217 3513854466266112361950913)
                ·
                  refine ⟨2635390849699584271463185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3513854466266112361950913 2635390849699584271463185)
                  ·
                    refine ⟨1976543137274688203597389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2635390849699584271463185 1976543137274688203597389)
                    ·
                      refine ⟨741203676478008076349021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1976543137274688203597389 741203676478008076349021)
                      ·
                        rfl

theorem cell23_1443489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_1443489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443489 prefixEnd_1443489 := by exact prefixLift 1443489
  have htrace : WordTrace (prefixWord ++ tailWord_1443489) baseStart_1443489 baseEnd_1443489 := by
    simpa [prefixWord, tailWord_1443489, baseEnd_1443489] using wordTrace_append hprefix tailTrace_1443489
  have hstable : (prefixWord ++ tailWord_1443489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443489).length < 2 ^ (prefixWord ++ tailWord_1443489).sum := by decide
  have hdescent : baseEnd_1443489 < baseStart_1443489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443492 : List Nat := [2, 3, 1, 2, 2, 2, 1, 4, 6]
def baseStart_1443492 : Nat := 118140960795 + 1443492 * 2 ^ 59
def prefixEnd_1443492 : Nat := 4983230072969 + 3 ^ 40 * 1443492 * 2
def baseEnd_1443492 : Nat := 82356135213330173845723

theorem tailTrace_1443492 : CollatzResearch.WordTrace tailWord_1443492 prefixEnd_1443492 82356135213330173845723 := by
  unfold tailWord_1443492
  simp only [CollatzResearch.WordTrace]
  refine ⟨26324239243241243825774365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35098985657654991767699153 26324239243241243825774365)
  ·
    refine ⟨9871589716215466434665387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26324239243241243825774365 9871589716215466434665387)
    ·
      refine ⟨14807384574323199651998081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9871589716215466434665387 14807384574323199651998081)
      ·
        refine ⟨11105538430742399738998561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14807384574323199651998081 11105538430742399738998561)
        ·
          refine ⟨8329153823056799804248921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11105538430742399738998561 8329153823056799804248921)
          ·
            refine ⟨6246865367292599853186691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8329153823056799804248921 6246865367292599853186691)
            ·
              refine ⟨9370298050938899779780037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6246865367292599853186691 9370298050938899779780037)
              ·
                refine ⟨1756930884551043708708757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9370298050938899779780037 1756930884551043708708757)
                ·
                  refine ⟨82356135213330173845723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1756930884551043708708757 82356135213330173845723)
                  ·
                    rfl

theorem cell23_1443492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_1443492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443492 prefixEnd_1443492 := by exact prefixLift 1443492
  have htrace : WordTrace (prefixWord ++ tailWord_1443492) baseStart_1443492 baseEnd_1443492 := by
    simpa [prefixWord, tailWord_1443492, baseEnd_1443492] using wordTrace_append hprefix tailTrace_1443492
  have hstable : (prefixWord ++ tailWord_1443492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443492).length < 2 ^ (prefixWord ++ tailWord_1443492).sum := by decide
  have hdescent : baseEnd_1443492 < baseStart_1443492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443519 : List Nat := [1, 1, 2, 2, 2, 3, 3, 2, 3, 1, 3]
def baseStart_1443519 : Nat := 118140960795 + 1443519 * 2 ^ 59
def prefixEnd_1443519 : Nat := 4983230072969 + 3 ^ 40 * 1443519 * 2
def baseEnd_1443519 : Nat := 741219080897642958973883

theorem tailTrace_1443519 : CollatzResearch.WordTrace tailWord_1443519 prefixEnd_1443519 741219080897642958973883 := by
  unfold tailWord_1443519
  simp only [CollatzResearch.WordTrace]
  refine ⟨52649463257384671262781611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35099642171589780841854407 52649463257384671262781611)
  ·
    refine ⟨78974194886077006894172417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52649463257384671262781611 78974194886077006894172417)
    ·
      refine ⟨59230646164557755170629313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78974194886077006894172417 59230646164557755170629313)
      ·
        refine ⟨44422984623418316377971985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59230646164557755170629313 44422984623418316377971985)
        ·
          refine ⟨33317238467563737283478989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44422984623418316377971985 33317238467563737283478989)
          ·
            refine ⟨12493964425336401481304621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33317238467563737283478989 12493964425336401481304621)
            ·
              refine ⟨4685236659501150555489233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12493964425336401481304621 4685236659501150555489233)
              ·
                refine ⟨3513927494625862916616925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4685236659501150555489233 3513927494625862916616925)
                ·
                  refine ⟨1317722810484698593731347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3513927494625862916616925 1317722810484698593731347)
                  ·
                    refine ⟨1976584215727047890597021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1317722810484698593731347 1976584215727047890597021)
                    ·
                      refine ⟨741219080897642958973883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1976584215727047890597021 741219080897642958973883)
                      ·
                        rfl

theorem cell23_1443519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 1, 3].length) (baseStart_1443519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443519 prefixEnd_1443519 := by exact prefixLift 1443519
  have htrace : WordTrace (prefixWord ++ tailWord_1443519) baseStart_1443519 baseEnd_1443519 := by
    simpa [prefixWord, tailWord_1443519, baseEnd_1443519] using wordTrace_append hprefix tailTrace_1443519
  have hstable : (prefixWord ++ tailWord_1443519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443519).length < 2 ^ (prefixWord ++ tailWord_1443519).sum := by decide
  have hdescent : baseEnd_1443519 < baseStart_1443519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443562 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_1443562 : Nat := 118140960795 + 1443562 * 2 ^ 59
def prefixEnd_1443562 : Nat := 4983230072969 + 3 ^ 40 * 1443562 * 2
def baseEnd_1443562 : Nat := 741241160565786290736185

theorem tailTrace_1443562 : CollatzResearch.WordTrace tailWord_1443562 prefixEnd_1443562 741241160565786290736185 := by
  unfold tailWord_1443562
  simp only [CollatzResearch.WordTrace]
  refine ⟨13162757899057222401649235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35100687730819259737731293 13162757899057222401649235)
  ·
    refine ⟨19744136848585833602473853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13162757899057222401649235 19744136848585833602473853)
    ·
      refine ⟨7404051318219687600927695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19744136848585833602473853 7404051318219687600927695)
      ·
        refine ⟨11106076977329531401391543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7404051318219687600927695 11106076977329531401391543)
        ·
          refine ⟨16659115465994297102087315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11106076977329531401391543 16659115465994297102087315)
          ·
            refine ⟨24988673198991445653130973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16659115465994297102087315 24988673198991445653130973)
            ·
              refine ⟨9370752449621792119924115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24988673198991445653130973 9370752449621792119924115)
              ·
                refine ⟨14056128674432688179886173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9370752449621792119924115 14056128674432688179886173)
                ·
                  refine ⟨5271048252912258067457315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14056128674432688179886173 5271048252912258067457315)
                  ·
                    refine ⟨7906572379368387101185973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5271048252912258067457315 7906572379368387101185973)
                    ·
                      refine ⟨741241160565786290736185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7906572379368387101185973 741241160565786290736185)
                      ·
                        rfl

theorem cell23_1443562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_1443562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443562 prefixEnd_1443562 := by exact prefixLift 1443562
  have htrace : WordTrace (prefixWord ++ tailWord_1443562) baseStart_1443562 baseEnd_1443562 := by
    simpa [prefixWord, tailWord_1443562, baseEnd_1443562] using wordTrace_append hprefix tailTrace_1443562
  have hstable : (prefixWord ++ tailWord_1443562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443562).length < 2 ^ (prefixWord ++ tailWord_1443562).sum := by decide
  have hdescent : baseEnd_1443562 < baseStart_1443562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443569 : List Nat := [1, 2, 2, 2, 2, 5, 1, 1, 1, 6]
def baseStart_1443569 : Nat := 118140960795 + 1443569 * 2 ^ 59
def prefixEnd_1443569 : Nat := 4983230072969 + 3 ^ 40 * 1443569 * 2
def baseEnd_1443569 : Nat := 247081584976789254449551

theorem tailTrace_1443569 : CollatzResearch.WordTrace tailWord_1443569 prefixEnd_1443569 247081584976789254449551 := by
  unfold tailWord_1443569
  simp only [CollatzResearch.WordTrace]
  refine ⟨52651286907203529802101761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35100857938135686534734507 52651286907203529802101761)
  ·
    refine ⟨39488465180402647351576321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52651286907203529802101761 39488465180402647351576321)
    ·
      refine ⟨29616348885301985513682241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39488465180402647351576321 29616348885301985513682241)
      ·
        refine ⟨22212261663976489135261681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29616348885301985513682241 22212261663976489135261681)
        ·
          refine ⟨16659196247982366851446261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22212261663976489135261681 16659196247982366851446261)
          ·
            refine ⟨1561799648248346892323087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16659196247982366851446261 1561799648248346892323087)
            ·
              refine ⟨2342699472372520338484631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561799648248346892323087 2342699472372520338484631)
              ·
                refine ⟨3514049208558780507726947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342699472372520338484631 3514049208558780507726947)
                ·
                  refine ⟨5271073812838170761590421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3514049208558780507726947 5271073812838170761590421)
                  ·
                    refine ⟨247081584976789254449551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5271073812838170761590421 247081584976789254449551)
                    ·
                      rfl

theorem cell23_1443569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 6].length) (baseStart_1443569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443569 prefixEnd_1443569 := by exact prefixLift 1443569
  have htrace : WordTrace (prefixWord ++ tailWord_1443569) baseStart_1443569 baseEnd_1443569 := by
    simpa [prefixWord, tailWord_1443569, baseEnd_1443569] using wordTrace_append hprefix tailTrace_1443569
  have hstable : (prefixWord ++ tailWord_1443569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443569).length < 2 ^ (prefixWord ++ tailWord_1443569).sum := by decide
  have hdescent : baseEnd_1443569 < baseStart_1443569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443604 : List Nat := [2, 4, 4, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_1443604 : Nat := 118140960795 + 1443604 * 2 ^ 59
def prefixEnd_1443604 : Nat := 4983230072969 + 3 ^ 40 * 1443604 * 2
def baseEnd_1443604 : Nat := 741262726753275126410993

theorem tailTrace_1443604 : CollatzResearch.WordTrace tailWord_1443604 prefixEnd_1443604 741262726753275126410993 := by
  unfold tailWord_1443604
  simp only [CollatzResearch.WordTrace]
  refine ⟨26326281731038365389812933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35101708974717820519750577 26326281731038365389812933)
  ·
    refine ⟨4936177824569693510589925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26326281731038365389812933 4936177824569693510589925)
    ·
      refine ⟨925533342106817533235611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4936177824569693510589925 925533342106817533235611)
      ·
        refine ⟨1388300013160226299853417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 925533342106817533235611 1388300013160226299853417)
        ·
          refine ⟨1041225009870169724890063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1388300013160226299853417 1041225009870169724890063)
          ·
            refine ⟨1561837514805254587335095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041225009870169724890063 1561837514805254587335095)
            ·
              refine ⟨2342756272207881881002643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561837514805254587335095 2342756272207881881002643)
              ·
                refine ⟨3514134408311822821503965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342756272207881881002643 3514134408311822821503965)
                ·
                  refine ⟨1317800403116933558063987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3514134408311822821503965 1317800403116933558063987)
                  ·
                    refine ⟨1976700604675400337095981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1317800403116933558063987 1976700604675400337095981)
                    ·
                      refine ⟨741262726753275126410993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1976700604675400337095981 741262726753275126410993)
                      ·
                        rfl

theorem cell23_1443604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_1443604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443604 prefixEnd_1443604 := by exact prefixLift 1443604
  have htrace : WordTrace (prefixWord ++ tailWord_1443604) baseStart_1443604 baseEnd_1443604 := by
    simpa [prefixWord, tailWord_1443604, baseEnd_1443604] using wordTrace_append hprefix tailTrace_1443604
  have hstable : (prefixWord ++ tailWord_1443604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443604).length < 2 ^ (prefixWord ++ tailWord_1443604).sum := by decide
  have hdescent : baseEnd_1443604 < baseStart_1443604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443612 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 2, 7]
def baseStart_1443612 : Nat := 118140960795 + 1443612 * 2 ^ 59
def prefixEnd_1443612 : Nat := 4983230072969 + 3 ^ 40 * 1443612 * 2
def baseEnd_1443612 : Nat := 247088944866170365036985

theorem tailTrace_1443612 : CollatzResearch.WordTrace tailWord_1443612 prefixEnd_1443612 247088944866170365036985 := by
  unfold tailWord_1443612
  simp only [CollatzResearch.WordTrace]
  refine ⟨26326427623023874072958545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35101903497365165430611393 26326427623023874072958545)
  ·
    refine ⟨19744820717267905554718909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26326427623023874072958545 19744820717267905554718909)
    ·
      refine ⟨7404307768975464583019591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19744820717267905554718909 7404307768975464583019591)
      ·
        refine ⟨11106461653463196874529387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7404307768975464583019591 11106461653463196874529387)
        ·
          refine ⟨16659692480194795311794081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11106461653463196874529387 16659692480194795311794081)
          ·
            refine ⟨12494769360146096483845561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16659692480194795311794081 12494769360146096483845561)
            ·
              refine ⟨9371077020109572362884171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12494769360146096483845561 9371077020109572362884171)
              ·
                refine ⟨14056615530164358544326257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9371077020109572362884171 14056615530164358544326257)
                ·
                  refine ⟨10542461647623268908244693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14056615530164358544326257 10542461647623268908244693)
                  ·
                    refine ⟨247088944866170365036985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10542461647623268908244693 247088944866170365036985)
                    ·
                      rfl

theorem cell23_1443612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_1443612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443612 prefixEnd_1443612 := by exact prefixLift 1443612
  have htrace : WordTrace (prefixWord ++ tailWord_1443612) baseStart_1443612 baseEnd_1443612 := by
    simpa [prefixWord, tailWord_1443612, baseEnd_1443612] using wordTrace_append hprefix tailTrace_1443612
  have hstable : (prefixWord ++ tailWord_1443612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443612).length < 2 ^ (prefixWord ++ tailWord_1443612).sum := by decide
  have hdescent : baseEnd_1443612 < baseStart_1443612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443630 : List Nat := [4, 1, 3, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_1443630 : Nat := 118140960795 + 1443630 * 2 ^ 59
def prefixEnd_1443630 : Nat := 4983230072969 + 3 ^ 40 * 1443630 * 2
def baseEnd_1443630 : Nat := 741276077250292024685873

theorem tailTrace_1443630 : CollatzResearch.WordTrace tailWord_1443630 prefixEnd_1443630 741276077250292024685873 := by
  unfold tailWord_1443630
  simp only [CollatzResearch.WordTrace]
  refine ⟨6581688969997817152509043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35102341173321691480048229 6581688969997817152509043)
  ·
    refine ⟨9872533454996725728763565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6581688969997817152509043 9872533454996725728763565)
    ·
      refine ⟨3702200045623772148286337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9872533454996725728763565 3702200045623772148286337)
      ·
        refine ⟨2776650034217829111214753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3702200045623772148286337 2776650034217829111214753)
        ·
          refine ⟨2082487525663371833411065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2776650034217829111214753 2082487525663371833411065)
          ·
            refine ⟨1561865644247528875058299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2082487525663371833411065 1561865644247528875058299)
            ·
              refine ⟨2342798466371293312587449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561865644247528875058299 2342798466371293312587449)
              ·
                refine ⟨1757098849778469984440587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2342798466371293312587449 1757098849778469984440587)
                ·
                  refine ⟨2635648274667704976660881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1757098849778469984440587 2635648274667704976660881)
                  ·
                    refine ⟨1976736206000778732495661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2635648274667704976660881 1976736206000778732495661)
                    ·
                      refine ⟨741276077250292024685873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1976736206000778732495661 741276077250292024685873)
                      ·
                        rfl

theorem cell23_1443630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_1443630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443630 prefixEnd_1443630 := by exact prefixLift 1443630
  have htrace : WordTrace (prefixWord ++ tailWord_1443630) baseStart_1443630 baseEnd_1443630 := by
    simpa [prefixWord, tailWord_1443630, baseEnd_1443630] using wordTrace_append hprefix tailTrace_1443630
  have hstable : (prefixWord ++ tailWord_1443630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443630).length < 2 ^ (prefixWord ++ tailWord_1443630).sum := by decide
  have hdescent : baseEnd_1443630 < baseStart_1443630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443653 : List Nat := [1, 3, 1, 1, 1, 2, 7, 1, 1, 3, 2]
def baseStart_1443653 : Nat := 118140960795 + 1443653 * 2 ^ 59
def prefixEnd_1443653 : Nat := 4983230072969 + 3 ^ 40 * 1443653 * 2
def baseEnd_1443653 : Nat := 741287887305345434698267

theorem tailTrace_1443653 : CollatzResearch.WordTrace tailWord_1443653 prefixEnd_1443653 741287887305345434698267 := by
  unfold tailWord_1443653
  simp only [CollatzResearch.WordTrace]
  refine ⟨52654350638899212148159613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35102900425932808098773075 52654350638899212148159613)
  ·
    refine ⟨19745381489587204555559855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52654350638899212148159613 19745381489587204555559855)
    ·
      refine ⟨29618072234380806833339783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19745381489587204555559855 29618072234380806833339783)
      ·
        refine ⟨44427108351571210250009675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29618072234380806833339783 44427108351571210250009675)
        ·
          refine ⟨66640662527356815375014513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44427108351571210250009675 66640662527356815375014513)
          ·
            refine ⟨49980496895517611531260885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66640662527356815375014513 49980496895517611531260885)
            ·
              refine ⟨1171417895988694020263927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 49980496895517611531260885 1171417895988694020263927)
              ·
                refine ⟨1757126843983041030395891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1171417895988694020263927 1757126843983041030395891)
                ·
                  refine ⟨2635690265974561545593837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1757126843983041030395891 2635690265974561545593837)
                  ·
                    refine ⟨988383849740460579597689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2635690265974561545593837 988383849740460579597689)
                    ·
                      refine ⟨741287887305345434698267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 988383849740460579597689 741287887305345434698267)
                      ·
                        rfl

theorem cell23_1443653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 1, 3, 2].length) (baseStart_1443653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443653 prefixEnd_1443653 := by exact prefixLift 1443653
  have htrace : WordTrace (prefixWord ++ tailWord_1443653) baseStart_1443653 baseEnd_1443653 := by
    simpa [prefixWord, tailWord_1443653, baseEnd_1443653] using wordTrace_append hprefix tailTrace_1443653
  have hstable : (prefixWord ++ tailWord_1443653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443653).length < 2 ^ (prefixWord ++ tailWord_1443653).sum := by decide
  have hdescent : baseEnd_1443653 < baseStart_1443653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443662 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_1443662 : Nat := 118140960795 + 1443662 * 2 ^ 59
def prefixEnd_1443662 : Nat := 4983230072969 + 3 ^ 40 * 1443662 * 2
def baseEnd_1443662 : Nat := 741292508631235899485725

theorem tailTrace_1443662 : CollatzResearch.WordTrace tailWord_1443662 prefixEnd_1443662 741292508631235899485725 := by
  unfold tailWord_1443662
  simp only [CollatzResearch.WordTrace]
  refine ⟨6581834861983325835654655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35103119263911071123491493 6581834861983325835654655)
  ·
    refine ⟨9872752292974988753481983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6581834861983325835654655 9872752292974988753481983)
    ·
      refine ⟨14809128439462483130222975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9872752292974988753481983 14809128439462483130222975)
      ·
        refine ⟨22213692659193724695334463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14809128439462483130222975 22213692659193724695334463)
        ·
          refine ⟨33320538988790587043001695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22213692659193724695334463 33320538988790587043001695)
          ·
            refine ⟨49980808483185880564502543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33320538988790587043001695 49980808483185880564502543)
            ·
              refine ⟨74971212724778820846753815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49980808483185880564502543 74971212724778820846753815)
              ·
                refine ⟨112456819087168231270130723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74971212724778820846753815 112456819087168231270130723)
                ·
                  refine ⟨168685228630752346905196085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112456819087168231270130723 168685228630752346905196085)
                  ·
                    refine ⟨15814240184133032522362133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 168685228630752346905196085 15814240184133032522362133)
                    ·
                      refine ⟨741292508631235899485725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15814240184133032522362133 741292508631235899485725)
                      ·
                        rfl

theorem cell23_1443662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_1443662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443662 prefixEnd_1443662 := by exact prefixLift 1443662
  have htrace : WordTrace (prefixWord ++ tailWord_1443662) baseStart_1443662 baseEnd_1443662 := by
    simpa [prefixWord, tailWord_1443662, baseEnd_1443662] using wordTrace_append hprefix tailTrace_1443662
  have hstable : (prefixWord ++ tailWord_1443662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443662).length < 2 ^ (prefixWord ++ tailWord_1443662).sum := by decide
  have hdescent : baseEnd_1443662 < baseStart_1443662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443669 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 2, 4, 3]
def baseStart_1443669 : Nat := 118140960795 + 1443669 * 2 ^ 59
def prefixEnd_1443669 : Nat := 4983230072969 + 3 ^ 40 * 1443669 * 2
def baseEnd_1443669 : Nat := 741296102995817372098193

theorem tailTrace_1443669 : CollatzResearch.WordTrace tailWord_1443669 prefixEnd_1443669 741296102995817372098193 := by
  unfold tailWord_1443669
  simp only [CollatzResearch.WordTrace]
  refine ⟨52654934206841246880742061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35103289471227497920494707 52654934206841246880742061)
  ·
    refine ⟨19745600327565467580278273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52654934206841246880742061 19745600327565467580278273)
    ·
      refine ⟨14809200245674100685208705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19745600327565467580278273 14809200245674100685208705)
      ·
        refine ⟨11106900184255575513906529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14809200245674100685208705 11106900184255575513906529)
        ·
          refine ⟨8330175138191681635429897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11106900184255575513906529 8330175138191681635429897)
          ·
            refine ⟨6247631353643761226572423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8330175138191681635429897 6247631353643761226572423)
            ·
              refine ⟨9371447030465641839858635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6247631353643761226572423 9371447030465641839858635)
              ·
                refine ⟨14057170545698462759787953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9371447030465641839858635 14057170545698462759787953)
                ·
                  refine ⟨10542877909273847069840965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14057170545698462759787953 10542877909273847069840965)
                  ·
                    refine ⟨1976789607988846325595181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10542877909273847069840965 1976789607988846325595181)
                    ·
                      refine ⟨741296102995817372098193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1976789607988846325595181 741296102995817372098193)
                      ·
                        rfl

theorem cell23_1443669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_1443669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443669 prefixEnd_1443669 := by exact prefixLift 1443669
  have htrace : WordTrace (prefixWord ++ tailWord_1443669) baseStart_1443669 baseEnd_1443669 := by
    simpa [prefixWord, tailWord_1443669, baseEnd_1443669] using wordTrace_append hprefix tailTrace_1443669
  have hstable : (prefixWord ++ tailWord_1443669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443669).length < 2 ^ (prefixWord ++ tailWord_1443669).sum := by decide
  have hdescent : baseEnd_1443669 < baseStart_1443669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443676 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 2, 6]
def baseStart_1443676 : Nat := 118140960795 + 1443676 * 2 ^ 59
def prefixEnd_1443676 : Nat := 4983230072969 + 3 ^ 40 * 1443676 * 2
def baseEnd_1443676 : Nat := 247099899120132948236887

theorem tailTrace_1443676 : CollatzResearch.WordTrace tailWord_1443676 prefixEnd_1443676 247099899120132948236887 := by
  unfold tailWord_1443676
  simp only [CollatzResearch.WordTrace]
  refine ⟨26327594758907943538123441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35103459678543924717497921 26327594758907943538123441)
  ·
    refine ⟨19745696069180957653592581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26327594758907943538123441 19745696069180957653592581)
    ·
      refine ⟨3702318012971429560048609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19745696069180957653592581 3702318012971429560048609)
      ·
        refine ⟨2776738509728572170036457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3702318012971429560048609 2776738509728572170036457)
        ·
          refine ⟨2082553882296429127527343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2776738509728572170036457 2082553882296429127527343)
          ·
            refine ⟨3123830823444643691291015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082553882296429127527343 3123830823444643691291015)
            ·
              refine ⟨4685746235166965536936523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3123830823444643691291015 4685746235166965536936523)
              ·
                refine ⟨7028619352750448305404785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4685746235166965536936523 7028619352750448305404785)
                ·
                  refine ⟨5271464514562836229053589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7028619352750448305404785 5271464514562836229053589)
                  ·
                    refine ⟨247099899120132948236887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5271464514562836229053589 247099899120132948236887)
                    ·
                      rfl

theorem cell23_1443676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_1443676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443676 prefixEnd_1443676 := by exact prefixLift 1443676
  have htrace : WordTrace (prefixWord ++ tailWord_1443676) baseStart_1443676 baseEnd_1443676 := by
    simpa [prefixWord, tailWord_1443676, baseEnd_1443676] using wordTrace_append hprefix tailTrace_1443676
  have hstable : (prefixWord ++ tailWord_1443676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443676).length < 2 ^ (prefixWord ++ tailWord_1443676).sum := by decide
  have hdescent : baseEnd_1443676 < baseStart_1443676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443679 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 4]
def baseStart_1443679 : Nat := 118140960795 + 1443679 * 2 ^ 59
def prefixEnd_1443679 : Nat := 4983230072969 + 3 ^ 40 * 1443679 * 2
def baseEnd_1443679 : Nat := 741301237802362332973147

theorem tailTrace_1443679 : CollatzResearch.WordTrace tailWord_1443679 prefixEnd_1443679 741301237802362332973147 := by
  unfold tailWord_1443679
  simp only [CollatzResearch.WordTrace]
  refine ⟨52655298936805018588606091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35103532624536679059070727 52655298936805018588606091)
  ·
    refine ⟨78982948405207527882909137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52655298936805018588606091 78982948405207527882909137)
    ·
      refine ⟨59237211303905645912181853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78982948405207527882909137 59237211303905645912181853)
      ·
        refine ⟨22213954238964617217068195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59237211303905645912181853 22213954238964617217068195)
        ·
          refine ⟨33320931358446925825602293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22213954238964617217068195 33320931358446925825602293)
          ·
            refine ⟨3123837314854399296150215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33320931358446925825602293 3123837314854399296150215)
            ·
              refine ⟨4685755972281598944225323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3123837314854399296150215 4685755972281598944225323)
              ·
                refine ⟨7028633958422398416337985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4685755972281598944225323 7028633958422398416337985)
                ·
                  refine ⟨5271475468816798812253489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7028633958422398416337985 5271475468816798812253489)
                  ·
                    refine ⟨3953606601612599109190117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5271475468816798812253489 3953606601612599109190117)
                    ·
                      refine ⟨741301237802362332973147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3953606601612599109190117 741301237802362332973147)
                      ·
                        rfl

theorem cell23_1443679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_1443679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443679 prefixEnd_1443679 := by exact prefixLift 1443679
  have htrace : WordTrace (prefixWord ++ tailWord_1443679) baseStart_1443679 baseEnd_1443679 := by
    simpa [prefixWord, tailWord_1443679, baseEnd_1443679] using wordTrace_append hprefix tailTrace_1443679
  have hstable : (prefixWord ++ tailWord_1443679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443679).length < 2 ^ (prefixWord ++ tailWord_1443679).sum := by decide
  have hdescent : baseEnd_1443679 < baseStart_1443679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443683 : List Nat := [1, 1, 1, 5, 4, 1, 2, 1, 1, 4, 2]
def baseStart_1443683 : Nat := 118140960795 + 1443683 * 2 ^ 59
def prefixEnd_1443683 : Nat := 4983230072969 + 3 ^ 40 * 1443683 * 2
def baseEnd_1443683 : Nat := 741303291724980317323129

theorem tailTrace_1443683 : CollatzResearch.WordTrace tailWord_1443683 prefixEnd_1443683 741303291724980317323129 := by
  unfold tailWord_1443683
  simp only [CollatzResearch.WordTrace]
  refine ⟨52655444828790527271751703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35103629885860351514501135 52655444828790527271751703)
  ·
    refine ⟨78983167243185790907627555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52655444828790527271751703 78983167243185790907627555)
    ·
      refine ⟨118474750864778686361441333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78983167243185790907627555 118474750864778686361441333)
      ·
        refine ⟨11107007893573001846385125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118474750864778686361441333 11107007893573001846385125)
        ·
          refine ⟨2082563980044937846197211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11107007893573001846385125 2082563980044937846197211)
          ·
            refine ⟨3123845970067406769295817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082563980044937846197211 3123845970067406769295817)
            ·
              refine ⟨2342884477550555076971863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3123845970067406769295817 2342884477550555076971863)
              ·
                refine ⟨3514326716325832615457795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342884477550555076971863 3514326716325832615457795)
                ·
                  refine ⟨5271490074488748923186693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3514326716325832615457795 5271490074488748923186693)
                  ·
                    refine ⟨988404388966640423097505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5271490074488748923186693 988404388966640423097505)
                    ·
                      refine ⟨741303291724980317323129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 988404388966640423097505 741303291724980317323129)
                      ·
                        rfl

theorem cell23_1443683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_1443683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443683 prefixEnd_1443683 := by exact prefixLift 1443683
  have htrace : WordTrace (prefixWord ++ tailWord_1443683) baseStart_1443683 baseEnd_1443683 := by
    simpa [prefixWord, tailWord_1443683, baseEnd_1443683] using wordTrace_append hprefix tailTrace_1443683
  have hstable : (prefixWord ++ tailWord_1443683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443683).length < 2 ^ (prefixWord ++ tailWord_1443683).sum := by decide
  have hdescent : baseEnd_1443683 < baseStart_1443683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443734 : List Nat := [5, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_1443734 : Nat := 118140960795 + 1443734 * 2 ^ 59
def prefixEnd_1443734 : Nat := 4983230072969 + 3 ^ 40 * 1443734 * 2
def baseEnd_1443734 : Nat := 741329479238359617785395

theorem tailTrace_1443734 : CollatzResearch.WordTrace tailWord_1443734 prefixEnd_1443734 741329479238359617785395 := by
  unfold tailWord_1443734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3291081559475360186366141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35104869967737175321238837 3291081559475360186366141)
  ·
    refine ⟨1234155584803260069887303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3291081559475360186366141 1234155584803260069887303)
    ·
      refine ⟨1851233377204890104830955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1234155584803260069887303 1851233377204890104830955)
      ·
        refine ⟨2776850065807335157246433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1851233377204890104830955 2776850065807335157246433)
        ·
          refine ⟨2082637549355501367934825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2776850065807335157246433 2082637549355501367934825)
          ·
            refine ⟨1561978162016626025951119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2082637549355501367934825 1561978162016626025951119)
            ·
              refine ⟨2342967243024939038926679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561978162016626025951119 2342967243024939038926679)
              ·
                refine ⟨3514450864537408558390019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342967243024939038926679 3514450864537408558390019)
                ·
                  refine ⟨5271676296806112837585029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3514450864537408558390019 5271676296806112837585029)
                  ·
                    refine ⟨988439305651146157047193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5271676296806112837585029 988439305651146157047193)
                    ·
                      refine ⟨741329479238359617785395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 988439305651146157047193 741329479238359617785395)
                      ·
                        rfl

theorem cell23_1443734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_1443734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443734 prefixEnd_1443734 := by exact prefixLift 1443734
  have htrace : WordTrace (prefixWord ++ tailWord_1443734) baseStart_1443734 baseEnd_1443734 := by
    simpa [prefixWord, tailWord_1443734, baseEnd_1443734] using wordTrace_append hprefix tailTrace_1443734
  have hstable : (prefixWord ++ tailWord_1443734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443734).length < 2 ^ (prefixWord ++ tailWord_1443734).sum := by decide
  have hdescent : baseEnd_1443734 < baseStart_1443734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443759 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 3]
def baseStart_1443759 : Nat := 118140960795 + 1443759 * 2 ^ 59
def prefixEnd_1443759 : Nat := 4983230072969 + 3 ^ 40 * 1443759 * 2
def baseEnd_1443759 : Nat := 741342316254722019972779

theorem tailTrace_1443759 : CollatzResearch.WordTrace tailWord_1443759 prefixEnd_1443759 741342316254722019972779 := by
  unfold tailWord_1443759
  simp only [CollatzResearch.WordTrace]
  refine ⟨52658216776515192251518331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35105477851010128167678887 52658216776515192251518331)
  ·
    refine ⟨78987325164772788377277497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52658216776515192251518331 78987325164772788377277497)
    ·
      refine ⟨59240493873579591282958123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78987325164772788377277497 59240493873579591282958123)
      ·
        refine ⟨88860740810369386924437185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59240493873579591282958123 88860740810369386924437185)
        ·
          refine ⟨66645555607777040193327889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88860740810369386924437185 66645555607777040193327889)
          ·
            refine ⟨49984166705832780144995917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66645555607777040193327889 49984166705832780144995917)
            ·
              refine ⟨18744062514687292554373469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49984166705832780144995917 18744062514687292554373469)
              ·
                refine ⟨7029023443007734707890051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18744062514687292554373469 7029023443007734707890051)
                ·
                  refine ⟨10543535164511602061835077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7029023443007734707890051 10543535164511602061835077)
                  ·
                    refine ⟨1976912843345925386594077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10543535164511602061835077 1976912843345925386594077)
                    ·
                      refine ⟨741342316254722019972779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1976912843345925386594077 741342316254722019972779)
                      ·
                        rfl

theorem cell23_1443759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 3].length) (baseStart_1443759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443759 prefixEnd_1443759 := by exact prefixLift 1443759
  have htrace : WordTrace (prefixWord ++ tailWord_1443759) baseStart_1443759 baseEnd_1443759 := by
    simpa [prefixWord, tailWord_1443759, baseEnd_1443759] using wordTrace_append hprefix tailTrace_1443759
  have hstable : (prefixWord ++ tailWord_1443759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443759).length < 2 ^ (prefixWord ++ tailWord_1443759).sum := by decide
  have hdescent : baseEnd_1443759 < baseStart_1443759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443776 : List Nat := [2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 3]
def baseStart_1443776 : Nat := 118140960795 + 1443776 * 2 ^ 59
def prefixEnd_1443776 : Nat := 4983230072969 + 3 ^ 40 * 1443776 * 2
def baseEnd_1443776 : Nat := 741351045425848453460201

theorem tailTrace_1443776 : CollatzResearch.WordTrace tailWord_1443776 prefixEnd_1443776 741351045425848453460201 := by
  unfold tailWord_1443776
  simp only [CollatzResearch.WordTrace]
  refine ⟨26329418408726802077443591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35105891211635736103258121 26329418408726802077443591)
  ·
    refine ⟨39494127613090203116165387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26329418408726802077443591 39494127613090203116165387)
    ·
      refine ⟨59241191419635304674248081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39494127613090203116165387 59241191419635304674248081)
      ·
        refine ⟨44430893564726478505686061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59241191419635304674248081 44430893564726478505686061)
        ·
          refine ⟨16661585086772429439632273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44430893564726478505686061 16661585086772429439632273)
          ·
            refine ⟨12496188815079322079724205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16661585086772429439632273 12496188815079322079724205)
            ·
              refine ⟨4686070805654745779896577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12496188815079322079724205 4686070805654745779896577)
              ·
                refine ⟨3514553104241059334922433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4686070805654745779896577 3514553104241059334922433)
                ·
                  refine ⟨2635914828180794501191825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3514553104241059334922433 2635914828180794501191825)
                  ·
                    refine ⟨1976936121135595875893869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2635914828180794501191825 1976936121135595875893869)
                    ·
                      refine ⟨741351045425848453460201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1976936121135595875893869 741351045425848453460201)
                      ·
                        rfl

theorem cell23_1443776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_1443776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443776 prefixEnd_1443776 := by exact prefixLift 1443776
  have htrace : WordTrace (prefixWord ++ tailWord_1443776) baseStart_1443776 baseEnd_1443776 := by
    simpa [prefixWord, tailWord_1443776, baseEnd_1443776] using wordTrace_append hprefix tailTrace_1443776
  have hstable : (prefixWord ++ tailWord_1443776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443776).length < 2 ^ (prefixWord ++ tailWord_1443776).sum := by decide
  have hdescent : baseEnd_1443776 < baseStart_1443776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1443796 : List Nat := [2, 4, 1, 2, 1, 1, 3, 3, 6]
def baseStart_1443796 : Nat := 118140960795 + 1443796 * 2 ^ 59
def prefixEnd_1443796 : Nat := 4983230072969 + 3 ^ 40 * 1443796 * 2
def baseEnd_1443796 : Nat := 82373479448770930578901

theorem tailTrace_1443796 : CollatzResearch.WordTrace tailWord_1443796 prefixEnd_1443796 82373479448770930578901 := by
  unfold tailWord_1443796
  simp only [CollatzResearch.WordTrace]
  refine ⟨26329783138690573785307621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35106377518254098380410161 26329783138690573785307621)
  ·
    refine ⟨4936834338504482584745179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26329783138690573785307621 4936834338504482584745179)
    ·
      refine ⟨7405251507756723877117769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4936834338504482584745179 7405251507756723877117769)
      ·
        refine ⟨5553938630817542907838327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7405251507756723877117769 5553938630817542907838327)
        ·
          refine ⟨8330907946226314361757491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5553938630817542907838327 8330907946226314361757491)
          ·
            refine ⟨12496361919339471542636237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8330907946226314361757491 12496361919339471542636237)
            ·
              refine ⟨4686135719752301828488589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12496361919339471542636237 4686135719752301828488589)
              ·
                refine ⟨1757300894907113185683221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4686135719752301828488589 1757300894907113185683221)
                ·
                  refine ⟨82373479448770930578901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1757300894907113185683221 82373479448770930578901)
                  ·
                    rfl

theorem cell23_1443796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_1443796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1443796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1443796 prefixEnd_1443796 := by exact prefixLift 1443796
  have htrace : WordTrace (prefixWord ++ tailWord_1443796) baseStart_1443796 baseEnd_1443796 := by
    simpa [prefixWord, tailWord_1443796, baseEnd_1443796] using wordTrace_append hprefix tailTrace_1443796
  have hstable : (prefixWord ++ tailWord_1443796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1443796).length < 2 ^ (prefixWord ++ tailWord_1443796).sum := by decide
  have hdescent : baseEnd_1443796 < baseStart_1443796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1443796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
