import V185TrunkScan23Chunk1060

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6280746 : List Nat := [3, 1, 4, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_6280746 : Nat := 118140960795 + 6280746 * 2 ^ 59
def prefixEnd_6280746 : Nat := 4983230072969 + 3 ^ 40 * 6280746 * 2
def baseEnd_6280746 : Nat := 3225041566803788786090381

theorem tailTrace_6280746 : CollatzResearch.WordTrace tailWord_6280746 prefixEnd_6280746 3225041566803788786090381 := by
  unfold tailWord_6280746
  simp only [CollatzResearch.WordTrace]
  refine ⟨57269406525984345715651523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152718417402624921908404061 57269406525984345715651523)
  ·
    refine ⟨85904109788976518573477285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57269406525984345715651523 85904109788976518573477285)
    ·
      refine ⟨16107020585433097232526991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85904109788976518573477285 16107020585433097232526991)
      ·
        refine ⟨24160530878149645848790487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16107020585433097232526991 24160530878149645848790487)
        ·
          refine ⟨36240796317224468773185731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24160530878149645848790487 36240796317224468773185731)
          ·
            refine ⟨54361194475836703159778597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36240796317224468773185731 54361194475836703159778597)
            ·
              refine ⟨10192723964219381842458487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54361194475836703159778597 10192723964219381842458487)
              ·
                refine ⟨15289085946329072763687731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10192723964219381842458487 15289085946329072763687731)
                ·
                  refine ⟨22933628919493609145531597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15289085946329072763687731 22933628919493609145531597)
                  ·
                    refine ⟨8600110844810103429574349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22933628919493609145531597 8600110844810103429574349)
                    ·
                      refine ⟨3225041566803788786090381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8600110844810103429574349 3225041566803788786090381)
                      ·
                        rfl

theorem cell23_6280746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_6280746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280746 prefixEnd_6280746 := by exact prefixLift 6280746
  have htrace : WordTrace (prefixWord ++ tailWord_6280746) baseStart_6280746 baseEnd_6280746 := by
    simpa [prefixWord, tailWord_6280746, baseEnd_6280746] using wordTrace_append hprefix tailTrace_6280746
  have hstable : (prefixWord ++ tailWord_6280746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280746).length < 2 ^ (prefixWord ++ tailWord_6280746).sum := by decide
  have hdescent : baseEnd_6280746 < baseStart_6280746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280752 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 4]
def baseStart_6280752 : Nat := 118140960795 + 6280752 * 2 ^ 59
def prefixEnd_6280752 : Nat := 4983230072969 + 3 ^ 40 * 6280752 * 2
def baseEnd_6280752 : Nat := 3225044647687715762615353

theorem tailTrace_6280752 : CollatzResearch.WordTrace tailWord_6280752 prefixEnd_6280752 3225044647687715762615353 := by
  unfold tailWord_6280752
  simp only [CollatzResearch.WordTrace]
  refine ⟨114538922470957822943662255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152718563294610430591549673 114538922470957822943662255)
  ·
    refine ⟨171808383706436734415493383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114538922470957822943662255 171808383706436734415493383)
    ·
      refine ⟨257712575559655101623240075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171808383706436734415493383 257712575559655101623240075)
      ·
        refine ⟨386568863339482652434860113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257712575559655101623240075 386568863339482652434860113)
        ·
          refine ⟨289926647504611989326145085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386568863339482652434860113 289926647504611989326145085)
          ·
            refine ⟨108722492814229495997304407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289926647504611989326145085 108722492814229495997304407)
            ·
              refine ⟨163083739221344243995956611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108722492814229495997304407 163083739221344243995956611)
              ·
                refine ⟨244625608832016365993934917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163083739221344243995956611 244625608832016365993934917)
                ·
                  refine ⟨45867301656003068623862797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 244625608832016365993934917 45867301656003068623862797)
                  ·
                    refine ⟨17200238121001150733948549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45867301656003068623862797 17200238121001150733948549)
                    ·
                      refine ⟨3225044647687715762615353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17200238121001150733948549 3225044647687715762615353)
                      ·
                        rfl

theorem cell23_6280752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 4].length) (baseStart_6280752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280752 prefixEnd_6280752 := by exact prefixLift 6280752
  have htrace : WordTrace (prefixWord ++ tailWord_6280752) baseStart_6280752 baseEnd_6280752 := by
    simpa [prefixWord, tailWord_6280752, baseEnd_6280752] using wordTrace_append hprefix tailTrace_6280752
  have hstable : (prefixWord ++ tailWord_6280752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280752).length < 2 ^ (prefixWord ++ tailWord_6280752).sum := by decide
  have hdescent : baseEnd_6280752 < baseStart_6280752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280762 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 1, 8]
def baseStart_6280762 : Nat := 118140960795 + 6280762 * 2 ^ 59
def prefixEnd_6280762 : Nat := 4983230072969 + 3 ^ 40 * 6280762 * 2
def baseEnd_6280762 : Nat := 1075016594164753574496769

theorem tailTrace_6280762 : CollatzResearch.WordTrace tailWord_6280762 prefixEnd_6280762 1075016594164753574496769 := by
  unfold tailWord_6280762
  simp only [CollatzResearch.WordTrace]
  refine ⟨57269552417969854398797135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152718806447919611730125693 57269552417969854398797135)
  ·
    refine ⟨85904328626954781598195703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57269552417969854398797135 85904328626954781598195703)
    ·
      refine ⟨128856492940432172397293555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85904328626954781598195703 128856492940432172397293555)
      ·
        refine ⟨193284739410648258595940333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128856492940432172397293555 193284739410648258595940333)
        ·
          refine ⟨72481777278993096973477625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193284739410648258595940333 72481777278993096973477625)
          ·
            refine ⟨54361332959244822730108219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72481777278993096973477625 54361332959244822730108219)
            ·
              refine ⟨81541999438867234095162329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54361332959244822730108219 81541999438867234095162329)
              ·
                refine ⟨61156499579150425571371747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81541999438867234095162329 61156499579150425571371747)
                ·
                  refine ⟨91734749368725638357057621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61156499579150425571371747 91734749368725638357057621)
                  ·
                    refine ⟨1075016594164753574496769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91734749368725638357057621 1075016594164753574496769)
                    ·
                      rfl

theorem cell23_6280762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_6280762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280762 prefixEnd_6280762 := by exact prefixLift 6280762
  have htrace : WordTrace (prefixWord ++ tailWord_6280762) baseStart_6280762 baseEnd_6280762 := by
    simpa [prefixWord, tailWord_6280762, baseEnd_6280762] using wordTrace_append hprefix tailTrace_6280762
  have hstable : (prefixWord ++ tailWord_6280762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280762).length < 2 ^ (prefixWord ++ tailWord_6280762).sum := by decide
  have hdescent : baseEnd_6280762 < baseStart_6280762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280797 : List Nat := [1, 4, 4, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_6280797 : Nat := 118140960795 + 6280797 * 2 ^ 59
def prefixEnd_6280797 : Nat := 4983230072969 + 3 ^ 40 * 6280797 * 2
def baseEnd_6280797 : Nat := 3225067754317168086552647

theorem tailTrace_6280797 : CollatzResearch.WordTrace tailWord_6280797 prefixEnd_6280797 3225067754317168086552647 := by
  unfold tailWord_6280797
  simp only [CollatzResearch.WordTrace]
  refine ⟨229079486226752618572712645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152719657484501745715141763 229079486226752618572712645)
  ·
    refine ⟨42952403667516115982383621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229079486226752618572712645 42952403667516115982383621)
    ·
      refine ⟨8053575687659271746696929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42952403667516115982383621 8053575687659271746696929)
      ·
        refine ⟨6040181765744453810022697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8053575687659271746696929 6040181765744453810022697)
        ·
          refine ⟨4530136324308340357517023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6040181765744453810022697 4530136324308340357517023)
          ·
            refine ⟨6795204486462510536275535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4530136324308340357517023 6795204486462510536275535)
            ·
              refine ⟨10192806729693765804413303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6795204486462510536275535 10192806729693765804413303)
              ·
                refine ⟨15289210094540648706619955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10192806729693765804413303 15289210094540648706619955)
                ·
                  refine ⟨22933815141810973059929933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15289210094540648706619955 22933815141810973059929933)
                  ·
                    refine ⟨8600180678179114897473725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22933815141810973059929933 8600180678179114897473725)
                    ·
                      refine ⟨3225067754317168086552647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8600180678179114897473725 3225067754317168086552647)
                      ·
                        rfl

theorem cell23_6280797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_6280797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280797 prefixEnd_6280797 := by exact prefixLift 6280797
  have htrace : WordTrace (prefixWord ++ tailWord_6280797) baseStart_6280797 baseEnd_6280797 := by
    simpa [prefixWord, tailWord_6280797, baseEnd_6280797] using wordTrace_append hprefix tailTrace_6280797
  have hstable : (prefixWord ++ tailWord_6280797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280797).length < 2 ^ (prefixWord ++ tailWord_6280797).sum := by decide
  have hdescent : baseEnd_6280797 < baseStart_6280797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280803 : List Nat := [1, 1, 1, 5, 1, 5, 1, 1, 1, 4, 2]
def baseStart_6280803 : Nat := 118140960795 + 6280803 * 2 ^ 59
def prefixEnd_6280803 : Nat := 4983230072969 + 3 ^ 40 * 6280803 * 2
def baseEnd_6280803 : Nat := 3225070835201095063077619

theorem tailTrace_6280803 : CollatzResearch.WordTrace tailWord_6280803 prefixEnd_6280803 3225070835201095063077619 := by
  unfold tailWord_6280803
  simp only [CollatzResearch.WordTrace]
  refine ⟨229079705064730881597431063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152719803376487254398287375 229079705064730881597431063)
  ·
    refine ⟨343619557597096322396146595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229079705064730881597431063 343619557597096322396146595)
    ·
      refine ⟨515429336395644483594219893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343619557597096322396146595 515429336395644483594219893)
      ·
        refine ⟨48321500287091670336958115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 515429336395644483594219893 48321500287091670336958115)
        ·
          refine ⟨72482250430637505505437173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48321500287091670336958115 72482250430637505505437173)
          ·
            refine ⟨6795210977872266141134735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72482250430637505505437173 6795210977872266141134735)
            ·
              refine ⟨10192816466808399211702103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6795210977872266141134735 10192816466808399211702103)
              ·
                refine ⟨15289224700212598817553155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10192816466808399211702103 15289224700212598817553155)
                ·
                  refine ⟨22933837050318898226329733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15289224700212598817553155 22933837050318898226329733)
                  ·
                    refine ⟨4300094446934793417436825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22933837050318898226329733 4300094446934793417436825)
                    ·
                      refine ⟨3225070835201095063077619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4300094446934793417436825 3225070835201095063077619)
                      ·
                        rfl

theorem cell23_6280803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_6280803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280803 prefixEnd_6280803 := by exact prefixLift 6280803
  have htrace : WordTrace (prefixWord ++ tailWord_6280803) baseStart_6280803 baseEnd_6280803 := by
    simpa [prefixWord, tailWord_6280803, baseEnd_6280803] using wordTrace_append hprefix tailTrace_6280803
  have hstable : (prefixWord ++ tailWord_6280803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280803).length < 2 ^ (prefixWord ++ tailWord_6280803).sum := by decide
  have hdescent : baseEnd_6280803 < baseStart_6280803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280839 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 4, 5]
def baseStart_6280839 : Nat := 118140960795 + 6280839 * 2 ^ 59
def prefixEnd_6280839 : Nat := 4983230072969 + 3 ^ 40 * 6280839 * 2
def baseEnd_6280839 : Nat := 1075029773501552307409151

theorem tailTrace_6280839 : CollatzResearch.WordTrace tailWord_6280839 prefixEnd_6280839 1075029773501552307409151 := by
  unfold tailWord_6280839
  simp only [CollatzResearch.WordTrace]
  refine ⟨229081018092600459745741571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152720678728400306497161047 229081018092600459745741571)
  ·
    refine ⟨343621527138900689618612357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229081018092600459745741571 343621527138900689618612357)
    ·
      refine ⟨64429036338543879303489817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 343621527138900689618612357 64429036338543879303489817)
      ·
        refine ⟨48321777253907909477617363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64429036338543879303489817 48321777253907909477617363)
        ·
          refine ⟨72482665880861864216426045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48321777253907909477617363 72482665880861864216426045)
          ·
            refine ⟨27180999705323199081159767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72482665880861864216426045 27180999705323199081159767)
            ·
              refine ⟨40771499557984798621739651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27180999705323199081159767 40771499557984798621739651)
              ·
                refine ⟨61157249336977197932609477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40771499557984798621739651 61157249336977197932609477)
                ·
                  refine ⟨11466984250683224612364277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61157249336977197932609477 11466984250683224612364277)
                  ·
                    refine ⟨1075029773501552307409151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11466984250683224612364277 1075029773501552307409151)
                    ·
                      rfl

theorem cell23_6280839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_6280839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280839 prefixEnd_6280839 := by exact prefixLift 6280839
  have htrace : WordTrace (prefixWord ++ tailWord_6280839) baseStart_6280839 baseEnd_6280839 := by
    simpa [prefixWord, tailWord_6280839, baseEnd_6280839] using wordTrace_append hprefix tailTrace_6280839
  have hstable : (prefixWord ++ tailWord_6280839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280839).length < 2 ^ (prefixWord ++ tailWord_6280839).sum := by decide
  have hdescent : baseEnd_6280839 < baseStart_6280839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280896 : List Nat := [2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 3]
def baseStart_6280896 : Nat := 118140960795 + 6280896 * 2 ^ 59
def prefixEnd_6280896 : Nat := 4983230072969 + 3 ^ 40 * 6280896 * 2
def baseEnd_6280896 : Nat := 3225118588901963199214691

theorem tailTrace_6280896 : CollatzResearch.WordTrace tailWord_6280896 prefixEnd_6280896 3225118588901963199214691 := by
  unfold tailWord_6280896
  simp only [CollatzResearch.WordTrace]
  refine ⟨114541548526696979240283271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152722064702262638987044361 114541548526696979240283271)
  ·
    refine ⟨171812322790045468860424907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114541548526696979240283271 171812322790045468860424907)
    ·
      refine ⟨257718484185068203290637361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171812322790045468860424907 257718484185068203290637361)
      ·
        refine ⟨193288863138801152467978021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257718484185068203290637361 193288863138801152467978021)
        ·
          refine ⟨36241661838525216087745879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193288863138801152467978021 36241661838525216087745879)
          ·
            refine ⟨54362492757787824131618819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36241661838525216087745879 54362492757787824131618819)
            ·
              refine ⟨81543739136681736197428229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54362492757787824131618819 81543739136681736197428229)
              ·
                refine ⟨15289451088127825537017793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81543739136681736197428229 15289451088127825537017793)
                ·
                  refine ⟨11467088316095869152763345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15289451088127825537017793 11467088316095869152763345)
                  ·
                    refine ⟨8600316237071901864572509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11467088316095869152763345 8600316237071901864572509)
                    ·
                      refine ⟨3225118588901963199214691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8600316237071901864572509 3225118588901963199214691)
                      ·
                        rfl

theorem cell23_6280896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_6280896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280896 prefixEnd_6280896 := by exact prefixLift 6280896
  have htrace : WordTrace (prefixWord ++ tailWord_6280896) baseStart_6280896 baseEnd_6280896 := by
    simpa [prefixWord, tailWord_6280896, baseEnd_6280896] using wordTrace_append hprefix tailTrace_6280896
  have hstable : (prefixWord ++ tailWord_6280896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280896).length < 2 ^ (prefixWord ++ tailWord_6280896).sum := by decide
  have hdescent : baseEnd_6280896 < baseStart_6280896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280903 : List Nat := [1, 1, 4, 1, 1, 1, 5, 4, 1, 4]
def baseStart_6280903 : Nat := 118140960795 + 6280903 * 2 ^ 59
def prefixEnd_6280903 : Nat := 4983230072969 + 3 ^ 40 * 6280903 * 2
def baseEnd_6280903 : Nat := 1075040727755514890609053

theorem tailTrace_6280903 : CollatzResearch.WordTrace tailWord_6280903 prefixEnd_6280903 1075040727755514890609053 := by
  unfold tailWord_6280903
  simp only [CollatzResearch.WordTrace]
  refine ⟨229083352364368598676071363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152722234909579065784047575 229083352364368598676071363)
  ·
    refine ⟨343625028546552898014107045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229083352364368598676071363 343625028546552898014107045)
    ·
      refine ⟨64429692852478668377645071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 343625028546552898014107045 64429692852478668377645071)
      ·
        refine ⟨96644539278718002566467607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64429692852478668377645071 96644539278718002566467607)
        ·
          refine ⟨144966808918077003849701411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96644539278718002566467607 144966808918077003849701411)
          ·
            refine ⟨217450213377115505774552117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144966808918077003849701411 217450213377115505774552117)
            ·
              refine ⟨20385957504104578666364261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 217450213377115505774552117 20385957504104578666364261)
              ·
                refine ⟨3822367032019608499943299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20385957504104578666364261 3822367032019608499943299)
                ·
                  refine ⟨5733550548029412749914949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3822367032019608499943299 5733550548029412749914949)
                  ·
                    refine ⟨1075040727755514890609053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5733550548029412749914949 1075040727755514890609053)
                    ·
                      rfl

theorem cell23_6280903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_6280903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280903 prefixEnd_6280903 := by exact prefixLift 6280903
  have htrace : WordTrace (prefixWord ++ tailWord_6280903) baseStart_6280903 baseEnd_6280903 := by
    simpa [prefixWord, tailWord_6280903, baseEnd_6280903] using wordTrace_append hprefix tailTrace_6280903
  have hstable : (prefixWord ++ tailWord_6280903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280903).length < 2 ^ (prefixWord ++ tailWord_6280903).sum := by decide
  have hdescent : baseEnd_6280903 < baseStart_6280903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280959 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 3, 6]
def baseStart_6280959 : Nat := 118140960795 + 6280959 * 2 ^ 59
def prefixEnd_6280959 : Nat := 4983230072969 + 3 ^ 40 * 6280959 * 2
def baseEnd_6280959 : Nat := 1075050312727732150908967

theorem tailTrace_6280959 : CollatzResearch.WordTrace tailWord_6280959 prefixEnd_6280959 1075050312727732150908967 := by
  unfold tailWord_6280959
  simp only [CollatzResearch.WordTrace]
  refine ⟨229085394852165720240109931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152723596568110480160073287 229085394852165720240109931)
  ·
    refine ⟨343628092278248580360164897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229085394852165720240109931 343628092278248580360164897)
    ·
      refine ⟨257721069208686435270123673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343628092278248580360164897 257721069208686435270123673)
      ·
        refine ⟨193290801906514826452592755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257721069208686435270123673 193290801906514826452592755)
        ·
          refine ⟨289936202859772239678889133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193290801906514826452592755 289936202859772239678889133)
          ·
            refine ⟨108726076072414589879583425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289936202859772239678889133 108726076072414589879583425)
            ·
              refine ⟨81544557054310942409687569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108726076072414589879583425 81544557054310942409687569)
              ·
                refine ⟨61158417790733206807265677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81544557054310942409687569 61158417790733206807265677)
                ·
                  refine ⟨22934406671524952552724629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61158417790733206807265677 22934406671524952552724629)
                  ·
                    refine ⟨1075050312727732150908967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22934406671524952552724629 1075050312727732150908967)
                    ·
                      rfl

theorem cell23_6280959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 6].length) (baseStart_6280959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280959 prefixEnd_6280959 := by exact prefixLift 6280959
  have htrace : WordTrace (prefixWord ++ tailWord_6280959) baseStart_6280959 baseEnd_6280959 := by
    simpa [prefixWord, tailWord_6280959, baseEnd_6280959] using wordTrace_append hprefix tailTrace_6280959
  have hstable : (prefixWord ++ tailWord_6280959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280959).length < 2 ^ (prefixWord ++ tailWord_6280959).sum := by decide
  have hdescent : baseEnd_6280959 < baseStart_6280959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280983 : List Nat := [1, 1, 3, 4, 2, 1, 1, 4, 1, 1, 4]
def baseStart_6280983 : Nat := 118140960795 + 6280983 * 2 ^ 59
def prefixEnd_6280983 : Nat := 4983230072969 + 3 ^ 40 * 6280983 * 2
def baseEnd_6280983 : Nat := 3225163261718904358826791

theorem tailTrace_6280983 : CollatzResearch.WordTrace tailWord_6280983 prefixEnd_6280983 3225163261718904358826791 := by
  unfold tailWord_6280983
  simp only [CollatzResearch.WordTrace]
  refine ⟨229086270204078772338983603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152724180136052514892655735 229086270204078772338983603)
  ·
    refine ⟨343629405306118158508475405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229086270204078772338983603 343629405306118158508475405)
    ·
      refine ⟨128861026989794309440678277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343629405306118158508475405 128861026989794309440678277)
      ·
        refine ⟨24161442560586433020127177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128861026989794309440678277 24161442560586433020127177)
        ·
          refine ⟨18121081920439824765095383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24161442560586433020127177 18121081920439824765095383)
          ·
            refine ⟨27181622880659737147643075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18121081920439824765095383 27181622880659737147643075)
            ·
              refine ⟨40772434320989605721464613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27181622880659737147643075 40772434320989605721464613)
              ·
                refine ⟨7644831435185551072774615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40772434320989605721464613 7644831435185551072774615)
                ·
                  refine ⟨11467247152778326609161923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7644831435185551072774615 11467247152778326609161923)
                  ·
                    refine ⟨17200870729167489913742885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11467247152778326609161923 17200870729167489913742885)
                    ·
                      refine ⟨3225163261718904358826791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17200870729167489913742885 3225163261718904358826791)
                      ·
                        rfl

theorem cell23_6280983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_6280983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280983 prefixEnd_6280983 := by exact prefixLift 6280983
  have htrace : WordTrace (prefixWord ++ tailWord_6280983) baseStart_6280983 baseEnd_6280983 := by
    simpa [prefixWord, tailWord_6280983, baseEnd_6280983] using wordTrace_append hprefix tailTrace_6280983
  have hstable : (prefixWord ++ tailWord_6280983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280983).length < 2 ^ (prefixWord ++ tailWord_6280983).sum := by decide
  have hdescent : baseEnd_6280983 < baseStart_6280983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281030 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_6281030 : Nat := 118140960795 + 6281030 * 2 ^ 59
def prefixEnd_6281030 : Nat := 4983230072969 + 3 ^ 40 * 6281030 * 2
def baseEnd_6281030 : Nat := 3225187395309665674939075

theorem tailTrace_6281030 : CollatzResearch.WordTrace tailWord_6281030 prefixEnd_6281030 3225187395309665674939075 := by
  unfold tailWord_6281030
  simp only [CollatzResearch.WordTrace]
  refine ⟨7158999513590890605185767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 152725322956605666243963029 7158999513590890605185767)
  ·
    refine ⟨10738499270386335907778651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7158999513590890605185767 10738499270386335907778651)
    ·
      refine ⟨16107748905579503861667977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10738499270386335907778651 16107748905579503861667977)
      ·
        refine ⟨12080811679184627896250983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16107748905579503861667977 12080811679184627896250983)
        ·
          refine ⟨18121217518776941844376475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12080811679184627896250983 18121217518776941844376475)
          ·
            refine ⟨27181826278165412766564713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18121217518776941844376475 27181826278165412766564713)
            ·
              refine ⟨20386369708624059574923535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27181826278165412766564713 20386369708624059574923535)
              ·
                refine ⟨30579554562936089362385303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20386369708624059574923535 30579554562936089362385303)
                ·
                  refine ⟨45869331844404134043577955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30579554562936089362385303 45869331844404134043577955)
                  ·
                    refine ⟨68803997766606201065366933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45869331844404134043577955 68803997766606201065366933)
                    ·
                      refine ⟨3225187395309665674939075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68803997766606201065366933 3225187395309665674939075)
                      ·
                        rfl

theorem cell23_6281030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_6281030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281030 prefixEnd_6281030 := by exact prefixLift 6281030
  have htrace : WordTrace (prefixWord ++ tailWord_6281030) baseStart_6281030 baseEnd_6281030 := by
    simpa [prefixWord, tailWord_6281030, baseEnd_6281030] using wordTrace_append hprefix tailTrace_6281030
  have hstable : (prefixWord ++ tailWord_6281030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281030).length < 2 ^ (prefixWord ++ tailWord_6281030).sum := by decide
  have hdescent : baseEnd_6281030 < baseStart_6281030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281037 : List Nat := [1, 6, 1, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_6281037 : Nat := 118140960795 + 6281037 * 2 ^ 59
def prefixEnd_6281037 : Nat := 4983230072969 + 3 ^ 40 * 6281037 * 2
def baseEnd_6281037 : Nat := 3225190989674247147551543

theorem tailTrace_6281037 : CollatzResearch.WordTrace tailWord_6281037 prefixEnd_6281037 3225190989674247147551543 := by
  unfold tailWord_6281037
  simp only [CollatzResearch.WordTrace]
  refine ⟨229088239745883139561449365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152725493163922093040966243 229088239745883139561449365)
  ·
    refine ⟨10738511238088272166942939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 229088239745883139561449365 10738511238088272166942939)
    ·
      refine ⟨16107766857132408250414409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10738511238088272166942939 16107766857132408250414409)
      ·
        refine ⟨12080825142849306187810807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16107766857132408250414409 12080825142849306187810807)
        ·
          refine ⟨18121237714273959281716211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12080825142849306187810807 18121237714273959281716211)
          ·
            refine ⟨27181856571410938922574317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18121237714273959281716211 27181856571410938922574317)
            ·
              refine ⟨10193196214279102095965369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27181856571410938922574317 10193196214279102095965369)
              ·
                refine ⟨7644897160709326571974027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10193196214279102095965369 7644897160709326571974027)
                ·
                  refine ⟨11467345741063989857961041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7644897160709326571974027 11467345741063989857961041)
                  ·
                    refine ⟨8600509305797992393470781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11467345741063989857961041 8600509305797992393470781)
                    ·
                      refine ⟨3225190989674247147551543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8600509305797992393470781 3225190989674247147551543)
                      ·
                        rfl

theorem cell23_6281037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_6281037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281037 prefixEnd_6281037 := by exact prefixLift 6281037
  have htrace : WordTrace (prefixWord ++ tailWord_6281037) baseStart_6281037 baseEnd_6281037 := by
    simpa [prefixWord, tailWord_6281037, baseEnd_6281037] using wordTrace_append hprefix tailTrace_6281037
  have hstable : (prefixWord ++ tailWord_6281037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281037).length < 2 ^ (prefixWord ++ tailWord_6281037).sum := by decide
  have hdescent : baseEnd_6281037 < baseStart_6281037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281073 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 3, 4, 2]
def baseStart_6281073 : Nat := 118140960795 + 6281073 * 2 ^ 59
def prefixEnd_6281073 : Nat := 4983230072969 + 3 ^ 40 * 6281073 * 2
def baseEnd_6281073 : Nat := 3225209474977809006701377

theorem tailTrace_6281073 : CollatzResearch.WordTrace tailWord_6281073 prefixEnd_6281073 3225209474977809006701377 := by
  unfold tailWord_6281073
  simp only [CollatzResearch.WordTrace]
  refine ⟨229089552773752717709759873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152726368515835145139839915 229089552773752717709759873)
  ·
    refine ⟨171817164580314538282319905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229089552773752717709759873 171817164580314538282319905)
    ·
      refine ⟨128862873435235903711739929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171817164580314538282319905 128862873435235903711739929)
      ·
        refine ⟨96647155076426927783804947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128862873435235903711739929 96647155076426927783804947)
        ·
          refine ⟨144970732614640391675707421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96647155076426927783804947 144970732614640391675707421)
          ·
            refine ⟨54364024730490146878390283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144970732614640391675707421 54364024730490146878390283)
            ·
              refine ⟨81546037095735220317585425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54364024730490146878390283 81546037095735220317585425)
              ·
                refine ⟨61159527821801415238189069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81546037095735220317585425 61159527821801415238189069)
                ·
                  refine ⟨22934822933175530714320901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61159527821801415238189069 22934822933175530714320901)
                  ·
                    refine ⟨4300279299970412008935169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22934822933175530714320901 4300279299970412008935169)
                    ·
                      refine ⟨3225209474977809006701377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4300279299970412008935169 3225209474977809006701377)
                      ·
                        rfl

theorem cell23_6281073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_6281073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281073 prefixEnd_6281073 := by exact prefixLift 6281073
  have htrace : WordTrace (prefixWord ++ tailWord_6281073) baseStart_6281073 baseEnd_6281073 := by
    simpa [prefixWord, tailWord_6281073, baseEnd_6281073] using wordTrace_append hprefix tailTrace_6281073
  have hstable : (prefixWord ++ tailWord_6281073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281073).length < 2 ^ (prefixWord ++ tailWord_6281073).sum := by decide
  have hdescent : baseEnd_6281073 < baseStart_6281073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281113 : List Nat := [1, 2, 1, 2, 1, 3, 3, 5, 5]
def baseStart_6281113 : Nat := 118140960795 + 6281113 * 2 ^ 59
def prefixEnd_6281113 : Nat := 4983230072969 + 3 ^ 40 * 6281113 * 2
def baseEnd_6281113 : Nat := 358358890467109872244577

theorem tailTrace_6281113 : CollatzResearch.WordTrace tailWord_6281113 prefixEnd_6281113 358358890467109872244577 := by
  unfold tailWord_6281113
  simp only [CollatzResearch.WordTrace]
  refine ⟨229091011693607804541215993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152727341129071869694143995 229091011693607804541215993)
  ·
    refine ⟨171818258770205853405911995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229091011693607804541215993 171818258770205853405911995)
    ·
      refine ⟨257727388155308780108867993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171818258770205853405911995 257727388155308780108867993)
      ·
        refine ⟨193295541116481585081650995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257727388155308780108867993 193295541116481585081650995)
        ·
          refine ⟨289943311674722377622476493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193295541116481585081650995 289943311674722377622476493)
          ·
            refine ⟨108728741878020891608428685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289943311674722377622476493 108728741878020891608428685)
            ·
              refine ⟨40773278204257834353160757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108728741878020891608428685 40773278204257834353160757)
              ·
                refine ⟨3822494831649171970608821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40773278204257834353160757 3822494831649171970608821)
                ·
                  refine ⟨358358890467109872244577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3822494831649171970608821 358358890467109872244577)
                  ·
                    rfl

theorem cell23_6281113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 5].length) (baseStart_6281113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281113 prefixEnd_6281113 := by exact prefixLift 6281113
  have htrace : WordTrace (prefixWord ++ tailWord_6281113) baseStart_6281113 baseEnd_6281113 := by
    simpa [prefixWord, tailWord_6281113, baseEnd_6281113] using wordTrace_append hprefix tailTrace_6281113
  have hstable : (prefixWord ++ tailWord_6281113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281113).length < 2 ^ (prefixWord ++ tailWord_6281113).sum := by decide
  have hdescent : baseEnd_6281113 < baseStart_6281113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281118 : List Nat := [4, 3, 1, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_6281118 : Nat := 118140960795 + 6281118 * 2 ^ 59
def prefixEnd_6281118 : Nat := 4983230072969 + 3 ^ 40 * 6281118 * 2
def baseEnd_6281118 : Nat := 3225232581607261330638671

theorem tailTrace_6281118 : CollatzResearch.WordTrace tailWord_6281118 prefixEnd_6281118 3225232581607261330638671 := by
  unfold tailWord_6281118
  simp only [CollatzResearch.WordTrace]
  refine ⟨28636399257323711299393501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152727462705726460263432005 28636399257323711299393501)
  ·
    refine ⟨10738649721496391737272563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28636399257323711299393501 10738649721496391737272563)
    ·
      refine ⟨16107974582244587605908845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10738649721496391737272563 16107974582244587605908845)
      ·
        refine ⟨6040490468341720352215817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16107974582244587605908845 6040490468341720352215817)
        ·
          refine ⟨4530367851256290264161863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6040490468341720352215817 4530367851256290264161863)
          ·
            refine ⟨6795551776884435396242795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4530367851256290264161863 6795551776884435396242795)
            ·
              refine ⟨10193327665326653094364193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6795551776884435396242795 10193327665326653094364193)
              ·
                refine ⟨7644995748994989820773145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10193327665326653094364193 7644995748994989820773145)
                ·
                  refine ⟨5733746811746242365579859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7644995748994989820773145 5733746811746242365579859)
                  ·
                    refine ⟨8600620217619363548369789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5733746811746242365579859 8600620217619363548369789)
                    ·
                      refine ⟨3225232581607261330638671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8600620217619363548369789 3225232581607261330638671)
                      ·
                        rfl

theorem cell23_6281118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_6281118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281118 prefixEnd_6281118 := by exact prefixLift 6281118
  have htrace : WordTrace (prefixWord ++ tailWord_6281118) baseStart_6281118 baseEnd_6281118 := by
    simpa [prefixWord, tailWord_6281118, baseEnd_6281118] using wordTrace_append hprefix tailTrace_6281118
  have hstable : (prefixWord ++ tailWord_6281118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281118).length < 2 ^ (prefixWord ++ tailWord_6281118).sum := by decide
  have hdescent : baseEnd_6281118 < baseStart_6281118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281124 : List Nat := [2, 3, 1, 2, 1, 5, 1, 2, 2, 2, 2]
def baseStart_6281124 : Nat := 118140960795 + 6281124 * 2 ^ 59
def prefixEnd_6281124 : Nat := 4983230072969 + 3 ^ 40 * 6281124 * 2
def baseEnd_6281124 : Nat := 3225235662491188307163643

theorem tailTrace_6281124 : CollatzResearch.WordTrace tailWord_6281124 prefixEnd_6281124 3225235662491188307163643 := by
  unfold tailWord_6281124
  simp only [CollatzResearch.WordTrace]
  refine ⟨114545706448283976709933213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152727608597711968946577617 114545706448283976709933213)
  ·
    refine ⟨42954639918106491266224955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114545706448283976709933213 42954639918106491266224955)
    ·
      refine ⟨64431959877159736899337433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42954639918106491266224955 64431959877159736899337433)
      ·
        refine ⟨48323969907869802674503075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64431959877159736899337433 48323969907869802674503075)
        ·
          refine ⟨72485954861804704011754613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48323969907869802674503075 72485954861804704011754613)
          ·
            refine ⟨6795558268294191001101995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72485954861804704011754613 6795558268294191001101995)
            ·
              refine ⟨10193337402441286501652993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6795558268294191001101995 10193337402441286501652993)
              ·
                refine ⟨7645003051830964876239745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10193337402441286501652993 7645003051830964876239745)
                ·
                  refine ⟨5733752288873223657179809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7645003051830964876239745 5733752288873223657179809)
                  ·
                    refine ⟨4300314216654917742884857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5733752288873223657179809 4300314216654917742884857)
                    ·
                      refine ⟨3225235662491188307163643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4300314216654917742884857 3225235662491188307163643)
                      ·
                        rfl

theorem cell23_6281124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_6281124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281124 prefixEnd_6281124 := by exact prefixLift 6281124
  have htrace : WordTrace (prefixWord ++ tailWord_6281124) baseStart_6281124 baseEnd_6281124 := by
    simpa [prefixWord, tailWord_6281124, baseEnd_6281124] using wordTrace_append hprefix tailTrace_6281124
  have hstable : (prefixWord ++ tailWord_6281124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281124).length < 2 ^ (prefixWord ++ tailWord_6281124).sum := by decide
  have hdescent : baseEnd_6281124 < baseStart_6281124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281163 : List Nat := [1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 4]
def baseStart_6281163 : Nat := 118140960795 + 6281163 * 2 ^ 59
def prefixEnd_6281163 : Nat := 4983230072969 + 3 ^ 40 * 6281163 * 2
def baseEnd_6281163 : Nat := 3225255688236713654575963

theorem tailTrace_6281163 : CollatzResearch.WordTrace tailWord_6281163 prefixEnd_6281163 3225255688236713654575963 := by
  unfold tailWord_6281163
  simp only [CollatzResearch.WordTrace]
  refine ⟨229092835343426663080536143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152728556895617775387024095 229092835343426663080536143)
  ·
    refine ⟨343639253015139994620804215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229092835343426663080536143 343639253015139994620804215)
    ·
      refine ⟨515458879522709991931206323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343639253015139994620804215 515458879522709991931206323)
      ·
        refine ⟨773188319284064987896809485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515458879522709991931206323 773188319284064987896809485)
        ·
          refine ⟨289945619731524370461303557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 773188319284064987896809485 289945619731524370461303557)
          ·
            refine ⟨54364803699660819461494417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 289945619731524370461303557 54364803699660819461494417)
            ·
              refine ⟨40773602774745614596120813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54364803699660819461494417 40773602774745614596120813)
              ·
                refine ⟨15290101040529605473545305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40773602774745614596120813 15290101040529605473545305)
                ·
                  refine ⟨11467575780397204105158979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15290101040529605473545305 11467575780397204105158979)
                  ·
                    refine ⟨17201363670595806157738469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11467575780397204105158979 17201363670595806157738469)
                    ·
                      refine ⟨3225255688236713654575963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17201363670595806157738469 3225255688236713654575963)
                      ·
                        rfl

theorem cell23_6281163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 4].length) (baseStart_6281163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281163 prefixEnd_6281163 := by exact prefixLift 6281163
  have htrace : WordTrace (prefixWord ++ tailWord_6281163) baseStart_6281163 baseEnd_6281163 := by
    simpa [prefixWord, tailWord_6281163, baseEnd_6281163] using wordTrace_append hprefix tailTrace_6281163
  have hstable : (prefixWord ++ tailWord_6281163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281163).length < 2 ^ (prefixWord ++ tailWord_6281163).sum := by decide
  have hdescent : baseEnd_6281163 < baseStart_6281163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281213 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 2, 5, 3]
def baseStart_6281213 : Nat := 118140960795 + 6281213 * 2 ^ 59
def prefixEnd_6281213 : Nat := 4983230072969 + 3 ^ 40 * 6281213 * 2
def baseEnd_6281213 : Nat := 3225281362269438458950733

theorem tailTrace_6281213 : CollatzResearch.WordTrace tailWord_6281213 prefixEnd_6281213 3225281362269438458950733 := by
  unfold tailWord_6281213
  simp only [CollatzResearch.WordTrace]
  refine ⟨229094658993245521619856293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152729772662163681079904195 229094658993245521619856293)
  ·
    refine ⟨42955248561233535303723055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229094658993245521619856293 42955248561233535303723055)
    ·
      refine ⟨64432872841850302955584583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42955248561233535303723055 64432872841850302955584583)
      ·
        refine ⟨96649309262775454433376875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64432872841850302955584583 96649309262775454433376875)
        ·
          refine ⟨144973963894163181650065313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96649309262775454433376875 144973963894163181650065313)
          ·
            refine ⟨108730472920622386237548985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144973963894163181650065313 108730472920622386237548985)
            ·
              refine ⟨81547854690466789678161739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108730472920622386237548985 81547854690466789678161739)
              ·
                refine ⟨122321782035700184517242609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81547854690466789678161739 122321782035700184517242609)
                ·
                  refine ⟨91741336526775138387931957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122321782035700184517242609 91741336526775138387931957)
                  ·
                    refine ⟨8600750299385169223868621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91741336526775138387931957 8600750299385169223868621)
                    ·
                      refine ⟨3225281362269438458950733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8600750299385169223868621 3225281362269438458950733)
                      ·
                        rfl

theorem cell23_6281213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_6281213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281213 prefixEnd_6281213 := by exact prefixLift 6281213
  have htrace : WordTrace (prefixWord ++ tailWord_6281213) baseStart_6281213 baseEnd_6281213 := by
    simpa [prefixWord, tailWord_6281213, baseEnd_6281213] using wordTrace_append hprefix tailTrace_6281213
  have hstable : (prefixWord ++ tailWord_6281213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281213).length < 2 ^ (prefixWord ++ tailWord_6281213).sum := by decide
  have hdescent : baseEnd_6281213 < baseStart_6281213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281281 : List Nat := [1, 2, 5, 1, 2, 2, 2, 3, 1, 1, 3]
def baseStart_6281281 : Nat := 118140960795 + 6281281 * 2 ^ 59
def prefixEnd_6281281 : Nat := 4983230072969 + 3 ^ 40 * 6281281 * 2
def baseEnd_6281281 : Nat := 3225316278953944192900421

theorem tailTrace_6281281 : CollatzResearch.WordTrace tailWord_6281281 prefixEnd_6281281 3225316278953944192900421 := by
  unfold tailWord_6281281
  simp only [CollatzResearch.WordTrace]
  refine ⟨229097139156999169233331697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152731426104666112822221131 229097139156999169233331697)
  ·
    refine ⟨171822854367749376924998773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229097139156999169233331697 171822854367749376924998773)
    ·
      refine ⟨16108392596976504086718635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171822854367749376924998773 16108392596976504086718635)
      ·
        refine ⟨24162588895464756130077953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16108392596976504086718635 24162588895464756130077953)
        ·
          refine ⟨18121941671598567097558465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24162588895464756130077953 18121941671598567097558465)
          ·
            refine ⟨13591456253698925323168849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18121941671598567097558465 13591456253698925323168849)
            ·
              refine ⟨10193592190274193992376637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13591456253698925323168849 10193592190274193992376637)
              ·
                refine ⟨3822597071352822747141239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10193592190274193992376637 3822597071352822747141239)
                ·
                  refine ⟨5733895607029234120711859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3822597071352822747141239 5733895607029234120711859)
                  ·
                    refine ⟨8600843410543851181067789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5733895607029234120711859 8600843410543851181067789)
                    ·
                      refine ⟨3225316278953944192900421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8600843410543851181067789 3225316278953944192900421)
                      ·
                        rfl

theorem cell23_6281281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_6281281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281281 prefixEnd_6281281 := by exact prefixLift 6281281
  have htrace : WordTrace (prefixWord ++ tailWord_6281281) baseStart_6281281 baseEnd_6281281 := by
    simpa [prefixWord, tailWord_6281281, baseEnd_6281281] using wordTrace_append hprefix tailTrace_6281281
  have hstable : (prefixWord ++ tailWord_6281281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281281).length < 2 ^ (prefixWord ++ tailWord_6281281).sum := by decide
  have hdescent : baseEnd_6281281 < baseStart_6281281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281283 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 4]
def baseStart_6281283 : Nat := 118140960795 + 6281283 * 2 ^ 59
def prefixEnd_6281283 : Nat := 4983230072969 + 3 ^ 40 * 6281283 * 2
def baseEnd_6281283 : Nat := 3225317305915253185075411

theorem tailTrace_6281283 : CollatzResearch.WordTrace tailWord_6281283 prefixEnd_6281283 3225317305915253185075411 := by
  unfold tailWord_6281283
  simp only [CollatzResearch.WordTrace]
  refine ⟨229097212102991923574904503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152731474735327949049936335 229097212102991923574904503)
  ·
    refine ⟨343645818154487885362356755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229097212102991923574904503 343645818154487885362356755)
    ·
      refine ⟨515468727231731828043535133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343645818154487885362356755 515468727231731828043535133)
      ·
        refine ⟨193300772711899435516325675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 515468727231731828043535133 193300772711899435516325675)
        ·
          refine ⟨289951159067849153274488513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193300772711899435516325675 289951159067849153274488513)
          ·
            refine ⟨217463369300886864955866385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289951159067849153274488513 217463369300886864955866385)
            ·
              refine ⟨163097526975665148716899789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217463369300886864955866385 163097526975665148716899789)
              ·
                refine ⟨61161572615874430768837421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163097526975665148716899789 61161572615874430768837421)
                ·
                  refine ⟨22935589730952911538314033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61161572615874430768837421 22935589730952911538314033)
                  ·
                    refine ⟨17201692298214683653735525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22935589730952911538314033 17201692298214683653735525)
                    ·
                      refine ⟨3225317305915253185075411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17201692298214683653735525 3225317305915253185075411)
                      ·
                        rfl

theorem cell23_6281283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_6281283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281283 prefixEnd_6281283 := by exact prefixLift 6281283
  have htrace : WordTrace (prefixWord ++ tailWord_6281283) baseStart_6281283 baseEnd_6281283 := by
    simpa [prefixWord, tailWord_6281283, baseEnd_6281283] using wordTrace_append hprefix tailTrace_6281283
  have hstable : (prefixWord ++ tailWord_6281283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281283).length < 2 ^ (prefixWord ++ tailWord_6281283).sum := by decide
  have hdescent : baseEnd_6281283 < baseStart_6281283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281287 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 5, 2, 2]
def baseStart_6281287 : Nat := 118140960795 + 6281287 * 2 ^ 59
def prefixEnd_6281287 : Nat := 4983230072969 + 3 ^ 40 * 6281287 * 2
def baseEnd_6281287 : Nat := 3225319359837871169425393

theorem tailTrace_6281287 : CollatzResearch.WordTrace tailWord_6281287 prefixEnd_6281287 3225319359837871169425393 := by
  unfold tailWord_6281287
  simp only [CollatzResearch.WordTrace]
  refine ⟨229097357994977432258050115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152731571996651621505366743 229097357994977432258050115)
  ·
    refine ⟨343646036992466148387075173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229097357994977432258050115 343646036992466148387075173)
    ·
      refine ⟨64433631936087402822576595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 343646036992466148387075173 64433631936087402822576595)
      ·
        refine ⟨96650447904131104233864893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64433631936087402822576595 96650447904131104233864893)
        ·
          refine ⟨36243917964049164087699335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96650447904131104233864893 36243917964049164087699335)
          ·
            refine ⟨54365876946073746131549003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36243917964049164087699335 54365876946073746131549003)
            ·
              refine ⟨81548815419110619197323505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54365876946073746131549003 81548815419110619197323505)
              ·
                refine ⟨61161611564332964397992629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81548815419110619197323505 61161611564332964397992629)
                ·
                  refine ⟨5733901084156215412311809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61161611564332964397992629 5733901084156215412311809)
                  ·
                    refine ⟨4300425813117161559233857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5733901084156215412311809 4300425813117161559233857)
                    ·
                      refine ⟨3225319359837871169425393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4300425813117161559233857 3225319359837871169425393)
                      ·
                        rfl

theorem cell23_6281287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_6281287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281287 prefixEnd_6281287 := by exact prefixLift 6281287
  have htrace : WordTrace (prefixWord ++ tailWord_6281287) baseStart_6281287 baseEnd_6281287 := by
    simpa [prefixWord, tailWord_6281287, baseEnd_6281287] using wordTrace_append hprefix tailTrace_6281287
  have hstable : (prefixWord ++ tailWord_6281287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281287).length < 2 ^ (prefixWord ++ tailWord_6281287).sum := by decide
  have hdescent : baseEnd_6281287 < baseStart_6281287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281304 : List Nat := [2, 1, 2, 2, 1, 5, 2, 1, 3, 2, 2]
def baseStart_6281304 : Nat := 118140960795 + 6281304 * 2 ^ 59
def prefixEnd_6281304 : Nat := 4983230072969 + 3 ^ 40 * 6281304 * 2
def baseEnd_6281304 : Nat := 3225328089008997602912815

theorem tailTrace_6281304 : CollatzResearch.WordTrace tailWord_6281304 prefixEnd_6281304 3225328089008997602912815 := by
  unfold tailWord_6281304
  simp only [CollatzResearch.WordTrace]
  refine ⟨114548989017957922080709483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152731985357277229440945977 114548989017957922080709483)
  ·
    refine ⟨171823483526936883121064225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114548989017957922080709483 171823483526936883121064225)
    ·
      refine ⟨128867612645202662340798169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171823483526936883121064225 128867612645202662340798169)
      ·
        refine ⟨96650709483901996755598627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128867612645202662340798169 96650709483901996755598627)
        ·
          refine ⟨144976064225852995133397941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96650709483901996755598627 144976064225852995133397941)
          ·
            refine ⟨13591506021173718293756057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 144976064225852995133397941 13591506021173718293756057)
            ·
              refine ⟨10193629515880288720317043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13591506021173718293756057 10193629515880288720317043)
              ·
                refine ⟨15290444273820433080475565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10193629515880288720317043 15290444273820433080475565)
                ·
                  refine ⟨5733916602682662405178337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15290444273820433080475565 5733916602682662405178337)
                  ·
                    refine ⟨4300437452011996803883753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5733916602682662405178337 4300437452011996803883753)
                    ·
                      refine ⟨3225328089008997602912815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4300437452011996803883753 3225328089008997602912815)
                      ·
                        rfl

theorem cell23_6281304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_6281304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281304 prefixEnd_6281304 := by exact prefixLift 6281304
  have htrace : WordTrace (prefixWord ++ tailWord_6281304) baseStart_6281304 baseEnd_6281304 := by
    simpa [prefixWord, tailWord_6281304, baseEnd_6281304] using wordTrace_append hprefix tailTrace_6281304
  have hstable : (prefixWord ++ tailWord_6281304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281304).length < 2 ^ (prefixWord ++ tailWord_6281304).sum := by decide
  have hdescent : baseEnd_6281304 < baseStart_6281304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281314 : List Nat := [3, 3, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_6281314 : Nat := 118140960795 + 6281314 * 2 ^ 59
def prefixEnd_6281314 : Nat := 4983230072969 + 3 ^ 40 * 6281314 * 2
def baseEnd_6281314 : Nat := 1075111074605180854595923

theorem tailTrace_6281314 : CollatzResearch.WordTrace tailWord_6281314 prefixEnd_6281314 1075111074605180854595923 := by
  unfold tailWord_6281314
  simp only [CollatzResearch.WordTrace]
  refine ⟨57274585691469903967320749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152732228510586410579521997 57274585691469903967320749)
  ·
    refine ⟨21477969634301213987745281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57274585691469903967320749 21477969634301213987745281)
    ·
      refine ⟨16108477225725910490808961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21477969634301213987745281 16108477225725910490808961)
      ·
        refine ⟨12081357919294432868106721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16108477225725910490808961 12081357919294432868106721)
        ·
          refine ⟨9061018439470824651080041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12081357919294432868106721 9061018439470824651080041)
          ·
            refine ⟨6795763829603118488310031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9061018439470824651080041 6795763829603118488310031)
            ·
              refine ⟨10193645744404677732465047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6795763829603118488310031 10193645744404677732465047)
              ·
                refine ⟨15290468616607016598697571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10193645744404677732465047 15290468616607016598697571)
                ·
                  refine ⟨22935702924910524898046357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15290468616607016598697571 22935702924910524898046357)
                  ·
                    refine ⟨1075111074605180854595923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22935702924910524898046357 1075111074605180854595923)
                    ·
                      rfl

theorem cell23_6281314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_6281314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281314 prefixEnd_6281314 := by exact prefixLift 6281314
  have htrace : WordTrace (prefixWord ++ tailWord_6281314) baseStart_6281314 baseEnd_6281314 := by
    simpa [prefixWord, tailWord_6281314, baseEnd_6281314] using wordTrace_append hprefix tailTrace_6281314
  have hstable : (prefixWord ++ tailWord_6281314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281314).length < 2 ^ (prefixWord ++ tailWord_6281314).sum := by decide
  have hdescent : baseEnd_6281314 < baseStart_6281314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281317 : List Nat := [1, 3, 1, 3, 2, 4, 1, 1, 1, 2, 4]
def baseStart_6281317 : Nat := 118140960795 + 6281317 * 2 ^ 59
def prefixEnd_6281317 : Nat := 4983230072969 + 3 ^ 40 * 6281317 * 2
def baseEnd_6281317 : Nat := 3225334764257506052050255

theorem tailTrace_6281317 : CollatzResearch.WordTrace tailWord_6281317 prefixEnd_6281317 3225334764257506052050255 := by
  unfold tailWord_6281317
  simp only [CollatzResearch.WordTrace]
  refine ⟨229098452184868747381642205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152732301456579164921094803 229098452184868747381642205)
  ·
    refine ⟨85911919569325780268115827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229098452184868747381642205 85911919569325780268115827)
    ·
      refine ⟨128867879353988670402173741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85911919569325780268115827 128867879353988670402173741)
      ·
        refine ⟨48325454757745751400815153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128867879353988670402173741 48325454757745751400815153)
        ·
          refine ⟨36244091068309313550611365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48325454757745751400815153 36244091068309313550611365)
          ·
            refine ⟨6795767075307996290739631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36244091068309313550611365 6795767075307996290739631)
            ·
              refine ⟨10193650612961994436109447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6795767075307996290739631 10193650612961994436109447)
              ·
                refine ⟨15290475919442991654164171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10193650612961994436109447 15290475919442991654164171)
                ·
                  refine ⟨22935713879164487481246257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15290475919442991654164171 22935713879164487481246257)
                  ·
                    refine ⟨17201785409373365610934693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22935713879164487481246257 17201785409373365610934693)
                    ·
                      refine ⟨3225334764257506052050255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17201785409373365610934693 3225334764257506052050255)
                      ·
                        rfl

theorem cell23_6281317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_6281317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281317 prefixEnd_6281317 := by exact prefixLift 6281317
  have htrace : WordTrace (prefixWord ++ tailWord_6281317) baseStart_6281317 baseEnd_6281317 := by
    simpa [prefixWord, tailWord_6281317, baseEnd_6281317] using wordTrace_append hprefix tailTrace_6281317
  have hstable : (prefixWord ++ tailWord_6281317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281317).length < 2 ^ (prefixWord ++ tailWord_6281317).sum := by decide
  have hdescent : baseEnd_6281317 < baseStart_6281317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281337 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 4, 1, 3]
def baseStart_6281337 : Nat := 118140960795 + 6281337 * 2 ^ 59
def prefixEnd_6281337 : Nat := 4983230072969 + 3 ^ 40 * 6281337 * 2
def baseEnd_6281337 : Nat := 3225345033870595973800163

theorem tailTrace_6281337 : CollatzResearch.WordTrace tailWord_6281337 prefixEnd_6281337 3225345033870595973800163 := by
  unfold tailWord_6281337
  simp only [CollatzResearch.WordTrace]
  refine ⟨229099181644796290797370265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152732787763197527198246843 229099181644796290797370265)
  ·
    refine ⟨171824386233597218098027699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229099181644796290797370265 171824386233597218098027699)
    ·
      refine ⟨257736579350395827147041549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171824386233597218098027699 257736579350395827147041549)
      ·
        refine ⟨96651217256398435180140581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257736579350395827147041549 96651217256398435180140581)
        ·
          refine ⟨18122103235574706596276359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96651217256398435180140581 18122103235574706596276359)
          ·
            refine ⟨27183154853362059894414539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18122103235574706596276359 27183154853362059894414539)
            ·
              refine ⟨40774732280043089841621809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27183154853362059894414539 40774732280043089841621809)
              ·
                refine ⟨30581049210032317381216357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40774732280043089841621809 30581049210032317381216357)
                ·
                  refine ⟨5733946726881059508978067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30581049210032317381216357 5733946726881059508978067)
                  ·
                    refine ⟨8600920090321589263467101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5733946726881059508978067 8600920090321589263467101)
                    ·
                      refine ⟨3225345033870595973800163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8600920090321589263467101 3225345033870595973800163)
                      ·
                        rfl

theorem cell23_6281337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_6281337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281337 prefixEnd_6281337 := by exact prefixLift 6281337
  have htrace : WordTrace (prefixWord ++ tailWord_6281337) baseStart_6281337 baseEnd_6281337 := by
    simpa [prefixWord, tailWord_6281337, baseEnd_6281337] using wordTrace_append hprefix tailTrace_6281337
  have hstable : (prefixWord ++ tailWord_6281337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281337).length < 2 ^ (prefixWord ++ tailWord_6281337).sum := by decide
  have hdescent : baseEnd_6281337 < baseStart_6281337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281363 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 5]
def baseStart_6281363 : Nat := 118140960795 + 6281363 * 2 ^ 59
def prefixEnd_6281363 : Nat := 4983230072969 + 3 ^ 40 * 6281363 * 2
def baseEnd_6281363 : Nat := 3225358384367612872075043

theorem tailTrace_6281363 : CollatzResearch.WordTrace tailWord_6281363 prefixEnd_6281363 3225358384367612872075043 := by
  unfold tailWord_6281363
  simp only [CollatzResearch.WordTrace]
  refine ⟨229100129942702097237816743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152733419961801398158544495 229100129942702097237816743)
  ·
    refine ⟨343650194914053145856725115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229100129942702097237816743 343650194914053145856725115)
    ·
      refine ⟨515475292371079718785087673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343650194914053145856725115 515475292371079718785087673)
      ·
        refine ⟨386606469278309789088815755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 515475292371079718785087673 386606469278309789088815755)
        ·
          refine ⟨579909703917464683633223633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386606469278309789088815755 579909703917464683633223633)
          ·
            refine ⟨434932277938098512724917725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 579909703917464683633223633 434932277938098512724917725)
            ·
              refine ⟨163099604226786942271844147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 434932277938098512724917725 163099604226786942271844147)
              ·
                refine ⟨244649406340180413407766221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163099604226786942271844147 244649406340180413407766221)
                ·
                  refine ⟨91743527377567655027912333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244649406340180413407766221 91743527377567655027912333)
                  ·
                    refine ⟨34403822766587870635467125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91743527377567655027912333 34403822766587870635467125)
                    ·
                      refine ⟨3225358384367612872075043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34403822766587870635467125 3225358384367612872075043)
                      ·
                        rfl

theorem cell23_6281363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_6281363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281363 prefixEnd_6281363 := by exact prefixLift 6281363
  have htrace : WordTrace (prefixWord ++ tailWord_6281363) baseStart_6281363 baseEnd_6281363 := by
    simpa [prefixWord, tailWord_6281363, baseEnd_6281363] using wordTrace_append hprefix tailTrace_6281363
  have hstable : (prefixWord ++ tailWord_6281363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281363).length < 2 ^ (prefixWord ++ tailWord_6281363).sum := by decide
  have hdescent : baseEnd_6281363 < baseStart_6281363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281447 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 1, 7]
def baseStart_6281447 : Nat := 118140960795 + 6281447 * 2 ^ 59
def prefixEnd_6281447 : Nat := 4983230072969 + 3 ^ 40 * 6281447 * 2
def baseEnd_6281447 : Nat := 1075133838914196847808219

theorem tailTrace_6281447 : CollatzResearch.WordTrace tailWord_6281447 prefixEnd_6281447 1075133838914196847808219 := by
  unfold tailWord_6281447
  simp only [CollatzResearch.WordTrace]
  refine ⟨229103193674397779583874595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152735462449598519722583063 229103193674397779583874595)
  ·
    refine ⟨343654790511596669375811893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229103193674397779583874595 343654790511596669375811893)
    ·
      refine ⟨32217636610462187753982365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 343654790511596669375811893 32217636610462187753982365)
      ·
        refine ⟨12081613728923320407743387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32217636610462187753982365 12081613728923320407743387)
        ·
          refine ⟨18122420593384980611615081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12081613728923320407743387 18122420593384980611615081)
          ·
            refine ⟨13591815445038735458711311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18122420593384980611615081 13591815445038735458711311)
            ·
              refine ⟨20387723167558103188066967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13591815445038735458711311 20387723167558103188066967)
              ·
                refine ⟨30581584751337154782100451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20387723167558103188066967 30581584751337154782100451)
                ·
                  refine ⟨45872377127005732173150677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30581584751337154782100451 45872377127005732173150677)
                  ·
                    refine ⟨1075133838914196847808219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45872377127005732173150677 1075133838914196847808219)
                    ·
                      rfl

theorem cell23_6281447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_6281447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281447 prefixEnd_6281447 := by exact prefixLift 6281447
  have htrace : WordTrace (prefixWord ++ tailWord_6281447) baseStart_6281447 baseEnd_6281447 := by
    simpa [prefixWord, tailWord_6281447, baseEnd_6281447] using wordTrace_append hprefix tailTrace_6281447
  have hstable : (prefixWord ++ tailWord_6281447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281447).length < 2 ^ (prefixWord ++ tailWord_6281447).sum := by decide
  have hdescent : baseEnd_6281447 < baseStart_6281447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281554 : List Nat := [3, 2, 2, 1, 1, 1, 5, 2, 1, 5]
def baseStart_6281554 : Nat := 118140960795 + 6281554 * 2 ^ 59
def prefixEnd_6281554 : Nat := 4983230072969 + 3 ^ 40 * 6281554 * 2
def baseEnd_6281554 : Nat := 1075152153057540541595555

theorem tailTrace_6281554 : CollatzResearch.WordTrace tailWord_6281554 prefixEnd_6281554 1075152153057540541595555 := by
  unfold tailWord_6281554
  simp only [CollatzResearch.WordTrace]
  refine ⟨57276774071252534214504929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152738064190006757905346477 57276774071252534214504929)
  ·
    refine ⟨42957580553439400660878697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57276774071252534214504929 42957580553439400660878697)
    ·
      refine ⟨32218185415079550495659023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42957580553439400660878697 32218185415079550495659023)
      ·
        refine ⟨48327278122619325743488535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32218185415079550495659023 48327278122619325743488535)
        ·
          refine ⟨72490917183928988615232803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48327278122619325743488535 72490917183928988615232803)
          ·
            refine ⟨108736375775893482922849205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72490917183928988615232803 108736375775893482922849205)
            ·
              refine ⟨10194035228990014024017113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108736375775893482922849205 10194035228990014024017113)
              ·
                refine ⟨7645526421742510518012835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10194035228990014024017113 7645526421742510518012835)
                ·
                  refine ⟨11468289632613765777019253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7645526421742510518012835 11468289632613765777019253)
                  ·
                    refine ⟨1075152153057540541595555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11468289632613765777019253 1075152153057540541595555)
                    ·
                      rfl

theorem cell23_6281554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_6281554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281554 prefixEnd_6281554 := by exact prefixLift 6281554
  have htrace : WordTrace (prefixWord ++ tailWord_6281554) baseStart_6281554 baseEnd_6281554 := by
    simpa [prefixWord, tailWord_6281554, baseEnd_6281554] using wordTrace_append hprefix tailTrace_6281554
  have hstable : (prefixWord ++ tailWord_6281554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281554).length < 2 ^ (prefixWord ++ tailWord_6281554).sum := by decide
  have hdescent : baseEnd_6281554 < baseStart_6281554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281567 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 6, 4]
def baseStart_6281567 : Nat := 118140960795 + 6281567 * 2 ^ 59
def prefixEnd_6281567 : Nat := 4983230072969 + 3 ^ 40 * 6281567 * 2
def baseEnd_6281567 : Nat := 1075154378140376691308035

theorem tailTrace_6281567 : CollatzResearch.WordTrace tailWord_6281567 prefixEnd_6281567 1075154378140376691308035 := by
  unfold tailWord_6281567
  simp only [CollatzResearch.WordTrace]
  refine ⟨229107570433963040078242955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152738380289308693385495303 229107570433963040078242955)
  ·
    refine ⟨343661355650944560117364433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229107570433963040078242955 343661355650944560117364433)
    ·
      refine ⟨257746016738208420088023325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343661355650944560117364433 257746016738208420088023325)
      ·
        refine ⟨96654756276828157533008747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257746016738208420088023325 96654756276828157533008747)
        ·
          refine ⟨144982134415242236299513121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96654756276828157533008747 144982134415242236299513121)
          ·
            refine ⟨108736600811431677224634841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144982134415242236299513121 108736600811431677224634841)
            ·
              refine ⟨81552450608573757918476131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108736600811431677224634841 81552450608573757918476131)
              ·
                refine ⟨122328675912860636877714197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81552450608573757918476131 122328675912860636877714197)
                ·
                  refine ⟨5734156683415342353642853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 122328675912860636877714197 5734156683415342353642853)
                  ·
                    refine ⟨1075154378140376691308035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5734156683415342353642853 1075154378140376691308035)
                    ·
                      rfl

theorem cell23_6281567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 4].length) (baseStart_6281567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281567 prefixEnd_6281567 := by exact prefixLift 6281567
  have htrace : WordTrace (prefixWord ++ tailWord_6281567) baseStart_6281567 baseEnd_6281567 := by
    simpa [prefixWord, tailWord_6281567, baseEnd_6281567] using wordTrace_append hprefix tailTrace_6281567
  have hstable : (prefixWord ++ tailWord_6281567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281567).length < 2 ^ (prefixWord ++ tailWord_6281567).sum := by decide
  have hdescent : baseEnd_6281567 < baseStart_6281567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281580 : List Nat := [2, 2, 1, 1, 17]
def baseStart_6281580 : Nat := 118140960795 + 6281580 * 2 ^ 59
def prefixEnd_6281580 : Nat := 4983230072969 + 3 ^ 40 * 6281580 * 2
def baseEnd_6281580 : Nat := 4424512770465896465105

theorem tailTrace_6281580 : CollatzResearch.WordTrace tailWord_6281580 prefixEnd_6281580 4424512770465896465105 := by
  unfold tailWord_6281580
  simp only [CollatzResearch.WordTrace]
  refine ⟨114554022291457971649233097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152738696388610628865644129 114554022291457971649233097)
  ·
    refine ⟨85915516718593478736924823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114554022291457971649233097 85915516718593478736924823)
    ·
      refine ⟨128873275077890218105387235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85915516718593478736924823 128873275077890218105387235)
      ·
        refine ⟨193309912616835327158080853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128873275077890218105387235 193309912616835327158080853)
        ·
          refine ⟨4424512770465896465105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 17 193309912616835327158080853 4424512770465896465105)
          ·
            rfl

theorem cell23_6281580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 17].length) (baseStart_6281580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281580 prefixEnd_6281580 := by exact prefixLift 6281580
  have htrace : WordTrace (prefixWord ++ tailWord_6281580) baseStart_6281580 baseEnd_6281580 := by
    simpa [prefixWord, tailWord_6281580, baseEnd_6281580] using wordTrace_append hprefix tailTrace_6281580
  have hstable : (prefixWord ++ tailWord_6281580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281580).length < 2 ^ (prefixWord ++ tailWord_6281580).sum := by decide
  have hdescent : baseEnd_6281580 < baseStart_6281580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281584 : List Nat := [2, 1, 1, 1, 4, 3, 1, 4, 2, 4]
def baseStart_6281584 : Nat := 118140960795 + 6281584 * 2 ^ 59
def prefixEnd_6281584 : Nat := 4983230072969 + 3 ^ 40 * 6281584 * 2
def baseEnd_6281584 : Nat := 1075157287864085502470509

theorem tailTrace_6281584 : CollatzResearch.WordTrace tailWord_6281584 prefixEnd_6281584 1075157287864085502470509 := by
  unfold tailWord_6281584
  simp only [CollatzResearch.WordTrace]
  refine ⟨114554095237450725990805903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152738793649934301321074537 114554095237450725990805903)
  ·
    refine ⟨171831142856176088986208855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114554095237450725990805903 171831142856176088986208855)
    ·
      refine ⟨257746714284264133479313283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171831142856176088986208855 257746714284264133479313283)
      ·
        refine ⟨386620071426396200218969925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257746714284264133479313283 386620071426396200218969925)
        ·
          refine ⟨72491263392449287541056861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 386620071426396200218969925 72491263392449287541056861)
          ·
            refine ⟨27184223772168482827896323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72491263392449287541056861 27184223772168482827896323)
            ·
              refine ⟨40776335658252724241844485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27184223772168482827896323 40776335658252724241844485)
              ·
                refine ⟨7645562935922385795345841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40776335658252724241844485 7645562935922385795345841)
                ·
                  refine ⟨5734172201941789346509381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7645562935922385795345841 5734172201941789346509381)
                  ·
                    refine ⟨1075157287864085502470509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5734172201941789346509381 1075157287864085502470509)
                    ·
                      rfl

theorem cell23_6281584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 2, 4].length) (baseStart_6281584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281584 prefixEnd_6281584 := by exact prefixLift 6281584
  have htrace : WordTrace (prefixWord ++ tailWord_6281584) baseStart_6281584 baseEnd_6281584 := by
    simpa [prefixWord, tailWord_6281584, baseEnd_6281584] using wordTrace_append hprefix tailTrace_6281584
  have hstable : (prefixWord ++ tailWord_6281584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281584).length < 2 ^ (prefixWord ++ tailWord_6281584).sum := by decide
  have hdescent : baseEnd_6281584 < baseStart_6281584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281597 : List Nat := [1, 4, 1, 1, 2, 3, 3, 8]
def baseStart_6281597 : Nat := 118140960795 + 6281597 * 2 ^ 59
def prefixEnd_6281597 : Nat := 4983230072969 + 3 ^ 40 * 6281597 * 2
def baseEnd_6281597 : Nat := 119462168105213516909221

theorem tailTrace_6281597 : CollatzResearch.WordTrace tailWord_6281597 prefixEnd_6281597 119462168105213516909221 := by
  unfold tailWord_6281597
  simp only [CollatzResearch.WordTrace]
  refine ⟨229108664623854355201835045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152739109749236236801223363 229108664623854355201835045)
  ·
    refine ⟨42957874616972691600344071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229108664623854355201835045 42957874616972691600344071)
    ·
      refine ⟨64436811925459037400516107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42957874616972691600344071 64436811925459037400516107)
      ·
        refine ⟨96655217888188556100774161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64436811925459037400516107 96655217888188556100774161)
        ·
          refine ⟨72491413416141417075580621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96655217888188556100774161 72491413416141417075580621)
          ·
            refine ⟨27184280031053031403342733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72491413416141417075580621 27184280031053031403342733)
            ·
              refine ⟨10194105011644886776253525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27184280031053031403342733 10194105011644886776253525)
              ·
                refine ⟨119462168105213516909221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10194105011644886776253525 119462168105213516909221)
                ·
                  rfl

theorem cell23_6281597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 8].length) (baseStart_6281597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281597 prefixEnd_6281597 := by exact prefixLift 6281597
  have htrace : WordTrace (prefixWord ++ tailWord_6281597) baseStart_6281597 baseEnd_6281597 := by
    simpa [prefixWord, tailWord_6281597, baseEnd_6281597] using wordTrace_append hprefix tailTrace_6281597
  have hstable : (prefixWord ++ tailWord_6281597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281597).length < 2 ^ (prefixWord ++ tailWord_6281597).sum := by decide
  have hdescent : baseEnd_6281597 < baseStart_6281597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281601 : List Nat := [1, 2, 4, 3, 1, 1, 2, 3, 2, 4]
def baseStart_6281601 : Nat := 118140960795 + 6281601 * 2 ^ 59
def prefixEnd_6281601 : Nat := 4983230072969 + 3 ^ 40 * 6281601 * 2
def baseEnd_6281601 : Nat := 1075160197587794313632983

theorem tailTrace_6281601 : CollatzResearch.WordTrace tailWord_6281601 prefixEnd_6281601 1075160197587794313632983 := by
  unfold tailWord_6281601
  simp only [CollatzResearch.WordTrace]
  refine ⟨229108810515839863884980657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152739207010559909256653771 229108810515839863884980657)
  ·
    refine ⟨171831607886879897913735493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229108810515839863884980657 171831607886879897913735493)
    ·
      refine ⟨32218426478789980858825405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171831607886879897913735493 32218426478789980858825405)
      ·
        refine ⟨12081909929546242822059527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32218426478789980858825405 12081909929546242822059527)
        ·
          refine ⟨18122864894319364233089291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12081909929546242822059527 18122864894319364233089291)
          ·
            refine ⟨27184297341479046349633937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18122864894319364233089291 27184297341479046349633937)
            ·
              refine ⟨20388223006109284762225453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27184297341479046349633937 20388223006109284762225453)
              ·
                refine ⟨7645583627290981785834545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20388223006109284762225453 7645583627290981785834545)
                ·
                  refine ⟨5734187720468236339375909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7645583627290981785834545 5734187720468236339375909)
                  ·
                    refine ⟨1075160197587794313632983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5734187720468236339375909 1075160197587794313632983)
                    ·
                      rfl

theorem cell23_6281601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_6281601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281601 prefixEnd_6281601 := by exact prefixLift 6281601
  have htrace : WordTrace (prefixWord ++ tailWord_6281601) baseStart_6281601 baseEnd_6281601 := by
    simpa [prefixWord, tailWord_6281601, baseEnd_6281601] using wordTrace_append hprefix tailTrace_6281601
  have hstable : (prefixWord ++ tailWord_6281601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281601).length < 2 ^ (prefixWord ++ tailWord_6281601).sum := by decide
  have hdescent : baseEnd_6281601 < baseStart_6281601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281604 : List Nat := [2, 3, 2, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_6281604 : Nat := 118140960795 + 6281604 * 2 ^ 59
def prefixEnd_6281604 : Nat := 4983230072969 + 3 ^ 40 * 6281604 * 2
def baseEnd_6281604 : Nat := 3225482133205346429161435

theorem tailTrace_6281604 : CollatzResearch.WordTrace tailWord_6281604 prefixEnd_6281604 3225482133205346429161435 := by
  unfold tailWord_6281604
  simp only [CollatzResearch.WordTrace]
  refine ⟨114554459967414497698669933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152739279956552663598226577 114554459967414497698669933)
  ·
    refine ⟨42957922487780436637001225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114554459967414497698669933 42957922487780436637001225)
    ·
      refine ⟨32218441865835327477750919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42957922487780436637001225 32218441865835327477750919)
      ·
        refine ⟨48327662798752991216626379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32218441865835327477750919 48327662798752991216626379)
        ·
          refine ⟨72491494198129486824939569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48327662798752991216626379 72491494198129486824939569)
          ·
            refine ⟨54368620648597115118704677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72491494198129486824939569 54368620648597115118704677)
            ·
              refine ⟨10194116371611959084757127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54368620648597115118704677 10194116371611959084757127)
              ·
                refine ⟨15291174557417938627135691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10194116371611959084757127 15291174557417938627135691)
                ·
                  refine ⟨22936761836126907940703537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15291174557417938627135691 22936761836126907940703537)
                  ·
                    refine ⟨17202571377095180955527653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22936761836126907940703537 17202571377095180955527653)
                    ·
                      refine ⟨3225482133205346429161435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17202571377095180955527653 3225482133205346429161435)
                      ·
                        rfl

theorem cell23_6281604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_6281604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281604 prefixEnd_6281604 := by exact prefixLift 6281604
  have htrace : WordTrace (prefixWord ++ tailWord_6281604) baseStart_6281604 baseEnd_6281604 := by
    simpa [prefixWord, tailWord_6281604, baseEnd_6281604] using wordTrace_append hprefix tailTrace_6281604
  have hstable : (prefixWord ++ tailWord_6281604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281604).length < 2 ^ (prefixWord ++ tailWord_6281604).sum := by decide
  have hdescent : baseEnd_6281604 < baseStart_6281604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281652 : List Nat := [2, 5, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_6281652 : Nat := 118140960795 + 6281652 * 2 ^ 59
def prefixEnd_6281652 : Nat := 4983230072969 + 3 ^ 40 * 6281652 * 2
def baseEnd_6281652 : Nat := 1075168926758920747120405

theorem tailTrace_6281652 : CollatzResearch.WordTrace tailWord_6281652 prefixEnd_6281652 1075168926758920747120405 := by
  unfold tailWord_6281652
  simp only [CollatzResearch.WordTrace]
  refine ⟨114555335319327549797543605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152740447092436733063391473 114555335319327549797543605)
  ·
    refine ⟨10739562686186957793519713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114555335319327549797543605 10739562686186957793519713)
    ·
      refine ⟨8054672014640218345139785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10739562686186957793519713 8054672014640218345139785)
      ·
        refine ⟨6041004010980163758854839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8054672014640218345139785 6041004010980163758854839)
        ·
          refine ⟨9061506016470245638282259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6041004010980163758854839 9061506016470245638282259)
          ·
            refine ⟨13592259024705368457423389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9061506016470245638282259 13592259024705368457423389)
            ·
              refine ⟨5097097134264513171533771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13592259024705368457423389 5097097134264513171533771)
              ·
                refine ⟨7645645701396769757300657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5097097134264513171533771 7645645701396769757300657)
                ·
                  refine ⟨5734234276047577317975493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7645645701396769757300657 5734234276047577317975493)
                  ·
                    refine ⟨1075168926758920747120405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5734234276047577317975493 1075168926758920747120405)
                    ·
                      rfl

theorem cell23_6281652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_6281652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281652 prefixEnd_6281652 := by exact prefixLift 6281652
  have htrace : WordTrace (prefixWord ++ tailWord_6281652) baseStart_6281652 baseEnd_6281652 := by
    simpa [prefixWord, tailWord_6281652, baseEnd_6281652] using wordTrace_append hprefix tailTrace_6281652
  have hstable : (prefixWord ++ tailWord_6281652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281652).length < 2 ^ (prefixWord ++ tailWord_6281652).sum := by decide
  have hdescent : baseEnd_6281652 < baseStart_6281652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281665 : List Nat := [1, 2, 7, 1, 1, 2, 2, 7]
def baseStart_6281665 : Nat := 118140960795 + 6281665 * 2 ^ 59
def prefixEnd_6281665 : Nat := 4983230072969 + 3 ^ 40 * 6281665 * 2
def baseEnd_6281665 : Nat := 119463461315750766314765

theorem tailTrace_6281665 : CollatzResearch.WordTrace tailWord_6281665 prefixEnd_6281665 119463461315750766314765 := by
  unfold tailWord_6281665
  simp only [CollatzResearch.WordTrace]
  refine ⟨229111144787608002815310449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152740763191738668543540299 229111144787608002815310449)
  ·
    refine ⟨171833358590706002111482837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229111144787608002815310449 171833358590706002111482837)
    ·
      refine ⟨4027344341969671924487879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 171833358590706002111482837 4027344341969671924487879)
      ·
        refine ⟨6041016512954507886731819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4027344341969671924487879 6041016512954507886731819)
        ·
          refine ⟨9061524769431761830097729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6041016512954507886731819 9061524769431761830097729)
          ·
            refine ⟨6796143577073821372573297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9061524769431761830097729 6796143577073821372573297)
            ·
              refine ⟨5097107682805366029429973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6796143577073821372573297 5097107682805366029429973)
              ·
                refine ⟨119463461315750766314765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5097107682805366029429973 119463461315750766314765)
                ·
                  rfl

theorem cell23_6281665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 7].length) (baseStart_6281665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281665 prefixEnd_6281665 := by exact prefixLift 6281665
  have htrace : WordTrace (prefixWord ++ tailWord_6281665) baseStart_6281665 baseEnd_6281665 := by
    simpa [prefixWord, tailWord_6281665, baseEnd_6281665] using wordTrace_append hprefix tailTrace_6281665
  have hstable : (prefixWord ++ tailWord_6281665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281665).length < 2 ^ (prefixWord ++ tailWord_6281665).sum := by decide
  have hdescent : baseEnd_6281665 < baseStart_6281665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281667 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 5]
def baseStart_6281667 : Nat := 118140960795 + 6281667 * 2 ^ 59
def prefixEnd_6281667 : Nat := 4983230072969 + 3 ^ 40 * 6281667 * 2
def baseEnd_6281667 : Nat := 3225514482486579682673645

theorem tailTrace_6281667 : CollatzResearch.WordTrace tailWord_6281667 prefixEnd_6281667 3225514482486579682673645 := by
  unfold tailWord_6281667
  simp only [CollatzResearch.WordTrace]
  refine ⟨229111217733600757156883255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152740811822400504771255503 229111217733600757156883255)
  ·
    refine ⟨343666826600401135735324883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229111217733600757156883255 343666826600401135735324883)
    ·
      refine ⟨515500239900601703602987325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343666826600401135735324883 515500239900601703602987325)
      ·
        refine ⟨193312589962725638851120247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 515500239900601703602987325 193312589962725638851120247)
        ·
          refine ⟨289968884944088458276680371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193312589962725638851120247 289968884944088458276680371)
          ·
            refine ⟨434953327416132687415020557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289968884944088458276680371 434953327416132687415020557)
            ·
              refine ⟨163107497781049757780632709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 434953327416132687415020557 163107497781049757780632709)
              ·
                refine ⟨30582655833946829583868633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163107497781049757780632709 30582655833946829583868633)
                ·
                  refine ⟨22936991875460122187901475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30582655833946829583868633 22936991875460122187901475)
                  ·
                    refine ⟨34405487813190183281852213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22936991875460122187901475 34405487813190183281852213)
                    ·
                      refine ⟨3225514482486579682673645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34405487813190183281852213 3225514482486579682673645)
                      ·
                        rfl

theorem cell23_6281667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_6281667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281667 prefixEnd_6281667 := by exact prefixLift 6281667
  have htrace : WordTrace (prefixWord ++ tailWord_6281667) baseStart_6281667 baseEnd_6281667 := by
    simpa [prefixWord, tailWord_6281667, baseEnd_6281667] using wordTrace_append hprefix tailTrace_6281667
  have hstable : (prefixWord ++ tailWord_6281667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281667).length < 2 ^ (prefixWord ++ tailWord_6281667).sum := by decide
  have hdescent : baseEnd_6281667 < baseStart_6281667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281684 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_6281684 : Nat := 118140960795 + 6281684 * 2 ^ 59
def prefixEnd_6281684 : Nat := 4983230072969 + 3 ^ 40 * 6281684 * 2
def baseEnd_6281684 : Nat := 3225523211657706116161067

theorem tailTrace_6281684 : CollatzResearch.WordTrace tailWord_6281684 prefixEnd_6281684 3225523211657706116161067 := by
  unfold tailWord_6281684
  simp only [CollatzResearch.WordTrace]
  refine ⟨114555918887269584530126053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152741225183026112706834737 114555918887269584530126053)
  ·
    refine ⟨21479234791363047099398635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114555918887269584530126053 21479234791363047099398635)
    ·
      refine ⟨32218852187044570649097953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21479234791363047099398635 32218852187044570649097953)
      ·
        refine ⟨24164139140283427986823465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32218852187044570649097953 24164139140283427986823465)
        ·
          refine ⟨18123104355212570990117599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24164139140283427986823465 18123104355212570990117599)
          ·
            refine ⟨27184656532818856485176399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18123104355212570990117599 27184656532818856485176399)
            ·
              refine ⟨40776984799228284727764599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27184656532818856485176399 40776984799228284727764599)
              ·
                refine ⟨61165477198842427091646899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40776984799228284727764599 61165477198842427091646899)
                ·
                  refine ⟨91748215798263640637470349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61165477198842427091646899 91748215798263640637470349)
                  ·
                    refine ⟨34405580924348865239051381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91748215798263640637470349 34405580924348865239051381)
                    ·
                      refine ⟨3225523211657706116161067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34405580924348865239051381 3225523211657706116161067)
                      ·
                        rfl

theorem cell23_6281684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_6281684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281684 prefixEnd_6281684 := by exact prefixLift 6281684
  have htrace : WordTrace (prefixWord ++ tailWord_6281684) baseStart_6281684 baseEnd_6281684 := by
    simpa [prefixWord, tailWord_6281684, baseEnd_6281684] using wordTrace_append hprefix tailTrace_6281684
  have hstable : (prefixWord ++ tailWord_6281684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281684).length < 2 ^ (prefixWord ++ tailWord_6281684).sum := by decide
  have hdescent : baseEnd_6281684 < baseStart_6281684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281697 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_6281697 : Nat := 118140960795 + 6281697 * 2 ^ 59
def prefixEnd_6281697 : Nat := 4983230072969 + 3 ^ 40 * 6281697 * 2
def baseEnd_6281697 : Nat := 3225529886906214565298507

theorem tailTrace_6281697 : CollatzResearch.WordTrace tailWord_6281697 prefixEnd_6281697 3225529886906214565298507 := by
  unfold tailWord_6281697
  simp only [CollatzResearch.WordTrace]
  refine ⟨229112311923492072280475345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152741541282328048186983563 229112311923492072280475345)
  ·
    refine ⟨171834233942619054210356509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229112311923492072280475345 171834233942619054210356509)
    ·
      refine ⟨64437837728482145328883691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171834233942619054210356509 64437837728482145328883691)
      ·
        refine ⟨96656756592723217993325537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64437837728482145328883691 96656756592723217993325537)
        ·
          refine ⟨72492567444542413494994153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96656756592723217993325537 72492567444542413494994153)
          ·
            refine ⟨54369425583406810121245615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72492567444542413494994153 54369425583406810121245615)
            ·
              refine ⟨81554138375110215181868423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54369425583406810121245615 81554138375110215181868423)
              ·
                refine ⟨122331207562665322772802635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81554138375110215181868423 122331207562665322772802635)
                ·
                  refine ⟨183496811343997984159203953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122331207562665322772802635 183496811343997984159203953)
                  ·
                    refine ⟨137622608507998488119402965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 183496811343997984159203953 137622608507998488119402965)
                    ·
                      refine ⟨3225529886906214565298507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137622608507998488119402965 3225529886906214565298507)
                      ·
                        rfl

theorem cell23_6281697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_6281697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281697 prefixEnd_6281697 := by exact prefixLift 6281697
  have htrace : WordTrace (prefixWord ++ tailWord_6281697) baseStart_6281697 baseEnd_6281697 := by
    simpa [prefixWord, tailWord_6281697, baseEnd_6281697] using wordTrace_append hprefix tailTrace_6281697
  have hstable : (prefixWord ++ tailWord_6281697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281697).length < 2 ^ (prefixWord ++ tailWord_6281697).sum := by decide
  have hdescent : baseEnd_6281697 < baseStart_6281697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281704 : List Nat := [2, 1, 4, 1, 1, 3, 3, 1, 7]
def baseStart_6281704 : Nat := 118140960795 + 6281704 * 2 ^ 59
def prefixEnd_6281704 : Nat := 4983230072969 + 3 ^ 40 * 6281704 * 2
def baseEnd_6281704 : Nat := 358392609030088448656775

theorem tailTrace_6281704 : CollatzResearch.WordTrace tailWord_6281704 prefixEnd_6281704 358392609030088448656775 := by
  unfold tailWord_6281704
  simp only [CollatzResearch.WordTrace]
  refine ⟨114556283617233356237990083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152741711489644474983986777 114556283617233356237990083)
  ·
    refine ⟨171834425425850034356985125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114556283617233356237990083 171834425425850034356985125)
    ·
      refine ⟨32218954767346881441934711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171834425425850034356985125 32218954767346881441934711)
      ·
        refine ⟨48328432151020322162902067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32218954767346881441934711 48328432151020322162902067)
        ·
          refine ⟨72492648226530483244353101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48328432151020322162902067 72492648226530483244353101)
          ·
            refine ⟨27184743084948931216632413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72492648226530483244353101 27184743084948931216632413)
            ·
              refine ⟨10194278656855849206237155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27184743084948931216632413 10194278656855849206237155)
              ·
                refine ⟨15291417985283773809355733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10194278656855849206237155 15291417985283773809355733)
                ·
                  refine ⟨358392609030088448656775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15291417985283773809355733 358392609030088448656775)
                  ·
                    rfl

theorem cell23_6281704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 7].length) (baseStart_6281704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281704 prefixEnd_6281704 := by exact prefixLift 6281704
  have htrace : WordTrace (prefixWord ++ tailWord_6281704) baseStart_6281704 baseEnd_6281704 := by
    simpa [prefixWord, tailWord_6281704, baseEnd_6281704] using wordTrace_append hprefix tailTrace_6281704
  have hstable : (prefixWord ++ tailWord_6281704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281704).length < 2 ^ (prefixWord ++ tailWord_6281704).sum := by decide
  have hdescent : baseEnd_6281704 < baseStart_6281704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281727 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 7]
def baseStart_6281727 : Nat := 118140960795 + 6281727 * 2 ^ 59
def prefixEnd_6281727 : Nat := 4983230072969 + 3 ^ 40 * 6281727 * 2
def baseEnd_6281727 : Nat := 3225545291325849447923369

theorem tailTrace_6281727 : CollatzResearch.WordTrace tailWord_6281727 prefixEnd_6281727 3225545291325849447923369 := by
  unfold tailWord_6281727
  simp only [CollatzResearch.WordTrace]
  refine ⟨229113406113383387404067435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152742270742255591602711623 229113406113383387404067435)
  ·
    refine ⟨343670109170075081106101153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229113406113383387404067435 343670109170075081106101153)
    ·
      refine ⟨257752581877556310829575865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343670109170075081106101153 257752581877556310829575865)
      ·
        refine ⟨193314436408167233122181899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257752581877556310829575865 193314436408167233122181899)
        ·
          refine ⟨289971654612250849683272849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193314436408167233122181899 289971654612250849683272849)
          ·
            refine ⟨217478740959188137262454637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289971654612250849683272849 217478740959188137262454637)
            ·
              refine ⟨81554527859695551473420489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217478740959188137262454637 81554527859695551473420489)
              ·
                refine ⟨61165895894771663605065367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81554527859695551473420489 61165895894771663605065367)
                ·
                  refine ⟨91748843842157495407598051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61165895894771663605065367 91748843842157495407598051)
                  ·
                    refine ⟨137623265763236243111397077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91748843842157495407598051 137623265763236243111397077)
                    ·
                      refine ⟨3225545291325849447923369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137623265763236243111397077 3225545291325849447923369)
                      ·
                        rfl

theorem cell23_6281727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_6281727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281727 prefixEnd_6281727 := by exact prefixLift 6281727
  have htrace : WordTrace (prefixWord ++ tailWord_6281727) baseStart_6281727 baseEnd_6281727 := by
    simpa [prefixWord, tailWord_6281727, baseEnd_6281727] using wordTrace_append hprefix tailTrace_6281727
  have hstable : (prefixWord ++ tailWord_6281727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281727).length < 2 ^ (prefixWord ++ tailWord_6281727).sum := by decide
  have hdescent : baseEnd_6281727 < baseStart_6281727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281781 : List Nat := [1, 3, 3, 1, 1, 2, 3, 2, 3, 4]
def baseStart_6281781 : Nat := 118140960795 + 6281781 * 2 ^ 59
def prefixEnd_6281781 : Nat := 4983230072969 + 3 ^ 40 * 6281781 * 2
def baseEnd_6281781 : Nat := 1075191006427064078882707

theorem tailTrace_6281781 : CollatzResearch.WordTrace tailWord_6281781 prefixEnd_6281781 1075191006427064078882707 := by
  unfold tailWord_6281781
  simp only [CollatzResearch.WordTrace]
  refine ⟨229115375655187754626533197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152743583770125169751022131 229115375655187754626533197)
  ·
    refine ⟨85918265870695407984949949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229115375655187754626533197 85918265870695407984949949)
    ·
      refine ⟨32219349701510777994356231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85918265870695407984949949 32219349701510777994356231)
      ·
        refine ⟨48329024552266166991534347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32219349701510777994356231 48329024552266166991534347)
        ·
          refine ⟨72493536828399250487301521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48329024552266166991534347 72493536828399250487301521)
          ·
            refine ⟨54370152621299437865476141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72493536828399250487301521 54370152621299437865476141)
            ·
              refine ⟨20388807232987289199553553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54370152621299437865476141 20388807232987289199553553)
              ·
                refine ⟨15291605424740466899665165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20388807232987289199553553 15291605424740466899665165)
                ·
                  refine ⟨5734352034277675087374437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15291605424740466899665165 5734352034277675087374437)
                  ·
                    refine ⟨1075191006427064078882707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5734352034277675087374437 1075191006427064078882707)
                    ·
                      rfl

theorem cell23_6281781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_6281781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281781 prefixEnd_6281781 := by exact prefixLift 6281781
  have htrace : WordTrace (prefixWord ++ tailWord_6281781) baseStart_6281781 baseEnd_6281781 := by
    simpa [prefixWord, tailWord_6281781, baseEnd_6281781] using wordTrace_append hprefix tailTrace_6281781
  have hstable : (prefixWord ++ tailWord_6281781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281781).length < 2 ^ (prefixWord ++ tailWord_6281781).sum := by decide
  have hdescent : baseEnd_6281781 < baseStart_6281781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281788 : List Nat := [2, 2, 2, 2, 3, 3, 1, 1, 2, 1, 4]
def baseStart_6281788 : Nat := 118140960795 + 6281788 * 2 ^ 59
def prefixEnd_6281788 : Nat := 4983230072969 + 3 ^ 40 * 6281788 * 2
def baseEnd_6281788 : Nat := 3225576613645773709260589

theorem tailTrace_6281788 : CollatzResearch.WordTrace tailWord_6281788 prefixEnd_6281788 3225576613645773709260589 := by
  unfold tailWord_6281788
  simp only [CollatzResearch.WordTrace]
  refine ⟨114557815483081197411019009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152743753977441596548025345 114557815483081197411019009)
  ·
    refine ⟨85918361612310898058264257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114557815483081197411019009 85918361612310898058264257)
    ·
      refine ⟨64438771209233173543698193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85918361612310898058264257 64438771209233173543698193)
      ·
        refine ⟨48329078406924880157773645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64438771209233173543698193 48329078406924880157773645)
        ·
          refine ⟨18123404402596830059165117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48329078406924880157773645 18123404402596830059165117)
          ·
            refine ⟨6796276650973811272186919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18123404402596830059165117 6796276650973811272186919)
            ·
              refine ⟨10194414976460716908280379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6796276650973811272186919 10194414976460716908280379)
              ·
                refine ⟨15291622464691075362420569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10194414976460716908280379 15291622464691075362420569)
                ·
                  refine ⟨11468716848518306521815427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15291622464691075362420569 11468716848518306521815427)
                  ·
                    refine ⟨17203075272777459782723141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11468716848518306521815427 17203075272777459782723141)
                    ·
                      refine ⟨3225576613645773709260589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17203075272777459782723141 3225576613645773709260589)
                      ·
                        rfl

theorem cell23_6281788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_6281788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281788 prefixEnd_6281788 := by exact prefixLift 6281788
  have htrace : WordTrace (prefixWord ++ tailWord_6281788) baseStart_6281788 baseEnd_6281788 := by
    simpa [prefixWord, tailWord_6281788, baseEnd_6281788] using wordTrace_append hprefix tailTrace_6281788
  have hstable : (prefixWord ++ tailWord_6281788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281788).length < 2 ^ (prefixWord ++ tailWord_6281788).sum := by decide
  have hdescent : baseEnd_6281788 < baseStart_6281788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281824 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 5, 5]
def baseStart_6281824 : Nat := 118140960795 + 6281824 * 2 ^ 59
def prefixEnd_6281824 : Nat := 4983230072969 + 3 ^ 40 * 6281824 * 2
def baseEnd_6281824 : Nat := 1075198366316445189470141

theorem tailTrace_6281824 : CollatzResearch.WordTrace tailWord_6281824 prefixEnd_6281824 1075198366316445189470141 := by
  unfold tailWord_6281824
  simp only [CollatzResearch.WordTrace]
  refine ⟨114558471997015986485174263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152744629329354648646899017 114558471997015986485174263)
  ·
    refine ⟨171837707995523979727761395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114558471997015986485174263 171837707995523979727761395)
    ·
      refine ⟨257756561993285969591642093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171837707995523979727761395 257756561993285969591642093)
      ·
        refine ⟨96658710747482238596865785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257756561993285969591642093 96658710747482238596865785)
        ·
          refine ⟨72494033060611678947649339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96658710747482238596865785 72494033060611678947649339)
          ·
            refine ⟨108741049590917518421474009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72494033060611678947649339 108741049590917518421474009)
            ·
              refine ⟨81555787193188138816105507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108741049590917518421474009 81555787193188138816105507)
              ·
                refine ⟨122333680789782208224158261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81555787193188138816105507 122333680789782208224158261)
                ·
                  refine ⟨11468782574042082021014837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122333680789782208224158261 11468782574042082021014837)
                  ·
                    refine ⟨1075198366316445189470141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11468782574042082021014837 1075198366316445189470141)
                    ·
                      rfl

theorem cell23_6281824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 5, 5].length) (baseStart_6281824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281824 prefixEnd_6281824 := by exact prefixLift 6281824
  have htrace : WordTrace (prefixWord ++ tailWord_6281824) baseStart_6281824 baseEnd_6281824 := by
    simpa [prefixWord, tailWord_6281824, baseEnd_6281824] using wordTrace_append hprefix tailTrace_6281824
  have hstable : (prefixWord ++ tailWord_6281824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281824).length < 2 ^ (prefixWord ++ tailWord_6281824).sum := by decide
  have hdescent : baseEnd_6281824 < baseStart_6281824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281881 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 3, 2, 3]
def baseStart_6281881 : Nat := 118140960795 + 6281881 * 2 ^ 59
def prefixEnd_6281881 : Nat := 4983230072969 + 3 ^ 40 * 6281881 * 2
def baseEnd_6281881 : Nat := 3225624367346641845397661

theorem tailTrace_6281881 : CollatzResearch.WordTrace tailWord_6281881 prefixEnd_6281881 3225624367346641845397661 := by
  unfold tailWord_6281881
  simp only [CollatzResearch.WordTrace]
  refine ⟨229119022954825471705173497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152746015303216981136782331 229119022954825471705173497)
  ·
    refine ⟨171839267216119103778880123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229119022954825471705173497 171839267216119103778880123)
    ·
      refine ⟨257758900824178655668320185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171839267216119103778880123 257758900824178655668320185)
      ·
        refine ⟨193319175618133991751240139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257758900824178655668320185 193319175618133991751240139)
        ·
          refine ⟨289978763427200987626860209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193319175618133991751240139 289978763427200987626860209)
          ·
            refine ⟨217484072570400740720145157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289978763427200987626860209 217484072570400740720145157)
            ·
              refine ⟨40778263606950138885027217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217484072570400740720145157 40778263606950138885027217)
              ·
                refine ⟨30583697705212604163770413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40778263606950138885027217 30583697705212604163770413)
                ·
                  refine ⟨11468886639454726561413905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30583697705212604163770413 11468886639454726561413905)
                  ·
                    refine ⟨8601664979591044921060429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11468886639454726561413905 8601664979591044921060429)
                    ·
                      refine ⟨3225624367346641845397661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8601664979591044921060429 3225624367346641845397661)
                      ·
                        rfl

theorem cell23_6281881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_6281881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281881 prefixEnd_6281881 := by exact prefixLift 6281881
  have htrace : WordTrace (prefixWord ++ tailWord_6281881) baseStart_6281881 baseEnd_6281881 := by
    simpa [prefixWord, tailWord_6281881, baseEnd_6281881] using wordTrace_append hprefix tailTrace_6281881
  have hstable : (prefixWord ++ tailWord_6281881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281881).length < 2 ^ (prefixWord ++ tailWord_6281881).sum := by decide
  have hdescent : baseEnd_6281881 < baseStart_6281881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281895 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_6281895 : Nat := 118140960795 + 6281895 * 2 ^ 59
def prefixEnd_6281895 : Nat := 4983230072969 + 3 ^ 40 * 6281895 * 2
def baseEnd_6281895 : Nat := 3225631556075804790622597

theorem tailTrace_6281895 : CollatzResearch.WordTrace tailWord_6281895 prefixEnd_6281895 3225631556075804790622597 := by
  unfold tailWord_6281895
  simp only [CollatzResearch.WordTrace]
  refine ⟨229119533576774752096183139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152746355717849834730788759 229119533576774752096183139)
  ·
    refine ⟨343679300365162128144274709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229119533576774752096183139 343679300365162128144274709)
    ·
      refine ⟨16109967204616974756762877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 343679300365162128144274709 16109967204616974756762877)
      ·
        refine ⟨6041237701731365533786079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16109967204616974756762877 6041237701731365533786079)
        ·
          refine ⟨9061856552597048300679119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6041237701731365533786079 9061856552597048300679119)
          ·
            refine ⟨13592784828895572451018679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9061856552597048300679119 13592784828895572451018679)
            ·
              refine ⟨20389177243343358676528019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13592784828895572451018679 20389177243343358676528019)
              ·
                refine ⟨30583765865015038014792029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20389177243343358676528019 30583765865015038014792029)
                ·
                  refine ⟨11468912199380639255547011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30583765865015038014792029 11468912199380639255547011)
                  ·
                    refine ⟨17203368299070958883320517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11468912199380639255547011 17203368299070958883320517)
                    ·
                      refine ⟨3225631556075804790622597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17203368299070958883320517 3225631556075804790622597)
                      ·
                        rfl

theorem cell23_6281895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_6281895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281895 prefixEnd_6281895 := by exact prefixLift 6281895
  have htrace : WordTrace (prefixWord ++ tailWord_6281895) baseStart_6281895 baseEnd_6281895 := by
    simpa [prefixWord, tailWord_6281895, baseEnd_6281895] using wordTrace_append hprefix tailTrace_6281895
  have hstable : (prefixWord ++ tailWord_6281895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281895).length < 2 ^ (prefixWord ++ tailWord_6281895).sum := by decide
  have hdescent : baseEnd_6281895 < baseStart_6281895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281901 : List Nat := [1, 5, 2, 1, 1, 2, 2, 9]
def baseStart_6281901 : Nat := 118140960795 + 6281901 * 2 ^ 59
def prefixEnd_6281901 : Nat := 4983230072969 + 3 ^ 40 * 6281901 * 2
def baseEnd_6281901 : Nat := 119467949517027102486947

theorem tailTrace_6281901 : CollatzResearch.WordTrace tailWord_6281901 prefixEnd_6281901 119467949517027102486947 := by
  unfold tailWord_6281901
  simp only [CollatzResearch.WordTrace]
  refine ⟨229119752414753015120901557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152746501609835343413934371 229119752414753015120901557)
  ·
    refine ⟨21479976788883095167584521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229119752414753015120901557 21479976788883095167584521)
    ·
      refine ⟨16109982591662321375688391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21479976788883095167584521 16109982591662321375688391)
      ·
        refine ⟨24164973887493482063532587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16109982591662321375688391 24164973887493482063532587)
        ·
          refine ⟨36247460831240223095298881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24164973887493482063532587 36247460831240223095298881)
          ·
            refine ⟨27185595623430167321474161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36247460831240223095298881 27185595623430167321474161)
            ·
              refine ⟨20389196717572625491105621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27185595623430167321474161 20389196717572625491105621)
              ·
                refine ⟨119467949517027102486947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20389196717572625491105621 119467949517027102486947)
                ·
                  rfl

theorem cell23_6281901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 9].length) (baseStart_6281901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281901 prefixEnd_6281901 := by exact prefixLift 6281901
  have htrace : WordTrace (prefixWord ++ tailWord_6281901) baseStart_6281901 baseEnd_6281901 := by
    simpa [prefixWord, tailWord_6281901, baseEnd_6281901] using wordTrace_append hprefix tailTrace_6281901
  have hstable : (prefixWord ++ tailWord_6281901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281901).length < 2 ^ (prefixWord ++ tailWord_6281901).sum := by decide
  have hdescent : baseEnd_6281901 < baseStart_6281901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281955 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 3, 3, 2]
def baseStart_6281955 : Nat := 118140960795 + 6281955 * 2 ^ 59
def prefixEnd_6281955 : Nat := 4983230072969 + 3 ^ 40 * 6281955 * 2
def baseEnd_6281955 : Nat := 3225662364915074555872321

theorem tailTrace_6281955 : CollatzResearch.WordTrace tailWord_6281955 prefixEnd_6281955 3225662364915074555872321 := by
  unfold tailWord_6281955
  simp only [CollatzResearch.WordTrace]
  refine ⟨229121721956557382343367319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152747814637704921562244879 229121721956557382343367319)
  ·
    refine ⟨343682582934836073515050979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229121721956557382343367319 343682582934836073515050979)
    ·
      refine ⟨515523874402254110272576469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343682582934836073515050979 515523874402254110272576469)
      ·
        refine ⟨12082590806302830709513511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 515523874402254110272576469 12082590806302830709513511)
        ·
          refine ⟨18123886209454246064270267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12082590806302830709513511 18123886209454246064270267)
          ·
            refine ⟨27185829314181369096405401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18123886209454246064270267 27185829314181369096405401)
            ·
              refine ⟨20389371985636026822304051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27185829314181369096405401 20389371985636026822304051)
              ·
                refine ⟨30584057978454040233456077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20389371985636026822304051 30584057978454040233456077)
                ·
                  refine ⟨11469021741920265087546029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30584057978454040233456077 11469021741920265087546029)
                  ·
                    refine ⟨4300883153220099407829761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11469021741920265087546029 4300883153220099407829761)
                    ·
                      refine ⟨3225662364915074555872321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4300883153220099407829761 3225662364915074555872321)
                      ·
                        rfl

theorem cell23_6281955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_6281955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281955 prefixEnd_6281955 := by exact prefixLift 6281955
  have htrace : WordTrace (prefixWord ++ tailWord_6281955) baseStart_6281955 baseEnd_6281955 := by
    simpa [prefixWord, tailWord_6281955, baseEnd_6281955] using wordTrace_append hprefix tailTrace_6281955
  have hstable : (prefixWord ++ tailWord_6281955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281955).length < 2 ^ (prefixWord ++ tailWord_6281955).sum := by decide
  have hdescent : baseEnd_6281955 < baseStart_6281955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281968 : List Nat := [2, 1, 1, 1, 3, 1, 3, 4, 1, 4, 2]
def baseStart_6281968 : Nat := 118140960795 + 6281968 * 2 ^ 59
def prefixEnd_6281968 : Nat := 4983230072969 + 3 ^ 40 * 6281968 * 2
def baseEnd_6281968 : Nat := 3225669040163583005009761

theorem tailTrace_6281968 : CollatzResearch.WordTrace tailWord_6281968 prefixEnd_6281968 3225669040163583005009761 := by
  unfold tailWord_6281968
  simp only [CollatzResearch.WordTrace]
  refine ⟨114561098052755142781795279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152748130737006857042393705 114561098052755142781795279)
  ·
    refine ⟨171841647079132714172692919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114561098052755142781795279 171841647079132714172692919)
    ·
      refine ⟨257762470618699071259039379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171841647079132714172692919 257762470618699071259039379)
      ·
        refine ⟨386643705928048606888559069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257762470618699071259039379 386643705928048606888559069)
        ·
          refine ⟨144991389723018227583209651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 386643705928048606888559069 144991389723018227583209651)
          ·
            refine ⟨217487084584527341374814477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144991389723018227583209651 217487084584527341374814477)
            ·
              refine ⟨81557656719197753015555429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217487084584527341374814477 81557656719197753015555429)
              ·
                refine ⟨15292060634849578690416643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81557656719197753015555429 15292060634849578690416643)
                ·
                  refine ⟨22938090952274368035624965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15292060634849578690416643 22938090952274368035624965)
                  ·
                    refine ⟨4300892053551444006679681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22938090952274368035624965 4300892053551444006679681)
                    ·
                      refine ⟨3225669040163583005009761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4300892053551444006679681 3225669040163583005009761)
                      ·
                        rfl

theorem cell23_6281968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 1, 4, 2].length) (baseStart_6281968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281968 prefixEnd_6281968 := by exact prefixLift 6281968
  have htrace : WordTrace (prefixWord ++ tailWord_6281968) baseStart_6281968 baseEnd_6281968 := by
    simpa [prefixWord, tailWord_6281968, baseEnd_6281968] using wordTrace_append hprefix tailTrace_6281968
  have hstable : (prefixWord ++ tailWord_6281968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281968).length < 2 ^ (prefixWord ++ tailWord_6281968).sum := by decide
  have hdescent : baseEnd_6281968 < baseStart_6281968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6281981 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_6281981 : Nat := 118140960795 + 6281981 * 2 ^ 59
def prefixEnd_6281981 : Nat := 4983230072969 + 3 ^ 40 * 6281981 * 2
def baseEnd_6281981 : Nat := 3225675715412091454147201

theorem tailTrace_6281981 : CollatzResearch.WordTrace tailWord_6281981 prefixEnd_6281981 3225675715412091454147201 := by
  unfold tailWord_6281981
  simp only [CollatzResearch.WordTrace]
  refine ⟨229122670254463188783813797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152748446836308792522542531 229122670254463188783813797)
  ·
    refine ⟨42960500672711847896965087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229122670254463188783813797 42960500672711847896965087)
    ·
      refine ⟨64440751009067771845447631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42960500672711847896965087 64440751009067771845447631)
      ·
        refine ⟨96661126513601657768171447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64440751009067771845447631 96661126513601657768171447)
        ·
          refine ⟨144991689770402486652257171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96661126513601657768171447 144991689770402486652257171)
          ·
            refine ⟨217487534655603729978385757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144991689770402486652257171 217487534655603729978385757)
            ·
              refine ⟨81557825495851398741894659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217487534655603729978385757 81557825495851398741894659)
              ·
                refine ⟨122336738243777098112841989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81557825495851398741894659 122336738243777098112841989)
                ·
                  refine ⟨22938138420708205896157873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122336738243777098112841989 22938138420708205896157873)
                  ·
                    refine ⟨17203603815531154422118405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22938138420708205896157873 17203603815531154422118405)
                    ·
                      refine ⟨3225675715412091454147201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17203603815531154422118405 3225675715412091454147201)
                      ·
                        rfl

theorem cell23_6281981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_6281981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6281981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6281981 prefixEnd_6281981 := by exact prefixLift 6281981
  have htrace : WordTrace (prefixWord ++ tailWord_6281981) baseStart_6281981 baseEnd_6281981 := by
    simpa [prefixWord, tailWord_6281981, baseEnd_6281981] using wordTrace_append hprefix tailTrace_6281981
  have hstable : (prefixWord ++ tailWord_6281981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6281981).length < 2 ^ (prefixWord ++ tailWord_6281981).sum := by decide
  have hdescent : baseEnd_6281981 < baseStart_6281981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6281981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282021 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 1, 7]
def baseStart_6282021 : Nat := 118140960795 + 6282021 * 2 ^ 59
def prefixEnd_6282021 : Nat := 4983230072969 + 3 ^ 40 * 6282021 * 2
def baseEnd_6282021 : Nat := 1075232084879423765882339

theorem tailTrace_6282021 : CollatzResearch.WordTrace tailWord_6282021 prefixEnd_6282021 1075232084879423765882339 := by
  unfold tailWord_6282021
  simp only [CollatzResearch.WordTrace]
  refine ⟨229124129174318275615269917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152749419449545517076846611 229124129174318275615269917)
  ·
    refine ⟨85921548440369353355726219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229124129174318275615269917 85921548440369353355726219)
    ·
      refine ⟨128882322660554030033589329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85921548440369353355726219 128882322660554030033589329)
      ·
        refine ⟨96661741995415522525191997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128882322660554030033589329 96661741995415522525191997)
        ·
          refine ⟨36248153248280820946946999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96661741995415522525191997 36248153248280820946946999)
          ·
            refine ⟨54372229872421231420420499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36248153248280820946946999 54372229872421231420420499)
            ·
              refine ⟨81558344808631847130630749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54372229872421231420420499 81558344808631847130630749)
              ·
                refine ⟨30584379303236942673986531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81558344808631847130630749 30584379303236942673986531)
                ·
                  refine ⟨45876568954855414010979797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30584379303236942673986531 45876568954855414010979797)
                  ·
                    refine ⟨1075232084879423765882339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45876568954855414010979797 1075232084879423765882339)
                    ·
                      rfl

theorem cell23_6282021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_6282021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282021 prefixEnd_6282021 := by exact prefixLift 6282021
  have htrace : WordTrace (prefixWord ++ tailWord_6282021) baseStart_6282021 baseEnd_6282021 := by
    simpa [prefixWord, tailWord_6282021, baseEnd_6282021] using wordTrace_append hprefix tailTrace_6282021
  have hstable : (prefixWord ++ tailWord_6282021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282021).length < 2 ^ (prefixWord ++ tailWord_6282021).sum := by decide
  have hdescent : baseEnd_6282021 < baseStart_6282021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282042 : List Nat := [3, 1, 1, 1, 6, 1, 3, 2, 5]
def baseStart_6282042 : Nat := 118140960795 + 6282042 * 2 ^ 59
def prefixEnd_6282042 : Nat := 4983230072969 + 3 ^ 40 * 6282042 * 2
def baseEnd_6282042 : Nat := 358411893081335079498269

theorem tailTrace_6282042 : CollatzResearch.WordTrace tailWord_6282042 prefixEnd_6282042 358411893081335079498269 := by
  unfold tailWord_6282042
  simp only [CollatzResearch.WordTrace]
  refine ⟨57281223776810549050446095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152749930071494797467856253 57281223776810549050446095)
  ·
    refine ⟨85921835665215823575669143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57281223776810549050446095 85921835665215823575669143)
    ·
      refine ⟨128882753497823735363503715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85921835665215823575669143 128882753497823735363503715)
      ·
        refine ⟨193324130246735603045255573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128882753497823735363503715 193324130246735603045255573)
        ·
          refine ⟨9062068605315731392746355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 193324130246735603045255573 9062068605315731392746355)
          ·
            refine ⟨13593102907973597089119533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9062068605315731392746355 13593102907973597089119533)
            ·
              refine ⟨5097413590490098908419825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13593102907973597089119533 5097413590490098908419825)
              ·
                refine ⟨3823060192867574181314869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5097413590490098908419825 3823060192867574181314869)
                ·
                  refine ⟨358411893081335079498269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3823060192867574181314869 358411893081335079498269)
                  ·
                    rfl

theorem cell23_6282042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 5].length) (baseStart_6282042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282042 prefixEnd_6282042 := by exact prefixLift 6282042
  have htrace : WordTrace (prefixWord ++ tailWord_6282042) baseStart_6282042 baseEnd_6282042 := by
    simpa [prefixWord, tailWord_6282042, baseEnd_6282042] using wordTrace_append hprefix tailTrace_6282042
  have hstable : (prefixWord ++ tailWord_6282042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282042).length < 2 ^ (prefixWord ++ tailWord_6282042).sum := by decide
  have hdescent : baseEnd_6282042 < baseStart_6282042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282081 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 8]
def baseStart_6282081 : Nat := 118140960795 + 6282081 * 2 ^ 59
def prefixEnd_6282081 : Nat := 4983230072969 + 3 ^ 40 * 6282081 * 2
def baseEnd_6282081 : Nat := 358414118164171229210749

theorem tailTrace_6282081 : CollatzResearch.WordTrace tailWord_6282081 prefixEnd_6282081 358414118164171229210749 := by
  unfold tailWord_6282081
  simp only [CollatzResearch.WordTrace]
  refine ⟨229126317554100905862454097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152750878369400603908302731 229126317554100905862454097)
  ·
    refine ⟨171844738165575679396840573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229126317554100905862454097 171844738165575679396840573)
    ·
      refine ⟨64441776812090879773815215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171844738165575679396840573 64441776812090879773815215)
      ·
        refine ⟨96662665218136319660722823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64441776812090879773815215 96662665218136319660722823)
        ·
          refine ⟨144993997827204479491084235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96662665218136319660722823 144993997827204479491084235)
          ·
            refine ⟨217490996740806719236626353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144993997827204479491084235 217490996740806719236626353)
            ·
              refine ⟨163118247555605039427469765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217490996740806719236626353 163118247555605039427469765)
              ·
                refine ⟨30584671416675944892650581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163118247555605039427469765 30584671416675944892650581)
                ·
                  refine ⟨358414118164171229210749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30584671416675944892650581 358414118164171229210749)
                  ·
                    rfl

theorem cell23_6282081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 8].length) (baseStart_6282081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282081 prefixEnd_6282081 := by exact prefixLift 6282081
  have htrace : WordTrace (prefixWord ++ tailWord_6282081) baseStart_6282081 baseEnd_6282081 := by
    simpa [prefixWord, tailWord_6282081, baseEnd_6282081] using wordTrace_append hprefix tailTrace_6282081
  have hstable : (prefixWord ++ tailWord_6282081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282081).length < 2 ^ (prefixWord ++ tailWord_6282081).sum := by decide
  have hdescent : baseEnd_6282081 < baseStart_6282081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282098 : List Nat := [3, 2, 1, 2, 1, 1, 3, 4, 6]
def baseStart_6282098 : Nat := 118140960795 + 6282098 * 2 ^ 59
def prefixEnd_6282098 : Nat := 4983230072969 + 3 ^ 40 * 6282098 * 2
def baseEnd_6282098 : Nat := 358415088072074166264907

theorem tailTrace_6282098 : CollatzResearch.WordTrace tailWord_6282098 prefixEnd_6282098 358415088072074166264907 := by
  unfold tailWord_6282098
  simp only [CollatzResearch.WordTrace]
  refine ⟨57281734398759829441455737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152751291730026211843881965 57281734398759829441455737)
  ·
    refine ⟨42961300799069872081091803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57281734398759829441455737 42961300799069872081091803)
    ·
      refine ⟨64441951198604808121637705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42961300799069872081091803 64441951198604808121637705)
      ·
        refine ⟨48331463398953606091228279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64441951198604808121637705 48331463398953606091228279)
        ·
          refine ⟨72497195098430409136842419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48331463398953606091228279 72497195098430409136842419)
          ·
            refine ⟨108745792647645613705263629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72497195098430409136842419 108745792647645613705263629)
            ·
              refine ⟨40779672242867105139473861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108745792647645613705263629 40779672242867105139473861)
              ·
                refine ⟨7646188545537582213651349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40779672242867105139473861 7646188545537582213651349)
                ·
                  refine ⟨358415088072074166264907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7646188545537582213651349 358415088072074166264907)
                  ·
                    rfl

theorem cell23_6282098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_6282098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282098 prefixEnd_6282098 := by exact prefixLift 6282098
  have htrace : WordTrace (prefixWord ++ tailWord_6282098) baseStart_6282098 baseEnd_6282098 := by
    simpa [prefixWord, tailWord_6282098, baseEnd_6282098] using wordTrace_append hprefix tailTrace_6282098
  have hstable : (prefixWord ++ tailWord_6282098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282098).length < 2 ^ (prefixWord ++ tailWord_6282098).sum := by decide
  have hdescent : baseEnd_6282098 < baseStart_6282098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282135 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 1, 5, 2]
def baseStart_6282135 : Nat := 118140960795 + 6282135 * 2 ^ 59
def prefixEnd_6282135 : Nat := 4983230072969 + 3 ^ 40 * 6282135 * 2
def baseEnd_6282135 : Nat := 3225754791432883851621493

theorem tailTrace_6282135 : CollatzResearch.WordTrace tailWord_6282135 prefixEnd_6282135 3225754791432883851621493 := by
  unfold tailWord_6282135
  simp only [CollatzResearch.WordTrace]
  refine ⟨229128287095905273084919859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152752191397270182056613239 229128287095905273084919859)
  ·
    refine ⟨343692430643857909627379789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229128287095905273084919859 343692430643857909627379789)
    ·
      refine ⟨128884661491446716110267421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343692430643857909627379789 128884661491446716110267421)
      ·
        refine ⟨48331748059292518541350283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128884661491446716110267421 48331748059292518541350283)
        ·
          refine ⟨72497622088938777812025425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48331748059292518541350283 72497622088938777812025425)
          ·
            refine ⟨54373216566704083359019069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72497622088938777812025425 54373216566704083359019069)
            ·
              refine ⟨20389956212514031259632151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54373216566704083359019069 20389956212514031259632151)
              ·
                refine ⟨30584934318771046889448227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20389956212514031259632151 30584934318771046889448227)
                ·
                  refine ⟨45877401478156570334172341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30584934318771046889448227 45877401478156570334172341)
                  ·
                    refine ⟨4301006388577178468828657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45877401478156570334172341 4301006388577178468828657)
                    ·
                      refine ⟨3225754791432883851621493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4301006388577178468828657 3225754791432883851621493)
                      ·
                        rfl

theorem cell23_6282135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_6282135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282135 prefixEnd_6282135 := by exact prefixLift 6282135
  have htrace : WordTrace (prefixWord ++ tailWord_6282135) baseStart_6282135 baseEnd_6282135 := by
    simpa [prefixWord, tailWord_6282135, baseEnd_6282135] using wordTrace_append hprefix tailTrace_6282135
  have hstable : (prefixWord ++ tailWord_6282135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282135).length < 2 ^ (prefixWord ++ tailWord_6282135).sum := by decide
  have hdescent : baseEnd_6282135 < baseStart_6282135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282168 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 3, 1, 5]
def baseStart_6282168 : Nat := 118140960795 + 6282168 * 2 ^ 59
def prefixEnd_6282168 : Nat := 4983230072969 + 3 ^ 40 * 6282168 * 2
def baseEnd_6282168 : Nat := 3225771736294482222508841

theorem tailTrace_6282168 : CollatzResearch.WordTrace tailWord_6282168 prefixEnd_6282168 3225771736294482222508841 := by
  unfold tailWord_6282168
  simp only [CollatzResearch.WordTrace]
  refine ⟨114564745352392859860435579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152752993803190479813914105 114564745352392859860435579)
  ·
    refine ⟨171847118028589289790653369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114564745352392859860435579 171847118028589289790653369)
    ·
      refine ⟨128885338521441967342990027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171847118028589289790653369 128885338521441967342990027)
      ·
        refine ⟨193328007782162951014485041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128885338521441967342990027 193328007782162951014485041)
        ·
          refine ⟨144996005836622213260863781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193328007782162951014485041 144996005836622213260863781)
          ·
            refine ⟨27186751094366664986411959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144996005836622213260863781 27186751094366664986411959)
            ·
              refine ⟨40780126641549997479617939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27186751094366664986411959 40780126641549997479617939)
              ·
                refine ⟨61170189962324996219426909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40780126641549997479617939 61170189962324996219426909)
                ·
                  refine ⟨22938821235871873582285091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61170189962324996219426909 22938821235871873582285091)
                  ·
                    refine ⟨34408231853807810373427637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22938821235871873582285091 34408231853807810373427637)
                    ·
                      refine ⟨3225771736294482222508841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34408231853807810373427637 3225771736294482222508841)
                      ·
                        rfl

theorem cell23_6282168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_6282168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282168 prefixEnd_6282168 := by exact prefixLift 6282168
  have htrace : WordTrace (prefixWord ++ tailWord_6282168) baseStart_6282168 baseEnd_6282168 := by
    simpa [prefixWord, tailWord_6282168, baseEnd_6282168] using wordTrace_append hprefix tailTrace_6282168
  have hstable : (prefixWord ++ tailWord_6282168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282168).length < 2 ^ (prefixWord ++ tailWord_6282168).sum := by decide
  have hdescent : baseEnd_6282168 < baseStart_6282168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282188 : List Nat := [2, 2, 1, 4, 1, 1, 3, 9]
def baseStart_6282188 : Nat := 118140960795 + 6282188 * 2 ^ 59
def prefixEnd_6282188 : Nat := 4983230072969 + 3 ^ 40 * 6282188 * 2
def baseEnd_6282188 : Nat := 119473407626206375713287

theorem tailTrace_6282188 : CollatzResearch.WordTrace tailWord_6282188 prefixEnd_6282188 119473407626206375713287 := by
  unfold tailWord_6282188
  simp only [CollatzResearch.WordTrace]
  refine ⟨114565110082356631568299609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152753480109808842091066145 114565110082356631568299609)
  ·
    refine ⟨85923832561767473676224707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114565110082356631568299609 85923832561767473676224707)
    ·
      refine ⟨128885748842651210514337061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85923832561767473676224707 128885748842651210514337061)
      ·
        refine ⟨24166077907997101971438199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128885748842651210514337061 24166077907997101971438199)
        ·
          refine ⟨36249116861995652957157299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24166077907997101971438199 36249116861995652957157299)
          ·
            refine ⟨54373675292993479435735949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36249116861995652957157299 54373675292993479435735949)
            ·
              refine ⟨20390128234872554788400981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54373675292993479435735949 20390128234872554788400981)
              ·
                refine ⟨119473407626206375713287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20390128234872554788400981 119473407626206375713287)
                ·
                  rfl

theorem cell23_6282188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 9].length) (baseStart_6282188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282188 prefixEnd_6282188 := by exact prefixLift 6282188
  have htrace : WordTrace (prefixWord ++ tailWord_6282188) baseStart_6282188 baseEnd_6282188 := by
    simpa [prefixWord, tailWord_6282188, baseEnd_6282188] using wordTrace_append hprefix tailTrace_6282188
  have hstable : (prefixWord ++ tailWord_6282188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282188).length < 2 ^ (prefixWord ++ tailWord_6282188).sum := by decide
  have hdescent : baseEnd_6282188 < baseStart_6282188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282199 : List Nat := [1, 1, 3, 2, 1, 1, 2, 7, 1, 2, 2]
def baseStart_6282199 : Nat := 118140960795 + 6282199 * 2 ^ 59
def prefixEnd_6282199 : Nat := 4983230072969 + 3 ^ 40 * 6282199 * 2
def baseEnd_6282199 : Nat := 3225787654194771601221199

theorem tailTrace_6282199 : CollatzResearch.WordTrace tailWord_6282199 prefixEnd_6282199 3225787654194771601221199 := by
  unfold tailWord_6282199
  simp only [CollatzResearch.WordTrace]
  refine ⟨229130621367673412015249651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152753747578448941343499767 229130621367673412015249651)
  ·
    refine ⟨343695932051510118022874477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229130621367673412015249651 343695932051510118022874477)
    ·
      refine ⟨128885974519316294258577929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343695932051510118022874477 128885974519316294258577929)
      ·
        refine ⟨96664480889487220693933447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128885974519316294258577929 96664480889487220693933447)
        ·
          refine ⟨144996721334230831040900171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96664480889487220693933447 144996721334230831040900171)
          ·
            refine ⟨217495082001346246561350257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144996721334230831040900171 217495082001346246561350257)
            ·
              refine ⟨163121311501009684921012693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217495082001346246561350257 163121311501009684921012693)
              ·
                refine ⟨3823155738304914490336235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 163121311501009684921012693 3823155738304914490336235)
                ·
                  refine ⟨5734733607457371735504353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3823155738304914490336235 5734733607457371735504353)
                  ·
                    refine ⟨4301050205593028801628265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5734733607457371735504353 4301050205593028801628265)
                    ·
                      refine ⟨3225787654194771601221199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4301050205593028801628265 3225787654194771601221199)
                      ·
                        rfl

theorem cell23_6282199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 1, 2, 2].length) (baseStart_6282199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282199 prefixEnd_6282199 := by exact prefixLift 6282199
  have htrace : WordTrace (prefixWord ++ tailWord_6282199) baseStart_6282199 baseEnd_6282199 := by
    simpa [prefixWord, tailWord_6282199, baseEnd_6282199] using wordTrace_append hprefix tailTrace_6282199
  have hstable : (prefixWord ++ tailWord_6282199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282199).length < 2 ^ (prefixWord ++ tailWord_6282199).sum := by decide
  have hdescent : baseEnd_6282199 < baseStart_6282199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282202 : List Nat := [3, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3]
def baseStart_6282202 : Nat := 118140960795 + 6282202 * 2 ^ 59
def prefixEnd_6282202 : Nat := 4983230072969 + 3 ^ 40 * 6282202 * 2
def baseEnd_6282202 : Nat := 3225789194636735089483685

theorem tailTrace_6282202 : CollatzResearch.WordTrace tailWord_6282202 prefixEnd_6282202 3225789194636735089483685 := by
  unfold tailWord_6282202
  simp only [CollatzResearch.WordTrace]
  refine ⟨57282682696665635881902215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152753820524441695685072573 57282682696665635881902215)
  ·
    refine ⟨85924024044998453822853323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57282682696665635881902215 85924024044998453822853323)
    ·
      refine ⟨128886036067497680734279985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85924024044998453822853323 128886036067497680734279985)
      ·
        refine ⟨96664527050623260550709989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128886036067497680734279985 96664527050623260550709989)
        ·
          refine ⟨18124598821991861353258123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96664527050623260550709989 18124598821991861353258123)
          ·
            refine ⟨27186898232987792029887185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18124598821991861353258123 27186898232987792029887185)
            ·
              refine ⟨20390173674740844022415389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27186898232987792029887185 20390173674740844022415389)
              ·
                refine ⟨7646315128027816508405771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20390173674740844022415389 7646315128027816508405771)
                ·
                  refine ⟨11469472692041724762608657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7646315128027816508405771 11469472692041724762608657)
                  ·
                    refine ⟨8602104519031293571956493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11469472692041724762608657 8602104519031293571956493)
                    ·
                      refine ⟨3225789194636735089483685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8602104519031293571956493 3225789194636735089483685)
                      ·
                        rfl

theorem cell23_6282202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_6282202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282202 prefixEnd_6282202 := by exact prefixLift 6282202
  have htrace : WordTrace (prefixWord ++ tailWord_6282202) baseStart_6282202 baseEnd_6282202 := by
    simpa [prefixWord, tailWord_6282202, baseEnd_6282202] using wordTrace_append hprefix tailTrace_6282202
  have hstable : (prefixWord ++ tailWord_6282202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282202).length < 2 ^ (prefixWord ++ tailWord_6282202).sum := by decide
  have hdescent : baseEnd_6282202 < baseStart_6282202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282205 : List Nat := [1, 4, 3, 1, 2, 3, 9]
def baseStart_6282205 : Nat := 118140960795 + 6282205 * 2 ^ 59
def prefixEnd_6282205 : Nat := 4983230072969 + 3 ^ 40 * 6282205 * 2
def baseEnd_6282205 : Nat := 39824576976280229354891

theorem tailTrace_6282205 : CollatzResearch.WordTrace tailWord_6282205 prefixEnd_6282205 39824576976280229354891 := by
  unfold tailWord_6282205
  simp only [CollatzResearch.WordTrace]
  refine ⟨229130840205651675039968069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152753893470434450026645379 229130840205651675039968069)
  ·
    refine ⟨42962032538559689069994013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229130840205651675039968069 42962032538559689069994013)
    ·
      refine ⟨16110762201959883401247755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42962032538559689069994013 16110762201959883401247755)
      ·
        refine ⟨24166143302939825101871633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16110762201959883401247755 24166143302939825101871633)
        ·
          refine ⟨18124607477204868826403725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24166143302939825101871633 18124607477204868826403725)
          ·
            refine ⟨6796727803951825809901397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18124607477204868826403725 6796727803951825809901397)
            ·
              refine ⟨39824576976280229354891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6796727803951825809901397 39824576976280229354891)
              ·
                rfl

theorem cell23_6282205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 9].length) (baseStart_6282205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282205 prefixEnd_6282205 := by exact prefixLift 6282205
  have htrace : WordTrace (prefixWord ++ tailWord_6282205) baseStart_6282205 baseEnd_6282205 := by
    simpa [prefixWord, tailWord_6282205, baseEnd_6282205] using wordTrace_append hprefix tailTrace_6282205
  have hstable : (prefixWord ++ tailWord_6282205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282205).length < 2 ^ (prefixWord ++ tailWord_6282205).sum := by decide
  have hdescent : baseEnd_6282205 < baseStart_6282205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282275 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 3]
def baseStart_6282275 : Nat := 118140960795 + 6282275 * 2 ^ 59
def prefixEnd_6282275 : Nat := 4983230072969 + 3 ^ 40 * 6282275 * 2
def baseEnd_6282275 : Nat := 3225826678724513303870849

theorem tailTrace_6282275 : CollatzResearch.WordTrace tailWord_6282275 prefixEnd_6282275 3225826678724513303870849 := by
  unfold tailWord_6282275
  simp only [CollatzResearch.WordTrace]
  refine ⟨229133393315398076995016279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152755595543598717996677519 229133393315398076995016279)
  ·
    refine ⟨343700089973097115492524419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229133393315398076995016279 343700089973097115492524419)
    ·
      refine ⟨515550134959645673238786629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343700089973097115492524419 515550134959645673238786629)
      ·
        refine ⟨96665650304933563732272493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 515550134959645673238786629 96665650304933563732272493)
        ·
          refine ⟨36249618864350086399602185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96665650304933563732272493 36249618864350086399602185)
          ·
            refine ⟨27187214148262564799701639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36249618864350086399602185 27187214148262564799701639)
            ·
              refine ⟨40780821222393847199552459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27187214148262564799701639 40780821222393847199552459)
              ·
                refine ⟨61171231833590770799328689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40780821222393847199552459 61171231833590770799328689)
                ·
                  refine ⟨45878423875193078099496517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61171231833590770799328689 45878423875193078099496517)
                  ·
                    refine ⟨8602204476598702143655597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45878423875193078099496517 8602204476598702143655597)
                    ·
                      refine ⟨3225826678724513303870849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8602204476598702143655597 3225826678724513303870849)
                      ·
                        rfl

theorem cell23_6282275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_6282275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282275 prefixEnd_6282275 := by exact prefixLift 6282275
  have htrace : WordTrace (prefixWord ++ tailWord_6282275) baseStart_6282275 baseEnd_6282275 := by
    simpa [prefixWord, tailWord_6282275, baseEnd_6282275] using wordTrace_append hprefix tailTrace_6282275
  have hstable : (prefixWord ++ tailWord_6282275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282275).length < 2 ^ (prefixWord ++ tailWord_6282275).sum := by decide
  have hdescent : baseEnd_6282275 < baseStart_6282275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282282 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 2, 6]
def baseStart_6282282 : Nat := 118140960795 + 6282282 * 2 ^ 59
def prefixEnd_6282282 : Nat := 4983230072969 + 3 ^ 40 * 6282282 * 2
def baseEnd_6282282 : Nat := 1075276757696364925494439

theorem tailTrace_6282282 : CollatzResearch.WordTrace tailWord_6282282 prefixEnd_6282282 1075276757696364925494439 := by
  unfold tailWord_6282282
  simp only [CollatzResearch.WordTrace]
  refine ⟨57283412156593179297630275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152755765750915144793680733 57283412156593179297630275)
  ·
    refine ⟨85925118234889768946445413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57283412156593179297630275 85925118234889768946445413)
    ·
      refine ⟨16110959669041831677458515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85925118234889768946445413 16110959669041831677458515)
      ·
        refine ⟨24166439503562747516187773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16110959669041831677458515 24166439503562747516187773)
        ·
          refine ⟨9062414813836030318570415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24166439503562747516187773 9062414813836030318570415)
          ·
            refine ⟨13593622220754045477855623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9062414813836030318570415 13593622220754045477855623)
            ·
              refine ⟨20390433331131068216783435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13593622220754045477855623 20390433331131068216783435)
              ·
                refine ⟨30585649996696602325175153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20390433331131068216783435 30585649996696602325175153)
                ·
                  refine ⟨22939237497522451743881365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30585649996696602325175153 22939237497522451743881365)
                  ·
                    refine ⟨1075276757696364925494439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22939237497522451743881365 1075276757696364925494439)
                    ·
                      rfl

theorem cell23_6282282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_6282282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282282 prefixEnd_6282282 := by exact prefixLift 6282282
  have htrace : WordTrace (prefixWord ++ tailWord_6282282) baseStart_6282282 baseEnd_6282282 := by
    simpa [prefixWord, tailWord_6282282, baseEnd_6282282] using wordTrace_append hprefix tailTrace_6282282
  have hstable : (prefixWord ++ tailWord_6282282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282282).length < 2 ^ (prefixWord ++ tailWord_6282282).sum := by decide
  have hdescent : baseEnd_6282282 < baseStart_6282282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282289 : List Nat := [1, 2, 2, 3, 1, 2, 1, 5, 2, 2, 2]
def baseStart_6282289 : Nat := 118140960795 + 6282289 * 2 ^ 59
def prefixEnd_6282289 : Nat := 4983230072969 + 3 ^ 40 * 6282289 * 2
def baseEnd_6282289 : Nat := 3225833867453676249095785

theorem tailTrace_6282289 : CollatzResearch.WordTrace tailWord_6282289 prefixEnd_6282289 3225833867453676249095785 := by
  unfold tailWord_6282289
  simp only [CollatzResearch.WordTrace]
  refine ⟨229133903937347357386025921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152755935958231571590683947 229133903937347357386025921)
  ·
    refine ⟨171850427953010518039519441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229133903937347357386025921 171850427953010518039519441)
    ·
      refine ⟨128887820964757888529639581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171850427953010518039519441 128887820964757888529639581)
      ·
        refine ⟨48332932861784208198614843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128887820964757888529639581 48332932861784208198614843)
        ·
          refine ⟨72499399292676312297922265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48332932861784208198614843 72499399292676312297922265)
          ·
            refine ⟨54374549469507234223441699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72499399292676312297922265 54374549469507234223441699)
            ·
              refine ⟨81561824204260851335162549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54374549469507234223441699 81561824204260851335162549)
              ·
                refine ⟨7646421019149454812671489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81561824204260851335162549 7646421019149454812671489)
                ·
                  refine ⟨5734815764362091109503617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7646421019149454812671489 5734815764362091109503617)
                  ·
                    refine ⟨4301111823271568332127713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5734815764362091109503617 4301111823271568332127713)
                    ·
                      refine ⟨3225833867453676249095785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4301111823271568332127713 3225833867453676249095785)
                      ·
                        rfl

theorem cell23_6282289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_6282289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282289 prefixEnd_6282289 := by exact prefixLift 6282289
  have htrace : WordTrace (prefixWord ++ tailWord_6282289) baseStart_6282289 baseEnd_6282289 := by
    simpa [prefixWord, tailWord_6282289, baseEnd_6282289] using wordTrace_append hprefix tailTrace_6282289
  have hstable : (prefixWord ++ tailWord_6282289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282289).length < 2 ^ (prefixWord ++ tailWord_6282289).sum := by decide
  have hdescent : baseEnd_6282289 < baseStart_6282289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282310 : List Nat := [6, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_6282310 : Nat := 118140960795 + 6282310 * 2 ^ 59
def prefixEnd_6282310 : Nat := 4983230072969 + 3 ^ 40 * 6282310 * 2
def baseEnd_6282310 : Nat := 3225844650547420666933189

theorem tailTrace_6282310 : CollatzResearch.WordTrace tailWord_6282310 prefixEnd_6282310 3225844650547420666933189 := by
  unfold tailWord_6282310
  simp only [CollatzResearch.WordTrace]
  refine ⟨7160458433445977436641887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 152756446580180851981693589 7160458433445977436641887)
  ·
    refine ⟨10740687650168966154962831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7160458433445977436641887 10740687650168966154962831)
    ·
      refine ⟨16111031475253449232444247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10740687650168966154962831 16111031475253449232444247)
      ·
        refine ⟨24166547212880173848666371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16111031475253449232444247 24166547212880173848666371)
        ·
          refine ⟨36249820819320260772999557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24166547212880173848666371 36249820819320260772999557)
          ·
            refine ⟨6796841403622548894937417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36249820819320260772999557 6796841403622548894937417)
            ·
              refine ⟨5097631052716911671203063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6796841403622548894937417 5097631052716911671203063)
              ·
                refine ⟨7646446579075367506804595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5097631052716911671203063 7646446579075367506804595)
                ·
                  refine ⟨11469669868613051260206893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7646446579075367506804595 11469669868613051260206893)
                  ·
                    refine ⟨4301126200729894222577585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11469669868613051260206893 4301126200729894222577585)
                    ·
                      refine ⟨3225844650547420666933189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4301126200729894222577585 3225844650547420666933189)
                      ·
                        rfl

theorem cell23_6282310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_6282310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282310 prefixEnd_6282310 := by exact prefixLift 6282310
  have htrace : WordTrace (prefixWord ++ tailWord_6282310) baseStart_6282310 baseEnd_6282310 := by
    simpa [prefixWord, tailWord_6282310, baseEnd_6282310] using wordTrace_append hprefix tailTrace_6282310
  have hstable : (prefixWord ++ tailWord_6282310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282310).length < 2 ^ (prefixWord ++ tailWord_6282310).sum := by decide
  have hdescent : baseEnd_6282310 < baseStart_6282310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282312 : List Nat := [2, 1, 3, 1, 1, 1, 6, 3, 5]
def baseStart_6282312 : Nat := 118140960795 + 6282312 * 2 ^ 59
def prefixEnd_6282312 : Nat := 4983230072969 + 3 ^ 40 * 6282312 * 2
def baseEnd_6282312 : Nat := 358427297500969962123131

theorem tailTrace_6282312 : CollatzResearch.WordTrace tailWord_6282312 prefixEnd_6282312 358427297500969962123131 := by
  unfold tailWord_6282312
  simp only [CollatzResearch.WordTrace]
  refine ⟨114567371408132016157056595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152756495210842688209408793 114567371408132016157056595)
  ·
    refine ⟨171851057112198024235584893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114567371408132016157056595 171851057112198024235584893)
    ·
      refine ⟨64444146417074259088344335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171851057112198024235584893 64444146417074259088344335)
      ·
        refine ⟨96666219625611388632516503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64444146417074259088344335 96666219625611388632516503)
        ·
          refine ⟨144999329438417082948774755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96666219625611388632516503 144999329438417082948774755)
          ·
            refine ⟨217498994157625624423162133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144999329438417082948774755 217498994157625624423162133)
            ·
              refine ⟨10195265351138701144835725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 217498994157625624423162133 10195265351138701144835725)
              ·
                refine ⟨3823224506677012929313397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10195265351138701144835725 3823224506677012929313397)
                ·
                  refine ⟨358427297500969962123131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3823224506677012929313397 358427297500969962123131)
                  ·
                    rfl

theorem cell23_6282312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 5].length) (baseStart_6282312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282312 prefixEnd_6282312 := by exact prefixLift 6282312
  have htrace : WordTrace (prefixWord ++ tailWord_6282312) baseStart_6282312 baseEnd_6282312 := by
    simpa [prefixWord, tailWord_6282312, baseEnd_6282312] using wordTrace_append hprefix tailTrace_6282312
  have hstable : (prefixWord ++ tailWord_6282312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282312).length < 2 ^ (prefixWord ++ tailWord_6282312).sum := by decide
  have hdescent : baseEnd_6282312 < baseStart_6282312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282322 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_6282322 : Nat := 118140960795 + 6282322 * 2 ^ 59
def prefixEnd_6282322 : Nat := 4983230072969 + 3 ^ 40 * 6282322 * 2
def baseEnd_6282322 : Nat := 3225850812315274619983133

theorem tailTrace_6282322 : CollatzResearch.WordTrace tailWord_6282322 prefixEnd_6282322 3225850812315274619983133 := by
  unfold tailWord_6282322
  simp only [CollatzResearch.WordTrace]
  refine ⟨57283776886556951005494305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152756738364151869347984813 57283776886556951005494305)
  ·
    refine ⟨42962832664917713254120729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57283776886556951005494305 42962832664917713254120729)
    ·
      refine ⟨32222124498688284940590547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42962832664917713254120729 32222124498688284940590547)
      ·
        refine ⟨48333186748032427410885821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32222124498688284940590547 48333186748032427410885821)
        ·
          refine ⟨18124945030512160279082183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48333186748032427410885821 18124945030512160279082183)
          ·
            refine ⟨27187417545768240418623275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18124945030512160279082183 27187417545768240418623275)
            ·
              refine ⟨40781126318652360627934913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27187417545768240418623275 40781126318652360627934913)
              ·
                refine ⟨30585844738989270470951185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40781126318652360627934913 30585844738989270470951185)
                ·
                  refine ⟨22939383554241952853213389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30585844738989270470951185 22939383554241952853213389)
                  ·
                    refine ⟨8602268832840732319955021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22939383554241952853213389 8602268832840732319955021)
                    ·
                      refine ⟨3225850812315274619983133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8602268832840732319955021 3225850812315274619983133)
                      ·
                        rfl

theorem cell23_6282322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_6282322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282322 prefixEnd_6282322 := by exact prefixLift 6282322
  have htrace : WordTrace (prefixWord ++ tailWord_6282322) baseStart_6282322 baseEnd_6282322 := by
    simpa [prefixWord, tailWord_6282322, baseEnd_6282322] using wordTrace_append hprefix tailTrace_6282322
  have hstable : (prefixWord ++ tailWord_6282322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282322).length < 2 ^ (prefixWord ++ tailWord_6282322).sum := by decide
  have hdescent : baseEnd_6282322 < baseStart_6282322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282325 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 4, 5]
def baseStart_6282325 : Nat := 118140960795 + 6282325 * 2 ^ 59
def prefixEnd_6282325 : Nat := 4983230072969 + 3 ^ 40 * 6282325 * 2
def baseEnd_6282325 : Nat := 1075284117585746036081873

theorem tailTrace_6282325 : CollatzResearch.WordTrace tailWord_6282325 prefixEnd_6282325 1075284117585746036081873 := by
  unfold tailWord_6282325
  simp only [CollatzResearch.WordTrace]
  refine ⟨229135216965216935534336429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152756811310144623689557619 229135216965216935534336429)
  ·
    refine ⟨85925706361956350825376161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229135216965216935534336429 85925706361956350825376161)
    ·
      refine ⟨64444279771467263119032121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85925706361956350825376161 64444279771467263119032121)
      ·
        refine ⟨48333209828600447339274091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64444279771467263119032121 48333209828600447339274091)
        ·
          refine ⟨72499814742900671008911137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48333209828600447339274091 72499814742900671008911137)
          ·
            refine ⟨54374861057175503256683353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72499814742900671008911137 54374861057175503256683353)
            ·
              refine ⟨40781145792881627442512515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54374861057175503256683353 40781145792881627442512515)
              ·
                refine ⟨61171718689322441163768773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40781145792881627442512515 61171718689322441163768773)
                ·
                  refine ⟨11469697254247957718206645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61171718689322441163768773 11469697254247957718206645)
                  ·
                    refine ⟨1075284117585746036081873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11469697254247957718206645 1075284117585746036081873)
                    ·
                      rfl

theorem cell23_6282325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_6282325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282325 prefixEnd_6282325 := by exact prefixLift 6282325
  have htrace : WordTrace (prefixWord ++ tailWord_6282325) baseStart_6282325 baseEnd_6282325 := by
    simpa [prefixWord, tailWord_6282325, baseEnd_6282325] using wordTrace_append hprefix tailTrace_6282325
  have hstable : (prefixWord ++ tailWord_6282325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282325).length < 2 ^ (prefixWord ++ tailWord_6282325).sum := by decide
  have hdescent : baseEnd_6282325 < baseStart_6282325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282345 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 1, 3, 4]
def baseStart_6282345 : Nat := 118140960795 + 6282345 * 2 ^ 59
def prefixEnd_6282345 : Nat := 4983230072969 + 3 ^ 40 * 6282345 * 2
def baseEnd_6282345 : Nat := 3225862622370328029995527

theorem tailTrace_6282345 : CollatzResearch.WordTrace tailWord_6282345 prefixEnd_6282345 3225862622370328029995527 := by
  unfold tailWord_6282345
  simp only [CollatzResearch.WordTrace]
  refine ⟨229135946425144478950064489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152757297616762985966709659 229135946425144478950064489)
  ·
    refine ⟨171851959818858359212548367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229135946425144478950064489 171851959818858359212548367)
    ·
      refine ⟨257777939728287538818822551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171851959818858359212548367 257777939728287538818822551)
      ·
        refine ⟨386666909592431308228233827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257777939728287538818822551 386666909592431308228233827)
        ·
          refine ⟨580000364388646962342350741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386666909592431308228233827 580000364388646962342350741)
          ·
            refine ⟨27187517080717826359797691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 580000364388646962342350741 27187517080717826359797691)
            ·
              refine ⟨40781275621076739539696537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27187517080717826359797691 40781275621076739539696537)
              ·
                refine ⟨30585956715807554654772403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40781275621076739539696537 30585956715807554654772403)
                ·
                  refine ⟨45878935073711331982158605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30585956715807554654772403 45878935073711331982158605)
                  ·
                    refine ⟨17204600652641749493309477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45878935073711331982158605 17204600652641749493309477)
                    ·
                      refine ⟨3225862622370328029995527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17204600652641749493309477 3225862622370328029995527)
                      ·
                        rfl

theorem cell23_6282345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 3, 4].length) (baseStart_6282345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282345 prefixEnd_6282345 := by exact prefixLift 6282345
  have htrace : WordTrace (prefixWord ++ tailWord_6282345) baseStart_6282345 baseEnd_6282345 := by
    simpa [prefixWord, tailWord_6282345, baseEnd_6282345] using wordTrace_append hprefix tailTrace_6282345
  have hstable : (prefixWord ++ tailWord_6282345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282345).length < 2 ^ (prefixWord ++ tailWord_6282345).sum := by decide
  have hdescent : baseEnd_6282345 < baseStart_6282345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282395 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 3]
def baseStart_6282395 : Nat := 118140960795 + 6282395 * 2 ^ 59
def prefixEnd_6282395 : Nat := 4983230072969 + 3 ^ 40 * 6282395 * 2
def baseEnd_6282395 : Nat := 3225888296403052834370297

theorem tailTrace_6282395 : CollatzResearch.WordTrace tailWord_6282395 prefixEnd_6282395 3225888296403052834370297 := by
  unfold tailWord_6282395
  simp only [CollatzResearch.WordTrace]
  refine ⟨229137770074963337489384639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152758513383308891659589759 229137770074963337489384639)
  ·
    refine ⟨343706655112445006234076959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229137770074963337489384639 343706655112445006234076959)
    ·
      refine ⟨515559982668667509351115439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343706655112445006234076959 515559982668667509351115439)
      ·
        refine ⟨773339974003001264026673159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515559982668667509351115439 773339974003001264026673159)
        ·
          refine ⟨1160009961004501896040009739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 773339974003001264026673159 1160009961004501896040009739)
          ·
            refine ⟨1740014941506752844060014609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160009961004501896040009739 1740014941506752844060014609)
            ·
              refine ⟨1305011206130064633045010957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1740014941506752844060014609 1305011206130064633045010957)
              ·
                refine ⟨489379202298774237391879109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1305011206130064633045010957 489379202298774237391879109)
                ·
                  refine ⟨91758600431020169510977333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 489379202298774237391879109 91758600431020169510977333)
                  ·
                    refine ⟨8602368790408140891654125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91758600431020169510977333 8602368790408140891654125)
                    ·
                      refine ⟨3225888296403052834370297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8602368790408140891654125 3225888296403052834370297)
                      ·
                        rfl

theorem cell23_6282395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 3].length) (baseStart_6282395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282395 prefixEnd_6282395 := by exact prefixLift 6282395
  have htrace : WordTrace (prefixWord ++ tailWord_6282395) baseStart_6282395 baseEnd_6282395 := by
    simpa [prefixWord, tailWord_6282395, baseEnd_6282395] using wordTrace_append hprefix tailTrace_6282395
  have hstable : (prefixWord ++ tailWord_6282395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282395).length < 2 ^ (prefixWord ++ tailWord_6282395).sum := by decide
  have hdescent : baseEnd_6282395 < baseStart_6282395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282486 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2]
def baseStart_6282486 : Nat := 118140960795 + 6282486 * 2 ^ 59
def prefixEnd_6282486 : Nat := 4983230072969 + 3 ^ 40 * 6282486 * 2
def baseEnd_6282486 : Nat := 3225935023142611978332379

theorem tailTrace_6282486 : CollatzResearch.WordTrace tailWord_6282486 prefixEnd_6282486 3225935023142611978332379 := by
  unfold tailWord_6282486
  simp only [CollatzResearch.WordTrace]
  refine ⟨14321318069852103751934207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152760726078422440020631541 14321318069852103751934207)
  ·
    refine ⟨21481977104778155627901311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14321318069852103751934207 21481977104778155627901311)
    ·
      refine ⟨32222965657167233441851967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21481977104778155627901311 32222965657167233441851967)
      ·
        refine ⟨48334448485750850162777951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32222965657167233441851967 48334448485750850162777951)
        ·
          refine ⟨72501672728626275244166927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48334448485750850162777951 72501672728626275244166927)
          ·
            refine ⟨108752509092939412866250391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72501672728626275244166927 108752509092939412866250391)
            ·
              refine ⟨163128763639409119299375587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108752509092939412866250391 163128763639409119299375587)
              ·
                refine ⟨244693145459113678949063381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163128763639409119299375587 244693145459113678949063381)
                ·
                  refine ⟨5734995596697976850368673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 244693145459113678949063381 5734995596697976850368673)
                  ·
                    refine ⟨4301246697523482637776505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5734995596697976850368673 4301246697523482637776505)
                    ·
                      refine ⟨3225935023142611978332379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4301246697523482637776505 3225935023142611978332379)
                      ·
                        rfl

theorem cell23_6282486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_6282486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282486 prefixEnd_6282486 := by exact prefixLift 6282486
  have htrace : WordTrace (prefixWord ++ tailWord_6282486) baseStart_6282486 baseEnd_6282486 := by
    simpa [prefixWord, tailWord_6282486, baseEnd_6282486] using wordTrace_append hprefix tailTrace_6282486
  have hstable : (prefixWord ++ tailWord_6282486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282486).length < 2 ^ (prefixWord ++ tailWord_6282486).sum := by decide
  have hdescent : baseEnd_6282486 < baseStart_6282486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282489 : List Nat := [1, 2, 1, 3, 1, 1, 5, 3, 1, 2, 3]
def baseStart_6282489 : Nat := 118140960795 + 6282489 * 2 ^ 59
def prefixEnd_6282489 : Nat := 4983230072969 + 3 ^ 40 * 6282489 * 2
def baseEnd_6282489 : Nat := 3225936563584575466594865

theorem tailTrace_6282489 : CollatzResearch.WordTrace tailWord_6282489 prefixEnd_6282489 3225936563584575466594865 := by
  unfold tailWord_6282489
  simp only [CollatzResearch.WordTrace]
  refine ⟨229141198536622791543306521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152760799024415194362204347 229141198536622791543306521)
  ·
    refine ⟨171855898902467093657479891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229141198536622791543306521 171855898902467093657479891)
    ·
      refine ⟨257783848353700640486219837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171855898902467093657479891 257783848353700640486219837)
      ·
        refine ⟨96668943132637740182332439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257783848353700640486219837 96668943132637740182332439)
        ·
          refine ⟨145003414698956610273498659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96668943132637740182332439 145003414698956610273498659)
          ·
            refine ⟨217505122048434915410247989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145003414698956610273498659 217505122048434915410247989)
            ·
              refine ⟨20391105192040773319710749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 217505122048434915410247989 20391105192040773319710749)
              ·
                refine ⟨7646664447015289994891531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20391105192040773319710749 7646664447015289994891531)
                ·
                  refine ⟨11469996670522934992337297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7646664447015289994891531 11469996670522934992337297)
                  ·
                    refine ⟨8602497502892201244252973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11469996670522934992337297 8602497502892201244252973)
                    ·
                      refine ⟨3225936563584575466594865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8602497502892201244252973 3225936563584575466594865)
                      ·
                        rfl

theorem cell23_6282489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_6282489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282489 prefixEnd_6282489 := by exact prefixLift 6282489
  have htrace : WordTrace (prefixWord ++ tailWord_6282489) baseStart_6282489 baseEnd_6282489 := by
    simpa [prefixWord, tailWord_6282489, baseEnd_6282489] using wordTrace_append hprefix tailTrace_6282489
  have hstable : (prefixWord ++ tailWord_6282489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282489).length < 2 ^ (prefixWord ++ tailWord_6282489).sum := by decide
  have hdescent : baseEnd_6282489 < baseStart_6282489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282492 : List Nat := [2, 2, 2, 1, 5, 1, 10]
def baseStart_6282492 : Nat := 118140960795 + 6282492 * 2 ^ 59
def prefixEnd_6282492 : Nat := 4983230072969 + 3 ^ 40 * 6282492 * 2
def baseEnd_6282492 : Nat := 39826396346006653763671

theorem tailTrace_6282492 : CollatzResearch.WordTrace tailWord_6282492 prefixEnd_6282492 39826396346006653763671 := by
  unfold tailWord_6282492
  simp only [CollatzResearch.WordTrace]
  refine ⟨114570653977805961527832865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152760871970407948703777153 114570653977805961527832865)
  ·
    refine ⟨85927990483354471145874649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114570653977805961527832865 85927990483354471145874649)
    ·
      refine ⟨64445992862515853359405987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85927990483354471145874649 64445992862515853359405987)
      ·
        refine ⟨96668989293773780039108981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64445992862515853359405987 96668989293773780039108981)
        ·
          refine ⟨9062717746291291878666467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96668989293773780039108981 9062717746291291878666467)
          ·
            refine ⟨13594076619436937817999701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9062717746291291878666467 13594076619436937817999701)
            ·
              refine ⟨39826396346006653763671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13594076619436937817999701 39826396346006653763671)
              ·
                rfl

theorem cell23_6282492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 10].length) (baseStart_6282492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282492 prefixEnd_6282492 := by exact prefixLift 6282492
  have htrace : WordTrace (prefixWord ++ tailWord_6282492) baseStart_6282492 baseEnd_6282492 := by
    simpa [prefixWord, tailWord_6282492, baseEnd_6282492] using wordTrace_append hprefix tailTrace_6282492
  have hstable : (prefixWord ++ tailWord_6282492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282492).length < 2 ^ (prefixWord ++ tailWord_6282492).sum := by decide
  have hdescent : baseEnd_6282492 < baseStart_6282492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282526 : List Nat := [4, 3, 2, 1, 2, 1, 1, 9]
def baseStart_6282526 : Nat := 118140960795 + 6282526 * 2 ^ 59
def prefixEnd_6282526 : Nat := 4983230072969 + 3 ^ 40 * 6282526 * 2
def baseEnd_6282526 : Nat := 119479835643288585993785

theorem tailTrace_6282526 : CollatzResearch.WordTrace tailWord_6282526 prefixEnd_6282526 119479835643288585993785 := by
  unfold tailWord_6282526
  simp only [CollatzResearch.WordTrace]
  refine ⟨28642818504686093357800429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152761698691659164574935621 28642818504686093357800429)
  ·
    refine ⟨10741056939257285009175161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28642818504686093357800429 10741056939257285009175161)
    ·
      refine ⟨8055792704442963756881371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10741056939257285009175161 8055792704442963756881371)
      ·
        refine ⟨12083689056664445635322057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8055792704442963756881371 12083689056664445635322057)
        ·
          refine ⟨9062766792498334226491543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12083689056664445635322057 9062766792498334226491543)
          ·
            refine ⟨13594150188747501339737315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9062766792498334226491543 13594150188747501339737315)
            ·
              refine ⟨20391225283121252009605973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13594150188747501339737315 20391225283121252009605973)
              ·
                refine ⟨119479835643288585993785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20391225283121252009605973 119479835643288585993785)
                ·
                  rfl

theorem cell23_6282526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 9].length) (baseStart_6282526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282526 prefixEnd_6282526 := by exact prefixLift 6282526
  have htrace : WordTrace (prefixWord ++ tailWord_6282526) baseStart_6282526 baseEnd_6282526 := by
    simpa [prefixWord, tailWord_6282526, baseEnd_6282526] using wordTrace_append hprefix tailTrace_6282526
  have hstable : (prefixWord ++ tailWord_6282526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282526).length < 2 ^ (prefixWord ++ tailWord_6282526).sum := by decide
  have hdescent : baseEnd_6282526 < baseStart_6282526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282532 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_6282532 : Nat := 118140960795 + 6282532 * 2 ^ 59
def prefixEnd_6282532 : Nat := 4983230072969 + 3 ^ 40 * 6282532 * 2
def baseEnd_6282532 : Nat := 3225958643252718798357167

theorem tailTrace_6282532 : CollatzResearch.WordTrace tailWord_6282532 prefixEnd_6282532 3225958643252718798357167 := by
  unfold tailWord_6282532
  simp only [CollatzResearch.WordTrace]
  refine ⟨114571383437733504943560925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152761844583644673258081233 114571383437733504943560925)
  ·
    refine ⟨42964268789150064353835347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114571383437733504943560925 42964268789150064353835347)
    ·
      refine ⟨64446403183725096530753021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42964268789150064353835347 64446403183725096530753021)
      ·
        refine ⟨24167401193896911199032383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64446403183725096530753021 24167401193896911199032383)
        ·
          refine ⟨36251101790845366798548575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24167401193896911199032383 36251101790845366798548575)
          ·
            refine ⟨54376652686268050197822863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36251101790845366798548575 54376652686268050197822863)
            ·
              refine ⟨81564979029402075296734295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54376652686268050197822863 81564979029402075296734295)
              ·
                refine ⟨122347468544103112945101443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81564979029402075296734295 122347468544103112945101443)
                ·
                  refine ⟨183521202816154669417652165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122347468544103112945101443 183521202816154669417652165)
                  ·
                    refine ⟨34410225528029000515809781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 183521202816154669417652165 34410225528029000515809781)
                    ·
                      refine ⟨3225958643252718798357167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34410225528029000515809781 3225958643252718798357167)
                      ·
                        rfl

theorem cell23_6282532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_6282532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282532 prefixEnd_6282532 := by exact prefixLift 6282532
  have htrace : WordTrace (prefixWord ++ tailWord_6282532) baseStart_6282532 baseEnd_6282532 := by
    simpa [prefixWord, tailWord_6282532, baseEnd_6282532] using wordTrace_append hprefix tailTrace_6282532
  have hstable : (prefixWord ++ tailWord_6282532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282532).length < 2 ^ (prefixWord ++ tailWord_6282532).sum := by decide
  have hdescent : baseEnd_6282532 < baseStart_6282532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282536 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_6282536 : Nat := 118140960795 + 6282536 * 2 ^ 59
def prefixEnd_6282536 : Nat := 4983230072969 + 3 ^ 40 * 6282536 * 2
def baseEnd_6282536 : Nat := 3225960697175336782707149

theorem tailTrace_6282536 : CollatzResearch.WordTrace tailWord_6282536 prefixEnd_6282536 3225960697175336782707149 := by
  unfold tailWord_6282536
  simp only [CollatzResearch.WordTrace]
  refine ⟨114571456383726259285133731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152761941844968345713511641 114571456383726259285133731)
  ·
    refine ⟨171857184575589388927700597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114571456383726259285133731 171857184575589388927700597)
    ·
      refine ⟨16111611053961505211971931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171857184575589388927700597 16111611053961505211971931)
      ·
        refine ⟨24167416580942257817957897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16111611053961505211971931 24167416580942257817957897)
        ·
          refine ⟨18125562435706693363468423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24167416580942257817957897 18125562435706693363468423)
          ·
            refine ⟨27188343653560040045202635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18125562435706693363468423 27188343653560040045202635)
            ·
              refine ⟨40782515480340060067803953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27188343653560040045202635 40782515480340060067803953)
              ·
                refine ⟨30586886610255045050852965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40782515480340060067803953 30586886610255045050852965)
                ·
                  refine ⟨5735041239422820947034931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30586886610255045050852965 5735041239422820947034931)
                  ·
                    refine ⟨8602561859134231420552397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5735041239422820947034931 8602561859134231420552397)
                    ·
                      refine ⟨3225960697175336782707149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8602561859134231420552397 3225960697175336782707149)
                      ·
                        rfl

theorem cell23_6282536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_6282536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282536 prefixEnd_6282536 := by exact prefixLift 6282536
  have htrace : WordTrace (prefixWord ++ tailWord_6282536) baseStart_6282536 baseEnd_6282536 := by
    simpa [prefixWord, tailWord_6282536, baseEnd_6282536] using wordTrace_append hprefix tailTrace_6282536
  have hstable : (prefixWord ++ tailWord_6282536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282536).length < 2 ^ (prefixWord ++ tailWord_6282536).sum := by decide
  have hdescent : baseEnd_6282536 < baseStart_6282536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282619 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 1, 7, 2]
def baseStart_6282619 : Nat := 118140960795 + 6282619 * 2 ^ 59
def prefixEnd_6282619 : Nat := 4983230072969 + 3 ^ 40 * 6282619 * 2
def baseEnd_6282619 : Nat := 3226003316069659957969267

theorem tailTrace_6282619 : CollatzResearch.WordTrace tailWord_6282619 prefixEnd_6282619 3226003316069659957969267 := by
  unfold tailWord_6282619
  simp only [CollatzResearch.WordTrace]
  refine ⟨229145940026151823745538911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152763960017434549163692607 229145940026151823745538911)
  ·
    refine ⟨343718910039227735618308367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229145940026151823745538911 343718910039227735618308367)
    ·
      refine ⟨515578365058841603427462551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343718910039227735618308367 515578365058841603427462551)
      ·
        refine ⟨773367547588262405141193827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515578365058841603427462551 773367547588262405141193827)
        ·
          refine ⟨1160051321382393607711790741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 773367547588262405141193827 1160051321382393607711790741)
          ·
            refine ⟨54377405689799700361490191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1160051321382393607711790741 54377405689799700361490191)
            ·
              refine ⟨81566108534699550542235287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54377405689799700361490191 81566108534699550542235287)
              ·
                refine ⟨122349162802049325813352931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81566108534699550542235287 122349162802049325813352931)
                ·
                  refine ⟨183523744203073988720029397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122349162802049325813352931 183523744203073988720029397)
                  ·
                    refine ⟨4301337754759546610625689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 183523744203073988720029397 4301337754759546610625689)
                    ·
                      refine ⟨3226003316069659957969267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4301337754759546610625689 3226003316069659957969267)
                      ·
                        rfl

theorem cell23_6282619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 7, 2].length) (baseStart_6282619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282619 prefixEnd_6282619 := by exact prefixLift 6282619
  have htrace : WordTrace (prefixWord ++ tailWord_6282619) baseStart_6282619 baseEnd_6282619 := by
    simpa [prefixWord, tailWord_6282619, baseEnd_6282619] using wordTrace_append hprefix tailTrace_6282619
  have hstable : (prefixWord ++ tailWord_6282619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282619).length < 2 ^ (prefixWord ++ tailWord_6282619).sum := by decide
  have hdescent : baseEnd_6282619 < baseStart_6282619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282649 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 1, 3, 4]
def baseStart_6282649 : Nat := 118140960795 + 6282649 * 2 ^ 59
def prefixEnd_6282649 : Nat := 4983230072969 + 3 ^ 40 * 6282649 * 2
def baseEnd_6282649 : Nat := 3226018720489294840594129

theorem tailTrace_6282649 : CollatzResearch.WordTrace tailWord_6282649 prefixEnd_6282649 3226018720489294840594129 := by
  unfold tailWord_6282649
  simp only [CollatzResearch.WordTrace]
  refine ⟨229147034216043138869131001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152764689477362092579420667 229147034216043138869131001)
  ·
    refine ⟨171860275662032354151848251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229147034216043138869131001 171860275662032354151848251)
    ·
      refine ⟨257790413493048531227772377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171860275662032354151848251 257790413493048531227772377)
      ·
        refine ⟨193342810119786398420829283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257790413493048531227772377 193342810119786398420829283)
        ·
          refine ⟨290014215179679597631243925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193342810119786398420829283 290014215179679597631243925)
          ·
            refine ⟨13594416336547481138964559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 290014215179679597631243925 13594416336547481138964559)
            ·
              refine ⟨20391624504821221708446839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13594416336547481138964559 20391624504821221708446839)
              ·
                refine ⟨30587436757231832562670259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20391624504821221708446839 30587436757231832562670259)
                ·
                  refine ⟨45881155135847748844005389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30587436757231832562670259 45881155135847748844005389)
                  ·
                    refine ⟨17205433175942905816502021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45881155135847748844005389 17205433175942905816502021)
                    ·
                      refine ⟨3226018720489294840594129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17205433175942905816502021 3226018720489294840594129)
                      ·
                        rfl

theorem cell23_6282649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_6282649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282649 prefixEnd_6282649 := by exact prefixLift 6282649
  have htrace : WordTrace (prefixWord ++ tailWord_6282649) baseStart_6282649 baseEnd_6282649 := by
    simpa [prefixWord, tailWord_6282649, baseEnd_6282649] using wordTrace_append hprefix tailTrace_6282649
  have hstable : (prefixWord ++ tailWord_6282649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282649).length < 2 ^ (prefixWord ++ tailWord_6282649).sum := by decide
  have hdescent : baseEnd_6282649 < baseStart_6282649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282659 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 5, 4]
def baseStart_6282659 : Nat := 118140960795 + 6282659 * 2 ^ 59
def prefixEnd_6282659 : Nat := 4983230072969 + 3 ^ 40 * 6282659 * 2
def baseEnd_6282659 : Nat := 1075341285098613267156361

theorem tailTrace_6282659 : CollatzResearch.WordTrace tailWord_6282659 prefixEnd_6282659 1075341285098613267156361 := by
  unfold tailWord_6282659
  simp only [CollatzResearch.WordTrace]
  refine ⟨229147398946006910576995031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152764932630671273717996687 229147398946006910576995031)
  ·
    refine ⟨343721098419010365865492547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229147398946006910576995031 343721098419010365865492547)
    ·
      refine ⟨515581647628515548798238821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343721098419010365865492547 515581647628515548798238821)
      ·
        refine ⟨96671558930346665399669779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 515581647628515548798238821 96671558930346665399669779)
        ·
          refine ⟨145007338395519998099504669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96671558930346665399669779 145007338395519998099504669)
          ·
            refine ⟨54377751898319999287314251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145007338395519998099504669 54377751898319999287314251)
            ·
              refine ⟨81566627847479998930971377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54377751898319999287314251 81566627847479998930971377)
              ·
                refine ⟨61174970885609999198228533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81566627847479998930971377 61174970885609999198228533)
                ·
                  refine ⟨5735153520525937424833925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61174970885609999198228533 5735153520525937424833925)
                  ·
                    refine ⟨1075341285098613267156361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5735153520525937424833925 1075341285098613267156361)
                    ·
                      rfl

theorem cell23_6282659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 4].length) (baseStart_6282659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282659 prefixEnd_6282659 := by exact prefixLift 6282659
  have htrace : WordTrace (prefixWord ++ tailWord_6282659) baseStart_6282659 baseEnd_6282659 := by
    simpa [prefixWord, tailWord_6282659, baseEnd_6282659] using wordTrace_append hprefix tailTrace_6282659
  have hstable : (prefixWord ++ tailWord_6282659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282659).length < 2 ^ (prefixWord ++ tailWord_6282659).sum := by decide
  have hdescent : baseEnd_6282659 < baseStart_6282659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282784 : List Nat := [2, 1, 1, 6, 1, 3, 2, 2, 1, 1, 3]
def baseStart_6282784 : Nat := 118140960795 + 6282784 * 2 ^ 59
def prefixEnd_6282784 : Nat := 4983230072969 + 3 ^ 40 * 6282784 * 2
def baseEnd_6282784 : Nat := 3226088040377651812406009

theorem tailTrace_6282784 : CollatzResearch.WordTrace tailWord_6282784 prefixEnd_6282784 3226088040377651812406009 := by
  unfold tailWord_6282784
  simp only [CollatzResearch.WordTrace]
  refine ⟨114575979035277028462647703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152767972047036037950196937 114575979035277028462647703)
  ·
    refine ⟨171863968552915542693971555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114575979035277028462647703 171863968552915542693971555)
    ·
      refine ⟨257795952829373314040957333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171863968552915542693971555 257795952829373314040957333)
      ·
        refine ⟨12084185288876874095669875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 257795952829373314040957333 12084185288876874095669875)
        ·
          refine ⟨18126277933315311143504813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12084185288876874095669875 18126277933315311143504813)
          ·
            refine ⟨6797354224993241678814305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18126277933315311143504813 6797354224993241678814305)
            ·
              refine ⟨5098015668744931259110729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6797354224993241678814305 5098015668744931259110729)
              ·
                refine ⟨3823511751558698444333047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5098015668744931259110729 3823511751558698444333047)
                ·
                  refine ⟨5735267627338047666499571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3823511751558698444333047 5735267627338047666499571)
                  ·
                    refine ⟨8602901441007071499749357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5735267627338047666499571 8602901441007071499749357)
                    ·
                      refine ⟨3226088040377651812406009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8602901441007071499749357 3226088040377651812406009)
                      ·
                        rfl

theorem cell23_6282784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_6282784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282784 prefixEnd_6282784 := by exact prefixLift 6282784
  have htrace : WordTrace (prefixWord ++ tailWord_6282784) baseStart_6282784 baseEnd_6282784 := by
    simpa [prefixWord, tailWord_6282784, baseEnd_6282784] using wordTrace_append hprefix tailTrace_6282784
  have hstable : (prefixWord ++ tailWord_6282784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282784).length < 2 ^ (prefixWord ++ tailWord_6282784).sum := by decide
  have hdescent : baseEnd_6282784 < baseStart_6282784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282813 : List Nat := [1, 4, 1, 3, 3, 1, 3, 7]
def baseStart_6282813 : Nat := 118140960795 + 6282813 * 2 ^ 59
def prefixEnd_6282813 : Nat := 4983230072969 + 3 ^ 40 * 6282813 * 2
def baseEnd_6282813 : Nat := 119485293752467859220125

theorem tailTrace_6282813 : CollatzResearch.WordTrace tailWord_6282813 prefixEnd_6282813 119485293752467859220125 := by
  unfold tailWord_6282813
  simp only [CollatzResearch.WordTrace]
  refine ⟨229153015787448994878101093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152768677191632663252067395 229153015787448994878101093)
  ·
    refine ⟨42966190460146686539643955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229153015787448994878101093 42966190460146686539643955)
    ·
      refine ⟨64449285690220029809465933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42966190460146686539643955 64449285690220029809465933)
      ·
        refine ⟨24168482133832511178549725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64449285690220029809465933 24168482133832511178549725)
        ·
          refine ⟨9063180800187191691956147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24168482133832511178549725 9063180800187191691956147)
          ·
            refine ⟨13594771200280787537934221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9063180800187191691956147 13594771200280787537934221)
            ·
              refine ⟨5098039200105295326725333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13594771200280787537934221 5098039200105295326725333)
              ·
                refine ⟨119485293752467859220125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5098039200105295326725333 119485293752467859220125)
                ·
                  rfl

theorem cell23_6282813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 7].length) (baseStart_6282813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282813 prefixEnd_6282813 := by exact prefixLift 6282813
  have htrace : WordTrace (prefixWord ++ tailWord_6282813) baseStart_6282813 baseEnd_6282813 := by
    simpa [prefixWord, tailWord_6282813, baseEnd_6282813] using wordTrace_append hprefix tailTrace_6282813
  have hstable : (prefixWord ++ tailWord_6282813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282813).length < 2 ^ (prefixWord ++ tailWord_6282813).sum := by decide
  have hdescent : baseEnd_6282813 < baseStart_6282813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282896 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 3]
def baseStart_6282896 : Nat := 118140960795 + 6282896 * 2 ^ 59
def prefixEnd_6282896 : Nat := 4983230072969 + 3 ^ 40 * 6282896 * 2
def baseEnd_6282896 : Nat := 3226145550210955374205493

theorem tailTrace_6282896 : CollatzResearch.WordTrace tailWord_6282896 prefixEnd_6282896 3226145550210955374205493 := by
  unfold tailWord_6282896
  simp only [CollatzResearch.WordTrace]
  refine ⟨114578021523074150026686271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152770695364098866702248361 114578021523074150026686271)
  ·
    refine ⟨171867032284611225040029407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114578021523074150026686271 171867032284611225040029407)
    ·
      refine ⟨257800548426916837560044111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171867032284611225040029407 257800548426916837560044111)
      ·
        refine ⟨386700822640375256340066167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257800548426916837560044111 386700822640375256340066167)
        ·
          refine ⟨580051233960562884510099251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386700822640375256340066167 580051233960562884510099251)
          ·
            refine ⟨870076850940844326765148877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580051233960562884510099251 870076850940844326765148877)
            ·
              refine ⟨326278819102816622536930829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 870076850940844326765148877 326278819102816622536930829)
              ·
                refine ⟨122354557163556233451349061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 326278819102816622536930829 122354557163556233451349061)
                ·
                  refine ⟨22941479468166793772127949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122354557163556233451349061 22941479468166793772127949)
                  ·
                    refine ⟨8603054800562547664547981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22941479468166793772127949 8603054800562547664547981)
                    ·
                      refine ⟨3226145550210955374205493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8603054800562547664547981 3226145550210955374205493)
                      ·
                        rfl

theorem cell23_6282896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 3].length) (baseStart_6282896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282896 prefixEnd_6282896 := by exact prefixLift 6282896
  have htrace : WordTrace (prefixWord ++ tailWord_6282896) baseStart_6282896 baseEnd_6282896 := by
    simpa [prefixWord, tailWord_6282896, baseEnd_6282896] using wordTrace_append hprefix tailTrace_6282896
  have hstable : (prefixWord ++ tailWord_6282896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282896).length < 2 ^ (prefixWord ++ tailWord_6282896).sum := by decide
  have hdescent : baseEnd_6282896 < baseStart_6282896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282903 : List Nat := [1, 1, 3, 3, 2, 4, 1, 1, 7]
def baseStart_6282903 : Nat := 118140960795 + 6282903 * 2 ^ 59
def prefixEnd_6282903 : Nat := 4983230072969 + 3 ^ 40 * 6282903 * 2
def baseEnd_6282903 : Nat := 358461016063948538535329

theorem tailTrace_6282903 : CollatzResearch.WordTrace tailWord_6282903 prefixEnd_6282903 358461016063948538535329 := by
  unfold tailWord_6282903
  simp only [CollatzResearch.WordTrace]
  refine ⟨229156298357122940248877363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152770865571415293499251575 229156298357122940248877363)
  ·
    refine ⟨343734447535684410373316045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229156298357122940248877363 343734447535684410373316045)
    ·
      refine ⟨128900417825881653889993517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343734447535684410373316045 128900417825881653889993517)
      ·
        refine ⟨48337656684705620208747569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128900417825881653889993517 48337656684705620208747569)
        ·
          refine ⟨36253242513529215156560677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48337656684705620208747569 36253242513529215156560677)
          ·
            refine ⟨6797482971286727841855127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36253242513529215156560677 6797482971286727841855127)
            ·
              refine ⟨10196224456930091762782691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6797482971286727841855127 10196224456930091762782691)
              ·
                refine ⟨15294336685395137644174037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10196224456930091762782691 15294336685395137644174037)
                ·
                  refine ⟨358461016063948538535329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15294336685395137644174037 358461016063948538535329)
                  ·
                    rfl

theorem cell23_6282903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 7].length) (baseStart_6282903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282903 prefixEnd_6282903 := by exact prefixLift 6282903
  have htrace : WordTrace (prefixWord ++ tailWord_6282903) baseStart_6282903 baseEnd_6282903 := by
    simpa [prefixWord, tailWord_6282903, baseEnd_6282903] using wordTrace_append hprefix tailTrace_6282903
  have hstable : (prefixWord ++ tailWord_6282903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282903).length < 2 ^ (prefixWord ++ tailWord_6282903).sum := by decide
  have hdescent : baseEnd_6282903 < baseStart_6282903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282936 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 1, 3, 4]
def baseStart_6282936 : Nat := 118140960795 + 6282936 * 2 ^ 59
def prefixEnd_6282936 : Nat := 4983230072969 + 3 ^ 40 * 6282936 * 2
def baseEnd_6282936 : Nat := 3226166089437135217705309

theorem tailTrace_6282936 : CollatzResearch.WordTrace tailWord_6282936 prefixEnd_6282936 3226166089437135217705309 := by
  unfold tailWord_6282936
  simp only [CollatzResearch.WordTrace]
  refine ⟨114578750983001693442414331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152771667977335591256552441 114578750983001693442414331)
  ·
    refine ⟨171868126474502540163621497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114578750983001693442414331 171868126474502540163621497)
    ·
      refine ⟨128901094855876905122716123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171868126474502540163621497 128901094855876905122716123)
      ·
        refine ⟨193351642283815357684074185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128901094855876905122716123 193351642283815357684074185)
        ·
          refine ⟨145013731712861518263055639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193351642283815357684074185 145013731712861518263055639)
          ·
            refine ⟨217520597569292277394583459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145013731712861518263055639 217520597569292277394583459)
            ·
              refine ⟨326280896353938416091875189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217520597569292277394583459 326280896353938416091875189)
              ·
                refine ⟨30588834033181726508613299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 326280896353938416091875189 30588834033181726508613299)
                ·
                  refine ⟨45883251049772589762919949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30588834033181726508613299 45883251049772589762919949)
                  ·
                    refine ⟨17206219143664721161094981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45883251049772589762919949 17206219143664721161094981)
                    ·
                      refine ⟨3226166089437135217705309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17206219143664721161094981 3226166089437135217705309)
                      ·
                        rfl

theorem cell23_6282936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_6282936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282936 prefixEnd_6282936 := by exact prefixLift 6282936
  have htrace : WordTrace (prefixWord ++ tailWord_6282936) baseStart_6282936 baseEnd_6282936 := by
    simpa [prefixWord, tailWord_6282936, baseEnd_6282936] using wordTrace_append hprefix tailTrace_6282936
  have hstable : (prefixWord ++ tailWord_6282936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282936).length < 2 ^ (prefixWord ++ tailWord_6282936).sum := by decide
  have hdescent : baseEnd_6282936 < baseStart_6282936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282954 : List Nat := [3, 1, 2, 1, 6, 1, 2, 2, 5]
def baseStart_6282954 : Nat := 118140960795 + 6282954 * 2 ^ 59
def prefixEnd_6282954 : Nat := 4983230072969 + 3 ^ 40 * 6282954 * 2
def baseEnd_6282954 : Nat := 358463925787657349697803

theorem tailTrace_6282954 : CollatzResearch.WordTrace tailWord_6282954 prefixEnd_6282954 358463925787657349697803 := by
  unfold tailWord_6282954
  simp only [CollatzResearch.WordTrace]
  refine ⟨57289539619984543989745979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152772105653292117305989277 57289539619984543989745979)
  ·
    refine ⟨85934309429976815984618969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57289539619984543989745979 85934309429976815984618969)
    ·
      refine ⟨64450732072482611988464227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85934309429976815984618969 64450732072482611988464227)
      ·
        refine ⟨96676098108723917982696341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64450732072482611988464227 96676098108723917982696341)
        ·
          refine ⟨4531692098846433655438891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96676098108723917982696341 4531692098846433655438891)
          ·
            refine ⟨6797538148269650483158337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4531692098846433655438891 6797538148269650483158337)
            ·
              refine ⟨5098153611202237862368753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6797538148269650483158337 5098153611202237862368753)
              ·
                refine ⟨3823615208401678396776565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5098153611202237862368753 3823615208401678396776565)
                ·
                  refine ⟨358463925787657349697803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3823615208401678396776565 358463925787657349697803)
                  ·
                    rfl

theorem cell23_6282954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 5].length) (baseStart_6282954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282954 prefixEnd_6282954 := by exact prefixLift 6282954
  have htrace : WordTrace (prefixWord ++ tailWord_6282954) baseStart_6282954 baseEnd_6282954 := by
    simpa [prefixWord, tailWord_6282954, baseEnd_6282954] using wordTrace_append hprefix tailTrace_6282954
  have hstable : (prefixWord ++ tailWord_6282954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282954).length < 2 ^ (prefixWord ++ tailWord_6282954).sum := by decide
  have hdescent : baseEnd_6282954 < baseStart_6282954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282957 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_6282957 : Nat := 118140960795 + 6282957 * 2 ^ 59
def prefixEnd_6282957 : Nat := 4983230072969 + 3 ^ 40 * 6282957 * 2
def baseEnd_6282957 : Nat := 3226176872530879635542713

theorem tailTrace_6282957 : CollatzResearch.WordTrace tailWord_6282957 prefixEnd_6282957 3226176872530879635542713 := by
  unfold tailWord_6282957
  simp only [CollatzResearch.WordTrace]
  refine ⟨229158267898927307471343125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152772178599284871647562083 229158267898927307471343125)
  ·
    refine ⟨10741793807762217537719209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 229158267898927307471343125 10741793807762217537719209)
    ·
      refine ⟨8056345355821663153289407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10741793807762217537719209 8056345355821663153289407)
      ·
        refine ⟨12084518033732494729934111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8056345355821663153289407 12084518033732494729934111)
        ·
          refine ⟨18126777050598742094901167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12084518033732494729934111 18126777050598742094901167)
          ·
            refine ⟨27190165575898113142351751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18126777050598742094901167 27190165575898113142351751)
            ·
              refine ⟨40785248363847169713527627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27190165575898113142351751 40785248363847169713527627)
              ·
                refine ⟨61177872545770754570291441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40785248363847169713527627 61177872545770754570291441)
                ·
                  refine ⟨45883404409328065927718581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61177872545770754570291441 45883404409328065927718581)
                  ·
                    refine ⟨4301569163374506180723617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45883404409328065927718581 4301569163374506180723617)
                    ·
                      refine ⟨3226176872530879635542713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4301569163374506180723617 3226176872530879635542713)
                      ·
                        rfl

theorem cell23_6282957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_6282957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282957 prefixEnd_6282957 := by exact prefixLift 6282957
  have htrace : WordTrace (prefixWord ++ tailWord_6282957) baseStart_6282957 baseEnd_6282957 := by
    simpa [prefixWord, tailWord_6282957, baseEnd_6282957] using wordTrace_append hprefix tailTrace_6282957
  have hstable : (prefixWord ++ tailWord_6282957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282957).length < 2 ^ (prefixWord ++ tailWord_6282957).sum := by decide
  have hdescent : baseEnd_6282957 < baseStart_6282957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6282970 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2]
def baseStart_6282970 : Nat := 118140960795 + 6282970 * 2 ^ 59
def prefixEnd_6282970 : Nat := 4983230072969 + 3 ^ 40 * 6282970 * 2
def baseEnd_6282970 : Nat := 3226183547779388084680153

theorem tailTrace_6282970 : CollatzResearch.WordTrace tailWord_6282970 prefixEnd_6282970 3226183547779388084680153 := by
  unfold tailWord_6282970
  simp only [CollatzResearch.WordTrace]
  refine ⟨57289685511970052672891591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152772494698586807127710909 57289685511970052672891591)
  ·
    refine ⟨85934528267955079009337387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57289685511970052672891591 85934528267955079009337387)
    ·
      refine ⟨128901792401932618514006081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85934528267955079009337387 128901792401932618514006081)
      ·
        refine ⟨96676344301449463885504561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128901792401932618514006081 96676344301449463885504561)
        ·
          refine ⟨72507258226087097914128421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96676344301449463885504561 72507258226087097914128421)
          ·
            refine ⟨13595110917391330858899079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72507258226087097914128421 13595110917391330858899079)
            ·
              refine ⟨20392666376086996288348619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13595110917391330858899079 20392666376086996288348619)
              ·
                refine ⟨30588999564130494432522929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20392666376086996288348619 30588999564130494432522929)
                ·
                  refine ⟨22941749673097870824392197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30588999564130494432522929 22941749673097870824392197)
                  ·
                    refine ⟨4301578063705850779573537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22941749673097870824392197 4301578063705850779573537)
                    ·
                      refine ⟨3226183547779388084680153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4301578063705850779573537 3226183547779388084680153)
                      ·
                        rfl

theorem cell23_6282970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_6282970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6282970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6282970 prefixEnd_6282970 := by exact prefixLift 6282970
  have htrace : WordTrace (prefixWord ++ tailWord_6282970) baseStart_6282970 baseEnd_6282970 := by
    simpa [prefixWord, tailWord_6282970, baseEnd_6282970] using wordTrace_append hprefix tailTrace_6282970
  have hstable : (prefixWord ++ tailWord_6282970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6282970).length < 2 ^ (prefixWord ++ tailWord_6282970).sum := by decide
  have hdescent : baseEnd_6282970 < baseStart_6282970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6282970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283020 : List Nat := [2, 2, 1, 2, 2, 1, 3, 3, 3, 1, 3]
def baseStart_6283020 : Nat := 118140960795 + 6283020 * 2 ^ 59
def prefixEnd_6283020 : Nat := 4983230072969 + 3 ^ 40 * 6283020 * 2
def baseEnd_6283020 : Nat := 3226209221812112889054923

theorem tailTrace_6283020 : CollatzResearch.WordTrace tailWord_6283020 prefixEnd_6283020 3226209221812112889054923 := by
  unfold tailWord_6283020
  simp only [CollatzResearch.WordTrace]
  refine ⟨114580282848849534615443257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152773710465132712820591009 114580282848849534615443257)
  ·
    refine ⟨85935212136637150961582443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114580282848849534615443257 85935212136637150961582443)
    ·
      refine ⟨128902818204955726442373665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85935212136637150961582443 128902818204955726442373665)
      ·
        refine ⟨96677113653716794831780249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128902818204955726442373665 96677113653716794831780249)
        ·
          refine ⟨72507835240287596123835187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96677113653716794831780249 72507835240287596123835187)
          ·
            refine ⟨108761752860431394185752781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72507835240287596123835187 108761752860431394185752781)
            ·
              refine ⟨40785657322661772819657293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108761752860431394185752781 40785657322661772819657293)
              ·
                refine ⟨15294621495998164807371485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40785657322661772819657293 15294621495998164807371485)
                ·
                  refine ⟨5735483060999311802764307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15294621495998164807371485 5735483060999311802764307)
                  ·
                    refine ⟨8603224591498967704146461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5735483060999311802764307 8603224591498967704146461)
                    ·
                      refine ⟨3226209221812112889054923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8603224591498967704146461 3226209221812112889054923)
                      ·
                        rfl

theorem cell23_6283020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_6283020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283020 prefixEnd_6283020 := by exact prefixLift 6283020
  have htrace : WordTrace (prefixWord ++ tailWord_6283020) baseStart_6283020 baseEnd_6283020 := by
    simpa [prefixWord, tailWord_6283020, baseEnd_6283020] using wordTrace_append hprefix tailTrace_6283020
  have hstable : (prefixWord ++ tailWord_6283020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283020).length < 2 ^ (prefixWord ++ tailWord_6283020).sum := by decide
  have hdescent : baseEnd_6283020 < baseStart_6283020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283040 : List Nat := [2, 1, 1, 5, 1, 1, 4, 2, 1, 5]
def baseStart_6283040 : Nat := 118140960795 + 6283040 * 2 ^ 59
def prefixEnd_6283040 : Nat := 4983230072969 + 3 ^ 40 * 6283040 * 2
def baseEnd_6283040 : Nat := 1075406497141734270268277

theorem tailTrace_6283040 : CollatzResearch.WordTrace tailWord_6283040 prefixEnd_6283040 1075406497141734270268277 := by
  unfold tailWord_6283040
  simp only [CollatzResearch.WordTrace]
  refine ⟨114580647578813306323307287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152774196771751075097743049 114580647578813306323307287)
  ·
    refine ⟨171870971368219959484960931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114580647578813306323307287 171870971368219959484960931)
    ·
      refine ⟨257806457052329939227441397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171870971368219959484960931 257806457052329939227441397)
      ·
        refine ⟨24169355348655931802572631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 257806457052329939227441397 24169355348655931802572631)
        ·
          refine ⟨36254033022983897703858947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24169355348655931802572631 36254033022983897703858947)
          ·
            refine ⟨54381049534475846555788421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36254033022983897703858947 54381049534475846555788421)
            ·
              refine ⟨10196446787714221229210329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54381049534475846555788421 10196446787714221229210329)
              ·
                refine ⟨7647335090785665921907747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10196446787714221229210329 7647335090785665921907747)
                ·
                  refine ⟨11471002636178498882861621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7647335090785665921907747 11471002636178498882861621)
                  ·
                    refine ⟨1075406497141734270268277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11471002636178498882861621 1075406497141734270268277)
                    ·
                      rfl

theorem cell23_6283040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 1, 5].length) (baseStart_6283040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283040 prefixEnd_6283040 := by exact prefixLift 6283040
  have htrace : WordTrace (prefixWord ++ tailWord_6283040) baseStart_6283040 baseEnd_6283040 := by
    simpa [prefixWord, tailWord_6283040, baseEnd_6283040] using wordTrace_append hprefix tailTrace_6283040
  have hstable : (prefixWord ++ tailWord_6283040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283040).length < 2 ^ (prefixWord ++ tailWord_6283040).sum := by decide
  have hdescent : baseEnd_6283040 < baseStart_6283040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283043 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 4]
def baseStart_6283043 : Nat := 118140960795 + 6283043 * 2 ^ 59
def prefixEnd_6283043 : Nat := 4983230072969 + 3 ^ 40 * 6283043 * 2
def baseEnd_6283043 : Nat := 3226221031867166299067317

theorem tailTrace_6283043 : CollatzResearch.WordTrace tailWord_6283043 prefixEnd_6283043 3226221031867166299067317 := by
  unfold tailWord_6283043
  simp only [CollatzResearch.WordTrace]
  refine ⟨229161404576615744158973783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152774269717743829439315855 229161404576615744158973783)
  ·
    refine ⟨343742106864923616238460675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229161404576615744158973783 343742106864923616238460675)
    ·
      refine ⟨515613160297385424357691013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343742106864923616238460675 515613160297385424357691013)
      ·
        refine ⟨96677467555759767067067065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 515613160297385424357691013 96677467555759767067067065)
        ·
          refine ⟨72508100666819825300300299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96677467555759767067067065 72508100666819825300300299)
          ·
            refine ⟨108762151000229737950450449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72508100666819825300300299 108762151000229737950450449)
            ·
              refine ⟨81571613250172303462837837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108762151000229737950450449 81571613250172303462837837)
              ·
                refine ⟨30589354968814613798564189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81571613250172303462837837 30589354968814613798564189)
                ·
                  refine ⟨11471008113305480174461571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30589354968814613798564189 11471008113305480174461571)
                  ·
                    refine ⟨17206512169958220261692357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11471008113305480174461571 17206512169958220261692357)
                    ·
                      refine ⟨3226221031867166299067317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17206512169958220261692357 3226221031867166299067317)
                      ·
                        rfl

theorem cell23_6283043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_6283043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283043 prefixEnd_6283043 := by exact prefixLift 6283043
  have htrace : WordTrace (prefixWord ++ tailWord_6283043) baseStart_6283043 baseEnd_6283043 := by
    simpa [prefixWord, tailWord_6283043, baseEnd_6283043] using wordTrace_append hprefix tailTrace_6283043
  have hstable : (prefixWord ++ tailWord_6283043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283043).length < 2 ^ (prefixWord ++ tailWord_6283043).sum := by decide
  have hdescent : baseEnd_6283043 < baseStart_6283043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283071 : List Nat := [1, 1, 2, 2, 6, 1, 3, 2, 1, 1, 3]
def baseStart_6283071 : Nat := 118140960795 + 6283071 * 2 ^ 59
def prefixEnd_6283071 : Nat := 4983230072969 + 3 ^ 40 * 6283071 * 2
def baseEnd_6283071 : Nat := 3226235409325492189517189

theorem tailTrace_6283071 : CollatzResearch.WordTrace tailWord_6283071 prefixEnd_6283071 3226235409325492189517189 := by
  unfold tailWord_6283071
  simp only [CollatzResearch.WordTrace]
  refine ⟨229162425820514304940993067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152774950547009536627328711 229162425820514304940993067)
  ·
    refine ⟨343743638730771457411489601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229162425820514304940993067 343743638730771457411489601)
    ·
      refine ⟨257807729048078593058617201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343743638730771457411489601 257807729048078593058617201)
      ·
        refine ⟨193355796786058944793962901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257807729048078593058617201 193355796786058944793962901)
        ·
          refine ⟨9063552974346513037217011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 193355796786058944793962901 9063552974346513037217011)
          ·
            refine ⟨13595329461519769555825517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9063552974346513037217011 13595329461519769555825517)
            ·
              refine ⟨5098248548069913583434569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13595329461519769555825517 5098248548069913583434569)
              ·
                refine ⟨3823686411052435187575927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5098248548069913583434569 3823686411052435187575927)
                ·
                  refine ⟨5735529616578652781363891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3823686411052435187575927 5735529616578652781363891)
                  ·
                    refine ⟨8603294424867979172045837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5735529616578652781363891 8603294424867979172045837)
                    ·
                      refine ⟨3226235409325492189517189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8603294424867979172045837 3226235409325492189517189)
                      ·
                        rfl

theorem cell23_6283071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 1, 1, 3].length) (baseStart_6283071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283071 prefixEnd_6283071 := by exact prefixLift 6283071
  have htrace : WordTrace (prefixWord ++ tailWord_6283071) baseStart_6283071 baseEnd_6283071 := by
    simpa [prefixWord, tailWord_6283071, baseEnd_6283071] using wordTrace_append hprefix tailTrace_6283071
  have hstable : (prefixWord ++ tailWord_6283071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283071).length < 2 ^ (prefixWord ++ tailWord_6283071).sum := by decide
  have hdescent : baseEnd_6283071 < baseStart_6283071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283114 : List Nat := [3, 1, 3, 4, 1, 2, 1, 1, 1, 1, 5]
def baseStart_6283114 : Nat := 118140960795 + 6283114 * 2 ^ 59
def prefixEnd_6283114 : Nat := 4983230072969 + 3 ^ 40 * 6283114 * 2
def baseEnd_6283114 : Nat := 3226257488993635521279491

theorem tailTrace_6283114 : CollatzResearch.WordTrace tailWord_6283114 prefixEnd_6283114 3226257488993635521279491 := by
  unfold tailWord_6283114
  simp only [CollatzResearch.WordTrace]
  refine ⟨57290998539839630821202099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152775996106239015523205597 57290998539839630821202099)
  ·
    refine ⟨85936497809759446231803149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57290998539839630821202099 85936497809759446231803149)
    ·
      refine ⟨32226186678659792336926181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85936497809759446231803149 32226186678659792336926181)
      ·
        refine ⟨6042410002248711063173659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32226186678659792336926181 6042410002248711063173659)
        ·
          refine ⟨9063615003373066594760489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6042410002248711063173659 9063615003373066594760489)
          ·
            refine ⟨6797711252529799946070367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9063615003373066594760489 6797711252529799946070367)
            ·
              refine ⟨10196566878794699919105551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6797711252529799946070367 10196566878794699919105551)
              ·
                refine ⟨15294850318192049878658327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10196566878794699919105551 15294850318192049878658327)
                ·
                  refine ⟨22942275477288074817987491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15294850318192049878658327 22942275477288074817987491)
                  ·
                    refine ⟨34413413215932112226981237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22942275477288074817987491 34413413215932112226981237)
                    ·
                      refine ⟨3226257488993635521279491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34413413215932112226981237 3226257488993635521279491)
                      ·
                        rfl

theorem cell23_6283114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_6283114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283114 prefixEnd_6283114 := by exact prefixLift 6283114
  have htrace : WordTrace (prefixWord ++ tailWord_6283114) baseStart_6283114 baseEnd_6283114 := by
    simpa [prefixWord, tailWord_6283114, baseEnd_6283114] using wordTrace_append hprefix tailTrace_6283114
  have hstable : (prefixWord ++ tailWord_6283114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283114).length < 2 ^ (prefixWord ++ tailWord_6283114).sum := by decide
  have hdescent : baseEnd_6283114 < baseStart_6283114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283153 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 5]
def baseStart_6283153 : Nat := 118140960795 + 6283153 * 2 ^ 59
def prefixEnd_6283153 : Nat := 4983230072969 + 3 ^ 40 * 6283153 * 2
def baseEnd_6283153 : Nat := 3226277514739160868691811

theorem tailTrace_6283153 : CollatzResearch.WordTrace tailWord_6283153 prefixEnd_6283153 3226277514739160868691811 := by
  unfold tailWord_6283153
  simp only [CollatzResearch.WordTrace]
  refine ⟨229165416606217232945478113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152776944404144821963652075 229165416606217232945478113)
  ·
    refine ⟨171874062454662924709108585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229165416606217232945478113 171874062454662924709108585)
    ·
      refine ⟨128905546840997193531831439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171874062454662924709108585 128905546840997193531831439)
      ·
        refine ⟨193358320261495790297747159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128905546840997193531831439 193358320261495790297747159)
        ·
          refine ⟨290037480392243685446620739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193358320261495790297747159 290037480392243685446620739)
          ·
            refine ⟨435056220588365528169931109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290037480392243685446620739 435056220588365528169931109)
            ·
              refine ⟨81573041360318536531862083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 435056220588365528169931109 81573041360318536531862083)
              ·
                refine ⟨122359562040477804797793125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81573041360318536531862083 122359562040477804797793125)
                ·
                  refine ⟨22942417882589588399586211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122359562040477804797793125 22942417882589588399586211)
                  ·
                    refine ⟨34413626823884382599379317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22942417882589588399586211 34413626823884382599379317)
                    ·
                      refine ⟨3226277514739160868691811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34413626823884382599379317 3226277514739160868691811)
                      ·
                        rfl

theorem cell23_6283153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_6283153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283153 prefixEnd_6283153 := by exact prefixLift 6283153
  have htrace : WordTrace (prefixWord ++ tailWord_6283153) baseStart_6283153 baseEnd_6283153 := by
    simpa [prefixWord, tailWord_6283153, baseEnd_6283153] using wordTrace_append hprefix tailTrace_6283153
  have hstable : (prefixWord ++ tailWord_6283153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283153).length < 2 ^ (prefixWord ++ tailWord_6283153).sum := by decide
  have hdescent : baseEnd_6283153 < baseStart_6283153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283154 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_6283154 : Nat := 118140960795 + 6283154 * 2 ^ 59
def prefixEnd_6283154 : Nat := 4983230072969 + 3 ^ 40 * 6283154 * 2
def baseEnd_6283154 : Nat := 3226278028219815364779307

theorem tailTrace_6283154 : CollatzResearch.WordTrace tailWord_6283154 prefixEnd_6283154 3226278028219815364779307 := by
  unfold tailWord_6283154
  simp only [CollatzResearch.WordTrace]
  refine ⟨57291363269803402529066129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152776968719475740077509677 57291363269803402529066129)
  ·
    refine ⟨42968522452352551896799597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57291363269803402529066129 42968522452352551896799597)
    ·
      refine ⟨16113195919632206961299849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42968522452352551896799597 16113195919632206961299849)
      ·
        refine ⟨12084896939724155220974887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16113195919632206961299849 12084896939724155220974887)
        ·
          refine ⟨18127345409586232831462331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12084896939724155220974887 18127345409586232831462331)
          ·
            refine ⟨27191018114379349247193497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18127345409586232831462331 27191018114379349247193497)
            ·
              refine ⟨20393263585784511935395123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27191018114379349247193497 20393263585784511935395123)
              ·
                refine ⟨30589895378676767903092685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20393263585784511935395123 30589895378676767903092685)
                ·
                  refine ⟨11471210767003787963659757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30589895378676767903092685 11471210767003787963659757)
                  ·
                    refine ⟨4301704037626420486372409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11471210767003787963659757 4301704037626420486372409)
                    ·
                      refine ⟨3226278028219815364779307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4301704037626420486372409 3226278028219815364779307)
                      ·
                        rfl

theorem cell23_6283154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_6283154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283154 prefixEnd_6283154 := by exact prefixLift 6283154
  have htrace : WordTrace (prefixWord ++ tailWord_6283154) baseStart_6283154 baseEnd_6283154 := by
    simpa [prefixWord, tailWord_6283154, baseEnd_6283154] using wordTrace_append hprefix tailTrace_6283154
  have hstable : (prefixWord ++ tailWord_6283154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283154).length < 2 ^ (prefixWord ++ tailWord_6283154).sum := by decide
  have hdescent : baseEnd_6283154 < baseStart_6283154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283200 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 3]
def baseStart_6283200 : Nat := 118140960795 + 6283200 * 2 ^ 59
def prefixEnd_6283200 : Nat := 4983230072969 + 3 ^ 40 * 6283200 * 2
def baseEnd_6283200 : Nat := 3226301648329922184804095

theorem tailTrace_6283200 : CollatzResearch.WordTrace tailWord_6283200 prefixEnd_6283200 3226301648329922184804095 := by
  unfold tailWord_6283200
  simp only [CollatzResearch.WordTrace]
  refine ⟨114583565418523479986219527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152778087224697973314959369 114583565418523479986219527)
  ·
    refine ⟨171875348127785219979329291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114583565418523479986219527 171875348127785219979329291)
    ·
      refine ⟨257813022191677829968993937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171875348127785219979329291 257813022191677829968993937)
      ·
        refine ⟨193359766643758372476745453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257813022191677829968993937 193359766643758372476745453)
        ·
          refine ⟨72509912491409389678779545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193359766643758372476745453 72509912491409389678779545)
          ·
            refine ⟨54382434368557042259084659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72509912491409389678779545 54382434368557042259084659)
            ·
              refine ⟨81573651552835563388626989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54382434368557042259084659 81573651552835563388626989)
              ·
                refine ⟨30590119332313336270735121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81573651552835563388626989 30590119332313336270735121)
                ·
                  refine ⟨22942589499235002203051341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30590119332313336270735121 22942589499235002203051341)
                  ·
                    refine ⟨8603471062213125826144253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22942589499235002203051341 8603471062213125826144253)
                    ·
                      refine ⟨3226301648329922184804095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8603471062213125826144253 3226301648329922184804095)
                      ·
                        rfl

theorem cell23_6283200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_6283200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283200 prefixEnd_6283200 := by exact prefixLift 6283200
  have htrace : WordTrace (prefixWord ++ tailWord_6283200) baseStart_6283200 baseEnd_6283200 := by
    simpa [prefixWord, tailWord_6283200, baseEnd_6283200] using wordTrace_append hprefix tailTrace_6283200
  have hstable : (prefixWord ++ tailWord_6283200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283200).length < 2 ^ (prefixWord ++ tailWord_6283200).sum := by decide
  have hdescent : baseEnd_6283200 < baseStart_6283200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283220 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_6283220 : Nat := 118140960795 + 6283220 * 2 ^ 59
def prefixEnd_6283220 : Nat := 4983230072969 + 3 ^ 40 * 6283220 * 2
def baseEnd_6283220 : Nat := 1075437305981004035518001

theorem tailTrace_6283220 : CollatzResearch.WordTrace tailWord_6283220 prefixEnd_6283220 1075437305981004035518001 := by
  unfold tailWord_6283220
  simp only [CollatzResearch.WordTrace]
  refine ⟨114583930148487251694083557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152778573531316335592111409 114583930148487251694083557)
  ·
    refine ⟨21484486902841359692640667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114583930148487251694083557 21484486902841359692640667)
    ·
      refine ⟨32226730354262039538961001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21484486902841359692640667 32226730354262039538961001)
      ·
        refine ⟨24170047765696529654220751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32226730354262039538961001 24170047765696529654220751)
        ·
          refine ⟨36255071648544794481331127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24170047765696529654220751 36255071648544794481331127)
          ·
            refine ⟨54382607472817191721996691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36255071648544794481331127 54382607472817191721996691)
            ·
              refine ⟨81573911209225787582995037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54382607472817191721996691 81573911209225787582995037)
              ·
                refine ⟨30590216703459670343623139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81573911209225787582995037 30590216703459670343623139)
                ·
                  refine ⟨45885325055189505515434709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30590216703459670343623139 45885325055189505515434709)
                  ·
                    refine ⟨1075437305981004035518001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45885325055189505515434709 1075437305981004035518001)
                    ·
                      rfl

theorem cell23_6283220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_6283220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283220 prefixEnd_6283220 := by exact prefixLift 6283220
  have htrace : WordTrace (prefixWord ++ tailWord_6283220) baseStart_6283220 baseEnd_6283220 := by
    simpa [prefixWord, tailWord_6283220, baseEnd_6283220] using wordTrace_append hprefix tailTrace_6283220
  have hstable : (prefixWord ++ tailWord_6283220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283220).length < 2 ^ (prefixWord ++ tailWord_6283220).sum := by decide
  have hdescent : baseEnd_6283220 < baseStart_6283220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283274 : List Nat := [3, 1, 2, 2, 4, 1, 2, 1, 2, 1, 4]
def baseStart_6283274 : Nat := 118140960795 + 6283274 * 2 ^ 59
def prefixEnd_6283274 : Nat := 4983230072969 + 3 ^ 40 * 6283274 * 2
def baseEnd_6283274 : Nat := 3226339645898354895278755

theorem tailTrace_6283274 : CollatzResearch.WordTrace tailWord_6283274 prefixEnd_6283274 3226339645898354895278755 := by
  unfold tailWord_6283274
  simp only [CollatzResearch.WordTrace]
  refine ⟨57292457459694717652658219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152779886559185913740421917 57292457459694717652658219)
  ·
    refine ⟨85938686189542076478987329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57292457459694717652658219 85938686189542076478987329)
    ·
      refine ⟨64454014642156557359240497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85938686189542076478987329 64454014642156557359240497)
      ·
        refine ⟨48340510981617418019430373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64454014642156557359240497 48340510981617418019430373)
        ·
          refine ⟨9063845809053265878643195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48340510981617418019430373 9063845809053265878643195)
          ·
            refine ⟨13595768713579898817964793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9063845809053265878643195 13595768713579898817964793)
            ·
              refine ⟨10196826535184924113473595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13595768713579898817964793 10196826535184924113473595)
              ·
                refine ⟨15295239802777386170210393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10196826535184924113473595 15295239802777386170210393)
                ·
                  refine ⟨11471429852083039627657795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15295239802777386170210393 11471429852083039627657795)
                  ·
                    refine ⟨17207144778124559441486693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11471429852083039627657795 17207144778124559441486693)
                    ·
                      refine ⟨3226339645898354895278755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17207144778124559441486693 3226339645898354895278755)
                      ·
                        rfl

theorem cell23_6283274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_6283274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283274 prefixEnd_6283274 := by exact prefixLift 6283274
  have htrace : WordTrace (prefixWord ++ tailWord_6283274) baseStart_6283274 baseEnd_6283274 := by
    simpa [prefixWord, tailWord_6283274, baseEnd_6283274] using wordTrace_append hprefix tailTrace_6283274
  have hstable : (prefixWord ++ tailWord_6283274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283274).length < 2 ^ (prefixWord ++ tailWord_6283274).sum := by decide
  have hdescent : baseEnd_6283274 < baseStart_6283274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283301 : List Nat := [1, 3, 1, 2, 2, 3, 4, 2, 1, 4]
def baseStart_6283301 : Nat := 118140960795 + 6283301 * 2 ^ 59
def prefixEnd_6283301 : Nat := 4983230072969 + 3 ^ 40 * 6283301 * 2
def baseEnd_6283301 : Nat := 1075451169958675429880377

theorem tailTrace_6283301 : CollatzResearch.WordTrace tailWord_6283301 prefixEnd_6283301 1075451169958675429880377 := by
  unfold tailWord_6283301
  simp only [CollatzResearch.WordTrace]
  refine ⟨229170814609681054221865757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152780543073120702814577171 229170814609681054221865757)
  ·
    refine ⟨85939055478630395333199659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229170814609681054221865757 85939055478630395333199659)
    ·
      refine ⟨128908583217945592999799489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85939055478630395333199659 128908583217945592999799489)
      ·
        refine ⟨96681437413459194749849617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128908583217945592999799489 96681437413459194749849617)
        ·
          refine ⟨72511078060094396062387213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96681437413459194749849617 72511078060094396062387213)
          ·
            refine ⟨27191654272535398523395205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72511078060094396062387213 27191654272535398523395205)
            ·
              refine ⟨5098435176100387223136601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27191654272535398523395205 5098435176100387223136601)
              ·
                refine ⟨3823826382075290417352451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5098435176100387223136601 3823826382075290417352451)
                ·
                  refine ⟨5735739573112935626028677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3823826382075290417352451 5735739573112935626028677)
                  ·
                    refine ⟨1075451169958675429880377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5735739573112935626028677 1075451169958675429880377)
                    ·
                      rfl

theorem cell23_6283301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 1, 4].length) (baseStart_6283301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283301 prefixEnd_6283301 := by exact prefixLift 6283301
  have htrace : WordTrace (prefixWord ++ tailWord_6283301) baseStart_6283301 baseEnd_6283301 := by
    simpa [prefixWord, tailWord_6283301, baseEnd_6283301] using wordTrace_append hprefix tailTrace_6283301
  have hstable : (prefixWord ++ tailWord_6283301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283301).length < 2 ^ (prefixWord ++ tailWord_6283301).sum := by decide
  have hdescent : baseEnd_6283301 < baseStart_6283301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283324 : List Nat := [2, 2, 2, 2, 2, 1, 3, 2, 3, 1, 3]
def baseStart_6283324 : Nat := 118140960795 + 6283324 * 2 ^ 59
def prefixEnd_6283324 : Nat := 4983230072969 + 3 ^ 40 * 6283324 * 2
def baseEnd_6283324 : Nat := 3226365319931079699653525

theorem tailTrace_6283324 : CollatzResearch.WordTrace tailWord_6283324 prefixEnd_6283324 3226365319931079699653525 := by
  unfold tailWord_6283324
  simp only [CollatzResearch.WordTrace]
  refine ⟨114585826744298864574976513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152781102325731819433302017 114585826744298864574976513)
  ·
    refine ⟨85939370058224148431232385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114585826744298864574976513 85939370058224148431232385)
    ·
      refine ⟨64454527543668111323424289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85939370058224148431232385 64454527543668111323424289)
      ·
        refine ⟨48340895657751083492568217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64454527543668111323424289 48340895657751083492568217)
        ·
          refine ⟨36255671743313312619426163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48340895657751083492568217 36255671743313312619426163)
          ·
            refine ⟨54383507614969968929139245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36255671743313312619426163 54383507614969968929139245)
            ·
              refine ⟨20393815355613738348427217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54383507614969968929139245 20393815355613738348427217)
              ·
                refine ⟨15295361516710303761320413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20393815355613738348427217 15295361516710303761320413)
                ·
                  refine ⟨5735760568766363910495155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15295361516710303761320413 5735760568766363910495155)
                  ·
                    refine ⟨8603640853149545865742733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5735760568766363910495155 8603640853149545865742733)
                    ·
                      refine ⟨3226365319931079699653525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8603640853149545865742733 3226365319931079699653525)
                      ·
                        rfl

theorem cell23_6283324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_6283324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283324 prefixEnd_6283324 := by exact prefixLift 6283324
  have htrace : WordTrace (prefixWord ++ tailWord_6283324) baseStart_6283324 baseEnd_6283324 := by
    simpa [prefixWord, tailWord_6283324, baseEnd_6283324] using wordTrace_append hprefix tailTrace_6283324
  have hstable : (prefixWord ++ tailWord_6283324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283324).length < 2 ^ (prefixWord ++ tailWord_6283324).sum := by decide
  have hdescent : baseEnd_6283324 < baseStart_6283324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283367 : List Nat := [1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_6283367 : Nat := 118140960795 + 6283367 * 2 ^ 59
def prefixEnd_6283367 : Nat := 4983230072969 + 3 ^ 40 * 6283367 * 2
def baseEnd_6283367 : Nat := 3226387399599223031415827

theorem tailTrace_6283367 : CollatzResearch.WordTrace tailWord_6283367 prefixEnd_6283367 3226387399599223031415827 := by
  unfold tailWord_6283367
  simp only [CollatzResearch.WordTrace]
  refine ⟨229173221827441947493768355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152782147884961298329178903 229173221827441947493768355)
  ·
    refine ⟨343759832741162921240652533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229173221827441947493768355 343759832741162921240652533)
    ·
      refine ⟨32227484319484023866311175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 343759832741162921240652533 32227484319484023866311175)
      ·
        refine ⟨48341226479226035799466763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32227484319484023866311175 48341226479226035799466763)
        ·
          refine ⟨72511839718839053699200145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48341226479226035799466763 72511839718839053699200145)
          ·
            refine ⟨54383879789129290274400109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72511839718839053699200145 54383879789129290274400109)
            ·
              refine ⟨20393954920923483852900041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54383879789129290274400109 20393954920923483852900041)
              ·
                refine ⟨15295466190692612889675031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20393954920923483852900041 15295466190692612889675031)
                ·
                  refine ⟨22943199286038919334512547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15295466190692612889675031 22943199286038919334512547)
                  ·
                    refine ⟨34414798929058379001768821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22943199286038919334512547 34414798929058379001768821)
                    ·
                      refine ⟨3226387399599223031415827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34414798929058379001768821 3226387399599223031415827)
                      ·
                        rfl

theorem cell23_6283367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_6283367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283367 prefixEnd_6283367 := by exact prefixLift 6283367
  have htrace : WordTrace (prefixWord ++ tailWord_6283367) baseStart_6283367 baseEnd_6283367 := by
    simpa [prefixWord, tailWord_6283367, baseEnd_6283367] using wordTrace_append hprefix tailTrace_6283367
  have hstable : (prefixWord ++ tailWord_6283367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283367).length < 2 ^ (prefixWord ++ tailWord_6283367).sum := by decide
  have hdescent : baseEnd_6283367 < baseStart_6283367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283415 : List Nat := [1, 1, 3, 3, 5, 1, 1, 1, 3, 2, 2]
def baseStart_6283415 : Nat := 118140960795 + 6283415 * 2 ^ 59
def prefixEnd_6283415 : Nat := 4983230072969 + 3 ^ 40 * 6283415 * 2
def baseEnd_6283415 : Nat := 3226412046670638843615607

theorem tailTrace_6283415 : CollatzResearch.WordTrace tailWord_6283415 prefixEnd_6283415 3226412046670638843615607 := by
  unfold tailWord_6283415
  simp only [CollatzResearch.WordTrace]
  refine ⟨229174972531268051691515699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152783315020845367794343799 229174972531268051691515699)
  ·
    refine ⟨343762458796902077537273549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229174972531268051691515699 343762458796902077537273549)
    ·
      refine ⟨128910922048838279076477581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343762458796902077537273549 128910922048838279076477581)
      ·
        refine ⟨48341595768314354653679093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128910922048838279076477581 48341595768314354653679093)
        ·
          refine ⟨4532024603279470748782415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48341595768314354653679093 4532024603279470748782415)
          ·
            refine ⟨6798036904919206123173623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4532024603279470748782415 6798036904919206123173623)
            ·
              refine ⟨10197055357378809184760435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6798036904919206123173623 10197055357378809184760435)
              ·
                refine ⟨15295583036068213777140653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10197055357378809184760435 15295583036068213777140653)
                ·
                  refine ⟨5735843638525580166427745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15295583036068213777140653 5735843638525580166427745)
                  ·
                    refine ⟨4301882728894185124820809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5735843638525580166427745 4301882728894185124820809)
                    ·
                      refine ⟨3226412046670638843615607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4301882728894185124820809 3226412046670638843615607)
                      ·
                        rfl

theorem cell23_6283415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_6283415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283415 prefixEnd_6283415 := by exact prefixLift 6283415
  have htrace : WordTrace (prefixWord ++ tailWord_6283415) baseStart_6283415 baseEnd_6283415 := by
    simpa [prefixWord, tailWord_6283415, baseEnd_6283415] using wordTrace_append hprefix tailTrace_6283415
  have hstable : (prefixWord ++ tailWord_6283415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283415).length < 2 ^ (prefixWord ++ tailWord_6283415).sum := by decide
  have hdescent : baseEnd_6283415 < baseStart_6283415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283467 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 4]
def baseStart_6283467 : Nat := 118140960795 + 6283467 * 2 ^ 59
def prefixEnd_6283467 : Nat := 4983230072969 + 3 ^ 40 * 6283467 * 2
def baseEnd_6283467 : Nat := 3226438747664672640165367

theorem tailTrace_6283467 : CollatzResearch.WordTrace tailWord_6283467 prefixEnd_6283467 3226438747664672640165367 := by
  unfold tailWord_6283467
  simp only [CollatzResearch.WordTrace]
  refine ⟨229176869127079664572408655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152784579418053109714939103 229176869127079664572408655)
  ·
    refine ⟨343765303690619496858612983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229176869127079664572408655 343765303690619496858612983)
    ·
      refine ⟨515647955535929245287919475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343765303690619496858612983 515647955535929245287919475)
      ·
        refine ⟨773471933303893867931879213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515647955535929245287919475 773471933303893867931879213)
        ·
          refine ⟨290051974988960200474454705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 773471933303893867931879213 290051974988960200474454705)
          ·
            refine ⟨217538981241720150355841029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290051974988960200474454705 217538981241720150355841029)
            ·
              refine ⟨40788558982822528191720193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217538981241720150355841029 40788558982822528191720193)
              ·
                refine ⟨30591419237116896143790145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40788558982822528191720193 30591419237116896143790145)
                ·
                  refine ⟨22943564427837672107842609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30591419237116896143790145 22943564427837672107842609)
                  ·
                    refine ⟨17207673320878254080881957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22943564427837672107842609 17207673320878254080881957)
                    ·
                      refine ⟨3226438747664672640165367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17207673320878254080881957 3226438747664672640165367)
                      ·
                        rfl

theorem cell23_6283467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 4].length) (baseStart_6283467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283467 prefixEnd_6283467 := by exact prefixLift 6283467
  have htrace : WordTrace (prefixWord ++ tailWord_6283467) baseStart_6283467 baseEnd_6283467 := by
    simpa [prefixWord, tailWord_6283467, baseEnd_6283467] using wordTrace_append hprefix tailTrace_6283467
  have hstable : (prefixWord ++ tailWord_6283467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283467).length < 2 ^ (prefixWord ++ tailWord_6283467).sum := by decide
  have hdescent : baseEnd_6283467 < baseStart_6283467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283474 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_6283474 : Nat := 118140960795 + 6283474 * 2 ^ 59
def prefixEnd_6283474 : Nat := 4983230072969 + 3 ^ 40 * 6283474 * 2
def baseEnd_6283474 : Nat := 3226442342029254112777835

theorem tailTrace_6283474 : CollatzResearch.WordTrace tailWord_6283474 prefixEnd_6283474 3226442342029254112777835 := by
  unfold tailWord_6283474
  simp only [CollatzResearch.WordTrace]
  refine ⟨57294281109513576191978369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152784749625369536511942317 57294281109513576191978369)
  ·
    refine ⟨42970710832135182143983777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57294281109513576191978369 42970710832135182143983777)
    ·
      refine ⟨32228033124101386607987833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42970710832135182143983777 32228033124101386607987833)
      ·
        refine ⟨24171024843076039955990875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32228033124101386607987833 24171024843076039955990875)
        ·
          refine ⟨36256537264614059933986313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24171024843076039955990875 36256537264614059933986313)
          ·
            refine ⟨27192402948460544950489735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36256537264614059933986313 27192402948460544950489735)
            ·
              refine ⟨40788604422690817425734603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27192402948460544950489735 40788604422690817425734603)
              ·
                refine ⟨61182906634036226138601905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40788604422690817425734603 61182906634036226138601905)
                ·
                  refine ⟨45887179975527169603951429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61182906634036226138601905 45887179975527169603951429)
                  ·
                    refine ⟨8603846245411344300740893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45887179975527169603951429 8603846245411344300740893)
                    ·
                      refine ⟨3226442342029254112777835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8603846245411344300740893 3226442342029254112777835)
                      ·
                        rfl

theorem cell23_6283474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_6283474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283474 prefixEnd_6283474 := by exact prefixLift 6283474
  have htrace : WordTrace (prefixWord ++ tailWord_6283474) baseStart_6283474 baseEnd_6283474 := by
    simpa [prefixWord, tailWord_6283474, baseEnd_6283474] using wordTrace_append hprefix tailTrace_6283474
  have hstable : (prefixWord ++ tailWord_6283474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283474).length < 2 ^ (prefixWord ++ tailWord_6283474).sum := by decide
  have hdescent : baseEnd_6283474 < baseStart_6283474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283507 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 1, 7]
def baseStart_6283507 : Nat := 118140960795 + 6283507 * 2 ^ 59
def prefixEnd_6283507 : Nat := 4983230072969 + 3 ^ 40 * 6283507 * 2
def baseEnd_6283507 : Nat := 1075486428963617494555061

theorem tailTrace_6283507 : CollatzResearch.WordTrace tailWord_6283507 prefixEnd_6283507 1075486428963617494555061 := by
  unfold tailWord_6283507
  simp only [CollatzResearch.WordTrace]
  refine ⟨229178328046934751403864775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152785552031289834269243183 229178328046934751403864775)
  ·
    refine ⟨343767492070402127105797163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229178328046934751403864775 343767492070402127105797163)
    ·
      refine ⟨515651238105603190658695745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343767492070402127105797163 515651238105603190658695745)
      ·
        refine ⟨386738428579202392994021809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 515651238105603190658695745 386738428579202392994021809)
        ·
          refine ⟨290053821434401794745516357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386738428579202392994021809 290053821434401794745516357)
          ·
            refine ⟨54385091518950336514784317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 290053821434401794745516357 54385091518950336514784317)
            ·
              refine ⟨20394409319606376193044119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54385091518950336514784317 20394409319606376193044119)
              ·
                refine ⟨30591613979409564289566179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20394409319606376193044119 30591613979409564289566179)
                ·
                  refine ⟨45887420969114346434349269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30591613979409564289566179 45887420969114346434349269)
                  ·
                    refine ⟨1075486428963617494555061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45887420969114346434349269 1075486428963617494555061)
                    ·
                      rfl

theorem cell23_6283507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 7].length) (baseStart_6283507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283507 prefixEnd_6283507 := by exact prefixLift 6283507
  have htrace : WordTrace (prefixWord ++ tailWord_6283507) baseStart_6283507 baseEnd_6283507 := by
    simpa [prefixWord, tailWord_6283507, baseEnd_6283507] using wordTrace_append hprefix tailTrace_6283507
  have hstable : (prefixWord ++ tailWord_6283507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283507).length < 2 ^ (prefixWord ++ tailWord_6283507).sum := by decide
  have hdescent : baseEnd_6283507 < baseStart_6283507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283517 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_6283517 : Nat := 118140960795 + 6283517 * 2 ^ 59
def prefixEnd_6283517 : Nat := 4983230072969 + 3 ^ 40 * 6283517 * 2
def baseEnd_6283517 : Nat := 3226464421697397444540137

theorem tailTrace_6283517 : CollatzResearch.WordTrace tailWord_6283517 prefixEnd_6283517 3226464421697397444540137 := by
  unfold tailWord_6283517
  simp only [CollatzResearch.WordTrace]
  refine ⟨229178692776898523111728805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152785795184599015407819203 229178692776898523111728805)
  ·
    refine ⟨42971004895668473083449151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229178692776898523111728805 42971004895668473083449151)
    ·
      refine ⟨64456507343502709625173727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42971004895668473083449151 64456507343502709625173727)
      ·
        refine ⟨96684761015254064437760591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64456507343502709625173727 96684761015254064437760591)
        ·
          refine ⟨145027141522881096656640887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96684761015254064437760591 145027141522881096656640887)
          ·
            refine ⟨217540712284321644984961331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145027141522881096656640887 217540712284321644984961331)
            ·
              refine ⟨326311068426482467477441997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217540712284321644984961331 326311068426482467477441997)
              ·
                refine ⟨122366650659930925304040749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 326311068426482467477441997 122366650659930925304040749)
                ·
                  refine ⟨45887493997474096989015281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122366650659930925304040749 45887493997474096989015281)
                  ·
                    refine ⟨34415620498105572741761461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45887493997474096989015281 34415620498105572741761461)
                    ·
                      refine ⟨3226464421697397444540137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34415620498105572741761461 3226464421697397444540137)
                      ·
                        rfl

theorem cell23_6283517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_6283517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283517 prefixEnd_6283517 := by exact prefixLift 6283517
  have htrace : WordTrace (prefixWord ++ tailWord_6283517) baseStart_6283517 baseEnd_6283517 := by
    simpa [prefixWord, tailWord_6283517, baseEnd_6283517] using wordTrace_append hprefix tailTrace_6283517
  have hstable : (prefixWord ++ tailWord_6283517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283517).length < 2 ^ (prefixWord ++ tailWord_6283517).sum := by decide
  have hdescent : baseEnd_6283517 < baseStart_6283517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283522 : List Nat := [3, 4, 1, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_6283522 : Nat := 118140960795 + 6283522 * 2 ^ 59
def prefixEnd_6283522 : Nat := 4983230072969 + 3 ^ 40 * 6283522 * 2
def baseEnd_6283522 : Nat := 3226466989100669924977615

theorem tailTrace_6283522 : CollatzResearch.WordTrace tailWord_6283522 prefixEnd_6283522 3226466989100669924977615 := by
  unfold tailWord_6283522
  simp only [CollatzResearch.WordTrace]
  refine ⟨57294718785470102241415205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152785916761253605977107213 57294718785470102241415205)
  ·
    refine ⟨10742759772275644170265351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57294718785470102241415205 10742759772275644170265351)
    ·
      refine ⟨16114139658413466255398027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10742759772275644170265351 16114139658413466255398027)
      ·
        refine ⟨24171209487620199383097041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16114139658413466255398027 24171209487620199383097041)
        ·
          refine ⟨18128407115715149537322781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24171209487620199383097041 18128407115715149537322781)
          ·
            refine ⟨6798152668393181076496043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18128407115715149537322781 6798152668393181076496043)
            ·
              refine ⟨10197229002589771614744065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6798152668393181076496043 10197229002589771614744065)
              ·
                refine ⟨7647921751942328711058049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10197229002589771614744065 7647921751942328711058049)
                ·
                  refine ⟨5735941313956746533293537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7647921751942328711058049 5735941313956746533293537)
                  ·
                    refine ⟨4301955985467559899970153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5735941313956746533293537 4301955985467559899970153)
                    ·
                      refine ⟨3226466989100669924977615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4301955985467559899970153 3226466989100669924977615)
                      ·
                        rfl

theorem cell23_6283522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_6283522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283522 prefixEnd_6283522 := by exact prefixLift 6283522
  have htrace : WordTrace (prefixWord ++ tailWord_6283522) baseStart_6283522 baseEnd_6283522 := by
    simpa [prefixWord, tailWord_6283522, baseEnd_6283522] using wordTrace_append hprefix tailTrace_6283522
  have hstable : (prefixWord ++ tailWord_6283522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283522).length < 2 ^ (prefixWord ++ tailWord_6283522).sum := by decide
  have hdescent : baseEnd_6283522 < baseStart_6283522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283564 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 3]
def baseStart_6283564 : Nat := 118140960795 + 6283564 * 2 ^ 59
def prefixEnd_6283564 : Nat := 4983230072969 + 3 ^ 40 * 6283564 * 2
def baseEnd_6283564 : Nat := 3226488555288158760652421

theorem tailTrace_6283564 : CollatzResearch.WordTrace tailWord_6283564 prefixEnd_6283564 3226488555288158760652421 := by
  unfold tailWord_6283564
  simp only [CollatzResearch.WordTrace]
  refine ⟨114590203503864125069344873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152786938005152166759126497 114590203503864125069344873)
  ·
    refine ⟨85942652627898093802008655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114590203503864125069344873 85942652627898093802008655)
    ·
      refine ⟨128913978941847140703012983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85942652627898093802008655 128913978941847140703012983)
      ·
        refine ⟨193370968412770711054519475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128913978941847140703012983 193370968412770711054519475)
        ·
          refine ⟨290056452619156066581779213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193370968412770711054519475 290056452619156066581779213)
          ·
            refine ⟨108771169732183524968167205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290056452619156066581779213 108771169732183524968167205)
            ·
              refine ⟨20394594324784410931531351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108771169732183524968167205 20394594324784410931531351)
              ·
                refine ⟨30591891487176616397297027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20394594324784410931531351 30591891487176616397297027)
                ·
                  refine ⟨45887837230764924595945541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30591891487176616397297027 45887837230764924595945541)
                  ·
                    refine ⟨8603969480768423361739789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45887837230764924595945541 8603969480768423361739789)
                    ·
                      refine ⟨3226488555288158760652421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8603969480768423361739789 3226488555288158760652421)
                      ·
                        rfl

theorem cell23_6283564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_6283564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283564 prefixEnd_6283564 := by exact prefixLift 6283564
  have htrace : WordTrace (prefixWord ++ tailWord_6283564) baseStart_6283564 baseEnd_6283564 := by
    simpa [prefixWord, tailWord_6283564, baseEnd_6283564] using wordTrace_append hprefix tailTrace_6283564
  have hstable : (prefixWord ++ tailWord_6283564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283564).length < 2 ^ (prefixWord ++ tailWord_6283564).sum := by decide
  have hdescent : baseEnd_6283564 < baseStart_6283564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283567 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 8]
def baseStart_6283567 : Nat := 118140960795 + 6283567 * 2 ^ 59
def prefixEnd_6283567 : Nat := 4983230072969 + 3 ^ 40 * 6283567 * 2
def baseEnd_6283567 : Nat := 358498899525569138768323

theorem tailTrace_6283567 : CollatzResearch.WordTrace tailWord_6283567 prefixEnd_6283567 358498899525569138768323 := by
  unfold tailWord_6283567
  simp only [CollatzResearch.WordTrace]
  refine ⟨229180516426717381651048955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152787010951144921100699303 229180516426717381651048955)
  ·
    refine ⟨343770774640076072476573433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229180516426717381651048955 343770774640076072476573433)
    ·
      refine ⟨257828080980057054357430075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343770774640076072476573433 257828080980057054357430075)
      ·
        refine ⟨386742121470085581536145113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257828080980057054357430075 386742121470085581536145113)
        ·
          refine ⟨290056591102564186152108835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386742121470085581536145113 290056591102564186152108835)
          ·
            refine ⟨435084886653846279228163253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290056591102564186152108835 435084886653846279228163253)
            ·
              refine ⟨40789208123798088677640305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 435084886653846279228163253 40789208123798088677640305)
              ·
                refine ⟨30591906092848566508230229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40789208123798088677640305 30591906092848566508230229)
                ·
                  refine ⟨358498899525569138768323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30591906092848566508230229 358498899525569138768323)
                  ·
                    rfl

theorem cell23_6283567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 8].length) (baseStart_6283567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283567 prefixEnd_6283567 := by exact prefixLift 6283567
  have htrace : WordTrace (prefixWord ++ tailWord_6283567) baseStart_6283567 baseEnd_6283567 := by
    simpa [prefixWord, tailWord_6283567, baseEnd_6283567] using wordTrace_append hprefix tailTrace_6283567
  have hstable : (prefixWord ++ tailWord_6283567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283567).length < 2 ^ (prefixWord ++ tailWord_6283567).sum := by decide
  have hdescent : baseEnd_6283567 < baseStart_6283567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283587 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 8]
def baseStart_6283587 : Nat := 118140960795 + 6283587 * 2 ^ 59
def prefixEnd_6283587 : Nat := 4983230072969 + 3 ^ 40 * 6283587 * 2
def baseEnd_6283587 : Nat := 3226500365343212170664815

theorem tailTrace_6283587 : CollatzResearch.WordTrace tailWord_6283587 prefixEnd_6283587 3226500365343212170664815 := by
  unfold tailWord_6283587
  simp only [CollatzResearch.WordTrace]
  refine ⟨229181245886644925066777015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152787497257763283377851343 229181245886644925066777015)
  ·
    refine ⟨343771868829967387600165523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229181245886644925066777015 343771868829967387600165523)
    ·
      refine ⟨515657803244951081400248285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343771868829967387600165523 515657803244951081400248285)
      ·
        refine ⟨193371676216856655525093107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 515657803244951081400248285 193371676216856655525093107)
        ·
          refine ⟨290057514325284983287639661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193371676216856655525093107 290057514325284983287639661)
          ·
            refine ⟨108771567871981868732864873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290057514325284983287639661 108771567871981868732864873)
            ·
              refine ⟨81578675903986401549648655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108771567871981868732864873 81578675903986401549648655)
              ·
                refine ⟨122368013855979602324472983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81578675903986401549648655 122368013855979602324472983)
                ·
                  refine ⟨183552020783969403486709475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122368013855979602324472983 183552020783969403486709475)
                  ·
                    refine ⟨275328031175954105230064213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 183552020783969403486709475 275328031175954105230064213)
                    ·
                      refine ⟨3226500365343212170664815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 275328031175954105230064213 3226500365343212170664815)
                      ·
                        rfl

theorem cell23_6283587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_6283587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283587 prefixEnd_6283587 := by exact prefixLift 6283587
  have htrace : WordTrace (prefixWord ++ tailWord_6283587) baseStart_6283587 baseEnd_6283587 := by
    simpa [prefixWord, tailWord_6283587, baseEnd_6283587] using wordTrace_append hprefix tailTrace_6283587
  have hstable : (prefixWord ++ tailWord_6283587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283587).length < 2 ^ (prefixWord ++ tailWord_6283587).sum := by decide
  have hdescent : baseEnd_6283587 < baseStart_6283587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283601 : List Nat := [1, 2, 2, 1, 4, 2, 4, 1, 6]
def baseStart_6283601 : Nat := 118140960795 + 6283601 * 2 ^ 59
def prefixEnd_6283601 : Nat := 4983230072969 + 3 ^ 40 * 6283601 * 2
def baseEnd_6283601 : Nat := 358500839341375012876639

theorem tailTrace_6283601 : CollatzResearch.WordTrace tailWord_6283601 prefixEnd_6283601 358500839341375012876639 := by
  unfold tailWord_6283601
  simp only [CollatzResearch.WordTrace]
  refine ⟨229181756508594205457786657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152787837672396136971857771 229181756508594205457786657)
  ·
    refine ⟨171886317381445654093339993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229181756508594205457786657 171886317381445654093339993)
    ·
      refine ⟨128914738036084240570004995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171886317381445654093339993 128914738036084240570004995)
      ·
        refine ⟨193372107054126360855007493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128914738036084240570004995 193372107054126360855007493)
        ·
          refine ⟨36257270072648692660313905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193372107054126360855007493 36257270072648692660313905)
          ·
            refine ⟨27192952554486519495235429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36257270072648692660313905 27192952554486519495235429)
            ·
              refine ⟨5098678603966222405356643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27192952554486519495235429 5098678603966222405356643)
              ·
                refine ⟨7648017905949333608034965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5098678603966222405356643 7648017905949333608034965)
                ·
                  refine ⟨358500839341375012876639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7648017905949333608034965 358500839341375012876639)
                  ·
                    rfl

theorem cell23_6283601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 6].length) (baseStart_6283601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283601 prefixEnd_6283601 := by exact prefixLift 6283601
  have htrace : WordTrace (prefixWord ++ tailWord_6283601) baseStart_6283601 baseEnd_6283601 := by
    simpa [prefixWord, tailWord_6283601, baseEnd_6283601] using wordTrace_append hprefix tailTrace_6283601
  have hstable : (prefixWord ++ tailWord_6283601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283601).length < 2 ^ (prefixWord ++ tailWord_6283601).sum := by decide
  have hdescent : baseEnd_6283601 < baseStart_6283601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283645 : List Nat := [1, 4, 1, 1, 2, 4, 1, 4, 1, 1, 3]
def baseStart_6283645 : Nat := 118140960795 + 6283645 * 2 ^ 59
def prefixEnd_6283645 : Nat := 4983230072969 + 3 ^ 40 * 6283645 * 2
def baseEnd_6283645 : Nat := 3226530147221172943739549

theorem tailTrace_6283645 : CollatzResearch.WordTrace tailWord_6283645 prefixEnd_6283645 3226530147221172943739549 := by
  unfold tailWord_6283645
  simp only [CollatzResearch.WordTrace]
  refine ⟨229183361320434800972388389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152788907546956533981592259 229183361320434800972388389)
  ·
    refine ⟨42971880247581525182322823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229183361320434800972388389 42971880247581525182322823)
    ·
      refine ⟨64457820371372287773484235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42971880247581525182322823 64457820371372287773484235)
      ·
        refine ⟨96686730557058431660226353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64457820371372287773484235 96686730557058431660226353)
        ·
          refine ⟨72515047917793823745169765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96686730557058431660226353 72515047917793823745169765)
          ·
            refine ⟨13596571484586341952219331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72515047917793823745169765 13596571484586341952219331)
            ·
              refine ⟨20394857226879512928328997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13596571484586341952219331 20394857226879512928328997)
              ·
                refine ⟨3824035730039908674061687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20394857226879512928328997 3824035730039908674061687)
                ·
                  refine ⟨5736053595059863011092531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3824035730039908674061687 5736053595059863011092531)
                  ·
                    refine ⟨8604080392589794516638797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5736053595059863011092531 8604080392589794516638797)
                    ·
                      refine ⟨3226530147221172943739549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8604080392589794516638797 3226530147221172943739549)
                      ·
                        rfl

theorem cell23_6283645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 1, 1, 3].length) (baseStart_6283645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283645 prefixEnd_6283645 := by exact prefixLift 6283645
  have htrace : WordTrace (prefixWord ++ tailWord_6283645) baseStart_6283645 baseEnd_6283645 := by
    simpa [prefixWord, tailWord_6283645, baseEnd_6283645] using wordTrace_append hprefix tailTrace_6283645
  have hstable : (prefixWord ++ tailWord_6283645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283645).length < 2 ^ (prefixWord ++ tailWord_6283645).sum := by decide
  have hdescent : baseEnd_6283645 < baseStart_6283645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283671 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 3]
def baseStart_6283671 : Nat := 118140960795 + 6283671 * 2 ^ 59
def prefixEnd_6283671 : Nat := 4983230072969 + 3 ^ 40 * 6283671 * 2
def baseEnd_6283671 : Nat := 3226543497718189842014429

theorem tailTrace_6283671 : CollatzResearch.WordTrace tailWord_6283671 prefixEnd_6283671 3226543497718189842014429 := by
  unfold tailWord_6283671
  simp only [CollatzResearch.WordTrace]
  refine ⟨229184309618340607412834867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152789539745560404941889911 229184309618340607412834867)
  ·
    refine ⟨343776464427510911119252301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229184309618340607412834867 343776464427510911119252301)
    ·
      refine ⟨128916174160316591669719613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343776464427510911119252301 128916174160316591669719613)
      ·
        refine ⟨48343565310118721876144855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128916174160316591669719613 48343565310118721876144855)
        ·
          refine ⟨72515347965178082814217283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48343565310118721876144855 72515347965178082814217283)
          ·
            refine ⟨108773021947767124221325925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72515347965178082814217283 108773021947767124221325925)
            ·
              refine ⟨20394941615206335791498611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108773021947767124221325925 20394941615206335791498611)
              ·
                refine ⟨30592412422809503687247917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20394941615206335791498611 30592412422809503687247917)
                ·
                  refine ⟨11472154658553563882717969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30592412422809503687247917 11472154658553563882717969)
                  ·
                    refine ⟨8604115993915172912038477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11472154658553563882717969 8604115993915172912038477)
                    ·
                      refine ⟨3226543497718189842014429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8604115993915172912038477 3226543497718189842014429)
                      ·
                        rfl

theorem cell23_6283671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_6283671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283671 prefixEnd_6283671 := by exact prefixLift 6283671
  have htrace : WordTrace (prefixWord ++ tailWord_6283671) baseStart_6283671 baseEnd_6283671 := by
    simpa [prefixWord, tailWord_6283671, baseEnd_6283671] using wordTrace_append hprefix tailTrace_6283671
  have hstable : (prefixWord ++ tailWord_6283671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283671).length < 2 ^ (prefixWord ++ tailWord_6283671).sum := by decide
  have hdescent : baseEnd_6283671 < baseStart_6283671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283678 : List Nat := [4, 3, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_6283678 : Nat := 118140960795 + 6283678 * 2 ^ 59
def prefixEnd_6283678 : Nat := 4983230072969 + 3 ^ 40 * 6283678 * 2
def baseEnd_6283678 : Nat := 1075515697360923771542299

theorem tailTrace_6283678 : CollatzResearch.WordTrace tailWord_6283678 prefixEnd_6283678 1075515697360923771542299 := by
  unfold tailWord_6283678
  simp only [CollatzResearch.WordTrace]
  refine ⟨28648070616164405951042461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152789709952876831738893125 28648070616164405951042461)
  ·
    refine ⟨10743026481061652231640923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28648070616164405951042461 10743026481061652231640923)
    ·
      refine ⟨16114539721592478347461385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10743026481061652231640923 16114539721592478347461385)
      ·
        refine ⟨12085904791194358760596039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16114539721592478347461385 12085904791194358760596039)
        ·
          refine ⟨18128857186791538140894059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12085904791194358760596039 18128857186791538140894059)
          ·
            refine ⟨27193285780187307211341089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18128857186791538140894059 27193285780187307211341089)
            ·
              refine ⟨20394964335140480408505817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27193285780187307211341089 20394964335140480408505817)
              ·
                refine ⟨15296223251355360306379363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20394964335140480408505817 15296223251355360306379363)
                ·
                  refine ⟨22944334877033040459569045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15296223251355360306379363 22944334877033040459569045)
                  ·
                    refine ⟨1075515697360923771542299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22944334877033040459569045 1075515697360923771542299)
                    ·
                      rfl

theorem cell23_6283678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_6283678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283678 prefixEnd_6283678 := by exact prefixLift 6283678
  have htrace : WordTrace (prefixWord ++ tailWord_6283678) baseStart_6283678 baseEnd_6283678 := by
    simpa [prefixWord, tailWord_6283678, baseEnd_6283678] using wordTrace_append hprefix tailTrace_6283678
  have hstable : (prefixWord ++ tailWord_6283678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283678).length < 2 ^ (prefixWord ++ tailWord_6283678).sum := by decide
  have hdescent : baseEnd_6283678 < baseStart_6283678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283761 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 2, 4, 3]
def baseStart_6283761 : Nat := 118140960795 + 6283761 * 2 ^ 59
def prefixEnd_6283761 : Nat := 4983230072969 + 3 ^ 40 * 6283761 * 2
def baseEnd_6283761 : Nat := 3226589710977094489889015

theorem tailTrace_6283761 : CollatzResearch.WordTrace tailWord_6283761 prefixEnd_6283761 3226589710977094489889015 := by
  unfold tailWord_6283761
  simp only [CollatzResearch.WordTrace]
  refine ⟨229187592188014552783611137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152791728125343035189074091 229187592188014552783611137)
  ·
    refine ⟨171890694141010914587708353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229187592188014552783611137 171890694141010914587708353)
    ·
      refine ⟨128918020605758185940781265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171890694141010914587708353 128918020605758185940781265)
      ·
        refine ⟨96688515454318639455585949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128918020605758185940781265 96688515454318639455585949)
        ·
          refine ⟨36258193295369489795844731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96688515454318639455585949 36258193295369489795844731)
          ·
            refine ⟨54387289943054234693767097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36258193295369489795844731 54387289943054234693767097)
            ·
              refine ⟨40790467457290676020325323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54387289943054234693767097 40790467457290676020325323)
              ·
                refine ⟨61185701185936014030487985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40790467457290676020325323 61185701185936014030487985)
                ·
                  refine ⟨45889275889452010522865989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61185701185936014030487985 45889275889452010522865989)
                  ·
                    refine ⟨8604239229272251973037373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45889275889452010522865989 8604239229272251973037373)
                    ·
                      refine ⟨3226589710977094489889015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8604239229272251973037373 3226589710977094489889015)
                      ·
                        rfl

theorem cell23_6283761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_6283761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283761 prefixEnd_6283761 := by exact prefixLift 6283761
  have htrace : WordTrace (prefixWord ++ tailWord_6283761) baseStart_6283761 baseEnd_6283761 := by
    simpa [prefixWord, tailWord_6283761, baseEnd_6283761] using wordTrace_append hprefix tailTrace_6283761
  have hstable : (prefixWord ++ tailWord_6283761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283761).length < 2 ^ (prefixWord ++ tailWord_6283761).sum := by decide
  have hdescent : baseEnd_6283761 < baseStart_6283761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283775 : List Nat := [1, 1, 2, 2, 1, 2, 5, 3, 2, 2, 2]
def baseStart_6283775 : Nat := 118140960795 + 6283775 * 2 ^ 59
def prefixEnd_6283775 : Nat := 4983230072969 + 3 ^ 40 * 6283775 * 2
def baseEnd_6283775 : Nat := 3226596899706257435113951

theorem tailTrace_6283775 : CollatzResearch.WordTrace tailWord_6283775 prefixEnd_6283775 3226596899706257435113951 := by
  unfold tailWord_6283775
  simp only [CollatzResearch.WordTrace]
  refine ⟨229188102809963833174620779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152792068539975888783080519 229188102809963833174620779)
  ·
    refine ⟨343782154214945749761931169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229188102809963833174620779 343782154214945749761931169)
    ·
      refine ⟨257836615661209312321448377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343782154214945749761931169 257836615661209312321448377)
      ·
        refine ⟨193377461745906984241086283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257836615661209312321448377 193377461745906984241086283)
        ·
          refine ⟨290066192618860476361629425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193377461745906984241086283 290066192618860476361629425)
          ·
            refine ⟨217549644464145357271222069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290066192618860476361629425 217549644464145357271222069)
            ·
              refine ⟨20395279168513627244177069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 217549644464145357271222069 20395279168513627244177069)
              ·
                refine ⟨7648229688192610216566401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20395279168513627244177069 7648229688192610216566401)
                ·
                  refine ⟨5736172266144457662424801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7648229688192610216566401 5736172266144457662424801)
                  ·
                    refine ⟨4302129199608343246818601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5736172266144457662424801 4302129199608343246818601)
                    ·
                      refine ⟨3226596899706257435113951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4302129199608343246818601 3226596899706257435113951)
                      ·
                        rfl

theorem cell23_6283775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 2, 2].length) (baseStart_6283775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283775 prefixEnd_6283775 := by exact prefixLift 6283775
  have htrace : WordTrace (prefixWord ++ tailWord_6283775) baseStart_6283775 baseEnd_6283775 := by
    simpa [prefixWord, tailWord_6283775, baseEnd_6283775] using wordTrace_append hprefix tailTrace_6283775
  have hstable : (prefixWord ++ tailWord_6283775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283775).length < 2 ^ (prefixWord ++ tailWord_6283775).sum := by decide
  have hdescent : baseEnd_6283775 < baseStart_6283775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283831 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 4]
def baseStart_6283831 : Nat := 118140960795 + 6283831 * 2 ^ 59
def prefixEnd_6283831 : Nat := 4983230072969 + 3 ^ 40 * 6283831 * 2
def baseEnd_6283831 : Nat := 3226625654622909216013693

theorem tailTrace_6283831 : CollatzResearch.WordTrace tailWord_6283831 prefixEnd_6283831 3226625654622909216013693 := by
  unfold tailWord_6283831
  simp only [CollatzResearch.WordTrace]
  refine ⟨229190145297760954738659347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152793430198507303159106231 229190145297760954738659347)
  ·
    refine ⟨343785217946641432107989021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229190145297760954738659347 343785217946641432107989021)
    ·
      refine ⟨128919456729990537040495883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343785217946641432107989021 128919456729990537040495883)
      ·
        refine ⟨193379185094985805560743825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128919456729990537040495883 193379185094985805560743825)
        ·
          refine ⟨145034388821239354170557869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193379185094985805560743825 145034388821239354170557869)
          ·
            refine ⟨54387895807964757813959201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145034388821239354170557869 54387895807964757813959201)
            ·
              refine ⟨40790921855973568360469401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54387895807964757813959201 40790921855973568360469401)
              ·
                refine ⟨30593191391980176270352051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40790921855973568360469401 30593191391980176270352051)
                ·
                  refine ⟨45889787087970264405528077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30593191391980176270352051 45889787087970264405528077)
                  ·
                    refine ⟨17208670157988849152073029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45889787087970264405528077 17208670157988849152073029)
                    ·
                      refine ⟨3226625654622909216013693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17208670157988849152073029 3226625654622909216013693)
                      ·
                        rfl

theorem cell23_6283831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_6283831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283831 prefixEnd_6283831 := by exact prefixLift 6283831
  have htrace : WordTrace (prefixWord ++ tailWord_6283831) baseStart_6283831 baseEnd_6283831 := by
    simpa [prefixWord, tailWord_6283831, baseEnd_6283831] using wordTrace_append hprefix tailTrace_6283831
  have hstable : (prefixWord ++ tailWord_6283831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283831).length < 2 ^ (prefixWord ++ tailWord_6283831).sum := by decide
  have hdescent : baseEnd_6283831 < baseStart_6283831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283858 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 5, 4]
def baseStart_6283858 : Nat := 118140960795 + 6283858 * 2 ^ 59
def prefixEnd_6283858 : Nat := 4983230072969 + 3 ^ 40 * 6283858 * 2
def baseEnd_6283858 : Nat := 1075546506200193536792023

theorem tailTrace_6283858 : CollatzResearch.WordTrace tailWord_6283858 prefixEnd_6283858 1075546506200193536792023 := by
  unfold tailWord_6283858
  simp only [CollatzResearch.WordTrace]
  refine ⟨57297782517165784587473057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152794086712442092233261485 57297782517165784587473057)
  ·
    refine ⟨42973336887874338440604793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57297782517165784587473057 42973336887874338440604793)
    ·
      refine ⟨32230002665905753830453595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42973336887874338440604793 32230002665905753830453595)
      ·
        refine ⟨48345003998858630745680393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32230002665905753830453595 48345003998858630745680393)
        ·
          refine ⟨36258752999143973059260295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48345003998858630745680393 36258752999143973059260295)
          ·
            refine ⟨54388129498715959588890443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36258752999143973059260295 54388129498715959588890443)
            ·
              refine ⟨81582194248073939383335665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54388129498715959588890443 81582194248073939383335665)
              ·
                refine ⟨61186645686055454537501749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81582194248073939383335665 61186645686055454537501749)
                ·
                  refine ⟨5736248033067698862890789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61186645686055454537501749 5736248033067698862890789)
                  ·
                    refine ⟨1075546506200193536792023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5736248033067698862890789 1075546506200193536792023)
                    ·
                      rfl

theorem cell23_6283858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_6283858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283858 prefixEnd_6283858 := by exact prefixLift 6283858
  have htrace : WordTrace (prefixWord ++ tailWord_6283858) baseStart_6283858 baseEnd_6283858 := by
    simpa [prefixWord, tailWord_6283858, baseEnd_6283858] using wordTrace_append hprefix tailTrace_6283858
  have hstable : (prefixWord ++ tailWord_6283858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283858).length < 2 ^ (prefixWord ++ tailWord_6283858).sum := by decide
  have hdescent : baseEnd_6283858 < baseStart_6283858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283861 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_6283861 : Nat := 118140960795 + 6283861 * 2 ^ 59
def prefixEnd_6283861 : Nat := 4983230072969 + 3 ^ 40 * 6283861 * 2
def baseEnd_6283861 : Nat := 3226641059042544098638555

theorem tailTrace_6283861 : CollatzResearch.WordTrace tailWord_6283861 prefixEnd_6283861 3226641059042544098638555 := by
  unfold tailWord_6283861
  simp only [CollatzResearch.WordTrace]
  refine ⟨229191239487652269862251437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152794159658434846574834291 229191239487652269862251437)
  ·
    refine ⟨85946714807869601198344289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229191239487652269862251437 85946714807869601198344289)
    ·
      refine ⟨64460036105902200898758217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85946714807869601198344289 64460036105902200898758217)
      ·
        refine ⟨48345027079426650674068663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64460036105902200898758217 48345027079426650674068663)
        ·
          refine ⟨72517540619139976011102995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48345027079426650674068663 72517540619139976011102995)
          ·
            refine ⟨108776310928709964016654493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72517540619139976011102995 108776310928709964016654493)
            ·
              refine ⟨40791116598266236506245435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108776310928709964016654493 40791116598266236506245435)
              ·
                refine ⟨61186674897399354759368153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40791116598266236506245435 61186674897399354759368153)
                ·
                  refine ⟨45890006173049516069526115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61186674897399354759368153 45890006173049516069526115)
                  ·
                    refine ⟨68835009259574274104289173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45890006173049516069526115 68835009259574274104289173)
                    ·
                      refine ⟨3226641059042544098638555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68835009259574274104289173 3226641059042544098638555)
                      ·
                        rfl

theorem cell23_6283861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_6283861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283861 prefixEnd_6283861 := by exact prefixLift 6283861
  have htrace : WordTrace (prefixWord ++ tailWord_6283861) baseStart_6283861 baseEnd_6283861 := by
    simpa [prefixWord, tailWord_6283861, baseEnd_6283861] using wordTrace_append hprefix tailTrace_6283861
  have hstable : (prefixWord ++ tailWord_6283861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283861).length < 2 ^ (prefixWord ++ tailWord_6283861).sum := by decide
  have hdescent : baseEnd_6283861 < baseStart_6283861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283875 : List Nat := [1, 1, 1, 5, 1, 2, 1, 6, 1, 4]
def baseStart_6283875 : Nat := 118140960795 + 6283875 * 2 ^ 59
def prefixEnd_6283875 : Nat := 4983230072969 + 3 ^ 40 * 6283875 * 2
def baseEnd_6283875 : Nat := 1075549415923902347954497

theorem tailTrace_6283875 : CollatzResearch.WordTrace tailWord_6283875 prefixEnd_6283875 1075549415923902347954497 := by
  unfold tailWord_6283875
  simp only [CollatzResearch.WordTrace]
  refine ⟨229191750109601550253261079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152794500073067700168840719 229191750109601550253261079)
  ·
    refine ⟨343787625164402325379891619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229191750109601550253261079 343787625164402325379891619)
    ·
      refine ⟨515681437746603488069837429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343787625164402325379891619 515681437746603488069837429)
      ·
        refine ⟨48345134788744077006547259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 515681437746603488069837429 48345134788744077006547259)
        ·
          refine ⟨72517702183116115509820889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48345134788744077006547259 72517702183116115509820889)
          ·
            refine ⟨54388276637337086632365667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72517702183116115509820889 54388276637337086632365667)
            ·
              refine ⟨81582414956005629948548501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54388276637337086632365667 81582414956005629948548501)
              ·
                refine ⟨3824175701062763903838211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81582414956005629948548501 3824175701062763903838211)
                ·
                  refine ⟨5736263551594145855757317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3824175701062763903838211 5736263551594145855757317)
                  ·
                    refine ⟨1075549415923902347954497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5736263551594145855757317 1075549415923902347954497)
                    ·
                      rfl

theorem cell23_6283875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 1, 4].length) (baseStart_6283875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283875 prefixEnd_6283875 := by exact prefixLift 6283875
  have htrace : WordTrace (prefixWord ++ tailWord_6283875) baseStart_6283875 baseEnd_6283875 := by
    simpa [prefixWord, tailWord_6283875, baseEnd_6283875] using wordTrace_append hprefix tailTrace_6283875
  have hstable : (prefixWord ++ tailWord_6283875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283875).length < 2 ^ (prefixWord ++ tailWord_6283875).sum := by decide
  have hdescent : baseEnd_6283875 < baseStart_6283875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283921 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 4]
def baseStart_6283921 : Nat := 118140960795 + 6283921 * 2 ^ 59
def prefixEnd_6283921 : Nat := 4983230072969 + 3 ^ 40 * 6283921 * 2
def baseEnd_6283921 : Nat := 3226671867881813863888279

theorem tailTrace_6283921 : CollatzResearch.WordTrace tailWord_6283921 prefixEnd_6283921 3226671867881813863888279 := by
  unfold tailWord_6283921
  simp only [CollatzResearch.WordTrace]
  refine ⟨229193427867434900109435617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152795618578289933406290411 229193427867434900109435617)
  ·
    refine ⟨171895070900576175082076713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229193427867434900109435617 171895070900576175082076713)
    ·
      refine ⟨128921303175432131311557535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171895070900576175082076713 128921303175432131311557535)
      ·
        refine ⟨193381954763148196967336303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128921303175432131311557535 193381954763148196967336303)
        ·
          refine ⟨290072932144722295451004455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193381954763148196967336303 290072932144722295451004455)
          ·
            refine ⟨435109398217083443176506683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290072932144722295451004455 435109398217083443176506683)
            ·
              refine ⟨652664097325625164764760025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435109398217083443176506683 652664097325625164764760025)
              ·
                refine ⟨489498072994218873573570019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 652664097325625164764760025 489498072994218873573570019)
                ·
                  refine ⟨734247109491328310360355029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489498072994218873573570019 734247109491328310360355029)
                  ·
                    refine ⟨17208916628703007274070821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 734247109491328310360355029 17208916628703007274070821)
                    ·
                      refine ⟨3226671867881813863888279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17208916628703007274070821 3226671867881813863888279)
                      ·
                        rfl

theorem cell23_6283921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_6283921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283921 prefixEnd_6283921 := by exact prefixLift 6283921
  have htrace : WordTrace (prefixWord ++ tailWord_6283921) baseStart_6283921 baseEnd_6283921 := by
    simpa [prefixWord, tailWord_6283921, baseEnd_6283921] using wordTrace_append hprefix tailTrace_6283921
  have hstable : (prefixWord ++ tailWord_6283921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283921).length < 2 ^ (prefixWord ++ tailWord_6283921).sum := by decide
  have hdescent : baseEnd_6283921 < baseStart_6283921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283932 : List Nat := [2, 2, 3, 2, 2, 1, 3, 1, 3, 1, 3]
def baseStart_6283932 : Nat := 118140960795 + 6283932 * 2 ^ 59
def prefixEnd_6283932 : Nat := 4983230072969 + 3 ^ 40 * 6283932 * 2
def baseEnd_6283932 : Nat := 3226677516169013320850729

theorem tailTrace_6283932 : CollatzResearch.WordTrace tailWord_6283932 prefixEnd_6283932 3226677516169013320850729 := by
  unfold tailWord_6283932
  simp only [CollatzResearch.WordTrace]
  refine ⟨114596914535197524494043025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152795886046930032658724033 114596914535197524494043025)
  ·
    refine ⟨85947685901398143370532269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114596914535197524494043025 85947685901398143370532269)
    ·
      refine ⟨32230382213024303763949601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85947685901398143370532269 32230382213024303763949601)
      ·
        refine ⟨24172786659768227822962201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32230382213024303763949601 24172786659768227822962201)
        ·
          refine ⟨18129589994826170867221651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24172786659768227822962201 18129589994826170867221651)
          ·
            refine ⟨27194384992239256300832477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18129589994826170867221651 27194384992239256300832477)
            ·
              refine ⟨10197894372089721112812179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27194384992239256300832477 10197894372089721112812179)
              ·
                refine ⟨15296841558134581669218269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10197894372089721112812179 15296841558134581669218269)
                ·
                  refine ⟨5736315584300468125956851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15296841558134581669218269 5736315584300468125956851)
                  ·
                    refine ⟨8604473376450702188935277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5736315584300468125956851 8604473376450702188935277)
                    ·
                      refine ⟨3226677516169013320850729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8604473376450702188935277 3226677516169013320850729)
                      ·
                        rfl

theorem cell23_6283932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_6283932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283932 prefixEnd_6283932 := by exact prefixLift 6283932
  have htrace : WordTrace (prefixWord ++ tailWord_6283932) baseStart_6283932 baseEnd_6283932 := by
    simpa [prefixWord, tailWord_6283932, baseEnd_6283932] using wordTrace_append hprefix tailTrace_6283932
  have hstable : (prefixWord ++ tailWord_6283932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283932).length < 2 ^ (prefixWord ++ tailWord_6283932).sum := by decide
  have hdescent : baseEnd_6283932 < baseStart_6283932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283955 : List Nat := [1, 1, 1, 2, 3, 4, 3, 2, 1, 1, 4]
def baseStart_6283955 : Nat := 118140960795 + 6283955 * 2 ^ 59
def prefixEnd_6283955 : Nat := 4983230072969 + 3 ^ 40 * 6283955 * 2
def baseEnd_6283955 : Nat := 3226689326224066730863123

theorem tailTrace_6283955 : CollatzResearch.WordTrace tailWord_6283955 prefixEnd_6283955 3226689326224066730863123 := by
  unfold tailWord_6283955
  simp only [CollatzResearch.WordTrace]
  refine ⟨229194667949311723916173319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152796445299541149277448879 229194667949311723916173319)
  ·
    refine ⟨343792001923967585874259979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229194667949311723916173319 343792001923967585874259979)
    ·
      refine ⟨515688002885951378811389969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343792001923967585874259979 515688002885951378811389969)
      ·
        refine ⟨386766002164463534108542477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 515688002885951378811389969 386766002164463534108542477)
        ·
          refine ⟨145037250811673825290703429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 386766002164463534108542477 145037250811673825290703429)
          ·
            refine ⟨27194484527188842242006893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145037250811673825290703429 27194484527188842242006893)
            ·
              refine ⟨10197931697695815840752585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27194484527188842242006893 10197931697695815840752585)
              ·
                refine ⟨7648448773271861880564439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10197931697695815840752585 7648448773271861880564439)
                ·
                  refine ⟨11472673159907792820846659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7648448773271861880564439 11472673159907792820846659)
                  ·
                    refine ⟨17209009739861689231269989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11472673159907792820846659 17209009739861689231269989)
                    ·
                      refine ⟨3226689326224066730863123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17209009739861689231269989 3226689326224066730863123)
                      ·
                        rfl

theorem cell23_6283955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 1, 4].length) (baseStart_6283955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283955 prefixEnd_6283955 := by exact prefixLift 6283955
  have htrace : WordTrace (prefixWord ++ tailWord_6283955) baseStart_6283955 baseEnd_6283955 := by
    simpa [prefixWord, tailWord_6283955, baseEnd_6283955] using wordTrace_append hprefix tailTrace_6283955
  have hstable : (prefixWord ++ tailWord_6283955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283955).length < 2 ^ (prefixWord ++ tailWord_6283955).sum := by decide
  have hdescent : baseEnd_6283955 < baseStart_6283955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283968 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 4]
def baseStart_6283968 : Nat := 118140960795 + 6283968 * 2 ^ 59
def prefixEnd_6283968 : Nat := 4983230072969 + 3 ^ 40 * 6283968 * 2
def baseEnd_6283968 : Nat := 3226696001472575180000563

theorem tailTrace_6283968 : CollatzResearch.WordTrace tailWord_6283968 prefixEnd_6283968 3226696001472575180000563 := by
  unfold tailWord_6283968
  simp only [CollatzResearch.WordTrace]
  refine ⟨114597571049132313568198279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152796761398843084757597705 114597571049132313568198279)
  ·
    refine ⟨171896356573698470352297419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114597571049132313568198279 171896356573698470352297419)
    ·
      refine ⟨257844534860547705528446129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171896356573698470352297419 257844534860547705528446129)
      ·
        refine ⟨193383401145410779146334597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257844534860547705528446129 193383401145410779146334597)
        ·
          refine ⟨36259387714764521089937737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193383401145410779146334597 36259387714764521089937737)
          ·
            refine ⟨27194540786073390817453303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36259387714764521089937737 27194540786073390817453303)
            ·
              refine ⟨40791811179110086226179955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27194540786073390817453303 40791811179110086226179955)
              ·
                refine ⟨61187716768665129339269933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40791811179110086226179955 61187716768665129339269933)
                ·
                  refine ⟨22945393788249423502226225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61187716768665129339269933 22945393788249423502226225)
                  ·
                    refine ⟨17209045341187067626669669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22945393788249423502226225 17209045341187067626669669)
                    ·
                      refine ⟨3226696001472575180000563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17209045341187067626669669 3226696001472575180000563)
                      ·
                        rfl

theorem cell23_6283968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_6283968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283968 prefixEnd_6283968 := by exact prefixLift 6283968
  have htrace : WordTrace (prefixWord ++ tailWord_6283968) baseStart_6283968 baseEnd_6283968 := by
    simpa [prefixWord, tailWord_6283968, baseEnd_6283968] using wordTrace_append hprefix tailTrace_6283968
  have hstable : (prefixWord ++ tailWord_6283968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283968).length < 2 ^ (prefixWord ++ tailWord_6283968).sum := by decide
  have hdescent : baseEnd_6283968 < baseStart_6283968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6283982 : List Nat := [4, 1, 1, 1, 3, 3, 2, 2, 2, 4]
def baseStart_6283982 : Nat := 118140960795 + 6283982 * 2 ^ 59
def prefixEnd_6283982 : Nat := 4983230072969 + 3 ^ 40 * 6283982 * 2
def baseEnd_6283982 : Nat := 1075567730067246041741833

theorem tailTrace_6283982 : CollatzResearch.WordTrace tailWord_6283982 prefixEnd_6283982 1075567730067246041741833 := by
  unfold tailWord_6283982
  simp only [CollatzResearch.WordTrace]
  refine ⟨28649456590026738440925775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152797101813475938351604133 28649456590026738440925775)
  ·
    refine ⟨42974184885040107661388663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28649456590026738440925775 42974184885040107661388663)
    ·
      refine ⟨64461277327560161492082995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42974184885040107661388663 64461277327560161492082995)
      ·
        refine ⟨96691915991340242238124493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64461277327560161492082995 96691915991340242238124493)
        ·
          refine ⟨36259468496752590839296685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96691915991340242238124493 36259468496752590839296685)
          ·
            refine ⟨13597300686282221564736257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36259468496752590839296685 13597300686282221564736257)
            ·
              refine ⟨10197975514711666173552193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13597300686282221564736257 10197975514711666173552193)
              ·
                refine ⟨7648481636033749630164145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10197975514711666173552193 7648481636033749630164145)
                ·
                  refine ⟨5736361227025312222623109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7648481636033749630164145 5736361227025312222623109)
                  ·
                    refine ⟨1075567730067246041741833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5736361227025312222623109 1075567730067246041741833)
                    ·
                      rfl

theorem cell23_6283982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_6283982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6283982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6283982 prefixEnd_6283982 := by exact prefixLift 6283982
  have htrace : WordTrace (prefixWord ++ tailWord_6283982) baseStart_6283982 baseEnd_6283982 := by
    simpa [prefixWord, tailWord_6283982, baseEnd_6283982] using wordTrace_append hprefix tailTrace_6283982
  have hstable : (prefixWord ++ tailWord_6283982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6283982).length < 2 ^ (prefixWord ++ tailWord_6283982).sum := by decide
  have hdescent : baseEnd_6283982 < baseStart_6283982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6283982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284005 : List Nat := [1, 3, 1, 4, 1, 2, 1, 3, 1, 3, 3]
def baseStart_6284005 : Nat := 118140960795 + 6284005 * 2 ^ 59
def prefixEnd_6284005 : Nat := 4983230072969 + 3 ^ 40 * 6284005 * 2
def baseEnd_6284005 : Nat := 3226715000256791535237893

theorem tailTrace_6284005 : CollatzResearch.WordTrace tailWord_6284005 prefixEnd_6284005 3226715000256791535237893 := by
  unfold tailWord_6284005
  simp only [CollatzResearch.WordTrace]
  refine ⟨229196491599130582455493469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152797661066087054970328979 229196491599130582455493469)
  ·
    refine ⟨85948684349673968420810051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229196491599130582455493469 85948684349673968420810051)
    ·
      refine ⟨128923026524510952631215077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85948684349673968420810051 128923026524510952631215077)
      ·
        refine ⟨24173067473345803618352827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128923026524510952631215077 24173067473345803618352827)
        ·
          refine ⟨36259601210018705427529241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24173067473345803618352827 36259601210018705427529241)
          ·
            refine ⟨27194700907514029070646931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36259601210018705427529241 27194700907514029070646931)
            ·
              refine ⟨40792051361271043605970397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27194700907514029070646931 40792051361271043605970397)
              ·
                refine ⟨15297019260476641352238899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40792051361271043605970397 15297019260476641352238899)
                ·
                  refine ⟨22945528890714962028358349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15297019260476641352238899 22945528890714962028358349)
                  ·
                    refine ⟨8604573334018110760634381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22945528890714962028358349 8604573334018110760634381)
                    ·
                      refine ⟨3226715000256791535237893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8604573334018110760634381 3226715000256791535237893)
                      ·
                        rfl

theorem cell23_6284005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_6284005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284005 prefixEnd_6284005 := by exact prefixLift 6284005
  have htrace : WordTrace (prefixWord ++ tailWord_6284005) baseStart_6284005 baseEnd_6284005 := by
    simpa [prefixWord, tailWord_6284005, baseEnd_6284005] using wordTrace_append hprefix tailTrace_6284005
  have hstable : (prefixWord ++ tailWord_6284005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284005).length < 2 ^ (prefixWord ++ tailWord_6284005).sum := by decide
  have hdescent : baseEnd_6284005 < baseStart_6284005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284022 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3]
def baseStart_6284022 : Nat := 118140960795 + 6284022 * 2 ^ 59
def prefixEnd_6284022 : Nat := 4983230072969 + 3 ^ 40 * 6284022 * 2
def baseEnd_6284022 : Nat := 3226723729427917968725315

theorem tailTrace_6284022 : CollatzResearch.WordTrace tailWord_6284022 prefixEnd_6284022 3226723729427917968725315 := by
  unfold tailWord_6284022
  simp only [CollatzResearch.WordTrace]
  refine ⟨14324819477504312147428895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152798074426712662905908213 14324819477504312147428895)
  ·
    refine ⟨21487229216256468221143343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14324819477504312147428895 21487229216256468221143343)
    ·
      refine ⟨32230843824384702331715015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21487229216256468221143343 32230843824384702331715015)
      ·
        refine ⟨48346265736577053497572523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32230843824384702331715015 48346265736577053497572523)
        ·
          refine ⟨72519398604865580246358785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48346265736577053497572523 72519398604865580246358785)
          ·
            refine ⟨54389548953649185184769089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72519398604865580246358785 54389548953649185184769089)
            ·
              refine ⟨40792161715236888888576817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54389548953649185184769089 40792161715236888888576817)
              ·
                refine ⟨30594121286427666666432613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40792161715236888888576817 30594121286427666666432613)
                ·
                  refine ⟨5736397741205187499956115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30594121286427666666432613 5736397741205187499956115)
                  ·
                    refine ⟨8604596611807781249934173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5736397741205187499956115 8604596611807781249934173)
                    ·
                      refine ⟨3226723729427917968725315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8604596611807781249934173 3226723729427917968725315)
                      ·
                        rfl

theorem cell23_6284022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_6284022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284022 prefixEnd_6284022 := by exact prefixLift 6284022
  have htrace : WordTrace (prefixWord ++ tailWord_6284022) baseStart_6284022 baseEnd_6284022 := by
    simpa [prefixWord, tailWord_6284022, baseEnd_6284022] using wordTrace_append hprefix tailTrace_6284022
  have hstable : (prefixWord ++ tailWord_6284022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284022).length < 2 ^ (prefixWord ++ tailWord_6284022).sum := by decide
  have hdescent : baseEnd_6284022 < baseStart_6284022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284039 : List Nat := [1, 1, 4, 4, 1, 1, 3, 2, 2, 1, 3]
def baseStart_6284039 : Nat := 118140960795 + 6284039 * 2 ^ 59
def prefixEnd_6284039 : Nat := 4983230072969 + 3 ^ 40 * 6284039 * 2
def baseEnd_6284039 : Nat := 3226732458599044402212737

theorem tailTrace_6284039 : CollatzResearch.WordTrace tailWord_6284039 prefixEnd_6284039 3226732458599044402212737 := by
  unfold tailWord_6284039
  simp only [CollatzResearch.WordTrace]
  refine ⟨229197731681007406262231171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152798487787338270841487447 229197731681007406262231171)
  ·
    refine ⟨343796597521511109393346757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229197731681007406262231171 343796597521511109393346757)
    ·
      refine ⟨64461862035283333011252517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 343796597521511109393346757 64461862035283333011252517)
      ·
        refine ⟨12086599131615624939609847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64461862035283333011252517 12086599131615624939609847)
        ·
          refine ⟨18129898697423437409414771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12086599131615624939609847 18129898697423437409414771)
          ·
            refine ⟨27194848046135156114122157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18129898697423437409414771 27194848046135156114122157)
            ·
              refine ⟨10198068017300683542795809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27194848046135156114122157 10198068017300683542795809)
              ·
                refine ⟨7648551012975512657096857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10198068017300683542795809 7648551012975512657096857)
                ·
                  refine ⟨5736413259731634492822643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7648551012975512657096857 5736413259731634492822643)
                  ·
                    refine ⟨8604619889597451739233965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5736413259731634492822643 8604619889597451739233965)
                    ·
                      refine ⟨3226732458599044402212737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8604619889597451739233965 3226732458599044402212737)
                      ·
                        rfl

theorem cell23_6284039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_6284039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284039 prefixEnd_6284039 := by exact prefixLift 6284039
  have htrace : WordTrace (prefixWord ++ tailWord_6284039) baseStart_6284039 baseEnd_6284039 := by
    simpa [prefixWord, tailWord_6284039, baseEnd_6284039] using wordTrace_append hprefix tailTrace_6284039
  have hstable : (prefixWord ++ tailWord_6284039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284039).length < 2 ^ (prefixWord ++ tailWord_6284039).sum := by decide
  have hdescent : baseEnd_6284039 < baseStart_6284039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284113 : List Nat := [1, 2, 2, 1, 6, 2, 2, 1, 2, 2, 2]
def baseStart_6284113 : Nat := 118140960795 + 6284113 * 2 ^ 59
def prefixEnd_6284113 : Nat := 4983230072969 + 3 ^ 40 * 6284113 * 2
def baseEnd_6284113 : Nat := 3226770456167477112687397

theorem tailTrace_6284113 : CollatzResearch.WordTrace tailWord_6284113 prefixEnd_6284113 3226770456167477112687397 := by
  unfold tailWord_6284113
  simp only [CollatzResearch.WordTrace]
  refine ⟨229200430682739316900424993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152800287121826211266949995 229200430682739316900424993)
  ·
    refine ⟨171900323012054487675318745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229200430682739316900424993 171900323012054487675318745)
    ·
      refine ⟨128925242259040865756489059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171900323012054487675318745 128925242259040865756489059)
      ·
        refine ⟨193387863388561298634733589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128925242259040865756489059 193387863388561298634733589)
        ·
          refine ⟨9065056096338810873503137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 193387863388561298634733589 9065056096338810873503137)
          ·
            refine ⟨6798792072254108155127353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9065056096338810873503137 6798792072254108155127353)
            ·
              refine ⟨5099094054190581116345515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6798792072254108155127353 5099094054190581116345515)
              ·
                refine ⟨7648641081285871674518273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5099094054190581116345515 7648641081285871674518273)
                ·
                  refine ⟨5736480810964403755888705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7648641081285871674518273 5736480810964403755888705)
                  ·
                    refine ⟨4302360608223302816916529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5736480810964403755888705 4302360608223302816916529)
                    ·
                      refine ⟨3226770456167477112687397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4302360608223302816916529 3226770456167477112687397)
                      ·
                        rfl

theorem cell23_6284113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 2, 2, 2].length) (baseStart_6284113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284113 prefixEnd_6284113 := by exact prefixLift 6284113
  have htrace : WordTrace (prefixWord ++ tailWord_6284113) baseStart_6284113 baseEnd_6284113 := by
    simpa [prefixWord, tailWord_6284113, baseEnd_6284113] using wordTrace_append hprefix tailTrace_6284113
  have hstable : (prefixWord ++ tailWord_6284113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284113).length < 2 ^ (prefixWord ++ tailWord_6284113).sum := by decide
  have hdescent : baseEnd_6284113 < baseStart_6284113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284132 : List Nat := [2, 3, 1, 1, 4, 2, 2, 1, 2, 5]
def baseStart_6284132 : Nat := 118140960795 + 6284132 * 2 ^ 59
def prefixEnd_6284132 : Nat := 4983230072969 + 3 ^ 40 * 6284132 * 2
def baseEnd_6284132 : Nat := 1075593404099970846116603

theorem tailTrace_6284132 : CollatzResearch.WordTrace tailWord_6284132 prefixEnd_6284132 1075593404099970846116603 := by
  unfold tailWord_6284132
  simp only [CollatzResearch.WordTrace]
  refine ⟨114600561834835241572683325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152800749113113655430244433 114600561834835241572683325)
  ·
    refine ⟨42975210688063215589756247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114600561834835241572683325 42975210688063215589756247)
    ·
      refine ⟨64462816032094823384634371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42975210688063215589756247 64462816032094823384634371)
      ·
        refine ⟨96694224048142235076951557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64462816032094823384634371 96694224048142235076951557)
        ·
          refine ⟨18130167009026669076928417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96694224048142235076951557 18130167009026669076928417)
          ·
            refine ⟨13597625256770001807696313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18130167009026669076928417 13597625256770001807696313)
            ·
              refine ⟨10198218942577501355772235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13597625256770001807696313 10198218942577501355772235)
              ·
                refine ⟨15297328413866252033658353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10198218942577501355772235 15297328413866252033658353)
                ·
                  refine ⟨11472996310399689025243765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15297328413866252033658353 11472996310399689025243765)
                  ·
                    refine ⟨1075593404099970846116603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11472996310399689025243765 1075593404099970846116603)
                    ·
                      rfl

theorem cell23_6284132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_6284132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284132 prefixEnd_6284132 := by exact prefixLift 6284132
  have htrace : WordTrace (prefixWord ++ tailWord_6284132) baseStart_6284132 baseEnd_6284132 := by
    simpa [prefixWord, tailWord_6284132, baseEnd_6284132] using wordTrace_append hprefix tailTrace_6284132
  have hstable : (prefixWord ++ tailWord_6284132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284132).length < 2 ^ (prefixWord ++ tailWord_6284132).sum := by decide
  have hdescent : baseEnd_6284132 < baseStart_6284132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284186 : List Nat := [3, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4]
def baseStart_6284186 : Nat := 118140960795 + 6284186 * 2 ^ 59
def prefixEnd_6284186 : Nat := 4983230072969 + 3 ^ 40 * 6284186 * 2
def baseEnd_6284186 : Nat := 3226807940255255327074561

theorem tailTrace_6284186 : CollatzResearch.WordTrace tailWord_6284186 prefixEnd_6284186 3226807940255255327074561 := by
  unfold tailWord_6284186
  simp only [CollatzResearch.WordTrace]
  refine ⟨57300773302868712591958103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152802062140983233578554941 57300773302868712591958103)
  ·
    refine ⟨85951159954303068887937155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57300773302868712591958103 85951159954303068887937155)
    ·
      refine ⟨128926739931454603331905733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85951159954303068887937155 128926739931454603331905733)
      ·
        refine ⟨24173763737147738124732325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128926739931454603331905733 24173763737147738124732325)
        ·
          refine ⟨4532580700715200898387311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24173763737147738124732325 4532580700715200898387311)
          ·
            refine ⟨6798871051072801347580967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4532580700715200898387311 6798871051072801347580967)
            ·
              refine ⟨10198306576609202021371451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6798871051072801347580967 10198306576609202021371451)
              ·
                refine ⟨15297459864913803032057177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10198306576609202021371451 15297459864913803032057177)
                ·
                  refine ⟨11473094898685352274042883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15297459864913803032057177 11473094898685352274042883)
                  ·
                    refine ⟨17209642348028028411064325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11473094898685352274042883 17209642348028028411064325)
                    ·
                      refine ⟨3226807940255255327074561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17209642348028028411064325 3226807940255255327074561)
                      ·
                        rfl

theorem cell23_6284186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_6284186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284186 prefixEnd_6284186 := by exact prefixLift 6284186
  have htrace : WordTrace (prefixWord ++ tailWord_6284186) baseStart_6284186 baseEnd_6284186 := by
    simpa [prefixWord, tailWord_6284186, baseEnd_6284186] using wordTrace_append hprefix tailTrace_6284186
  have hstable : (prefixWord ++ tailWord_6284186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284186).length < 2 ^ (prefixWord ++ tailWord_6284186).sum := by decide
  have hdescent : baseEnd_6284186 < baseStart_6284186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284209 : List Nat := [1, 2, 2, 4, 3, 2, 1, 2, 6]
def baseStart_6284209 : Nat := 118140960795 + 6284209 * 2 ^ 59
def prefixEnd_6284209 : Nat := 4983230072969 + 3 ^ 40 * 6284209 * 2
def baseEnd_6284209 : Nat := 358535527812256526342995

theorem tailTrace_6284209 : CollatzResearch.WordTrace tailWord_6284209 prefixEnd_6284209 358535527812256526342995 := by
  unfold tailWord_6284209
  simp only [CollatzResearch.WordTrace]
  refine ⟨229203932090391525295919681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152802621393594350197279787 229203932090391525295919681)
  ·
    refine ⟨171902949067793643971939761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229203932090391525295919681 171902949067793643971939761)
    ·
      refine ⟨128927211800845232978954821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171902949067793643971939761 128927211800845232978954821)
      ·
        refine ⟨24173852212658481183554029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128927211800845232978954821 24173852212658481183554029)
        ·
          refine ⟨9065194579746930443832761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24173852212658481183554029 9065194579746930443832761)
          ·
            refine ⟨6798895934810197832874571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9065194579746930443832761 6798895934810197832874571)
            ·
              refine ⟨10198343902215296749311857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6798895934810197832874571 10198343902215296749311857)
              ·
                refine ⟨7648757926661472561983893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10198343902215296749311857 7648757926661472561983893)
                ·
                  refine ⟨358535527812256526342995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7648757926661472561983893 358535527812256526342995)
                  ·
                    rfl

theorem cell23_6284209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 6].length) (baseStart_6284209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284209 prefixEnd_6284209 := by exact prefixLift 6284209
  have htrace : WordTrace (prefixWord ++ tailWord_6284209) baseStart_6284209 baseEnd_6284209 := by
    simpa [prefixWord, tailWord_6284209, baseEnd_6284209] using wordTrace_append hprefix tailTrace_6284209
  have hstable : (prefixWord ++ tailWord_6284209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284209).length < 2 ^ (prefixWord ++ tailWord_6284209).sum := by decide
  have hdescent : baseEnd_6284209 < baseStart_6284209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284246 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_6284246 : Nat := 118140960795 + 6284246 * 2 ^ 59
def prefixEnd_6284246 : Nat := 4983230072969 + 3 ^ 40 * 6284246 * 2
def baseEnd_6284246 : Nat := 3226838749094525092324285

theorem tailTrace_6284246 : CollatzResearch.WordTrace tailWord_6284246 prefixEnd_6284246 3226838749094525092324285 := by
  unfold tailWord_6284246
  simp only [CollatzResearch.WordTrace]
  refine ⟨14325330099453592538438537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152803521060838320410011061 14325330099453592538438537)
  ·
    refine ⟨10743997574590194403828903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14325330099453592538438537 10743997574590194403828903)
    ·
      refine ⟨16115996361885291605743355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10743997574590194403828903 16115996361885291605743355)
      ·
        refine ⟨24173994542827937408615033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16115996361885291605743355 24173994542827937408615033)
        ·
          refine ⟨18130495907120953056461275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24173994542827937408615033 18130495907120953056461275)
          ·
            refine ⟨27195743860681429584691913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18130495907120953056461275 27195743860681429584691913)
            ·
              refine ⟨20396807895511072188518935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27195743860681429584691913 20396807895511072188518935)
              ·
                refine ⟨30595211843266608282778403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20396807895511072188518935 30595211843266608282778403)
                ·
                  refine ⟨45892817764899912424167605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30595211843266608282778403 45892817764899912424167605)
                  ·
                    refine ⟨4302451665459366789765713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45892817764899912424167605 4302451665459366789765713)
                    ·
                      refine ⟨3226838749094525092324285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4302451665459366789765713 3226838749094525092324285)
                      ·
                        rfl

theorem cell23_6284246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_6284246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284246 prefixEnd_6284246 := by exact prefixLift 6284246
  have htrace : WordTrace (prefixWord ++ tailWord_6284246) baseStart_6284246 baseEnd_6284246 := by
    simpa [prefixWord, tailWord_6284246, baseEnd_6284246] using wordTrace_append hprefix tailTrace_6284246
  have hstable : (prefixWord ++ tailWord_6284246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284246).length < 2 ^ (prefixWord ++ tailWord_6284246).sum := by decide
  have hdescent : baseEnd_6284246 < baseStart_6284246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284253 : List Nat := [1, 4, 3, 1, 2, 1, 3, 3, 1, 1, 3]
def baseStart_6284253 : Nat := 118140960795 + 6284253 * 2 ^ 59
def prefixEnd_6284253 : Nat := 4983230072969 + 3 ^ 40 * 6284253 * 2
def baseEnd_6284253 : Nat := 3226842343459106564936753

theorem tailTrace_6284253 : CollatzResearch.WordTrace tailWord_6284253 prefixEnd_6284253 3226842343459106564936753 := by
  unfold tailWord_6284253
  simp only [CollatzResearch.WordTrace]
  refine ⟨229205536902232120810521413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152803691268154747207014275 229205536902232120810521413)
  ·
    refine ⟨42976038169168522651972765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229205536902232120810521413 42976038169168522651972765)
    ·
      refine ⟨16116014313438195994489787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42976038169168522651972765 16116014313438195994489787)
      ·
        refine ⟨24174021470157293991734681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16116014313438195994489787 24174021470157293991734681)
        ·
          refine ⟨18130516102617970493801011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24174021470157293991734681 18130516102617970493801011)
          ·
            refine ⟨27195774153926955740701517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18130516102617970493801011 27195774153926955740701517)
            ·
              refine ⟨10198415307722608402763069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27195774153926955740701517 10198415307722608402763069)
              ·
                refine ⟨3824405740395978151036151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10198415307722608402763069 3824405740395978151036151)
                ·
                  refine ⟨5736608610593967226554227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3824405740395978151036151 5736608610593967226554227)
                  ·
                    refine ⟨8604912915890950839831341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5736608610593967226554227 8604912915890950839831341)
                    ·
                      refine ⟨3226842343459106564936753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8604912915890950839831341 3226842343459106564936753)
                      ·
                        rfl

theorem cell23_6284253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_6284253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284253 prefixEnd_6284253 := by exact prefixLift 6284253
  have htrace : WordTrace (prefixWord ++ tailWord_6284253) baseStart_6284253 baseEnd_6284253 := by
    simpa [prefixWord, tailWord_6284253, baseEnd_6284253] using wordTrace_append hprefix tailTrace_6284253
  have hstable : (prefixWord ++ tailWord_6284253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284253).length < 2 ^ (prefixWord ++ tailWord_6284253).sum := by decide
  have hdescent : baseEnd_6284253 < baseStart_6284253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284270 : List Nat := [4, 1, 2, 1, 4, 1, 3, 2, 1, 1, 3]
def baseStart_6284270 : Nat := 118140960795 + 6284270 * 2 ^ 59
def prefixEnd_6284270 : Nat := 4983230072969 + 3 ^ 40 * 6284270 * 2
def baseEnd_6284270 : Nat := 3226851072630232998424175

theorem tailTrace_6284270 : CollatzResearch.WordTrace tailWord_6284270 prefixEnd_6284270 3226851072630232998424175 := by
  unfold tailWord_6284270
  simp only [CollatzResearch.WordTrace]
  refine ⟨28650769617896316589236283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152804104628780355142593509 28650769617896316589236283)
  ·
    refine ⟨42976154426844474883854425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28650769617896316589236283 42976154426844474883854425)
    ·
      refine ⟨32232115820133356162890819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42976154426844474883854425 32232115820133356162890819)
      ·
        refine ⟨48348173730200034244336229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32232115820133356162890819 48348173730200034244336229)
        ·
          refine ⟨9065282574412506420813043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48348173730200034244336229 9065282574412506420813043)
          ·
            refine ⟨13597923861618759631219565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9065282574412506420813043 13597923861618759631219565)
            ·
              refine ⟨5099221448107034861707337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13597923861618759631219565 5099221448107034861707337)
              ·
                refine ⟨3824416086080276146280503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5099221448107034861707337 3824416086080276146280503)
                ·
                  refine ⟨5736624129120414219420755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3824416086080276146280503 5736624129120414219420755)
                  ·
                    refine ⟨8604936193680621329131133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5736624129120414219420755 8604936193680621329131133)
                    ·
                      refine ⟨3226851072630232998424175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8604936193680621329131133 3226851072630232998424175)
                      ·
                        rfl

theorem cell23_6284270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_6284270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284270 prefixEnd_6284270 := by exact prefixLift 6284270
  have htrace : WordTrace (prefixWord ++ tailWord_6284270) baseStart_6284270 baseEnd_6284270 := by
    simpa [prefixWord, tailWord_6284270, baseEnd_6284270] using wordTrace_append hprefix tailTrace_6284270
  have hstable : (prefixWord ++ tailWord_6284270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284270).length < 2 ^ (prefixWord ++ tailWord_6284270).sum := by decide
  have hdescent : baseEnd_6284270 < baseStart_6284270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284285 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_6284285 : Nat := 118140960795 + 6284285 * 2 ^ 59
def prefixEnd_6284285 : Nat := 4983230072969 + 3 ^ 40 * 6284285 * 2
def baseEnd_6284285 : Nat := 3226858774840050439736605

theorem tailTrace_6284285 : CollatzResearch.WordTrace tailWord_6284285 prefixEnd_6284285 3226858774840050439736605 := by
  unfold tailWord_6284285
  simp only [CollatzResearch.WordTrace]
  refine ⟨229206704038116190275686309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152804469358744126850457539 229206704038116190275686309)
  ·
    refine ⟨42976257007146785676691183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229206704038116190275686309 42976257007146785676691183)
    ·
      refine ⟨64464385510720178515036775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42976257007146785676691183 64464385510720178515036775)
      ·
        refine ⟨96696578266080267772555163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64464385510720178515036775 96696578266080267772555163)
        ·
          refine ⟨145044867399120401658832745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96696578266080267772555163 145044867399120401658832745)
          ·
            refine ⟨108783650549340301244124559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145044867399120401658832745 108783650549340301244124559)
            ·
              refine ⟨163175475824010451866186839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108783650549340301244124559 163175475824010451866186839)
              ·
                refine ⟨244763213736015677799280259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163175475824010451866186839 244763213736015677799280259)
                ·
                  refine ⟨367144820604023516698920389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244763213736015677799280259 367144820604023516698920389)
                  ·
                    refine ⟨68839653863254409381047573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 367144820604023516698920389 68839653863254409381047573)
                    ·
                      refine ⟨3226858774840050439736605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68839653863254409381047573 3226858774840050439736605)
                      ·
                        rfl

theorem cell23_6284285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_6284285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284285 prefixEnd_6284285 := by exact prefixLift 6284285
  have htrace : WordTrace (prefixWord ++ tailWord_6284285) baseStart_6284285 baseEnd_6284285 := by
    simpa [prefixWord, tailWord_6284285, baseEnd_6284285] using wordTrace_append hprefix tailTrace_6284285
  have hstable : (prefixWord ++ tailWord_6284285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284285).length < 2 ^ (prefixWord ++ tailWord_6284285).sum := by decide
  have hdescent : baseEnd_6284285 < baseStart_6284285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284290 : List Nat := [3, 4, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_6284290 : Nat := 118140960795 + 6284290 * 2 ^ 59
def prefixEnd_6284290 : Nat := 4983230072969 + 3 ^ 40 * 6284290 * 2
def baseEnd_6284290 : Nat := 1075620447414440973391361

theorem tailTrace_6284290 : CollatzResearch.WordTrace tailWord_6284290 prefixEnd_6284290 1075620447414440973391361 := by
  unfold tailWord_6284290
  simp only [CollatzResearch.WordTrace]
  refine ⟨57301721600774519032404581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152804590935398717419745549 57301721600774519032404581)
  ·
    refine ⟨10744072800145222318575859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57301721600774519032404581 10744072800145222318575859)
    ·
      refine ⟨16116109200217833477863789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10744072800145222318575859 16116109200217833477863789)
      ·
        refine ⟨6043540950081687554198921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16116109200217833477863789 6043540950081687554198921)
        ·
          refine ⟨4532655712561265665649191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6043540950081687554198921 4532655712561265665649191)
          ·
            refine ⟨6798983568841898498473787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4532655712561265665649191 6798983568841898498473787)
            ·
              refine ⟨10198475353262847747710681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6798983568841898498473787 10198475353262847747710681)
              ·
                refine ⟨7648856514947135810783011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10198475353262847747710681 7648856514947135810783011)
                ·
                  refine ⟨11473284772420703716174517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7648856514947135810783011 11473284772420703716174517)
                  ·
                    refine ⟨1075620447414440973391361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11473284772420703716174517 1075620447414440973391361)
                    ·
                      rfl

theorem cell23_6284290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_6284290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284290 prefixEnd_6284290 := by exact prefixLift 6284290
  have htrace : WordTrace (prefixWord ++ tailWord_6284290) baseStart_6284290 baseEnd_6284290 := by
    simpa [prefixWord, tailWord_6284290, baseEnd_6284290] using wordTrace_append hprefix tailTrace_6284290
  have hstable : (prefixWord ++ tailWord_6284290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284290).length < 2 ^ (prefixWord ++ tailWord_6284290).sum := by decide
  have hdescent : baseEnd_6284290 < baseStart_6284290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284296 : List Nat := [2, 1, 3, 2, 1, 5, 1, 2, 1, 2, 3]
def baseStart_6284296 : Nat := 118140960795 + 6284296 * 2 ^ 59
def prefixEnd_6284296 : Nat := 4983230072969 + 3 ^ 40 * 6284296 * 2
def baseEnd_6284296 : Nat := 3226864423127249896699055

theorem tailTrace_6284296 : CollatzResearch.WordTrace tailWord_6284296 prefixEnd_6284296 3226864423127249896699055 := by
  unfold tailWord_6284296
  simp only [CollatzResearch.WordTrace]
  refine ⟨114603552620538169577168371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152804736827384226102891161 114603552620538169577168371)
  ·
    refine ⟨171905328930807254365752557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114603552620538169577168371 171905328930807254365752557)
    ·
      refine ⟨64464498349052720387157209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171905328930807254365752557 64464498349052720387157209)
      ·
        refine ⟨48348373761789540290367907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64464498349052720387157209 48348373761789540290367907)
        ·
          refine ⟨72522560642684310435551861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48348373761789540290367907 72522560642684310435551861)
          ·
            refine ⟨6798990060251654103332987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72522560642684310435551861 6798990060251654103332987)
            ·
              refine ⟨10198485090377481154999481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6798990060251654103332987 10198485090377481154999481)
              ·
                refine ⟨7648863817783110866249611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10198485090377481154999481 7648863817783110866249611)
                ·
                  refine ⟨11473295726674666299374417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7648863817783110866249611 11473295726674666299374417)
                  ·
                    refine ⟨8604971795005999724530813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11473295726674666299374417 8604971795005999724530813)
                    ·
                      refine ⟨3226864423127249896699055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8604971795005999724530813 3226864423127249896699055)
                      ·
                        rfl

theorem cell23_6284296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_6284296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284296 prefixEnd_6284296 := by exact prefixLift 6284296
  have htrace : WordTrace (prefixWord ++ tailWord_6284296) baseStart_6284296 baseEnd_6284296 := by
    simpa [prefixWord, tailWord_6284296, baseEnd_6284296] using wordTrace_append hprefix tailTrace_6284296
  have hstable : (prefixWord ++ tailWord_6284296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284296).length < 2 ^ (prefixWord ++ tailWord_6284296).sum := by decide
  have hdescent : baseEnd_6284296 < baseStart_6284296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284305 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 5]
def baseStart_6284305 : Nat := 118140960795 + 6284305 * 2 ^ 59
def prefixEnd_6284305 : Nat := 4983230072969 + 3 ^ 40 * 6284305 * 2
def baseEnd_6284305 : Nat := 3226869044453140361486513

theorem tailTrace_6284305 : CollatzResearch.WordTrace tailWord_6284305 prefixEnd_6284305 3226869044453140361486513 := by
  unfold tailWord_6284305
  simp only [CollatzResearch.WordTrace]
  refine ⟨229207433498043733691414369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152804955665362489127609579 229207433498043733691414369)
  ·
    refine ⟨171905575123532800268560777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229207433498043733691414369 171905575123532800268560777)
    ·
      refine ⟨128929181342649600201420583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171905575123532800268560777 128929181342649600201420583)
      ·
        refine ⟨193393772013974400302130875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128929181342649600201420583 193393772013974400302130875)
        ·
          refine ⟨290090658020961600453196313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193393772013974400302130875 290090658020961600453196313)
          ·
            refine ⟨217567993515721200339897235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290090658020961600453196313 217567993515721200339897235)
            ·
              refine ⟨326351990273581800509845853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217567993515721200339897235 326351990273581800509845853)
              ·
                refine ⟨122381996352593175191192195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 326351990273581800509845853 122381996352593175191192195)
                ·
                  refine ⟨183572994528889762786788293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122381996352593175191192195 183572994528889762786788293)
                  ·
                    refine ⟨34419936474166830522522805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 183572994528889762786788293 34419936474166830522522805)
                    ·
                      refine ⟨3226869044453140361486513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34419936474166830522522805 3226869044453140361486513)
                      ·
                        rfl

theorem cell23_6284305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_6284305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284305 prefixEnd_6284305 := by exact prefixLift 6284305
  have htrace : WordTrace (prefixWord ++ tailWord_6284305) baseStart_6284305 baseEnd_6284305 := by
    simpa [prefixWord, tailWord_6284305, baseEnd_6284305] using wordTrace_append hprefix tailTrace_6284305
  have hstable : (prefixWord ++ tailWord_6284305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284305).length < 2 ^ (prefixWord ++ tailWord_6284305).sum := by decide
  have hdescent : baseEnd_6284305 < baseStart_6284305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284309 : List Nat := [1, 3, 2, 1, 4, 2, 1, 2, 1, 3, 3]
def baseStart_6284309 : Nat := 118140960795 + 6284309 * 2 ^ 59
def prefixEnd_6284309 : Nat := 4983230072969 + 3 ^ 40 * 6284309 * 2
def baseEnd_6284309 : Nat := 3226871098375758345836495

theorem tailTrace_6284309 : CollatzResearch.WordTrace tailWord_6284309 prefixEnd_6284309 3226871098375758345836495 := by
  unfold tailWord_6284309
  simp only [CollatzResearch.WordTrace]
  refine ⟨229207579390029242374559981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152805052926686161583039987 229207579390029242374559981)
  ·
    refine ⟨85952842271260965890459993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229207579390029242374559981 85952842271260965890459993)
    ·
      refine ⟨64464631703445724417844995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85952842271260965890459993 64464631703445724417844995)
      ·
        refine ⟨96696947555168586626767493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64464631703445724417844995 96696947555168586626767493)
        ·
          refine ⟨18130677666594109992518905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96696947555168586626767493 18130677666594109992518905)
          ·
            refine ⟨13598008249945582494389179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18130677666594109992518905 13598008249945582494389179)
            ·
              refine ⟨20397012374918373741583769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13598008249945582494389179 20397012374918373741583769)
              ·
                refine ⟨15297759281188780306187827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20397012374918373741583769 15297759281188780306187827)
                ·
                  refine ⟨22946638921783170459281741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15297759281188780306187827 22946638921783170459281741)
                  ·
                    refine ⟨8604989595668688922230653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22946638921783170459281741 8604989595668688922230653)
                    ·
                      refine ⟨3226871098375758345836495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8604989595668688922230653 3226871098375758345836495)
                      ·
                        rfl

theorem cell23_6284309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_6284309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284309 prefixEnd_6284309 := by exact prefixLift 6284309
  have htrace : WordTrace (prefixWord ++ tailWord_6284309) baseStart_6284309 baseEnd_6284309 := by
    simpa [prefixWord, tailWord_6284309, baseEnd_6284309] using wordTrace_append hprefix tailTrace_6284309
  have hstable : (prefixWord ++ tailWord_6284309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284309).length < 2 ^ (prefixWord ++ tailWord_6284309).sum := by decide
  have hdescent : baseEnd_6284309 < baseStart_6284309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284327 : List Nat := [1, 1, 7, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_6284327 : Nat := 118140960795 + 6284327 * 2 ^ 59
def prefixEnd_6284327 : Nat := 4983230072969 + 3 ^ 40 * 6284327 * 2
def baseEnd_6284327 : Nat := 3226880341027539275411413

theorem tailTrace_6284327 : CollatzResearch.WordTrace tailWord_6284327 prefixEnd_6284327 3226880341027539275411413 := by
  unfold tailWord_6284327
  simp only [CollatzResearch.WordTrace]
  refine ⟨229208235903964031448715235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152805490602642687632476823 229208235903964031448715235)
  ·
    refine ⟨343812353855946047173072853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229208235903964031448715235 343812353855946047173072853)
    ·
      refine ⟨8058102043498735480618895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 343812353855946047173072853 8058102043498735480618895)
      ·
        refine ⟨12087153065248103220928343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8058102043498735480618895 12087153065248103220928343)
        ·
          refine ⟨18130729597872154831392515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12087153065248103220928343 18130729597872154831392515)
          ·
            refine ⟨27196094396808232247088773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18130729597872154831392515 27196094396808232247088773)
            ·
              refine ⟨5099267699401543546329145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27196094396808232247088773 5099267699401543546329145)
              ·
                refine ⟨3824450774551157659746859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5099267699401543546329145 3824450774551157659746859)
                ·
                  refine ⟨5736676161826736489620289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3824450774551157659746859 5736676161826736489620289)
                  ·
                    refine ⟨4302507121370052367215217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5736676161826736489620289 4302507121370052367215217)
                    ·
                      refine ⟨3226880341027539275411413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4302507121370052367215217 3226880341027539275411413)
                      ·
                        rfl

theorem cell23_6284327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_6284327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284327 prefixEnd_6284327 := by exact prefixLift 6284327
  have htrace : WordTrace (prefixWord ++ tailWord_6284327) baseStart_6284327 baseEnd_6284327 := by
    simpa [prefixWord, tailWord_6284327, baseEnd_6284327] using wordTrace_append hprefix tailTrace_6284327
  have hstable : (prefixWord ++ tailWord_6284327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284327).length < 2 ^ (prefixWord ++ tailWord_6284327).sum := by decide
  have hdescent : baseEnd_6284327 < baseStart_6284327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284352 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 3]
def baseStart_6284352 : Nat := 118140960795 + 6284352 * 2 ^ 59
def prefixEnd_6284352 : Nat := 4983230072969 + 3 ^ 40 * 6284352 * 2
def baseEnd_6284352 : Nat := 3226893178043901677598797

theorem tailTrace_6284352 : CollatzResearch.WordTrace tailWord_6284352 prefixEnd_6284352 3226893178043901677598797 := by
  unfold tailWord_6284352
  simp only [CollatzResearch.WordTrace]
  refine ⟨114604573864436730359187655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152806098485915640478916873 114604573864436730359187655)
  ·
    refine ⟨171906860796655095538781483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114604573864436730359187655 171906860796655095538781483)
    ·
      refine ⟨257860291194982643308172225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171906860796655095538781483 257860291194982643308172225)
      ·
        refine ⟨193395218396236982481129169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257860291194982643308172225 193395218396236982481129169)
        ·
          refine ⟨145046413797177736860846877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193395218396236982481129169 145046413797177736860846877)
          ·
            refine ⟨54392405173941651322817579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145046413797177736860846877 54392405173941651322817579)
            ·
              refine ⟨81588607760912476984226369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54392405173941651322817579 81588607760912476984226369)
              ·
                refine ⟨61191455820684357738169777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81588607760912476984226369 61191455820684357738169777)
                ·
                  refine ⟨45893591865513268303627333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61191455820684357738169777 45893591865513268303627333)
                  ·
                    refine ⟨8605048474783737806930125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45893591865513268303627333 8605048474783737806930125)
                    ·
                      refine ⟨3226893178043901677598797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8605048474783737806930125 3226893178043901677598797)
                      ·
                        rfl

theorem cell23_6284352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_6284352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284352 prefixEnd_6284352 := by exact prefixLift 6284352
  have htrace : WordTrace (prefixWord ++ tailWord_6284352) baseStart_6284352 baseEnd_6284352 := by
    simpa [prefixWord, tailWord_6284352, baseEnd_6284352] using wordTrace_append hprefix tailTrace_6284352
  have hstable : (prefixWord ++ tailWord_6284352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284352).length < 2 ^ (prefixWord ++ tailWord_6284352).sum := by decide
  have hdescent : baseEnd_6284352 < baseStart_6284352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284366 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2]
def baseStart_6284366 : Nat := 118140960795 + 6284366 * 2 ^ 59
def prefixEnd_6284366 : Nat := 4983230072969 + 3 ^ 40 * 6284366 * 2
def baseEnd_6284366 : Nat := 3226900366773064622823733

theorem tailTrace_6284366 : CollatzResearch.WordTrace tailWord_6284366 prefixEnd_6284366 3226900366773064622823733 := by
  unfold tailWord_6284366
  simp only [CollatzResearch.WordTrace]
  refine ⟨28651207293852842638673119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152806438900548494072923301 28651207293852842638673119)
  ·
    refine ⟨42976810940779263958009679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28651207293852842638673119 42976810940779263958009679)
    ·
      refine ⟨64465216411168895937014519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42976810940779263958009679 64465216411168895937014519)
      ·
        refine ⟨96697824616753343905521779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64465216411168895937014519 96697824616753343905521779)
        ·
          refine ⟨145046736925130015858282669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96697824616753343905521779 145046736925130015858282669)
          ·
            refine ⟨54392526346923755946856001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145046736925130015858282669 54392526346923755946856001)
            ·
              refine ⟨40794394760192816960142001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54392526346923755946856001 40794394760192816960142001)
              ·
                refine ⟨30595796070144612720106501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40794394760192816960142001 30595796070144612720106501)
                ·
                  refine ⟨5736711763152114885019969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30595796070144612720106501 5736711763152114885019969)
                  ·
                    refine ⟨4302533822364086163764977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5736711763152114885019969 4302533822364086163764977)
                    ·
                      refine ⟨3226900366773064622823733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4302533822364086163764977 3226900366773064622823733)
                      ·
                        rfl

theorem cell23_6284366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_6284366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284366 prefixEnd_6284366 := by exact prefixLift 6284366
  have htrace : WordTrace (prefixWord ++ tailWord_6284366) baseStart_6284366 baseEnd_6284366 := by
    simpa [prefixWord, tailWord_6284366, baseEnd_6284366] using wordTrace_append hprefix tailTrace_6284366
  have hstable : (prefixWord ++ tailWord_6284366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284366).length < 2 ^ (prefixWord ++ tailWord_6284366).sum := by decide
  have hdescent : baseEnd_6284366 < baseStart_6284366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284370 : List Nat := [3, 2, 2, 1, 3, 3, 2, 1, 1, 3, 2]
def baseStart_6284370 : Nat := 118140960795 + 6284370 * 2 ^ 59
def prefixEnd_6284370 : Nat := 4983230072969 + 3 ^ 40 * 6284370 * 2
def baseEnd_6284370 : Nat := 3226902420695682607173715

theorem tailTrace_6284370 : CollatzResearch.WordTrace tailWord_6284370 prefixEnd_6284370 3226902420695682607173715 := by
  unfold tailWord_6284370
  simp only [CollatzResearch.WordTrace]
  refine ⟨57302451060702062448132641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152806536161872166528353709 57302451060702062448132641)
  ·
    refine ⟨42976838295526546836099481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57302451060702062448132641 42976838295526546836099481)
    ·
      refine ⟨32232628721644910127074611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42976838295526546836099481 32232628721644910127074611)
      ·
        refine ⟨48348943082467365190611917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32232628721644910127074611 48348943082467365190611917)
        ·
          refine ⟨18130853655925261946479469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48348943082467365190611917 18130853655925261946479469)
          ·
            refine ⟨6799070120971973229929801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18130853655925261946479469 6799070120971973229929801)
            ·
              refine ⟨5099302590728979922447351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6799070120971973229929801 5099302590728979922447351)
              ·
                refine ⟨7648953886093469883671027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5099302590728979922447351 7648953886093469883671027)
                ·
                  refine ⟨11473430829140204825506541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7648953886093469883671027 11473430829140204825506541)
                  ·
                    refine ⟨4302536560927576809564953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11473430829140204825506541 4302536560927576809564953)
                    ·
                      refine ⟨3226902420695682607173715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4302536560927576809564953 3226902420695682607173715)
                      ·
                        rfl

theorem cell23_6284370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_6284370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284370 prefixEnd_6284370 := by exact prefixLift 6284370
  have htrace : WordTrace (prefixWord ++ tailWord_6284370) baseStart_6284370 baseEnd_6284370 := by
    simpa [prefixWord, tailWord_6284370, baseEnd_6284370] using wordTrace_append hprefix tailTrace_6284370
  have hstable : (prefixWord ++ tailWord_6284370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284370).length < 2 ^ (prefixWord ++ tailWord_6284370).sum := by decide
  have hdescent : baseEnd_6284370 < baseStart_6284370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284389 : List Nat := [1, 3, 1, 3, 2, 1, 1, 6, 5]
def baseStart_6284389 : Nat := 118140960795 + 6284389 * 2 ^ 59
def prefixEnd_6284389 : Nat := 4983230072969 + 3 ^ 40 * 6284389 * 2
def baseEnd_6284389 : Nat := 358545797425346448092903

theorem tailTrace_6284389 : CollatzResearch.WordTrace tailWord_6284389 prefixEnd_6284389 358545797425346448092903 := by
  unfold tailWord_6284389
  simp only [CollatzResearch.WordTrace]
  refine ⟨229210497229739416037472221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152806998153159610691648147 229210497229739416037472221)
  ·
    refine ⟨85953936461152281014052083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229210497229739416037472221 85953936461152281014052083)
    ·
      refine ⟨128930904691728421521078125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85953936461152281014052083 128930904691728421521078125)
      ·
        refine ⟨48349089259398158070404297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128930904691728421521078125 48349089259398158070404297)
        ·
          refine ⟨36261816944548618552803223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48349089259398158070404297 36261816944548618552803223)
          ·
            refine ⟨54392725416822927829204835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36261816944548618552803223 54392725416822927829204835)
            ·
              refine ⟨81589088125234391743807253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54392725416822927829204835 81589088125234391743807253)
              ·
                refine ⟨3824488505870362112990965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81589088125234391743807253 3824488505870362112990965)
                ·
                  refine ⟨358545797425346448092903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3824488505870362112990965 358545797425346448092903)
                  ·
                    rfl

theorem cell23_6284389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 5].length) (baseStart_6284389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284389 prefixEnd_6284389 := by exact prefixLift 6284389
  have htrace : WordTrace (prefixWord ++ tailWord_6284389) baseStart_6284389 baseEnd_6284389 := by
    simpa [prefixWord, tailWord_6284389, baseEnd_6284389] using wordTrace_append hprefix tailTrace_6284389
  have hstable : (prefixWord ++ tailWord_6284389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284389).length < 2 ^ (prefixWord ++ tailWord_6284389).sum := by decide
  have hdescent : baseEnd_6284389 < baseStart_6284389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284402 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 3, 7]
def baseStart_6284402 : Nat := 118140960795 + 6284402 * 2 ^ 59
def prefixEnd_6284402 : Nat := 4983230072969 + 3 ^ 40 * 6284402 * 2
def baseEnd_6284402 : Nat := 1075639617358875493991189

theorem tailTrace_6284402 : CollatzResearch.WordTrace tailWord_6284402 prefixEnd_6284402 1075639617358875493991189 := by
  unfold tailWord_6284402
  simp only [CollatzResearch.WordTrace]
  refine ⟨57302742844673079814423865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152807314252461546171796973 57302742844673079814423865)
  ·
    refine ⟨42977057133504809860817899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57302742844673079814423865 42977057133504809860817899)
    ·
      refine ⟨64465585700257214791226849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42977057133504809860817899 64465585700257214791226849)
      ·
        refine ⟨48349189275192911093420137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64465585700257214791226849 48349189275192911093420137)
        ·
          refine ⟨36261891956394683320065103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48349189275192911093420137 36261891956394683320065103)
          ·
            refine ⟨54392837934592024980097655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36261891956394683320065103 54392837934592024980097655)
            ·
              refine ⟨81589256901888037470146483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54392837934592024980097655 81589256901888037470146483)
              ·
                refine ⟨122383885352832056205219725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81589256901888037470146483 122383885352832056205219725)
                ·
                  refine ⟨45893957007312021076957397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122383885352832056205219725 45893957007312021076957397)
                  ·
                    refine ⟨1075639617358875493991189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45893957007312021076957397 1075639617358875493991189)
                    ·
                      rfl

theorem cell23_6284402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_6284402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284402 prefixEnd_6284402 := by exact prefixLift 6284402
  have htrace : WordTrace (prefixWord ++ tailWord_6284402) baseStart_6284402 baseEnd_6284402 := by
    simpa [prefixWord, tailWord_6284402, baseEnd_6284402] using wordTrace_append hprefix tailTrace_6284402
  have hstable : (prefixWord ++ tailWord_6284402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284402).length < 2 ^ (prefixWord ++ tailWord_6284402).sum := by decide
  have hdescent : baseEnd_6284402 < baseStart_6284402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284439 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 4]
def baseStart_6284439 : Nat := 118140960795 + 6284439 * 2 ^ 59
def prefixEnd_6284439 : Nat := 4983230072969 + 3 ^ 40 * 6284439 * 2
def baseEnd_6284439 : Nat := 3226937850860842837210897

theorem tailTrace_6284439 : CollatzResearch.WordTrace tailWord_6284439 prefixEnd_6284439 3226937850860842837210897 := by
  unfold tailWord_6284439
  simp only [CollatzResearch.WordTrace]
  refine ⟨229212320879558274576792371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152808213919705516384528247 229212320879558274576792371)
  ·
    refine ⟨343818481319337411865188557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229212320879558274576792371 343818481319337411865188557)
    ·
      refine ⟨128931930494751529449445709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343818481319337411865188557 128931930494751529449445709)
      ·
        refine ⟨48349473935531823543542141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128931930494751529449445709 48349473935531823543542141)
        ·
          refine ⟨18131052725824433828828303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48349473935531823543542141 18131052725824433828828303)
          ·
            refine ⟨27196579088736650743242455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18131052725824433828828303 27196579088736650743242455)
            ·
              refine ⟨40794868633104976114863683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27196579088736650743242455 40794868633104976114863683)
              ·
                refine ⟨61192302949657464172295525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40794868633104976114863683 61192302949657464172295525)
                ·
                  refine ⟨11473556803060774532305411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61192302949657464172295525 11473556803060774532305411)
                  ·
                    refine ⟨17210335204591161798458117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11473556803060774532305411 17210335204591161798458117)
                    ·
                      refine ⟨3226937850860842837210897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17210335204591161798458117 3226937850860842837210897)
                      ·
                        rfl

theorem cell23_6284439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_6284439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284439 prefixEnd_6284439 := by exact prefixLift 6284439
  have htrace : WordTrace (prefixWord ++ tailWord_6284439) baseStart_6284439 baseEnd_6284439 := by
    simpa [prefixWord, tailWord_6284439, baseEnd_6284439] using wordTrace_append hprefix tailTrace_6284439
  have hstable : (prefixWord ++ tailWord_6284439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284439).length < 2 ^ (prefixWord ++ tailWord_6284439).sum := by decide
  have hdescent : baseEnd_6284439 < baseStart_6284439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284446 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_6284446 : Nat := 118140960795 + 6284446 * 2 ^ 59
def prefixEnd_6284446 : Nat := 4983230072969 + 3 ^ 40 * 6284446 * 2
def baseEnd_6284446 : Nat := 3226941445225424309823365

theorem tailTrace_6284446 : CollatzResearch.WordTrace tailWord_6284446 prefixEnd_6284446 3226941445225424309823365 := by
  unfold tailWord_6284446
  simp only [CollatzResearch.WordTrace]
  refine ⟨28651572023816614346537149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152808384127021943181531461 28651572023816614346537149)
  ·
    refine ⟨10744339508931230379951431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28651572023816614346537149 10744339508931230379951431)
    ·
      refine ⟨16116509263396845569927147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10744339508931230379951431 16116509263396845569927147)
      ·
        refine ⟨24174763895095268354890721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16116509263396845569927147 24174763895095268354890721)
        ·
          refine ⟨18131072921321451266168041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24174763895095268354890721 18131072921321451266168041)
          ·
            refine ⟨13598304690991088449626031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18131072921321451266168041 13598304690991088449626031)
            ·
              refine ⟨20397457036486632674439047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13598304690991088449626031 20397457036486632674439047)
              ·
                refine ⟨30596185554729949011658571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20397457036486632674439047 30596185554729949011658571)
                ·
                  refine ⟨45894278332094923517487857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30596185554729949011658571 45894278332094923517487857)
                  ·
                    refine ⟨34420708749071192638115893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45894278332094923517487857 34420708749071192638115893)
                    ·
                      refine ⟨3226941445225424309823365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34420708749071192638115893 3226941445225424309823365)
                      ·
                        rfl

theorem cell23_6284446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_6284446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284446 prefixEnd_6284446 := by exact prefixLift 6284446
  have htrace : WordTrace (prefixWord ++ tailWord_6284446) baseStart_6284446 baseEnd_6284446 := by
    simpa [prefixWord, tailWord_6284446, baseEnd_6284446] using wordTrace_append hprefix tailTrace_6284446
  have hstable : (prefixWord ++ tailWord_6284446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284446).length < 2 ^ (prefixWord ++ tailWord_6284446).sum := by decide
  have hdescent : baseEnd_6284446 < baseStart_6284446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284470 : List Nat := [5, 1, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_6284470 : Nat := 118140960795 + 6284470 * 2 ^ 59
def prefixEnd_6284470 : Nat := 4983230072969 + 3 ^ 40 * 6284470 * 2
def baseEnd_6284470 : Nat := 1075651256253710738641085

theorem tailTrace_6284470 : CollatzResearch.WordTrace tailWord_6284470 prefixEnd_6284470 1075651256253710738641085 := by
  unfold tailWord_6284470
  simp only [CollatzResearch.WordTrace]
  refine ⟨14325840721402872929448179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152808967694963977914113909 14325840721402872929448179)
  ·
    refine ⟨21488761082104309394172269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14325840721402872929448179 21488761082104309394172269)
    ·
      refine ⟨8058285405789116022814601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21488761082104309394172269 8058285405789116022814601)
      ·
        refine ⟨6043714054341837017110951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8058285405789116022814601 6043714054341837017110951)
        ·
          refine ⟨9065571081512755525666427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6043714054341837017110951 9065571081512755525666427)
          ·
            refine ⟨13598356622269133288499641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9065571081512755525666427 13598356622269133288499641)
            ·
              refine ⟨10198767466701849966374731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13598356622269133288499641 10198767466701849966374731)
              ·
                refine ⟨15298151200052774949562097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10198767466701849966374731 15298151200052774949562097)
                ·
                  refine ⟨11473613400039581212171573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15298151200052774949562097 11473613400039581212171573)
                  ·
                    refine ⟨1075651256253710738641085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11473613400039581212171573 1075651256253710738641085)
                    ·
                      rfl

theorem cell23_6284470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_6284470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284470 prefixEnd_6284470 := by exact prefixLift 6284470
  have htrace : WordTrace (prefixWord ++ tailWord_6284470) baseStart_6284470 baseEnd_6284470 := by
    simpa [prefixWord, tailWord_6284470, baseEnd_6284470] using wordTrace_append hprefix tailTrace_6284470
  have hstable : (prefixWord ++ tailWord_6284470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284470).length < 2 ^ (prefixWord ++ tailWord_6284470).sum := by decide
  have hdescent : baseEnd_6284470 < baseStart_6284470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284476 : List Nat := [2, 2, 2, 3, 2, 1, 1, 3, 2, 2, 3]
def baseStart_6284476 : Nat := 118140960795 + 6284476 * 2 ^ 59
def prefixEnd_6284476 : Nat := 4983230072969 + 3 ^ 40 * 6284476 * 2
def baseEnd_6284476 : Nat := 3226956849645059192448227

theorem tailTrace_6284476 : CollatzResearch.WordTrace tailWord_6284476 prefixEnd_6284476 3226956849645059192448227 := by
  unfold tailWord_6284476
  simp only [CollatzResearch.WordTrace]
  refine ⟨114606835190212114947944641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152809113586949486597259521 114606835190212114947944641)
  ·
    refine ⟨85955126392659086210958481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114606835190212114947944641 85955126392659086210958481)
    ·
      refine ⟨64466344794494314658218861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85955126392659086210958481 64466344794494314658218861)
      ·
        refine ⟨24174879297935367996832073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64466344794494314658218861 24174879297935367996832073)
        ·
          refine ⟨18131159473451525997624055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24174879297935367996832073 18131159473451525997624055)
          ·
            refine ⟨27196739210177288996436083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18131159473451525997624055 27196739210177288996436083)
            ·
              refine ⟨40795108815265933494654125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27196739210177288996436083 40795108815265933494654125)
              ·
                refine ⟨15298165805724725060495297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40795108815265933494654125 15298165805724725060495297)
                ·
                  refine ⟨11473624354293543795371473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15298165805724725060495297 11473624354293543795371473)
                  ·
                    refine ⟨8605218265720157846528605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11473624354293543795371473 8605218265720157846528605)
                    ·
                      refine ⟨3226956849645059192448227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8605218265720157846528605 3226956849645059192448227)
                      ·
                        rfl

theorem cell23_6284476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_6284476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284476 prefixEnd_6284476 := by exact prefixLift 6284476
  have htrace : WordTrace (prefixWord ++ tailWord_6284476) baseStart_6284476 baseEnd_6284476 := by
    simpa [prefixWord, tailWord_6284476, baseEnd_6284476] using wordTrace_append hprefix tailTrace_6284476
  have hstable : (prefixWord ++ tailWord_6284476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284476).length < 2 ^ (prefixWord ++ tailWord_6284476).sum := by decide
  have hdescent : baseEnd_6284476 < baseStart_6284476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284506 : List Nat := [3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3]
def baseStart_6284506 : Nat := 118140960795 + 6284506 * 2 ^ 59
def prefixEnd_6284506 : Nat := 4983230072969 + 3 ^ 40 * 6284506 * 2
def baseEnd_6284506 : Nat := 3226972254064694075073089

theorem tailTrace_6284506 : CollatzResearch.WordTrace tailWord_6284506 prefixEnd_6284506 3226972254064694075073089 := by
  unfold tailWord_6284506
  simp only [CollatzResearch.WordTrace]
  refine ⟨57303691142578886254870343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152809843046877030012987581 57303691142578886254870343)
  ·
    refine ⟨85955536713868329382305515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57303691142578886254870343 85955536713868329382305515)
    ·
      refine ⟨128933305070802494073458273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85955536713868329382305515 128933305070802494073458273)
      ·
        refine ⟨96699978803101870555093705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128933305070802494073458273 96699978803101870555093705)
        ·
          refine ⟨72524984102326402916320279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96699978803101870555093705 72524984102326402916320279)
          ·
            refine ⟨108787476153489604374480419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72524984102326402916320279 108787476153489604374480419)
            ·
              refine ⟨163181214230234406561720629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108787476153489604374480419 163181214230234406561720629)
              ·
                refine ⟨15298238834084475615161309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163181214230234406561720629 15298238834084475615161309)
                ·
                  refine ⟨5736839562781678355685491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15298238834084475615161309 5736839562781678355685491)
                  ·
                    refine ⟨8605259344172517533528237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5736839562781678355685491 8605259344172517533528237)
                    ·
                      refine ⟨3226972254064694075073089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8605259344172517533528237 3226972254064694075073089)
                      ·
                        rfl

theorem cell23_6284506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_6284506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284506 prefixEnd_6284506 := by exact prefixLift 6284506
  have htrace : WordTrace (prefixWord ++ tailWord_6284506) baseStart_6284506 baseEnd_6284506 := by
    simpa [prefixWord, tailWord_6284506, baseEnd_6284506] using wordTrace_append hprefix tailTrace_6284506
  have hstable : (prefixWord ++ tailWord_6284506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284506).length < 2 ^ (prefixWord ++ tailWord_6284506).sum := by decide
  have hdescent : baseEnd_6284506 < baseStart_6284506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284516 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 4, 3, 2]
def baseStart_6284516 : Nat := 118140960795 + 6284516 * 2 ^ 59
def prefixEnd_6284516 : Nat := 4983230072969 + 3 ^ 40 * 6284516 * 2
def baseEnd_6284516 : Nat := 3226977388871239035948043

theorem tailTrace_6284516 : CollatzResearch.WordTrace tailWord_6284516 prefixEnd_6284516 3226977388871239035948043 := by
  unfold tailWord_6284516
  simp only [CollatzResearch.WordTrace]
  refine ⟨114607564650139658363672701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152810086200186211151563601 114607564650139658363672701)
  ·
    refine ⟨42977836743802371886377263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114607564650139658363672701 42977836743802371886377263)
    ·
      refine ⟨64466755115703557829565895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42977836743802371886377263 64466755115703557829565895)
      ·
        refine ⟨96700132673555336744348843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64466755115703557829565895 96700132673555336744348843)
        ·
          refine ⟨145050199010333005116523265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96700132673555336744348843 145050199010333005116523265)
          ·
            refine ⟨108787649257749753837392449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145050199010333005116523265 108787649257749753837392449)
            ·
              refine ⟨81590736943312315378044337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108787649257749753837392449 81590736943312315378044337)
              ·
                refine ⟨61193052707484236533533253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81590736943312315378044337 61193052707484236533533253)
                ·
                  refine ⟨11473697382653294350037485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61193052707484236533533253 11473697382653294350037485)
                  ·
                    refine ⟨4302636518494985381264057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11473697382653294350037485 4302636518494985381264057)
                    ·
                      refine ⟨3226977388871239035948043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4302636518494985381264057 3226977388871239035948043)
                      ·
                        rfl

theorem cell23_6284516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_6284516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284516 prefixEnd_6284516 := by exact prefixLift 6284516
  have htrace : WordTrace (prefixWord ++ tailWord_6284516) baseStart_6284516 baseEnd_6284516 := by
    simpa [prefixWord, tailWord_6284516, baseEnd_6284516] using wordTrace_append hprefix tailTrace_6284516
  have hstable : (prefixWord ++ tailWord_6284516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284516).length < 2 ^ (prefixWord ++ tailWord_6284516).sum := by decide
  have hdescent : baseEnd_6284516 < baseStart_6284516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284543 : List Nat := [1, 1, 2, 2, 1, 7, 2, 1, 1, 5]
def baseStart_6284543 : Nat := 118140960795 + 6284543 * 2 ^ 59
def prefixEnd_6284543 : Nat := 4983230072969 + 3 ^ 40 * 6284543 * 2
def baseEnd_6284543 : Nat := 1075663750949636810103473

theorem tailTrace_6284543 : CollatzResearch.WordTrace tailWord_6284543 prefixEnd_6284543 1075663750949636810103473 := by
  unfold tailWord_6284543
  simp only [CollatzResearch.WordTrace]
  refine ⟨229216114071181500338578283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152810742714121000225718855 229216114071181500338578283)
  ·
    refine ⟨343824171106772250507867425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229216114071181500338578283 343824171106772250507867425)
    ·
      refine ⟨257868128330079187880900569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343824171106772250507867425 257868128330079187880900569)
      ·
        refine ⟨193401096247559390910675427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257868128330079187880900569 193401096247559390910675427)
        ·
          refine ⟨290101644371339086366013141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193401096247559390910675427 290101644371339086366013141)
          ·
            refine ⟨6799257289953259836703433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 290101644371339086366013141 6799257289953259836703433)
            ·
              refine ⟨5099442967464944877527575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6799257289953259836703433 5099442967464944877527575)
              ·
                refine ⟨7649164451197417316291363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5099442967464944877527575 7649164451197417316291363)
                ·
                  refine ⟨11473746676796125974437045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7649164451197417316291363 11473746676796125974437045)
                  ·
                    refine ⟨1075663750949636810103473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11473746676796125974437045 1075663750949636810103473)
                    ·
                      rfl

theorem cell23_6284543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 1, 5].length) (baseStart_6284543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284543 prefixEnd_6284543 := by exact prefixLift 6284543
  have htrace : WordTrace (prefixWord ++ tailWord_6284543) baseStart_6284543 baseEnd_6284543 := by
    simpa [prefixWord, tailWord_6284543, baseEnd_6284543] using wordTrace_append hprefix tailTrace_6284543
  have hstable : (prefixWord ++ tailWord_6284543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284543).length < 2 ^ (prefixWord ++ tailWord_6284543).sum := by decide
  have hdescent : baseEnd_6284543 < baseStart_6284543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284549 : List Nat := [1, 3, 1, 1, 2, 1, 4, 3, 1, 1, 5]
def baseStart_6284549 : Nat := 118140960795 + 6284549 * 2 ^ 59
def prefixEnd_6284549 : Nat := 4983230072969 + 3 ^ 40 * 6284549 * 2
def baseEnd_6284549 : Nat := 3226994333732837406835391

theorem tailTrace_6284549 : CollatzResearch.WordTrace tailWord_6284549 prefixEnd_6284549 3226994333732837406835391 := by
  unfold tailWord_6284549
  simp only [CollatzResearch.WordTrace]
  refine ⟨229216332909159763363296701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152810888606106508908864467 229216332909159763363296701)
  ·
    refine ⟨85956124840934911261236263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229216332909159763363296701 85956124840934911261236263)
    ·
      refine ⟨128934187261402366891854395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85956124840934911261236263 128934187261402366891854395)
      ·
        refine ⟨193401280892103550337781593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128934187261402366891854395 193401280892103550337781593)
        ·
          refine ⟨145050960669077662753336195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193401280892103550337781593 145050960669077662753336195)
          ·
            refine ⟨217576441003616494130004293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145050960669077662753336195 217576441003616494130004293)
            ·
              refine ⟨40795582688178092649375805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217576441003616494130004293 40795582688178092649375805)
              ·
                refine ⟨15298343508066784743515927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40795582688178092649375805 15298343508066784743515927)
                ·
                  refine ⟨22947515262100177115273891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15298343508066784743515927 22947515262100177115273891)
                  ·
                    refine ⟨34421272893150265672910837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22947515262100177115273891 34421272893150265672910837)
                    ·
                      refine ⟨3226994333732837406835391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34421272893150265672910837 3226994333732837406835391)
                      ·
                        rfl

theorem cell23_6284549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_6284549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284549 prefixEnd_6284549 := by exact prefixLift 6284549
  have htrace : WordTrace (prefixWord ++ tailWord_6284549) baseStart_6284549 baseEnd_6284549 := by
    simpa [prefixWord, tailWord_6284549, baseEnd_6284549] using wordTrace_append hprefix tailTrace_6284549
  have hstable : (prefixWord ++ tailWord_6284549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284549).length < 2 ^ (prefixWord ++ tailWord_6284549).sum := by decide
  have hdescent : baseEnd_6284549 < baseStart_6284549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284556 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 4, 4]
def baseStart_6284556 : Nat := 118140960795 + 6284556 * 2 ^ 59
def prefixEnd_6284556 : Nat := 4983230072969 + 3 ^ 40 * 6284556 * 2
def baseEnd_6284556 : Nat := 1075665976032472959815953

theorem tailTrace_6284556 : CollatzResearch.WordTrace tailWord_6284556 prefixEnd_6284556 1075665976032472959815953 := by
  unfold tailWord_6284556
  simp only [CollatzResearch.WordTrace]
  refine ⟨114608294110067201779400761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152811058813422935705867681 114608294110067201779400761)
  ·
    refine ⟨85956220582550401334550571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114608294110067201779400761 85956220582550401334550571)
    ·
      refine ⟨128934330873825602001825857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85956220582550401334550571 128934330873825602001825857)
      ·
        refine ⟨96700748155369201501369393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128934330873825602001825857 96700748155369201501369393)
        ·
          refine ⟨72525561116526901126027045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96700748155369201501369393 72525561116526901126027045)
          ·
            refine ⟨13598542709348793961130071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72525561116526901126027045 13598542709348793961130071)
            ·
              refine ⟨20397814064023190941695107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13598542709348793961130071 20397814064023190941695107)
              ·
                refine ⟨30596721096034786412542661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20397814064023190941695107 30596721096034786412542661)
                ·
                  refine ⟨5736885205506522452351749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30596721096034786412542661 5736885205506522452351749)
                  ·
                    refine ⟨1075665976032472959815953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5736885205506522452351749 1075665976032472959815953)
                    ·
                      rfl

theorem cell23_6284556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 4, 4].length) (baseStart_6284556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284556 prefixEnd_6284556 := by exact prefixLift 6284556
  have htrace : WordTrace (prefixWord ++ tailWord_6284556) baseStart_6284556 baseEnd_6284556 := by
    simpa [prefixWord, tailWord_6284556, baseEnd_6284556] using wordTrace_append hprefix tailTrace_6284556
  have hstable : (prefixWord ++ tailWord_6284556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284556).length < 2 ^ (prefixWord ++ tailWord_6284556).sum := by decide
  have hdescent : baseEnd_6284556 < baseStart_6284556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284573 : List Nat := [1, 4, 2, 3, 1, 3, 1, 1, 1, 6]
def baseStart_6284573 : Nat := 118140960795 + 6284573 * 2 ^ 59
def prefixEnd_6284573 : Nat := 4983230072969 + 3 ^ 40 * 6284573 * 2
def baseEnd_6284573 : Nat := 1075668885756181770978427

theorem tailTrace_6284573 : CollatzResearch.WordTrace tailWord_6284573 prefixEnd_6284573 1075668885756181770978427 := by
  unfold tailWord_6284573
  simp only [CollatzResearch.WordTrace]
  refine ⟨229217208261072815462170373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152811472174048543641446915 229217208261072815462170373)
  ·
    refine ⟨42978226548951152899156945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229217208261072815462170373 42978226548951152899156945)
    ·
      refine ⟨32233669911713364674367709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42978226548951152899156945 32233669911713364674367709)
      ·
        refine ⟨12087626216892511752887891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32233669911713364674367709 12087626216892511752887891)
        ·
          refine ⟨18131439325338767629331837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12087626216892511752887891 18131439325338767629331837)
          ·
            refine ⟨6799289747002037860999439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18131439325338767629331837 6799289747002037860999439)
            ·
              refine ⟨10198934620503056791499159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6799289747002037860999439 10198934620503056791499159)
              ·
                refine ⟨15298401930754585187248739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10198934620503056791499159 15298401930754585187248739)
                ·
                  refine ⟨22947602896131877780873109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15298401930754585187248739 22947602896131877780873109)
                  ·
                    refine ⟨1075668885756181770978427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22947602896131877780873109 1075668885756181770978427)
                    ·
                      rfl

theorem cell23_6284573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_6284573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284573 prefixEnd_6284573 := by exact prefixLift 6284573
  have htrace : WordTrace (prefixWord ++ tailWord_6284573) baseStart_6284573 baseEnd_6284573 := by
    simpa [prefixWord, tailWord_6284573, baseEnd_6284573] using wordTrace_append hprefix tailTrace_6284573
  have hstable : (prefixWord ++ tailWord_6284573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284573).length < 2 ^ (prefixWord ++ tailWord_6284573).sum := by decide
  have hdescent : baseEnd_6284573 < baseStart_6284573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284576 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 6]
def baseStart_6284576 : Nat := 118140960795 + 6284576 * 2 ^ 59
def prefixEnd_6284576 : Nat := 4983230072969 + 3 ^ 40 * 6284576 * 2
def baseEnd_6284576 : Nat := 3227008197710508801197767

theorem tailTrace_6284576 : CollatzResearch.WordTrace tailWord_6284576 prefixEnd_6284576 3227008197710508801197767 := by
  unfold tailWord_6284576
  simp only [CollatzResearch.WordTrace]
  refine ⟨114608658840030973487264791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152811545120041297983019721 114608658840030973487264791)
  ·
    refine ⟨171912988260046460230897187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114608658840030973487264791 171912988260046460230897187)
    ·
      refine ⟨257869482390069690346345781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171912988260046460230897187 257869482390069690346345781)
      ·
        refine ⟨24175263974069033469969917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 257869482390069690346345781 24175263974069033469969917)
        ·
          refine ⟨9065723990275887551238719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24175263974069033469969917 9065723990275887551238719)
          ·
            refine ⟨13598585985413831326858079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9065723990275887551238719 13598585985413831326858079)
            ·
              refine ⟨20397878978120746990287119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13598585985413831326858079 20397878978120746990287119)
              ·
                refine ⟨30596818467181120485430679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20397878978120746990287119 30596818467181120485430679)
                ·
                  refine ⟨45895227700771680728146019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30596818467181120485430679 45895227700771680728146019)
                  ·
                    refine ⟨68842841551157521092219029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45895227700771680728146019 68842841551157521092219029)
                    ·
                      refine ⟨3227008197710508801197767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68842841551157521092219029 3227008197710508801197767)
                      ·
                        rfl

theorem cell23_6284576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_6284576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284576 prefixEnd_6284576 := by exact prefixLift 6284576
  have htrace : WordTrace (prefixWord ++ tailWord_6284576) baseStart_6284576 baseEnd_6284576 := by
    simpa [prefixWord, tailWord_6284576, baseEnd_6284576] using wordTrace_append hprefix tailTrace_6284576
  have hstable : (prefixWord ++ tailWord_6284576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284576).length < 2 ^ (prefixWord ++ tailWord_6284576).sum := by decide
  have hdescent : baseEnd_6284576 < baseStart_6284576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284586 : List Nat := [3, 1, 4, 2, 1, 2, 1, 9]
def baseStart_6284586 : Nat := 118140960795 + 6284586 * 2 ^ 59
def prefixEnd_6284586 : Nat := 4983230072969 + 3 ^ 40 * 6284586 * 2
def baseEnd_6284586 : Nat := 119519012315446435632323

theorem tailTrace_6284586 : CollatzResearch.WordTrace tailWord_6284586 prefixEnd_6284586 119519012315446435632323 := by
  unfold tailWord_6284586
  simp only [CollatzResearch.WordTrace]
  refine ⟨57304420602506429670598403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152811788273350479121595741 57304420602506429670598403)
  ·
    refine ⟨85956630903759644505897605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57304420602506429670598403 85956630903759644505897605)
    ·
      refine ⟨16116868294454933344855801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85956630903759644505897605 16116868294454933344855801)
      ·
        refine ⟨12087651220841200008641851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16116868294454933344855801 12087651220841200008641851)
        ·
          refine ⟨18131476831261800012962777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12087651220841200008641851 18131476831261800012962777)
          ·
            refine ⟨13598607623446350009722083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18131476831261800012962777 13598607623446350009722083)
            ·
              refine ⟨20397911435169525014583125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13598607623446350009722083 20397911435169525014583125)
              ·
                refine ⟨119519012315446435632323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20397911435169525014583125 119519012315446435632323)
                ·
                  rfl

theorem cell23_6284586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 9].length) (baseStart_6284586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284586 prefixEnd_6284586 := by exact prefixLift 6284586
  have htrace : WordTrace (prefixWord ++ tailWord_6284586) baseStart_6284586 baseEnd_6284586 := by
    simpa [prefixWord, tailWord_6284586, baseEnd_6284586] using wordTrace_append hprefix tailTrace_6284586
  have hstable : (prefixWord ++ tailWord_6284586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284586).length < 2 ^ (prefixWord ++ tailWord_6284586).sum := by decide
  have hdescent : baseEnd_6284586 < baseStart_6284586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284597 : List Nat := [1, 3, 3, 1, 2, 2, 3, 3, 1, 2, 2]
def baseStart_6284597 : Nat := 118140960795 + 6284597 * 2 ^ 59
def prefixEnd_6284597 : Nat := 4983230072969 + 3 ^ 40 * 6284597 * 2
def baseEnd_6284597 : Nat := 3227018980804253219035171

theorem tailTrace_6284597 : CollatzResearch.WordTrace tailWord_6284597 prefixEnd_6284597 3227018980804253219035171 := by
  unfold tailWord_6284597
  simp only [CollatzResearch.WordTrace]
  refine ⟨229218083612985867561044045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152812055741990578374029363 229218083612985867561044045)
  ·
    refine ⟨85956781354869700335391517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229218083612985867561044045 85956781354869700335391517)
    ·
      refine ⟨32233793008076137625771819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85956781354869700335391517 32233793008076137625771819)
      ·
        refine ⟨48350689512114206438657729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32233793008076137625771819 48350689512114206438657729)
        ·
          refine ⟨36263017134085654828993297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48350689512114206438657729 36263017134085654828993297)
          ·
            refine ⟨27197262850564241121744973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36263017134085654828993297 27197262850564241121744973)
            ·
              refine ⟨10198973568961590420654365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27197262850564241121744973 10198973568961590420654365)
              ·
                refine ⟨3824615088360596407745387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10198973568961590420654365 3824615088360596407745387)
                ·
                  refine ⟨5736922632540894611618081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3824615088360596407745387 5736922632540894611618081)
                  ·
                    refine ⟨4302691974405670958713561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5736922632540894611618081 4302691974405670958713561)
                    ·
                      refine ⟨3227018980804253219035171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4302691974405670958713561 3227018980804253219035171)
                      ·
                        rfl

theorem cell23_6284597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_6284597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284597 prefixEnd_6284597 := by exact prefixLift 6284597
  have htrace : WordTrace (prefixWord ++ tailWord_6284597) baseStart_6284597 baseEnd_6284597 := by
    simpa [prefixWord, tailWord_6284597, baseEnd_6284597] using wordTrace_append hprefix tailTrace_6284597
  have hstable : (prefixWord ++ tailWord_6284597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284597).length < 2 ^ (prefixWord ++ tailWord_6284597).sum := by decide
  have hdescent : baseEnd_6284597 < baseStart_6284597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284640 : List Nat := [2, 1, 1, 3, 4, 1, 3, 2, 1, 3, 2]
def baseStart_6284640 : Nat := 118140960795 + 6284640 * 2 ^ 59
def prefixEnd_6284640 : Nat := 4983230072969 + 3 ^ 40 * 6284640 * 2
def baseEnd_6284640 : Nat := 3227041060472396550797473

theorem tailTrace_6284640 : CollatzResearch.WordTrace tailWord_6284640 prefixEnd_6284640 3227041060472396550797473 := by
  unfold tailWord_6284640
  simp only [CollatzResearch.WordTrace]
  refine ⟨114609825975915042952429687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152813101301220057269906249 114609825975915042952429687)
  ·
    refine ⟨171914738963872564428644531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114609825975915042952429687 171914738963872564428644531)
    ·
      refine ⟨257872108445808846642966797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171914738963872564428644531 257872108445808846642966797)
      ·
        refine ⟨96702040667178317491112549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257872108445808846642966797 96702040667178317491112549)
        ·
          refine ⟨18131632625095934529583603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96702040667178317491112549 18131632625095934529583603)
          ·
            refine ⟨27197448937643901794375405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18131632625095934529583603 27197448937643901794375405)
            ·
              refine ⟨10199043351616463172890777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27197448937643901794375405 10199043351616463172890777)
              ·
                refine ⟨7649282513712347379668083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10199043351616463172890777 7649282513712347379668083)
                ·
                  refine ⟨11473923770568521069502125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7649282513712347379668083 11473923770568521069502125)
                  ·
                    refine ⟨4302721413963195401063297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11473923770568521069502125 4302721413963195401063297)
                    ·
                      refine ⟨3227041060472396550797473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4302721413963195401063297 3227041060472396550797473)
                      ·
                        rfl

theorem cell23_6284640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_6284640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284640 prefixEnd_6284640 := by exact prefixLift 6284640
  have htrace : WordTrace (prefixWord ++ tailWord_6284640) baseStart_6284640 baseEnd_6284640 := by
    simpa [prefixWord, tailWord_6284640, baseEnd_6284640] using wordTrace_append hprefix tailTrace_6284640
  have hstable : (prefixWord ++ tailWord_6284640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284640).length < 2 ^ (prefixWord ++ tailWord_6284640).sum := by decide
  have hdescent : baseEnd_6284640 < baseStart_6284640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284649 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 3, 4, 4]
def baseStart_6284649 : Nat := 118140960795 + 6284649 * 2 ^ 59
def prefixEnd_6284649 : Nat := 4983230072969 + 3 ^ 40 * 6284649 * 2
def baseEnd_6284649 : Nat := 3227045681798287015584931

theorem tailTrace_6284649 : CollatzResearch.WordTrace tailWord_6284649 prefixEnd_6284649 3227045681798287015584931 := by
  unfold tailWord_6284649
  simp only [CollatzResearch.WordTrace]
  refine ⟨229219980208797480441937001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152813320139198320294624667 229219980208797480441937001)
  ·
    refine ⟨171914985156598110331452751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229219980208797480441937001 171914985156598110331452751)
    ·
      refine ⟨257872477734897165497179127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171914985156598110331452751 257872477734897165497179127)
      ·
        refine ⟨386808716602345748245768691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257872477734897165497179127 386808716602345748245768691)
        ·
          refine ⟨580213074903518622368653037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386808716602345748245768691 580213074903518622368653037)
          ·
            refine ⟨217579903088819483388244889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 580213074903518622368653037 217579903088819483388244889)
            ·
              refine ⟨163184927316614612541183667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217579903088819483388244889 163184927316614612541183667)
              ·
                refine ⟨244777390974921918811775501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163184927316614612541183667 244777390974921918811775501)
                ·
                  refine ⟨91791521615595719554415813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244777390974921918811775501 91791521615595719554415813)
                  ·
                    refine ⟨17210910302924197416452965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91791521615595719554415813 17210910302924197416452965)
                    ·
                      refine ⟨3227045681798287015584931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17210910302924197416452965 3227045681798287015584931)
                      ·
                        rfl

theorem cell23_6284649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 4, 4].length) (baseStart_6284649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284649 prefixEnd_6284649 := by exact prefixLift 6284649
  have htrace : WordTrace (prefixWord ++ tailWord_6284649) baseStart_6284649 baseEnd_6284649 := by
    simpa [prefixWord, tailWord_6284649, baseEnd_6284649] using wordTrace_append hprefix tailTrace_6284649
  have hstable : (prefixWord ++ tailWord_6284649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284649).length < 2 ^ (prefixWord ++ tailWord_6284649).sum := by decide
  have hdescent : baseEnd_6284649 < baseStart_6284649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284653 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 3, 4, 2]
def baseStart_6284653 : Nat := 118140960795 + 6284653 * 2 ^ 59
def prefixEnd_6284653 : Nat := 4983230072969 + 3 ^ 40 * 6284653 * 2
def baseEnd_6284653 : Nat := 3227047735720904999934913

theorem tailTrace_6284653 : CollatzResearch.WordTrace tailWord_6284653 prefixEnd_6284653 3227047735720904999934913 := by
  unfold tailWord_6284653
  simp only [CollatzResearch.WordTrace]
  refine ⟨229220126100782989125082613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152813417400521992750055075 229220126100782989125082613)
  ·
    refine ⟨21489386821948405230476495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229220126100782989125082613 21489386821948405230476495)
    ·
      refine ⟨32234080232922607845714743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21489386821948405230476495 32234080232922607845714743)
      ·
        refine ⟨48351120349383911768572115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32234080232922607845714743 48351120349383911768572115)
        ·
          refine ⟨72526680524075867652858173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48351120349383911768572115 72526680524075867652858173)
          ·
            refine ⟨27197505196528450369821815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72526680524075867652858173 27197505196528450369821815)
            ·
              refine ⟨40796257794792675554732723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27197505196528450369821815 40796257794792675554732723)
              ·
                refine ⟨61194386692189013332099085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40796257794792675554732723 61194386692189013332099085)
                ·
                  refine ⟨22947895009570879999537157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61194386692189013332099085 22947895009570879999537157)
                  ·
                    refine ⟨4302730314294539999913217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22947895009570879999537157 4302730314294539999913217)
                    ·
                      refine ⟨3227047735720904999934913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4302730314294539999913217 3227047735720904999934913)
                      ·
                        rfl

theorem cell23_6284653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_6284653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284653 prefixEnd_6284653 := by exact prefixLift 6284653
  have htrace : WordTrace (prefixWord ++ tailWord_6284653) baseStart_6284653 baseEnd_6284653 := by
    simpa [prefixWord, tailWord_6284653, baseEnd_6284653] using wordTrace_append hprefix tailTrace_6284653
  have hstable : (prefixWord ++ tailWord_6284653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284653).length < 2 ^ (prefixWord ++ tailWord_6284653).sum := by decide
  have hdescent : baseEnd_6284653 < baseStart_6284653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284689 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 3, 7]
def baseStart_6284689 : Nat := 118140960795 + 6284689 * 2 ^ 59
def prefixEnd_6284689 : Nat := 4983230072969 + 3 ^ 40 * 6284689 * 2
def baseEnd_6284689 : Nat := 1075688740341488953028249

theorem tailTrace_6284689 : CollatzResearch.WordTrace tailWord_6284689 prefixEnd_6284689 1075688740341488953028249 := by
  unfold tailWord_6284689
  simp only [CollatzResearch.WordTrace]
  refine ⟨229221439128652567273393121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152814292752435044848928747 229221439128652567273393121)
  ·
    refine ⟨171916079346489425455044841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229221439128652567273393121 171916079346489425455044841)
    ·
      refine ⟨128937059509867069091283631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171916079346489425455044841 128937059509867069091283631)
      ·
        refine ⟨193405589264800603636925447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128937059509867069091283631 193405589264800603636925447)
        ·
          refine ⟨290108383897200905455388171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193405589264800603636925447 290108383897200905455388171)
          ·
            refine ⟨435162575845801358183082257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290108383897200905455388171 435162575845801358183082257)
            ·
              refine ⟨326371931884351018637311693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435162575845801358183082257 326371931884351018637311693)
              ·
                refine ⟨122389474456631631988991885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 326371931884351018637311693 122389474456631631988991885)
                ·
                  refine ⟨45896052921236861995871957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122389474456631631988991885 45896052921236861995871957)
                  ·
                    refine ⟨1075688740341488953028249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45896052921236861995871957 1075688740341488953028249)
                    ·
                      rfl

theorem cell23_6284689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_6284689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284689 prefixEnd_6284689 := by exact prefixLift 6284689
  have htrace : WordTrace (prefixWord ++ tailWord_6284689) baseStart_6284689 baseEnd_6284689 := by
    simpa [prefixWord, tailWord_6284689, baseEnd_6284689] using wordTrace_append hprefix tailTrace_6284689
  have hstable : (prefixWord ++ tailWord_6284689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284689).length < 2 ^ (prefixWord ++ tailWord_6284689).sum := by decide
  have hdescent : baseEnd_6284689 < baseStart_6284689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284719 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 1, 10]
def baseStart_6284719 : Nat := 118140960795 + 6284719 * 2 ^ 59
def prefixEnd_6284719 : Nat := 4983230072969 + 3 ^ 40 * 6284719 * 2
def baseEnd_6284719 : Nat := 1075693875148033913903203

theorem tailTrace_6284719 : CollatzResearch.WordTrace tailWord_6284719 prefixEnd_6284719 1075693875148033913903203 := by
  unfold tailWord_6284719
  simp only [CollatzResearch.WordTrace]
  refine ⟨229222533318543882396985211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152815022212362588264656807 229222533318543882396985211)
  ·
    refine ⟨343833799977815823595477817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229222533318543882396985211 343833799977815823595477817)
    ·
      refine ⟨257875349983361867696608363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343833799977815823595477817 257875349983361867696608363)
      ·
        refine ⟨386813024975042801544912545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257875349983361867696608363 386813024975042801544912545)
        ·
          refine ⟨290109768731282101158684409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386813024975042801544912545 290109768731282101158684409)
          ·
            refine ⟨217582326548461575869013307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290109768731282101158684409 217582326548461575869013307)
            ·
              refine ⟨326373489822692363803519961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217582326548461575869013307 326373489822692363803519961)
              ·
                refine ⟨244780117367019272852639971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326373489822692363803519961 244780117367019272852639971)
                ·
                  refine ⟨367170176050528909278959957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244780117367019272852639971 367170176050528909278959957)
                  ·
                    refine ⟨1075693875148033913903203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 367170176050528909278959957 1075693875148033913903203)
                    ·
                      rfl

theorem cell23_6284719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 10].length) (baseStart_6284719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284719 prefixEnd_6284719 := by exact prefixLift 6284719
  have htrace : WordTrace (prefixWord ++ tailWord_6284719) baseStart_6284719 baseEnd_6284719 := by
    simpa [prefixWord, tailWord_6284719, baseEnd_6284719] using wordTrace_append hprefix tailTrace_6284719
  have hstable : (prefixWord ++ tailWord_6284719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284719).length < 2 ^ (prefixWord ++ tailWord_6284719).sum := by decide
  have hdescent : baseEnd_6284719 < baseStart_6284719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284738 : List Nat := [3, 5, 2, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_6284738 : Nat := 118140960795 + 6284738 * 2 ^ 59
def prefixEnd_6284738 : Nat := 4983230072969 + 3 ^ 40 * 6284738 * 2
def baseEnd_6284738 : Nat := 3227091381576537167372023

theorem tailTrace_6284738 : CollatzResearch.WordTrace tailWord_6284738 prefixEnd_6284738 3227091381576537167372023 := by
  unfold tailWord_6284738
  simp only [CollatzResearch.WordTrace]
  refine ⟨57305806576368762160481717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152815484203650032427951245 57305806576368762160481717)
  ·
    refine ⟨5372419366534571452545161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57305806576368762160481717 5372419366534571452545161)
    ·
      refine ⟨4029314524900928589408871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5372419366534571452545161 4029314524900928589408871)
      ·
        refine ⟨6043971787351392884113307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4029314524900928589408871 6043971787351392884113307)
        ·
          refine ⟨9065957681027089326169961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6043971787351392884113307 9065957681027089326169961)
          ·
            refine ⟨6799468260770316994627471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9065957681027089326169961 6799468260770316994627471)
            ·
              refine ⟨10199202391155475491941207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6799468260770316994627471 10199202391155475491941207)
              ·
                refine ⟨15298803586733213237911811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10199202391155475491941207 15298803586733213237911811)
                ·
                  refine ⟨22948205380099819856867717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15298803586733213237911811 22948205380099819856867717)
                  ·
                    refine ⟨4302788508768716223162697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22948205380099819856867717 4302788508768716223162697)
                    ·
                      refine ⟨3227091381576537167372023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4302788508768716223162697 3227091381576537167372023)
                      ·
                        rfl

theorem cell23_6284738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_6284738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284738 prefixEnd_6284738 := by exact prefixLift 6284738
  have htrace : WordTrace (prefixWord ++ tailWord_6284738) baseStart_6284738 baseEnd_6284738 := by
    simpa [prefixWord, tailWord_6284738, baseEnd_6284738] using wordTrace_append hprefix tailTrace_6284738
  have hstable : (prefixWord ++ tailWord_6284738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284738).length < 2 ^ (prefixWord ++ tailWord_6284738).sum := by decide
  have hdescent : baseEnd_6284738 < baseStart_6284738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284743 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 2, 4, 2]
def baseStart_6284743 : Nat := 118140960795 + 6284743 * 2 ^ 59
def prefixEnd_6284743 : Nat := 4983230072969 + 3 ^ 40 * 6284743 * 2
def baseEnd_6284743 : Nat := 3227093948979809647809499

theorem tailTrace_6284743 : CollatzResearch.WordTrace tailWord_6284743 prefixEnd_6284743 3227093948979809647809499 := by
  unfold tailWord_6284743
  simp only [CollatzResearch.WordTrace]
  refine ⟨229223408670456934495858883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152815605780304622997239255 229223408670456934495858883)
  ·
    refine ⟨343835113005685401743788325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229223408670456934495858883 343835113005685401743788325)
    ·
      refine ⟨64469083688566012826960311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 343835113005685401743788325 64469083688566012826960311)
      ·
        refine ⟨96703625532849019240440467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64469083688566012826960311 96703625532849019240440467)
        ·
          refine ⟨145055438299273528860660701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96703625532849019240440467 145055438299273528860660701)
          ·
            refine ⟨54395789362227573322747763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145055438299273528860660701 54395789362227573322747763)
            ·
              refine ⟨81593684043341359984121645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54395789362227573322747763 81593684043341359984121645)
              ·
                refine ⟨30597631516253009994045617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81593684043341359984121645 30597631516253009994045617)
                ·
                  refine ⟨22948223637189757495534213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30597631516253009994045617 22948223637189757495534213)
                  ·
                    refine ⟨4302791931973079530412665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22948223637189757495534213 4302791931973079530412665)
                    ·
                      refine ⟨3227093948979809647809499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4302791931973079530412665 3227093948979809647809499)
                      ·
                        rfl

theorem cell23_6284743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_6284743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284743 prefixEnd_6284743 := by exact prefixLift 6284743
  have htrace : WordTrace (prefixWord ++ tailWord_6284743) baseStart_6284743 baseEnd_6284743 := by
    simpa [prefixWord, tailWord_6284743, baseEnd_6284743] using wordTrace_append hprefix tailTrace_6284743
  have hstable : (prefixWord ++ tailWord_6284743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284743).length < 2 ^ (prefixWord ++ tailWord_6284743).sum := by decide
  have hdescent : baseEnd_6284743 < baseStart_6284743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284803 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 1, 5, 2]
def baseStart_6284803 : Nat := 118140960795 + 6284803 * 2 ^ 59
def prefixEnd_6284803 : Nat := 4983230072969 + 3 ^ 40 * 6284803 * 2
def baseEnd_6284803 : Nat := 3227124757819079413059223

theorem tailTrace_6284803 : CollatzResearch.WordTrace tailWord_6284803 prefixEnd_6284803 3227124757819079413059223 := by
  unfold tailWord_6284803
  simp only [CollatzResearch.WordTrace]
  refine ⟨229225597050239564743043063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152817064700159709828695375 229225597050239564743043063)
  ·
    refine ⟨343838395575359347114564595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229225597050239564743043063 343838395575359347114564595)
    ·
      refine ⟨515757593363039020671846893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343838395575359347114564595 515757593363039020671846893)
      ·
        refine ⟨193409097511139632751942585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 515757593363039020671846893 193409097511139632751942585)
        ·
          refine ⟨145056823133354724563956939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193409097511139632751942585 145056823133354724563956939)
          ·
            refine ⟨217585234700032086845935409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145056823133354724563956939 217585234700032086845935409)
            ·
              refine ⟨163188926025024065134451557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217585234700032086845935409 163188926025024065134451557)
              ·
                refine ⟨30597923629692012212709667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163188926025024065134451557 30597923629692012212709667)
                ·
                  refine ⟨45896885444538018319064501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30597923629692012212709667 45896885444538018319064501)
                  ·
                    refine ⟨4302833010425439217412297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45896885444538018319064501 4302833010425439217412297)
                    ·
                      refine ⟨3227124757819079413059223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4302833010425439217412297 3227124757819079413059223)
                      ·
                        rfl

theorem cell23_6284803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 5, 2].length) (baseStart_6284803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284803 prefixEnd_6284803 := by exact prefixLift 6284803
  have htrace : WordTrace (prefixWord ++ tailWord_6284803) baseStart_6284803 baseEnd_6284803 := by
    simpa [prefixWord, tailWord_6284803, baseEnd_6284803] using wordTrace_append hprefix tailTrace_6284803
  have hstable : (prefixWord ++ tailWord_6284803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284803).length < 2 ^ (prefixWord ++ tailWord_6284803).sum := by decide
  have hdescent : baseEnd_6284803 < baseStart_6284803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284860 : List Nat := [2, 2, 2, 2, 4, 1, 2, 1, 1, 6]
def baseStart_6284860 : Nat := 118140960795 + 6284860 * 2 ^ 59
def prefixEnd_6284860 : Nat := 4983230072969 + 3 ^ 40 * 6284860 * 2
def baseEnd_6284860 : Nat := 1075718008738795230015487

theorem tailTrace_6284860 : CollatzResearch.WordTrace tailWord_6284860 prefixEnd_6284860 1075718008738795230015487 := by
  unfold tailWord_6284860
  simp only [CollatzResearch.WordTrace]
  refine ⟨114613838005516531738934017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152818450674022042318578689 114613838005516531738934017)
  ·
    refine ⟨85960378504137398804200513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114613838005516531738934017 85960378504137398804200513)
    ·
      refine ⟨64470283878103049103150385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85960378504137398804200513 64470283878103049103150385)
      ·
        refine ⟨48352712908577286827362789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64470283878103049103150385 48352712908577286827362789)
        ·
          refine ⟨9066133670358241280130523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48352712908577286827362789 9066133670358241280130523)
          ·
            refine ⟨13599200505537361920195785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9066133670358241280130523 13599200505537361920195785)
            ·
              refine ⟨10199400379153021440146839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13599200505537361920195785 10199400379153021440146839)
              ·
                refine ⟨15299100568729532160220259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10199400379153021440146839 15299100568729532160220259)
                ·
                  refine ⟨22948650853094298240330389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15299100568729532160220259 22948650853094298240330389)
                  ·
                    refine ⟨1075718008738795230015487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22948650853094298240330389 1075718008738795230015487)
                    ·
                      rfl

theorem cell23_6284860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_6284860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284860 prefixEnd_6284860 := by exact prefixLift 6284860
  have htrace : WordTrace (prefixWord ++ tailWord_6284860) baseStart_6284860 baseEnd_6284860 := by
    simpa [prefixWord, tailWord_6284860, baseEnd_6284860] using wordTrace_append hprefix tailTrace_6284860
  have hstable : (prefixWord ++ tailWord_6284860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284860).length < 2 ^ (prefixWord ++ tailWord_6284860).sum := by decide
  have hdescent : baseEnd_6284860 < baseStart_6284860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284863 : List Nat := [1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 4]
def baseStart_6284863 : Nat := 118140960795 + 6284863 * 2 ^ 59
def prefixEnd_6284863 : Nat := 4983230072969 + 3 ^ 40 * 6284863 * 2
def baseEnd_6284863 : Nat := 3227155566658349178308947

theorem tailTrace_6284863 : CollatzResearch.WordTrace tailWord_6284863 prefixEnd_6284863 3227155566658349178308947 := by
  unfold tailWord_6284863
  simp only [CollatzResearch.WordTrace]
  refine ⟨229227785430022194990227243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152818523620014796660151495 229227785430022194990227243)
  ·
    refine ⟨343841678145033292485340865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229227785430022194990227243 343841678145033292485340865)
    ·
      refine ⟨257881258608774969364005649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343841678145033292485340865 257881258608774969364005649)
      ·
        refine ⟨193410943956581227023004237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257881258608774969364005649 193410943956581227023004237)
        ·
          refine ⟨72529103983717960133626589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193410943956581227023004237 72529103983717960133626589)
          ·
            refine ⟨27198413993894235050109971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72529103983717960133626589 27198413993894235050109971)
            ·
              refine ⟨40797620990841352575164957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27198413993894235050109971 40797620990841352575164957)
              ·
                refine ⟨15299107871565507215686859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40797620990841352575164957 15299107871565507215686859)
                ·
                  refine ⟨22948661807348260823530289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15299107871565507215686859 22948661807348260823530289)
                  ·
                    refine ⟨17211496355511195617647717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22948661807348260823530289 17211496355511195617647717)
                    ·
                      refine ⟨3227155566658349178308947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17211496355511195617647717 3227155566658349178308947)
                      ·
                        rfl

theorem cell23_6284863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_6284863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284863 prefixEnd_6284863 := by exact prefixLift 6284863
  have htrace : WordTrace (prefixWord ++ tailWord_6284863) baseStart_6284863 baseEnd_6284863 := by
    simpa [prefixWord, tailWord_6284863, baseEnd_6284863] using wordTrace_append hprefix tailTrace_6284863
  have hstable : (prefixWord ++ tailWord_6284863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284863).length < 2 ^ (prefixWord ++ tailWord_6284863).sum := by decide
  have hdescent : baseEnd_6284863 < baseStart_6284863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284887 : List Nat := [1, 1, 3, 2, 2, 3, 4, 1, 1, 2, 3]
def baseStart_6284887 : Nat := 118140960795 + 6284887 * 2 ^ 59
def prefixEnd_6284887 : Nat := 4983230072969 + 3 ^ 40 * 6284887 * 2
def baseEnd_6284887 : Nat := 3227167890194057084408837

theorem tailTrace_6284887 : CollatzResearch.WordTrace tailWord_6284887 prefixEnd_6284887 3227167890194057084408837 := by
  unfold tailWord_6284887
  simp only [CollatzResearch.WordTrace]
  refine ⟨229228660781935247089100915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152819107187956831392733943 229228660781935247089100915)
  ·
    refine ⟨343842991172902870633651373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229228660781935247089100915 343842991172902870633651373)
    ·
      refine ⟨128941121689838576487619265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343842991172902870633651373 128941121689838576487619265)
      ·
        refine ⟨96705841267378932365714449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128941121689838576487619265 96705841267378932365714449)
        ·
          refine ⟨72529380950534199274285837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96705841267378932365714449 72529380950534199274285837)
          ·
            refine ⟨27198517856450324727857189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72529380950534199274285837 27198517856450324727857189)
            ·
              refine ⟨5099722098084435886473223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27198517856450324727857189 5099722098084435886473223)
              ·
                refine ⟨7649583147126653829709835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5099722098084435886473223 7649583147126653829709835)
                ·
                  refine ⟨11474374720689980744564753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7649583147126653829709835 11474374720689980744564753)
                  ·
                    refine ⟨8605781040517485558423565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11474374720689980744564753 8605781040517485558423565)
                    ·
                      refine ⟨3227167890194057084408837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8605781040517485558423565 3227167890194057084408837)
                      ·
                        rfl

theorem cell23_6284887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_6284887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284887 prefixEnd_6284887 := by exact prefixLift 6284887
  have htrace : WordTrace (prefixWord ++ tailWord_6284887) baseStart_6284887 baseEnd_6284887 := by
    simpa [prefixWord, tailWord_6284887, baseEnd_6284887] using wordTrace_append hprefix tailTrace_6284887
  have hstable : (prefixWord ++ tailWord_6284887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284887).length < 2 ^ (prefixWord ++ tailWord_6284887).sum := by decide
  have hdescent : baseEnd_6284887 < baseStart_6284887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284917 : List Nat := [1, 3, 4, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_6284917 : Nat := 118140960795 + 6284917 * 2 ^ 59
def prefixEnd_6284917 : Nat := 4983230072969 + 3 ^ 40 * 6284917 * 2
def baseEnd_6284917 : Nat := 3227183294613691967033699

theorem tailTrace_6284917 : CollatzResearch.WordTrace tailWord_6284917 prefixEnd_6284917 3227183294613691967033699 := by
  unfold tailWord_6284917
  simp only [CollatzResearch.WordTrace]
  refine ⟨229229754971826562212693005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152819836647884374808462003 229229754971826562212693005)
  ·
    refine ⟨85961158114434960829759877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229229754971826562212693005 85961158114434960829759877)
    ·
      refine ⟨16117717146456555155579977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85961158114434960829759877 16117717146456555155579977)
      ·
        refine ⟨12088287859842416366684983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16117717146456555155579977 12088287859842416366684983)
        ·
          refine ⟨18132431789763624550027475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12088287859842416366684983 18132431789763624550027475)
          ·
            refine ⟨27198647684645436825041213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18132431789763624550027475 27198647684645436825041213)
            ·
              refine ⟨10199492881742038809390455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27198647684645436825041213 10199492881742038809390455)
              ·
                refine ⟨15299239322613058214085683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10199492881742038809390455 15299239322613058214085683)
                ·
                  refine ⟨22948858983919587321128525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15299239322613058214085683 22948858983919587321128525)
                  ·
                    refine ⟨8605822118969845245423197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22948858983919587321128525 8605822118969845245423197)
                    ·
                      refine ⟨3227183294613691967033699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8605822118969845245423197 3227183294613691967033699)
                      ·
                        rfl

theorem cell23_6284917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_6284917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284917 prefixEnd_6284917 := by exact prefixLift 6284917
  have htrace : WordTrace (prefixWord ++ tailWord_6284917) baseStart_6284917 baseEnd_6284917 := by
    simpa [prefixWord, tailWord_6284917, baseEnd_6284917] using wordTrace_append hprefix tailTrace_6284917
  have hstable : (prefixWord ++ tailWord_6284917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284917).length < 2 ^ (prefixWord ++ tailWord_6284917).sum := by decide
  have hdescent : baseEnd_6284917 < baseStart_6284917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284940 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 3, 4, 2]
def baseStart_6284940 : Nat := 118140960795 + 6284940 * 2 ^ 59
def prefixEnd_6284940 : Nat := 4983230072969 + 3 ^ 40 * 6284940 * 2
def baseEnd_6284940 : Nat := 3227195104668745377046093

theorem tailTrace_6284940 : CollatzResearch.WordTrace tailWord_6284940 prefixEnd_6284940 3227195104668745377046093 := by
  unfold tailWord_6284940
  simp only [CollatzResearch.WordTrace]
  refine ⟨114615296925371618570390137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152820395900495491427186849 114615296925371618570390137)
  ·
    refine ⟨85961472694028713927792603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114615296925371618570390137 85961472694028713927792603)
    ·
      refine ⟨128942209041043070891688905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85961472694028713927792603 128942209041043070891688905)
      ·
        refine ⟨96706656780782303168766679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128942209041043070891688905 96706656780782303168766679)
        ·
          refine ⟨145059985171173454753150019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96706656780782303168766679 145059985171173454753150019)
          ·
            refine ⟨217589977756760182129725029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145059985171173454753150019 217589977756760182129725029)
            ·
              refine ⟨40798120829392534149323443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217589977756760182129725029 40798120829392534149323443)
              ·
                refine ⟨61197181244088801223985165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40798120829392534149323443 61197181244088801223985165)
                ·
                  refine ⟨22948942966533300458994437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61197181244088801223985165 22948942966533300458994437)
                  ·
                    refine ⟨4302926806224993836061457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22948942966533300458994437 4302926806224993836061457)
                    ·
                      refine ⟨3227195104668745377046093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4302926806224993836061457 3227195104668745377046093)
                      ·
                        rfl

theorem cell23_6284940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_6284940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284940 prefixEnd_6284940 := by exact prefixLift 6284940
  have htrace : WordTrace (prefixWord ++ tailWord_6284940) baseStart_6284940 baseEnd_6284940 := by
    simpa [prefixWord, tailWord_6284940, baseEnd_6284940] using wordTrace_append hprefix tailTrace_6284940
  have hstable : (prefixWord ++ tailWord_6284940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284940).length < 2 ^ (prefixWord ++ tailWord_6284940).sum := by decide
  have hdescent : baseEnd_6284940 < baseStart_6284940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284953 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 2, 2, 4]
def baseStart_6284953 : Nat := 118140960795 + 6284953 * 2 ^ 59
def prefixEnd_6284953 : Nat := 4983230072969 + 3 ^ 40 * 6284953 * 2
def baseEnd_6284953 : Nat := 3227201779917253826183533

theorem tailTrace_6284953 : CollatzResearch.WordTrace tailWord_6284953 prefixEnd_6284953 3227201779917253826183533 := by
  unfold tailWord_6284953
  simp only [CollatzResearch.WordTrace]
  refine ⟨229231067999696140361003513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152820711999797426907335675 229231067999696140361003513)
  ·
    refine ⟨171923300999772105270752635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229231067999696140361003513 171923300999772105270752635)
    ·
      refine ⟨257884951499658157906128953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171923300999772105270752635 257884951499658157906128953)
      ·
        refine ⟨193413713624743618429596715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257884951499658157906128953 193413713624743618429596715)
        ·
          refine ⟨290120570437115427644395073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193413713624743618429596715 290120570437115427644395073)
          ·
            refine ⟨217590427827836570733296305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290120570437115427644395073 217590427827836570733296305)
            ·
              refine ⟨163192820870877428049972229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217590427827836570733296305 163192820870877428049972229)
              ·
                refine ⟨30598653913289517759369793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163192820870877428049972229 30598653913289517759369793)
                ·
                  refine ⟨22948990434967138319527345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30598653913289517759369793 22948990434967138319527345)
                  ·
                    refine ⟨17211742826225353739645509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22948990434967138319527345 17211742826225353739645509)
                    ·
                      refine ⟨3227201779917253826183533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17211742826225353739645509 3227201779917253826183533)
                      ·
                        rfl

theorem cell23_6284953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_6284953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284953 prefixEnd_6284953 := by exact prefixLift 6284953
  have htrace : WordTrace (prefixWord ++ tailWord_6284953) baseStart_6284953 baseEnd_6284953 := by
    simpa [prefixWord, tailWord_6284953, baseEnd_6284953] using wordTrace_append hprefix tailTrace_6284953
  have hstable : (prefixWord ++ tailWord_6284953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284953).length < 2 ^ (prefixWord ++ tailWord_6284953).sum := by decide
  have hdescent : baseEnd_6284953 < baseStart_6284953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6284968 : List Nat := [2, 1, 7, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_6284968 : Nat := 118140960795 + 6284968 * 2 ^ 59
def prefixEnd_6284968 : Nat := 4983230072969 + 3 ^ 40 * 6284968 * 2
def baseEnd_6284968 : Nat := 3227209482127071267495965

theorem tailTrace_6284968 : CollatzResearch.WordTrace tailWord_6284968 prefixEnd_6284968 3227209482127071267495965 := by
  unfold tailWord_6284968
  simp only [CollatzResearch.WordTrace]
  refine ⟨114615807547320898961399779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152821076729761198615199705 114615807547320898961399779)
  ·
    refine ⟨171923711320981348442099669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114615807547320898961399779 171923711320981348442099669)
    ·
      refine ⟨4029461984085500354111711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 171923711320981348442099669 4029461984085500354111711)
      ·
        refine ⟨6044192976128250531167567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4029461984085500354111711 6044192976128250531167567)
        ·
          refine ⟨9066289464192375796751351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6044192976128250531167567 9066289464192375796751351)
          ·
            refine ⟨13599434196288563695127027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9066289464192375796751351 13599434196288563695127027)
            ·
              refine ⟨20399151294432845542690541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13599434196288563695127027 20399151294432845542690541)
              ·
                refine ⟨7649681735412317078508953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20399151294432845542690541 7649681735412317078508953)
                ·
                  refine ⟨5737261301559237808881715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7649681735412317078508953 5737261301559237808881715)
                  ·
                    refine ⟨8605891952338856713322573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5737261301559237808881715 8605891952338856713322573)
                    ·
                      refine ⟨3227209482127071267495965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8605891952338856713322573 3227209482127071267495965)
                      ·
                        rfl

theorem cell23_6284968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_6284968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6284968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6284968 prefixEnd_6284968 := by exact prefixLift 6284968
  have htrace : WordTrace (prefixWord ++ tailWord_6284968) baseStart_6284968 baseEnd_6284968 := by
    simpa [prefixWord, tailWord_6284968, baseEnd_6284968] using wordTrace_append hprefix tailTrace_6284968
  have hstable : (prefixWord ++ tailWord_6284968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6284968).length < 2 ^ (prefixWord ++ tailWord_6284968).sum := by decide
  have hdescent : baseEnd_6284968 < baseStart_6284968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6284968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285044 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_6285044 : Nat := 118140960795 + 6285044 * 2 ^ 59
def prefixEnd_6285044 : Nat := 4983230072969 + 3 ^ 40 * 6285044 * 2
def baseEnd_6285044 : Nat := 1075749502218937656715205

theorem tailTrace_6285044 : CollatzResearch.WordTrace tailWord_6285044 prefixEnd_6285044 1075749502218937656715205 := by
  unfold tailWord_6285044
  simp only [CollatzResearch.WordTrace]
  refine ⟨114617193521183231451283093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152822924694910975268377457 114617193521183231451283093)
  ·
    refine ⟨5372680946305463974278895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 114617193521183231451283093 5372680946305463974278895)
    ·
      refine ⟨8059021419458195961418343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5372680946305463974278895 8059021419458195961418343)
      ·
        refine ⟨12088532129187293942127515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8059021419458195961418343 12088532129187293942127515)
        ·
          refine ⟨18132798193780940913191273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12088532129187293942127515 18132798193780940913191273)
          ·
            refine ⟨13599598645335705684893455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18132798193780940913191273 13599598645335705684893455)
            ·
              refine ⟨20399397968003558527340183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13599598645335705684893455 20399397968003558527340183)
              ·
                refine ⟨30599096952005337791010275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20399397968003558527340183 30599096952005337791010275)
                ·
                  refine ⟨45898645428008006686515413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30599096952005337791010275 45898645428008006686515413)
                  ·
                    refine ⟨1075749502218937656715205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45898645428008006686515413 1075749502218937656715205)
                    ·
                      rfl

theorem cell23_6285044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_6285044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285044 prefixEnd_6285044 := by exact prefixLift 6285044
  have htrace : WordTrace (prefixWord ++ tailWord_6285044) baseStart_6285044 baseEnd_6285044 := by
    simpa [prefixWord, tailWord_6285044, baseEnd_6285044] using wordTrace_append hprefix tailTrace_6285044
  have hstable : (prefixWord ++ tailWord_6285044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285044).length < 2 ^ (prefixWord ++ tailWord_6285044).sum := by decide
  have hdescent : baseEnd_6285044 < baseStart_6285044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285060 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_6285060 : Nat := 118140960795 + 6285060 * 2 ^ 59
def prefixEnd_6285060 : Nat := 4983230072969 + 3 ^ 40 * 6285060 * 2
def baseEnd_6285060 : Nat := 3227256722347284907545541

theorem tailTrace_6285060 : CollatzResearch.WordTrace tailWord_6285060 prefixEnd_6285060 3227256722347284907545541 := by
  unfold tailWord_6285060
  simp only [CollatzResearch.WordTrace]
  refine ⟨114617485305154248817574317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152823313740205665090099089 114617485305154248817574317)
  ·
    refine ⟨42981556989432843306590369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114617485305154248817574317 42981556989432843306590369)
    ·
      refine ⟨32236167742074632479942777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42981556989432843306590369 32236167742074632479942777)
      ·
        refine ⟨24177125806555974359957083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32236167742074632479942777 24177125806555974359957083)
        ·
          refine ⟨36265688709833961539935625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24177125806555974359957083 36265688709833961539935625)
          ·
            refine ⟨27199266532375471154951719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36265688709833961539935625 27199266532375471154951719)
            ·
              refine ⟨40798899798563206732427579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27199266532375471154951719 40798899798563206732427579)
              ·
                refine ⟨61198349697844810098641369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40798899798563206732427579 61198349697844810098641369)
                ·
                  refine ⟨45898762273383607573981027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61198349697844810098641369 45898762273383607573981027)
                  ·
                    refine ⟨68848143410075411360971541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45898762273383607573981027 68848143410075411360971541)
                    ·
                      refine ⟨3227256722347284907545541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68848143410075411360971541 3227256722347284907545541)
                      ·
                        rfl

theorem cell23_6285060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_6285060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285060 prefixEnd_6285060 := by exact prefixLift 6285060
  have htrace : WordTrace (prefixWord ++ tailWord_6285060) baseStart_6285060 baseEnd_6285060 := by
    simpa [prefixWord, tailWord_6285060, baseEnd_6285060] using wordTrace_append hprefix tailTrace_6285060
  have hstable : (prefixWord ++ tailWord_6285060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285060).length < 2 ^ (prefixWord ++ tailWord_6285060).sum := by decide
  have hdescent : baseEnd_6285060 < baseStart_6285060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285074 : List Nat := [3, 2, 4, 1, 1, 1, 1, 3, 3, 4]
def baseStart_6285074 : Nat := 118140960795 + 6285074 * 2 ^ 59
def prefixEnd_6285074 : Nat := 4983230072969 + 3 ^ 40 * 6285074 * 2
def baseEnd_6285074 : Nat := 1075754637025482617590159

theorem tailTrace_6285074 : CollatzResearch.WordTrace tailWord_6285074 prefixEnd_6285074 1075754637025482617590159 := by
  unfold tailWord_6285074
  simp only [CollatzResearch.WordTrace]
  refine ⟨57308870308064444506539569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152823654154838518684105517 57308870308064444506539569)
  ·
    refine ⟨42981652731048333379904677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57308870308064444506539569 42981652731048333379904677)
    ·
      refine ⟨8059059887071562508732127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42981652731048333379904677 8059059887071562508732127)
      ·
        refine ⟨12088589830607343763098191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8059059887071562508732127 12088589830607343763098191)
        ·
          refine ⟨18132884745911015644647287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12088589830607343763098191 18132884745911015644647287)
          ·
            refine ⟨27199327118866523466970931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18132884745911015644647287 27199327118866523466970931)
            ·
              refine ⟨40798990678299785200456397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27199327118866523466970931 40798990678299785200456397)
              ·
                refine ⟨15299621504362419450171149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40798990678299785200456397 15299621504362419450171149)
                ·
                  refine ⟨5737358064135907293814181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15299621504362419450171149 5737358064135907293814181)
                  ·
                    refine ⟨1075754637025482617590159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5737358064135907293814181 1075754637025482617590159)
                    ·
                      rfl

theorem cell23_6285074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_6285074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285074 prefixEnd_6285074 := by exact prefixLift 6285074
  have htrace : WordTrace (prefixWord ++ tailWord_6285074) baseStart_6285074 baseEnd_6285074 := by
    simpa [prefixWord, tailWord_6285074, baseEnd_6285074] using wordTrace_append hprefix tailTrace_6285074
  have hstable : (prefixWord ++ tailWord_6285074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285074).length < 2 ^ (prefixWord ++ tailWord_6285074).sum := by decide
  have hdescent : baseEnd_6285074 < baseStart_6285074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285087 : List Nat := [1, 1, 2, 4, 2, 1, 5, 1, 6]
def baseStart_6285087 : Nat := 118140960795 + 6285087 * 2 ^ 59
def prefixEnd_6285087 : Nat := 4983230072969 + 3 ^ 40 * 6285087 * 2
def baseEnd_6285087 : Nat := 358585620702772922434213

theorem tailTrace_6285087 : CollatzResearch.WordTrace tailWord_6285087 prefixEnd_6285087 358585620702772922434213 := by
  unfold tailWord_6285087
  simp only [CollatzResearch.WordTrace]
  refine ⟨229235955381210681246381515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152823970254140454164254343 229235955381210681246381515)
  ·
    refine ⟨343853933071816021869572273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229235955381210681246381515 343853933071816021869572273)
    ·
      refine ⟨257890449803862016402179205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343853933071816021869572273 257890449803862016402179205)
      ·
        refine ⟨48354459338224128075408601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257890449803862016402179205 48354459338224128075408601)
        ·
          refine ⟨36265844503668096056556451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48354459338224128075408601 36265844503668096056556451)
          ·
            refine ⟨54398766755502144084834677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36265844503668096056556451 54398766755502144084834677)
            ·
              refine ⟨5099884383328326007953251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54398766755502144084834677 5099884383328326007953251)
              ·
                refine ⟨7649826574992489011929877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5099884383328326007953251 7649826574992489011929877)
                ·
                  refine ⟨358585620702772922434213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7649826574992489011929877 358585620702772922434213)
                  ·
                    rfl

theorem cell23_6285087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 6].length) (baseStart_6285087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285087 prefixEnd_6285087 := by exact prefixLift 6285087
  have htrace : WordTrace (prefixWord ++ tailWord_6285087) baseStart_6285087 baseEnd_6285087 := by
    simpa [prefixWord, tailWord_6285087, baseEnd_6285087] using wordTrace_append hprefix tailTrace_6285087
  have hstable : (prefixWord ++ tailWord_6285087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285087).length < 2 ^ (prefixWord ++ tailWord_6285087).sum := by decide
  have hdescent : baseEnd_6285087 < baseStart_6285087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285090 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_6285090 : Nat := 118140960795 + 6285090 * 2 ^ 59
def prefixEnd_6285090 : Nat := 4983230072969 + 3 ^ 40 * 6285090 * 2
def baseEnd_6285090 : Nat := 3227272126766919790170403

theorem tailTrace_6285090 : CollatzResearch.WordTrace tailWord_6285090 prefixEnd_6285090 3227272126766919790170403 := by
  unfold tailWord_6285090
  simp only [CollatzResearch.WordTrace]
  refine ⟨57309016200049953189685181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152824043200133208505827149 57309016200049953189685181)
  ·
    refine ⟨21490881075018732446131943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57309016200049953189685181 21490881075018732446131943)
    ·
      refine ⟨32236321612528098669197915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21490881075018732446131943 32236321612528098669197915)
      ·
        refine ⟨48354482418792148003796873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32236321612528098669197915 48354482418792148003796873)
        ·
          refine ⟨36265861814094111002847655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48354482418792148003796873 36265861814094111002847655)
          ·
            refine ⟨54398792721141166504271483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36265861814094111002847655 54398792721141166504271483)
            ·
              refine ⟨81598189081711749756407225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54398792721141166504271483 81598189081711749756407225)
              ·
                refine ⟨61198641811283812317305419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81598189081711749756407225 61198641811283812317305419)
                ·
                  refine ⟨91797962716925718475958129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61198641811283812317305419 91797962716925718475958129)
                  ·
                    refine ⟨68848472037694288856968597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91797962716925718475958129 68848472037694288856968597)
                    ·
                      refine ⟨3227272126766919790170403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68848472037694288856968597 3227272126766919790170403)
                      ·
                        rfl

theorem cell23_6285090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_6285090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285090 prefixEnd_6285090 := by exact prefixLift 6285090
  have htrace : WordTrace (prefixWord ++ tailWord_6285090) baseStart_6285090 baseEnd_6285090 := by
    simpa [prefixWord, tailWord_6285090, baseEnd_6285090] using wordTrace_append hprefix tailTrace_6285090
  have hstable : (prefixWord ++ tailWord_6285090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285090).length < 2 ^ (prefixWord ++ tailWord_6285090).sum := by decide
  have hdescent : baseEnd_6285090 < baseStart_6285090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285108 : List Nat := [2, 5, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_6285108 : Nat := 118140960795 + 6285108 * 2 ^ 59
def prefixEnd_6285108 : Nat := 4983230072969 + 3 ^ 40 * 6285108 * 2
def baseEnd_6285108 : Nat := 1075760456472900239915107

theorem tailTrace_6285108 : CollatzResearch.WordTrace tailWord_6285108 prefixEnd_6285108 1075760456472900239915107 := by
  unfold tailWord_6285108
  simp only [CollatzResearch.WordTrace]
  refine ⟨114618360657067300916447989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152824480876089734555263985 114618360657067300916447989)
  ·
    refine ⟨10745471311600059460916999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114618360657067300916447989 10745471311600059460916999)
    ·
      refine ⟨16118206967400089191375499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10745471311600059460916999 16118206967400089191375499)
      ·
        refine ⟨24177310451100133787063249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16118206967400089191375499 24177310451100133787063249)
        ·
          refine ⟨18132982838325100340297437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24177310451100133787063249 18132982838325100340297437)
          ·
            refine ⟨6799868564371912627611539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18132982838325100340297437 6799868564371912627611539)
            ·
              refine ⟨10199802846557868941417309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6799868564371912627611539 10199802846557868941417309)
              ·
                refine ⟨3824926067459200853031491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10199802846557868941417309 3824926067459200853031491)
                ·
                  refine ⟨5737389101188801279547237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3824926067459200853031491 5737389101188801279547237)
                  ·
                    refine ⟨1075760456472900239915107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5737389101188801279547237 1075760456472900239915107)
                    ·
                      rfl

theorem cell23_6285108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_6285108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285108 prefixEnd_6285108 := by exact prefixLift 6285108
  have htrace : WordTrace (prefixWord ++ tailWord_6285108) baseStart_6285108 baseEnd_6285108 := by
    simpa [prefixWord, tailWord_6285108, baseEnd_6285108] using wordTrace_append hprefix tailTrace_6285108
  have hstable : (prefixWord ++ tailWord_6285108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285108).length < 2 ^ (prefixWord ++ tailWord_6285108).sum := by decide
  have hdescent : baseEnd_6285108 < baseStart_6285108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285120 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 4]
def baseStart_6285120 : Nat := 118140960795 + 6285120 * 2 ^ 59
def prefixEnd_6285120 : Nat := 4983230072969 + 3 ^ 40 * 6285120 * 2
def baseEnd_6285120 : Nat := 3227287531186554672795265

theorem tailTrace_6285120 : CollatzResearch.WordTrace tailWord_6285120 prefixEnd_6285120 3227287531186554672795265 := by
  unfold tailWord_6285120
  simp only [CollatzResearch.WordTrace]
  refine ⟨114618579495045563941166407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152824772660060751921555209 114618579495045563941166407)
  ·
    refine ⟨171927869242568345911749611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114618579495045563941166407 171927869242568345911749611)
    ·
      refine ⟨257891803863852518867624417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171927869242568345911749611 257891803863852518867624417)
      ·
        refine ⟨193418852897889389150718313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257891803863852518867624417 193418852897889389150718313)
        ·
          refine ⟨145064139673417041863038735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193418852897889389150718313 145064139673417041863038735)
          ·
            refine ⟨217596209510125562794558103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145064139673417041863038735 217596209510125562794558103)
            ·
              refine ⟨326394314265188344191837155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217596209510125562794558103 326394314265188344191837155)
              ·
                refine ⟨489591471397782516287755733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326394314265188344191837155 489591471397782516287755733)
                ·
                  refine ⟨11474800110885527725494275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 489591471397782516287755733 11474800110885527725494275)
                  ·
                    refine ⟨17212200166328291588241413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11474800110885527725494275 17212200166328291588241413)
                    ·
                      refine ⟨3227287531186554672795265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17212200166328291588241413 3227287531186554672795265)
                      ·
                        rfl

theorem cell23_6285120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_6285120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285120 prefixEnd_6285120 := by exact prefixLift 6285120
  have htrace : WordTrace (prefixWord ++ tailWord_6285120) baseStart_6285120 baseEnd_6285120 := by
    simpa [prefixWord, tailWord_6285120, baseEnd_6285120] using wordTrace_append hprefix tailTrace_6285120
  have hstable : (prefixWord ++ tailWord_6285120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285120).length < 2 ^ (prefixWord ++ tailWord_6285120).sum := by decide
  have hdescent : baseEnd_6285120 < baseStart_6285120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285154 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_6285154 : Nat := 118140960795 + 6285154 * 2 ^ 59
def prefixEnd_6285154 : Nat := 4983230072969 + 3 ^ 40 * 6285154 * 2
def baseEnd_6285154 : Nat := 3227304989528807539770109

theorem tailTrace_6285154 : CollatzResearch.WordTrace tailWord_6285154 prefixEnd_6285154 3227304989528807539770109 := by
  unfold tailWord_6285154
  simp only [CollatzResearch.WordTrace]
  refine ⟨57309599767991987922267629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152825599381311967792713677 57309599767991987922267629)
  ·
    refine ⟨21491099912996995470850361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57309599767991987922267629 21491099912996995470850361)
    ·
      refine ⟨16118324934747746603137771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21491099912996995470850361 16118324934747746603137771)
      ·
        refine ⟨24177487402121619904706657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16118324934747746603137771 24177487402121619904706657)
        ·
          refine ⟨18133115551591214928529993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24177487402121619904706657 18133115551591214928529993)
          ·
            refine ⟨13599836663693411196397495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18133115551591214928529993 13599836663693411196397495)
            ·
              refine ⟨20399754995540116794596243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13599836663693411196397495 20399754995540116794596243)
              ·
                refine ⟨30599632493310175191894365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20399754995540116794596243 30599632493310175191894365)
                ·
                  refine ⟨11474862184991315696960387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30599632493310175191894365 11474862184991315696960387)
                  ·
                    refine ⟨17212293277486973545440581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11474862184991315696960387 17212293277486973545440581)
                    ·
                      refine ⟨3227304989528807539770109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17212293277486973545440581 3227304989528807539770109)
                      ·
                        rfl

theorem cell23_6285154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_6285154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285154 prefixEnd_6285154 := by exact prefixLift 6285154
  have htrace : WordTrace (prefixWord ++ tailWord_6285154) baseStart_6285154 baseEnd_6285154 := by
    simpa [prefixWord, tailWord_6285154, baseEnd_6285154] using wordTrace_append hprefix tailTrace_6285154
  have hstable : (prefixWord ++ tailWord_6285154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285154).length < 2 ^ (prefixWord ++ tailWord_6285154).sum := by decide
  have hdescent : baseEnd_6285154 < baseStart_6285154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285160 : List Nat := [2, 1, 4, 2, 1, 1, 1, 11]
def baseStart_6285160 : Nat := 118140960795 + 6285160 * 2 ^ 59
def prefixEnd_6285160 : Nat := 4983230072969 + 3 ^ 40 * 6285160 * 2
def baseEnd_6285160 : Nat := 119529928533804982085003

theorem tailTrace_6285160 : CollatzResearch.WordTrace tailWord_6285160 prefixEnd_6285160 119529928533804982085003 := by
  unfold tailWord_6285160
  simp only [CollatzResearch.WordTrace]
  refine ⟨114619308954973107356894467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152825745273297476475859289 114619308954973107356894467)
  ·
    refine ⟨171928963432459661035341701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114619308954973107356894467 171928963432459661035341701)
    ·
      refine ⟨32236680643586186444126569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171928963432459661035341701 32236680643586186444126569)
      ·
        refine ⟨24177510482689639833094927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32236680643586186444126569 24177510482689639833094927)
        ·
          refine ⟨36266265724034459749642391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24177510482689639833094927 36266265724034459749642391)
          ·
            refine ⟨54399398586051689624463587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36266265724034459749642391 54399398586051689624463587)
            ·
              refine ⟨81599097879077534436695381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54399398586051689624463587 81599097879077534436695381)
              ·
                refine ⟨119529928533804982085003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 81599097879077534436695381 119529928533804982085003)
                ·
                  rfl

theorem cell23_6285160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 11].length) (baseStart_6285160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285160 prefixEnd_6285160 := by exact prefixLift 6285160
  have htrace : WordTrace (prefixWord ++ tailWord_6285160) baseStart_6285160 baseEnd_6285160 := by
    simpa [prefixWord, tailWord_6285160, baseEnd_6285160] using wordTrace_append hprefix tailTrace_6285160
  have hstable : (prefixWord ++ tailWord_6285160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285160).length < 2 ^ (prefixWord ++ tailWord_6285160).sum := by decide
  have hdescent : baseEnd_6285160 < baseStart_6285160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285171 : List Nat := [1, 1, 1, 2, 2, 1, 3, 7, 1, 2, 2]
def baseStart_6285171 : Nat := 118140960795 + 6285171 * 2 ^ 59
def prefixEnd_6285171 : Nat := 4983230072969 + 3 ^ 40 * 6285171 * 2
def baseEnd_6285171 : Nat := 3227313718699933973257531

theorem tailTrace_6285171 : CollatzResearch.WordTrace tailWord_6285171 prefixEnd_6285171 3227313718699933973257531 := by
  unfold tailWord_6285171
  simp only [CollatzResearch.WordTrace]
  refine ⟨229239019112906363592439367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152826012741937575728292911 229239019112906363592439367)
  ·
    refine ⟨343858528669359545388659051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229239019112906363592439367 343858528669359545388659051)
    ·
      refine ⟨515787793004039318082988577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343858528669359545388659051 515787793004039318082988577)
      ·
        refine ⟨386840844753029488562241433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 515787793004039318082988577 386840844753029488562241433)
        ·
          refine ⟨290130633564772116421681075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386840844753029488562241433 290130633564772116421681075)
          ·
            refine ⟨435195950347158174632521613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290130633564772116421681075 435195950347158174632521613)
            ·
              refine ⟨163198481380184315487195605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 435195950347158174632521613 163198481380184315487195605)
              ·
                refine ⟨3824964407348069894231147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 163198481380184315487195605 3824964407348069894231147)
                ·
                  refine ⟨5737446611022104841346721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3824964407348069894231147 5737446611022104841346721)
                  ·
                    refine ⟨4303084958266578631010041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5737446611022104841346721 4303084958266578631010041)
                    ·
                      refine ⟨3227313718699933973257531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4303084958266578631010041 3227313718699933973257531)
                      ·
                        rfl

theorem cell23_6285171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 1, 2, 2].length) (baseStart_6285171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285171 prefixEnd_6285171 := by exact prefixLift 6285171
  have htrace : WordTrace (prefixWord ++ tailWord_6285171) baseStart_6285171 baseEnd_6285171 := by
    simpa [prefixWord, tailWord_6285171, baseEnd_6285171] using wordTrace_append hprefix tailTrace_6285171
  have hstable : (prefixWord ++ tailWord_6285171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285171).length < 2 ^ (prefixWord ++ tailWord_6285171).sum := by decide
  have hdescent : baseEnd_6285171 < baseStart_6285171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285182 : List Nat := [4, 2, 3, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_6285182 : Nat := 118140960795 + 6285182 * 2 ^ 59
def prefixEnd_6285182 : Nat := 4983230072969 + 3 ^ 40 * 6285182 * 2
def baseEnd_6285182 : Nat := 3227319366987133430219981

theorem tailTrace_6285182 : CollatzResearch.WordTrace tailWord_6285182 prefixEnd_6285182 3227319366987133430219981 := by
  unfold tailWord_6285182
  simp only [CollatzResearch.WordTrace]
  refine ⟨28654927539483314058886225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152826280210577674980726533 28654927539483314058886225)
  ·
    refine ⟨21491195654612485544164669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28654927539483314058886225 21491195654612485544164669)
    ·
      refine ⟨8059198370479682079061751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21491195654612485544164669 8059198370479682079061751)
      ·
        refine ⟨12088797555719523118592627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8059198370479682079061751 12088797555719523118592627)
        ·
          refine ⟨18133196333579284677888941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12088797555719523118592627 18133196333579284677888941)
          ·
            refine ⟨6799948625092231754208353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18133196333579284677888941 6799948625092231754208353)
            ·
              refine ⟨5099961468819173815656265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6799948625092231754208353 5099961468819173815656265)
              ·
                refine ⟨3824971101614380361742199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5099961468819173815656265 3824971101614380361742199)
                ·
                  refine ⟨5737456652421570542613299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3824971101614380361742199 5737456652421570542613299)
                  ·
                    refine ⟨8606184978632355813919949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5737456652421570542613299 8606184978632355813919949)
                    ·
                      refine ⟨3227319366987133430219981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8606184978632355813919949 3227319366987133430219981)
                      ·
                        rfl

theorem cell23_6285182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_6285182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285182 prefixEnd_6285182 := by exact prefixLift 6285182
  have htrace : WordTrace (prefixWord ++ tailWord_6285182) baseStart_6285182 baseEnd_6285182 := by
    simpa [prefixWord, tailWord_6285182, baseEnd_6285182] using wordTrace_append hprefix tailTrace_6285182
  have hstable : (prefixWord ++ tailWord_6285182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285182).length < 2 ^ (prefixWord ++ tailWord_6285182).sum := by decide
  have hdescent : baseEnd_6285182 < baseStart_6285182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285194 : List Nat := [3, 1, 2, 4, 2, 2, 1, 8]
def baseStart_6285194 : Nat := 118140960795 + 6285194 * 2 ^ 59
def prefixEnd_6285194 : Nat := 4983230072969 + 3 ^ 40 * 6285194 * 2
def baseEnd_6285194 : Nat := 119530575139073606787775

theorem tailTrace_6285194 : CollatzResearch.WordTrace tailWord_6285194 prefixEnd_6285194 119530575139073606787775 := by
  unfold tailWord_6285194
  simp only [CollatzResearch.WordTrace]
  refine ⟨57309964497955759630131659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152826571994548692347017757 57309964497955759630131659)
  ·
    refine ⟨85964946746933639445197489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57309964497955759630131659 85964946746933639445197489)
    ·
      refine ⟨64473710060200229583898117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85964946746933639445197489 64473710060200229583898117)
      ·
        refine ⟨12088820636287543046980897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64473710060200229583898117 12088820636287543046980897)
        ·
          refine ⟨9066615477215657285235673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12088820636287543046980897 9066615477215657285235673)
          ·
            refine ⟨6799961607911742963926755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9066615477215657285235673 6799961607911742963926755)
            ·
              refine ⟨10199942411867614445890133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6799961607911742963926755 10199942411867614445890133)
              ·
                refine ⟨119530575139073606787775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10199942411867614445890133 119530575139073606787775)
                ·
                  rfl

theorem cell23_6285194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 8].length) (baseStart_6285194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285194 prefixEnd_6285194 := by exact prefixLift 6285194
  have htrace : WordTrace (prefixWord ++ tailWord_6285194) baseStart_6285194 baseEnd_6285194 := by
    simpa [prefixWord, tailWord_6285194, baseEnd_6285194] using wordTrace_append hprefix tailTrace_6285194
  have hstable : (prefixWord ++ tailWord_6285194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285194).length < 2 ^ (prefixWord ++ tailWord_6285194).sum := by decide
  have hdescent : baseEnd_6285194 < baseStart_6285194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285204 : List Nat := [2, 4, 2, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_6285204 : Nat := 118140960795 + 6285204 * 2 ^ 59
def prefixEnd_6285204 : Nat := 4983230072969 + 3 ^ 40 * 6285204 * 2
def baseEnd_6285204 : Nat := 3227330663561532344144879

theorem tailTrace_6285204 : CollatzResearch.WordTrace tailWord_6285204 prefixEnd_6285204 3227330663561532344144879 := by
  unfold tailWord_6285204
  simp only [CollatzResearch.WordTrace]
  refine ⟨114620111360893405114195333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152826815147857873485593777 114620111360893405114195333)
  ·
    refine ⟨21491270880167513458911625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114620111360893405114195333 21491270880167513458911625)
    ·
      refine ⟨16118453160125635094183719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21491270880167513458911625 16118453160125635094183719)
      ·
        refine ⟨24177679740188452641275579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16118453160125635094183719 24177679740188452641275579)
        ·
          refine ⟨36266519610282678961913369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24177679740188452641275579 36266519610282678961913369)
          ·
            refine ⟨27199889707712009221435027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36266519610282678961913369 27199889707712009221435027)
            ·
              refine ⟨40799834561568013832152541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27199889707712009221435027 40799834561568013832152541)
              ·
                refine ⟨15299937960588005187057203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40799834561568013832152541 15299937960588005187057203)
                ·
                  refine ⟨22949906940882007780585805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15299937960588005187057203 22949906940882007780585805)
                  ·
                    refine ⟨8606215102830752917719677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22949906940882007780585805 8606215102830752917719677)
                    ·
                      refine ⟨3227330663561532344144879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8606215102830752917719677 3227330663561532344144879)
                      ·
                        rfl

theorem cell23_6285204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_6285204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285204 prefixEnd_6285204 := by exact prefixLift 6285204
  have htrace : WordTrace (prefixWord ++ tailWord_6285204) baseStart_6285204 baseEnd_6285204 := by
    simpa [prefixWord, tailWord_6285204, baseEnd_6285204] using wordTrace_append hprefix tailTrace_6285204
  have hstable : (prefixWord ++ tailWord_6285204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285204).length < 2 ^ (prefixWord ++ tailWord_6285204).sum := by decide
  have hdescent : baseEnd_6285204 < baseStart_6285204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285237 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 2, 6]
def baseStart_6285237 : Nat := 118140960795 + 6285237 * 2 ^ 59
def prefixEnd_6285237 : Nat := 4983230072969 + 3 ^ 40 * 6285237 * 2
def baseEnd_6285237 : Nat := 1075782536141043571677409

theorem tailTrace_6285237 : CollatzResearch.WordTrace tailWord_6285237 prefixEnd_6285237 1075782536141043571677409 := by
  unfold tailWord_6285237
  simp only [CollatzResearch.WordTrace]
  refine ⟨229241426330667256864341965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152827617553778171242894643 229241426330667256864341965)
  ·
    refine ⟨85965534874000221324128237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229241426330667256864341965 85965534874000221324128237)
    ·
      refine ⟨32237075577750082996548089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85965534874000221324128237 32237075577750082996548089)
      ·
        refine ⟨24177806683312562247411067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32237075577750082996548089 24177806683312562247411067)
        ·
          refine ⟨36266710024968843371116601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24177806683312562247411067 36266710024968843371116601)
          ·
            refine ⟨27200032518726632528337451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36266710024968843371116601 27200032518726632528337451)
            ·
              refine ⟨40800048778089948792506177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27200032518726632528337451 40800048778089948792506177)
              ·
                refine ⟨30600036583567461594379633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40800048778089948792506177 30600036583567461594379633)
                ·
                  refine ⟨22950027437675596195784725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30600036583567461594379633 22950027437675596195784725)
                  ·
                    refine ⟨1075782536141043571677409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22950027437675596195784725 1075782536141043571677409)
                    ·
                      rfl

theorem cell23_6285237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_6285237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285237 prefixEnd_6285237 := by exact prefixLift 6285237
  have htrace : WordTrace (prefixWord ++ tailWord_6285237) baseStart_6285237 baseEnd_6285237 := by
    simpa [prefixWord, tailWord_6285237, baseEnd_6285237] using wordTrace_append hprefix tailTrace_6285237
  have hstable : (prefixWord ++ tailWord_6285237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285237).length < 2 ^ (prefixWord ++ tailWord_6285237).sum := by decide
  have hdescent : baseEnd_6285237 < baseStart_6285237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285347 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 6]
def baseStart_6285347 : Nat := 118140960795 + 6285347 * 2 ^ 59
def prefixEnd_6285347 : Nat := 4983230072969 + 3 ^ 40 * 6285347 * 2
def baseEnd_6285347 : Nat := 3227404091295125284656721

theorem tailTrace_6285347 : CollatzResearch.WordTrace tailWord_6285347 prefixEnd_6285347 3227404091295125284656721 := by
  unfold tailWord_6285347
  simp only [CollatzResearch.WordTrace]
  refine ⟨229245438360268745650846295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152830292240179163767230863 229245438360268745650846295)
  ·
    refine ⟨343868157540403118476269443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229245438360268745650846295 343868157540403118476269443)
    ·
      refine ⟨515802236310604677714404165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343868157540403118476269443 515802236310604677714404165)
      ·
        refine ⟨96712919308238377071450781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 515802236310604677714404165 96712919308238377071450781)
        ·
          refine ⟨36267344740589391401794043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96712919308238377071450781 36267344740589391401794043)
          ·
            refine ⟨54401017110884087102691065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36267344740589391401794043 54401017110884087102691065)
            ·
              refine ⟨40800762833163065327018299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54401017110884087102691065 40800762833163065327018299)
              ·
                refine ⟨61201144249744597990527449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40800762833163065327018299 61201144249744597990527449)
                ·
                  refine ⟨45900858187308448492895587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61201144249744597990527449 45900858187308448492895587)
                  ·
                    refine ⟨68851287280962672739343381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45900858187308448492895587 68851287280962672739343381)
                    ·
                      refine ⟨3227404091295125284656721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68851287280962672739343381 3227404091295125284656721)
                      ·
                        rfl

theorem cell23_6285347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_6285347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285347 prefixEnd_6285347 := by exact prefixLift 6285347
  have htrace : WordTrace (prefixWord ++ tailWord_6285347) baseStart_6285347 baseEnd_6285347 := by
    simpa [prefixWord, tailWord_6285347, baseEnd_6285347] using wordTrace_append hprefix tailTrace_6285347
  have hstable : (prefixWord ++ tailWord_6285347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285347).length < 2 ^ (prefixWord ++ tailWord_6285347).sum := by decide
  have hdescent : baseEnd_6285347 < baseStart_6285347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285352 : List Nat := [2, 1, 5, 3, 2, 1, 2, 2, 5]
def baseStart_6285352 : Nat := 118140960795 + 6285352 * 2 ^ 59
def prefixEnd_6285352 : Nat := 4983230072969 + 3 ^ 40 * 6285352 * 2
def baseEnd_6285352 : Nat := 358600739855377529454911

theorem tailTrace_6285352 : CollatzResearch.WordTrace tailWord_6285352 prefixEnd_6285352 358600739855377529454911 := by
  unfold tailWord_6285352
  simp only [CollatzResearch.WordTrace]
  refine ⟨114622810362625315752389155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152830413816833754336518873 114622810362625315752389155)
  ·
    refine ⟨171934215543937973628583733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114622810362625315752389155 171934215543937973628583733)
    ·
      refine ⟨16118832707244185027679725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171934215543937973628583733 16118832707244185027679725)
      ·
        refine ⟨6044562265216569385379897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16118832707244185027679725 6044562265216569385379897)
        ·
          refine ⟨4533421698912427039034923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6044562265216569385379897 4533421698912427039034923)
          ·
            refine ⟨6800132548368640558552385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4533421698912427039034923 6800132548368640558552385)
            ·
              refine ⟨5100099411276480418914289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6800132548368640558552385 5100099411276480418914289)
              ·
                refine ⟨3825074558457360314185717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5100099411276480418914289 3825074558457360314185717)
                ·
                  refine ⟨358600739855377529454911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3825074558457360314185717 358600739855377529454911)
                  ·
                    rfl

theorem cell23_6285352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 5].length) (baseStart_6285352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285352 prefixEnd_6285352 := by exact prefixLift 6285352
  have htrace : WordTrace (prefixWord ++ tailWord_6285352) baseStart_6285352 baseEnd_6285352 := by
    simpa [prefixWord, tailWord_6285352, baseEnd_6285352] using wordTrace_append hprefix tailTrace_6285352
  have hstable : (prefixWord ++ tailWord_6285352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285352).length < 2 ^ (prefixWord ++ tailWord_6285352).sum := by decide
  have hdescent : baseEnd_6285352 < baseStart_6285352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285411 : List Nat := [1, 1, 1, 5, 1, 1, 2, 4, 2, 3, 2]
def baseStart_6285411 : Nat := 118140960795 + 6285411 * 2 ^ 59
def prefixEnd_6285411 : Nat := 4983230072969 + 3 ^ 40 * 6285411 * 2
def baseEnd_6285411 : Nat := 3227436954057013034256427

theorem tailTrace_6285411 : CollatzResearch.WordTrace tailWord_6285411 prefixEnd_6285411 3227436954057013034256427 := by
  unfold tailWord_6285411
  simp only [CollatzResearch.WordTrace]
  refine ⟨229247772632036884581176087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152831848421357923054117391 229247772632036884581176087)
  ·
    refine ⟨343871658948055326871764131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229247772632036884581176087 343871658948055326871764131)
    ·
      refine ⟨515807488422082990307646197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343871658948055326871764131 515807488422082990307646197)
      ·
        refine ⟨48356952039570280341341831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 515807488422082990307646197 48356952039570280341341831)
        ·
          refine ⟨72535428059355420512012747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48356952039570280341341831 72535428059355420512012747)
          ·
            refine ⟨108803142089033130768019121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72535428059355420512012747 108803142089033130768019121)
            ·
              refine ⟨81602356566774848076014341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108803142089033130768019121 81602356566774848076014341)
              ·
                refine ⟨15300441856270284014252689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81602356566774848076014341 15300441856270284014252689)
                ·
                  refine ⟨11475331392202713010689517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15300441856270284014252689 11475331392202713010689517)
                  ·
                    refine ⟨4303249272076017379008569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11475331392202713010689517 4303249272076017379008569)
                    ·
                      refine ⟨3227436954057013034256427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4303249272076017379008569 3227436954057013034256427)
                      ·
                        rfl

theorem cell23_6285411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_6285411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285411 prefixEnd_6285411 := by exact prefixLift 6285411
  have htrace : WordTrace (prefixWord ++ tailWord_6285411) baseStart_6285411 baseEnd_6285411 := by
    simpa [prefixWord, tailWord_6285411, baseEnd_6285411] using wordTrace_append hprefix tailTrace_6285411
  have hstable : (prefixWord ++ tailWord_6285411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285411).length < 2 ^ (prefixWord ++ tailWord_6285411).sum := by decide
  have hdescent : baseEnd_6285411 < baseStart_6285411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285444 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_6285444 : Nat := 118140960795 + 6285444 * 2 ^ 59
def prefixEnd_6285444 : Nat := 4983230072969 + 3 ^ 40 * 6285444 * 2
def baseEnd_6285444 : Nat := 3227453898918611405143775

theorem tailTrace_6285444 : CollatzResearch.WordTrace tailWord_6285444 prefixEnd_6285444 3227453898918611405143775 := by
  unfold tailWord_6285444
  simp only [CollatzResearch.WordTrace]
  refine ⟨114624488120458665608563693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152832650827278220811418257 114624488120458665608563693)
  ·
    refine ⟨42984183045171999603211385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114624488120458665608563693 42984183045171999603211385)
    ·
      refine ⟨32238137283878999702408539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42984183045171999603211385 32238137283878999702408539)
      ·
        refine ⟨48357205925818499553612809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32238137283878999702408539 48357205925818499553612809)
        ·
          refine ⟨36267904444363874665209607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48357205925818499553612809 36267904444363874665209607)
          ·
            refine ⟨54401856666545811997814411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36267904444363874665209607 54401856666545811997814411)
            ·
              refine ⟨81602784999818717996721617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54401856666545811997814411 81602784999818717996721617)
              ·
                refine ⟨61202088749864038497541213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81602784999818717996721617 61202088749864038497541213)
                ·
                  refine ⟨22950783281199014436577955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61202088749864038497541213 22950783281199014436577955)
                  ·
                    refine ⟨34426174921798521654866933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22950783281199014436577955 34426174921798521654866933)
                    ·
                      refine ⟨3227453898918611405143775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34426174921798521654866933 3227453898918611405143775)
                      ·
                        rfl

theorem cell23_6285444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_6285444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285444 prefixEnd_6285444 := by exact prefixLift 6285444
  have htrace : WordTrace (prefixWord ++ tailWord_6285444) baseStart_6285444 baseEnd_6285444 := by
    simpa [prefixWord, tailWord_6285444, baseEnd_6285444] using wordTrace_append hprefix tailTrace_6285444
  have hstable : (prefixWord ++ tailWord_6285444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285444).length < 2 ^ (prefixWord ++ tailWord_6285444).sum := by decide
  have hdescent : baseEnd_6285444 < baseStart_6285444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285461 : List Nat := [1, 3, 2, 1, 1, 1, 3, 5, 1, 2, 3]
def baseStart_6285461 : Nat := 118140960795 + 6285461 * 2 ^ 59
def prefixEnd_6285461 : Nat := 4983230072969 + 3 ^ 40 * 6285461 * 2
def baseEnd_6285461 : Nat := 3227462628089737838631197

theorem tailTrace_6285461 : CollatzResearch.WordTrace tailWord_6285461 prefixEnd_6285461 3227462628089737838631197 := by
  unfold tailWord_6285461
  simp only [CollatzResearch.WordTrace]
  refine ⟨229249596281855743120496237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152833064187903828746997491 229249596281855743120496237)
  ·
    refine ⟨85968598605695903670186089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229249596281855743120496237 85968598605695903670186089)
    ·
      refine ⟨64476448954271927752639567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85968598605695903670186089 64476448954271927752639567)
      ·
        refine ⟨96714673431407891628959351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64476448954271927752639567 96714673431407891628959351)
        ·
          refine ⟨145072010147111837443439027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96714673431407891628959351 145072010147111837443439027)
          ·
            refine ⟨217608015220667756165158541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145072010147111837443439027 217608015220667756165158541)
            ·
              refine ⟨81603005707750408561934453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217608015220667756165158541 81603005707750408561934453)
              ·
                refine ⟨7650281785101600802681355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81603005707750408561934453 7650281785101600802681355)
                ·
                  refine ⟨11475422677652401204022033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7650281785101600802681355 11475422677652401204022033)
                  ·
                    refine ⟨8606567008239300903016525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11475422677652401204022033 8606567008239300903016525)
                    ·
                      refine ⟨3227462628089737838631197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8606567008239300903016525 3227462628089737838631197)
                      ·
                        rfl

theorem cell23_6285461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_6285461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285461 prefixEnd_6285461 := by exact prefixLift 6285461
  have htrace : WordTrace (prefixWord ++ tailWord_6285461) baseStart_6285461 baseEnd_6285461 := by
    simpa [prefixWord, tailWord_6285461, baseEnd_6285461] using wordTrace_append hprefix tailTrace_6285461
  have hstable : (prefixWord ++ tailWord_6285461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285461).length < 2 ^ (prefixWord ++ tailWord_6285461).sum := by decide
  have hdescent : baseEnd_6285461 < baseStart_6285461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285485 : List Nat := [1, 5, 2, 1, 2, 1, 4, 1, 2, 4]
def baseStart_6285485 : Nat := 118140960795 + 6285485 * 2 ^ 59
def prefixEnd_6285485 : Nat := 4983230072969 + 3 ^ 40 * 6285485 * 2
def baseEnd_6285485 : Nat := 1075824983875148581577029

theorem tailTrace_6285485 : CollatzResearch.WordTrace tailWord_6285485 prefixEnd_6285485 1075824983875148581577029 := by
  unfold tailWord_6285485
  simp only [CollatzResearch.WordTrace]
  refine ⟨229250471633768795219369909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152833647755845863479579939 229250471633768795219369909)
  ·
    refine ⟨21492231715665824551815929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229250471633768795219369909 21492231715665824551815929)
    ·
      refine ⟨16119173786749368413861947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21492231715665824551815929 16119173786749368413861947)
      ·
        refine ⟨24178760680124052620792921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16119173786749368413861947 24178760680124052620792921)
        ·
          refine ⟨18134070510093039465594691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24178760680124052620792921 18134070510093039465594691)
          ·
            refine ⟨27201105765139559198392037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18134070510093039465594691 27201105765139559198392037)
            ·
              refine ⟨5100207330963667349698507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27201105765139559198392037 5100207330963667349698507)
              ·
                refine ⟨7650310996445501024547761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5100207330963667349698507 7650310996445501024547761)
                ·
                  refine ⟨5737733247334125768410821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7650310996445501024547761 5737733247334125768410821)
                  ·
                    refine ⟨1075824983875148581577029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5737733247334125768410821 1075824983875148581577029)
                    ·
                      rfl

theorem cell23_6285485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_6285485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285485 prefixEnd_6285485 := by exact prefixLift 6285485
  have htrace : WordTrace (prefixWord ++ tailWord_6285485) baseStart_6285485 baseEnd_6285485 := by
    simpa [prefixWord, tailWord_6285485, baseEnd_6285485] using wordTrace_append hprefix tailTrace_6285485
  have hstable : (prefixWord ++ tailWord_6285485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285485).length < 2 ^ (prefixWord ++ tailWord_6285485).sum := by decide
  have hdescent : baseEnd_6285485 < baseStart_6285485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285492 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_6285492 : Nat := 118140960795 + 6285492 * 2 ^ 59
def prefixEnd_6285492 : Nat := 4983230072969 + 3 ^ 40 * 6285492 * 2
def baseEnd_6285492 : Nat := 3227478545990027217343555

theorem tailTrace_6285492 : CollatzResearch.WordTrace tailWord_6285492 prefixEnd_6285492 3227478545990027217343555 := by
  unfold tailWord_6285492
  simp only [CollatzResearch.WordTrace]
  refine ⟨114625363472371717707437365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152833817963162290276583153 114625363472371717707437365)
  ·
    refine ⟨10746127825534848535072253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114625363472371717707437365 10746127825534848535072253)
    ·
      refine ⟨4029797934575568200652095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10746127825534848535072253 4029797934575568200652095)
      ·
        refine ⟨6044696901863352300978143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4029797934575568200652095 6044696901863352300978143)
        ·
          refine ⟨9067045352795028451467215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6044696901863352300978143 9067045352795028451467215)
          ·
            refine ⟨13600568029192542677200823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9067045352795028451467215 13600568029192542677200823)
            ·
              refine ⟨20400852043788814015801235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13600568029192542677200823 20400852043788814015801235)
              ·
                refine ⟨30601278065683221023701853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20400852043788814015801235 30601278065683221023701853)
                ·
                  refine ⟨11475479274631207883888195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30601278065683221023701853 11475479274631207883888195)
                  ·
                    refine ⟨17213218911946811825832293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11475479274631207883888195 17213218911946811825832293)
                    ·
                      refine ⟨3227478545990027217343555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17213218911946811825832293 3227478545990027217343555)
                      ·
                        rfl

theorem cell23_6285492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_6285492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285492 prefixEnd_6285492 := by exact prefixLift 6285492
  have htrace : WordTrace (prefixWord ++ tailWord_6285492) baseStart_6285492 baseEnd_6285492 := by
    simpa [prefixWord, tailWord_6285492, baseEnd_6285492] using wordTrace_append hprefix tailTrace_6285492
  have hstable : (prefixWord ++ tailWord_6285492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285492).length < 2 ^ (prefixWord ++ tailWord_6285492).sum := by decide
  have hdescent : baseEnd_6285492 < baseStart_6285492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285508 : List Nat := [2, 3, 3, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_6285508 : Nat := 118140960795 + 6285508 * 2 ^ 59
def prefixEnd_6285508 : Nat := 4983230072969 + 3 ^ 40 * 6285508 * 2
def baseEnd_6285508 : Nat := 3227486761680499154743481

theorem tailTrace_6285508 : CollatzResearch.WordTrace tailWord_6285508 prefixEnd_6285508 3227486761680499154743481 := by
  unfold tailWord_6285508
  simp only [CollatzResearch.WordTrace]
  refine ⟨114625655256342735073728589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152834207008456980098304785 114625655256342735073728589)
  ·
    refine ⟨42984620721128525652648221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114625655256342735073728589 42984620721128525652648221)
    ·
      refine ⟨16119232770423197119743083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42984620721128525652648221 16119232770423197119743083)
      ·
        refine ⟨24178849155634795679614625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16119232770423197119743083 24178849155634795679614625)
        ·
          refine ⟨18134136866726096759710969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24178849155634795679614625 18134136866726096759710969)
          ·
            refine ⟨13600602650044572569783227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18134136866726096759710969 13600602650044572569783227)
            ·
              refine ⟨20400903975066858854674841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13600602650044572569783227 20400903975066858854674841)
              ·
                refine ⟨15300677981300144141006131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20400903975066858854674841 15300677981300144141006131)
                ·
                  refine ⟨22951016971950216211509197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15300677981300144141006131 22951016971950216211509197)
                  ·
                    refine ⟨8606631364481331079315949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22951016971950216211509197 8606631364481331079315949)
                    ·
                      refine ⟨3227486761680499154743481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8606631364481331079315949 3227486761680499154743481)
                      ·
                        rfl

theorem cell23_6285508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_6285508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285508 prefixEnd_6285508 := by exact prefixLift 6285508
  have htrace : WordTrace (prefixWord ++ tailWord_6285508) baseStart_6285508 baseEnd_6285508 := by
    simpa [prefixWord, tailWord_6285508, baseEnd_6285508] using wordTrace_append hprefix tailTrace_6285508
  have hstable : (prefixWord ++ tailWord_6285508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285508).length < 2 ^ (prefixWord ++ tailWord_6285508).sum := by decide
  have hdescent : baseEnd_6285508 < baseStart_6285508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285526 : List Nat := [5, 2, 1, 2, 1, 1, 4, 2, 1, 2, 2]
def baseStart_6285526 : Nat := 118140960795 + 6285526 * 2 ^ 59
def prefixEnd_6285526 : Nat := 4983230072969 + 3 ^ 40 * 6285526 * 2
def baseEnd_6285526 : Nat := 3227496004332280084318399

theorem tailTrace_6285526 : CollatzResearch.WordTrace tailWord_6285526 prefixEnd_6285526 3227496004332280084318399 := by
  unfold tailWord_6285526
  simp only [CollatzResearch.WordTrace]
  refine ⟨14328247939163766201350777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152834644684413506147741621 14328247939163766201350777)
  ·
    refine ⟨10746185954372824651013083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14328247939163766201350777 10746185954372824651013083)
    ·
      refine ⟨16119278931559236976519625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10746185954372824651013083 16119278931559236976519625)
      ·
        refine ⟨12089459198669427732389719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16119278931559236976519625 12089459198669427732389719)
        ·
          refine ⟨18134188798004141598584579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12089459198669427732389719 18134188798004141598584579)
          ·
            refine ⟨27201283197006212397876869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18134188798004141598584579 27201283197006212397876869)
            ·
              refine ⟨5100240599438664824601913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27201283197006212397876869 5100240599438664824601913)
              ·
                refine ⟨3825180449578998618451435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5100240599438664824601913 3825180449578998618451435)
                ·
                  refine ⟨5737770674368497927677153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3825180449578998618451435 5737770674368497927677153)
                  ·
                    refine ⟨4303328005776373445757865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5737770674368497927677153 4303328005776373445757865)
                    ·
                      refine ⟨3227496004332280084318399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4303328005776373445757865 3227496004332280084318399)
                      ·
                        rfl

theorem cell23_6285526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_6285526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285526 prefixEnd_6285526 := by exact prefixLift 6285526
  have htrace : WordTrace (prefixWord ++ tailWord_6285526) baseStart_6285526 baseEnd_6285526 := by
    simpa [prefixWord, tailWord_6285526, baseEnd_6285526] using wordTrace_append hprefix tailTrace_6285526
  have hstable : (prefixWord ++ tailWord_6285526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285526).length < 2 ^ (prefixWord ++ tailWord_6285526).sum := by decide
  have hdescent : baseEnd_6285526 < baseStart_6285526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285541 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 2, 6]
def baseStart_6285541 : Nat := 118140960795 + 6285541 * 2 ^ 59
def prefixEnd_6285541 : Nat := 4983230072969 + 3 ^ 40 * 6285541 * 2
def baseEnd_6285541 : Nat := 1075834568847365841876943

theorem tailTrace_6285541 : CollatzResearch.WordTrace tailWord_6285541 prefixEnd_6285541 1075834568847365841876943 := by
  unfold tailWord_6285541
  simp only [CollatzResearch.WordTrace]
  refine ⟨229252514121565916783408477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152835009414377277855605651 229252514121565916783408477)
  ·
    refine ⟨85969692795587218793778179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229252514121565916783408477 85969692795587218793778179)
    ·
      refine ⟨128954539193380828190667269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85969692795587218793778179 128954539193380828190667269)
      ·
        refine ⟨24178976098758905285750113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128954539193380828190667269 24178976098758905285750113)
        ·
          refine ⟨18134232074069178964312585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24178976098758905285750113 18134232074069178964312585)
          ·
            refine ⟨13600674055551884223234439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18134232074069178964312585 13600674055551884223234439)
            ·
              refine ⟨20401011083327826334851659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13600674055551884223234439 20401011083327826334851659)
              ·
                refine ⟨30601516624991739502277489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20401011083327826334851659 30601516624991739502277489)
                ·
                  refine ⟨22951137468743804626708117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30601516624991739502277489 22951137468743804626708117)
                  ·
                    refine ⟨1075834568847365841876943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22951137468743804626708117 1075834568847365841876943)
                    ·
                      rfl

theorem cell23_6285541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_6285541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285541 prefixEnd_6285541 := by exact prefixLift 6285541
  have htrace : WordTrace (prefixWord ++ tailWord_6285541) baseStart_6285541 baseEnd_6285541 := by
    simpa [prefixWord, tailWord_6285541, baseEnd_6285541] using wordTrace_append hprefix tailTrace_6285541
  have hstable : (prefixWord ++ tailWord_6285541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285541).length < 2 ^ (prefixWord ++ tailWord_6285541).sum := by decide
  have hdescent : baseEnd_6285541 < baseStart_6285541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285548 : List Nat := [2, 2, 1, 1, 2, 3, 4, 1, 1, 4, 2]
def baseStart_6285548 : Nat := 118140960795 + 6285548 * 2 ^ 59
def prefixEnd_6285548 : Nat := 4983230072969 + 3 ^ 40 * 6285548 * 2
def baseEnd_6285548 : Nat := 3227507300906678998243297

theorem tailTrace_6285548 : CollatzResearch.WordTrace tailWord_6285548 prefixEnd_6285548 3227507300906678998243297 := by
  unfold tailWord_6285548
  simp only [CollatzResearch.WordTrace]
  refine ⟨114626384716270278489456649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152835179621693704652608865 114626384716270278489456649)
  ·
    refine ⟨85969788537202708867092487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114626384716270278489456649 85969788537202708867092487)
    ·
      refine ⟨128954682805804063300638731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85969788537202708867092487 128954682805804063300638731)
      ·
        refine ⟨193432024208706094950958097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128954682805804063300638731 193432024208706094950958097)
        ·
          refine ⟨145074018156529571213218573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193432024208706094950958097 145074018156529571213218573)
          ·
            refine ⟨54402756808698589204956965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145074018156529571213218573 54402756808698589204956965)
            ·
              refine ⟨10200516901630985475929431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54402756808698589204956965 10200516901630985475929431)
              ·
                refine ⟨15300775352446478213894147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10200516901630985475929431 15300775352446478213894147)
                ·
                  refine ⟨22951163028669717320841221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15300775352446478213894147 22951163028669717320841221)
                  ·
                    refine ⟨4303343067875571997657729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22951163028669717320841221 4303343067875571997657729)
                    ·
                      refine ⟨3227507300906678998243297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4303343067875571997657729 3227507300906678998243297)
                      ·
                        rfl

theorem cell23_6285548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 4, 2].length) (baseStart_6285548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285548 prefixEnd_6285548 := by exact prefixLift 6285548
  have htrace : WordTrace (prefixWord ++ tailWord_6285548) baseStart_6285548 baseEnd_6285548 := by
    simpa [prefixWord, tailWord_6285548, baseEnd_6285548] using wordTrace_append hprefix tailTrace_6285548
  have hstable : (prefixWord ++ tailWord_6285548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285548).length < 2 ^ (prefixWord ++ tailWord_6285548).sum := by decide
  have hdescent : baseEnd_6285548 < baseStart_6285548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285621 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_6285621 : Nat := 118140960795 + 6285621 * 2 ^ 59
def prefixEnd_6285621 : Nat := 4983230072969 + 3 ^ 40 * 6285621 * 2
def baseEnd_6285621 : Nat := 3227544784994457212630461

theorem tailTrace_6285621 : CollatzResearch.WordTrace tailWord_6285621 prefixEnd_6285621 3227544784994457212630461 := by
  unfold tailWord_6285621
  simp only [CollatzResearch.WordTrace]
  refine ⟨229255431961276090446320717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152836954640850726964213811 229255431961276090446320717)
  ·
    refine ⟨85970786985478533917370269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229255431961276090446320717 85970786985478533917370269)
    ·
      refine ⟨32239045119554450219013851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85970786985478533917370269 32239045119554450219013851)
      ·
        refine ⟨48358567679331675328520777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32239045119554450219013851 48358567679331675328520777)
        ·
          refine ⟨36268925759498756496390583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48358567679331675328520777 36268925759498756496390583)
          ·
            refine ⟨54403388639248134744585875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36268925759498756496390583 54403388639248134744585875)
            ·
              refine ⟨81605082958872202116878813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54403388639248134744585875 81605082958872202116878813)
              ·
                refine ⟨30601906109577075793829555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81605082958872202116878813 30601906109577075793829555)
                ·
                  refine ⟨45902859164365613690744333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30601906109577075793829555 45902859164365613690744333)
                  ·
                    refine ⟨17213572186637105134029125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45902859164365613690744333 17213572186637105134029125)
                    ·
                      refine ⟨3227544784994457212630461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17213572186637105134029125 3227544784994457212630461)
                      ·
                        rfl

theorem cell23_6285621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_6285621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285621 prefixEnd_6285621 := by exact prefixLift 6285621
  have htrace : WordTrace (prefixWord ++ tailWord_6285621) baseStart_6285621 baseEnd_6285621 := by
    simpa [prefixWord, tailWord_6285621, baseEnd_6285621] using wordTrace_append hprefix tailTrace_6285621
  have hstable : (prefixWord ++ tailWord_6285621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285621).length < 2 ^ (prefixWord ++ tailWord_6285621).sum := by decide
  have hdescent : baseEnd_6285621 < baseStart_6285621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285648 : List Nat := [2, 1, 1, 1, 1, 6, 3, 1, 3, 4]
def baseStart_6285648 : Nat := 118140960795 + 6285648 * 2 ^ 59
def prefixEnd_6285648 : Nat := 4983230072969 + 3 ^ 40 * 6285648 * 2
def baseEnd_6285648 : Nat := 1075852882990709535664279

theorem tailTrace_6285648 : CollatzResearch.WordTrace tailWord_6285648 prefixEnd_6285648 1075852882990709535664279 := by
  unfold tailWord_6285648
  simp only [CollatzResearch.WordTrace]
  refine ⟨114628208366089137028776799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152837611154785516038369065 114628208366089137028776799)
  ·
    refine ⟨171942312549133705543165199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114628208366089137028776799 171942312549133705543165199)
    ·
      refine ⟨257913468823700558314747799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171942312549133705543165199 257913468823700558314747799)
      ·
        refine ⟨386870203235550837472121699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257913468823700558314747799 386870203235550837472121699)
        ·
          refine ⟨580305304853326256208182549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386870203235550837472121699 580305304853326256208182549)
          ·
            refine ⟨27201811164999668259758557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 580305304853326256208182549 27201811164999668259758557)
            ·
              refine ⟨10200679186874875597409459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27201811164999668259758557 10200679186874875597409459)
              ·
                refine ⟨15301018780312313396114189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10200679186874875597409459 15301018780312313396114189)
                ·
                  refine ⟨5737882042617117523542821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15301018780312313396114189 5737882042617117523542821)
                  ·
                    refine ⟨1075852882990709535664279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5737882042617117523542821 1075852882990709535664279)
                    ·
                      rfl

theorem cell23_6285648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 3, 4].length) (baseStart_6285648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285648 prefixEnd_6285648 := by exact prefixLift 6285648
  have htrace : WordTrace (prefixWord ++ tailWord_6285648) baseStart_6285648 baseEnd_6285648 := by
    simpa [prefixWord, tailWord_6285648, baseEnd_6285648] using wordTrace_append hprefix tailTrace_6285648
  have hstable : (prefixWord ++ tailWord_6285648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285648).length < 2 ^ (prefixWord ++ tailWord_6285648).sum := by decide
  have hdescent : baseEnd_6285648 < baseStart_6285648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285699 : List Nat := [1, 1, 1, 3, 6, 2, 2, 2, 1, 4]
def baseStart_6285699 : Nat := 118140960795 + 6285699 * 2 ^ 59
def prefixEnd_6285699 : Nat := 4983230072969 + 3 ^ 40 * 6285699 * 2
def baseEnd_6285699 : Nat := 1075861612161835969151701

theorem tailTrace_6285699 : CollatzResearch.WordTrace tailWord_6285699 prefixEnd_6285699 1075861612161835969151701 := by
  unfold tailWord_6285699
  simp only [CollatzResearch.WordTrace]
  refine ⟨229258276854993509767660151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152838851236662339845106767 229258276854993509767660151)
  ·
    refine ⟨343887415282490264651490227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229258276854993509767660151 343887415282490264651490227)
    ·
      refine ⟨515831122923735396977235341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343887415282490264651490227 515831122923735396977235341)
      ·
        refine ⟨193436671096400773866463253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 515831122923735396977235341 193436671096400773866463253)
        ·
          refine ⟨9067343957643786274990465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 193436671096400773866463253 9067343957643786274990465)
          ·
            refine ⟨6800507968232839706242849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9067343957643786274990465 6800507968232839706242849)
            ·
              refine ⟨5100380976174629779682137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6800507968232839706242849 5100380976174629779682137)
              ·
                refine ⟨3825285732130972334761603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5100380976174629779682137 3825285732130972334761603)
                ·
                  refine ⟨5737928598196458502142405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3825285732130972334761603 5737928598196458502142405)
                  ·
                    refine ⟨1075861612161835969151701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5737928598196458502142405 1075861612161835969151701)
                    ·
                      rfl

theorem cell23_6285699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 1, 4].length) (baseStart_6285699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285699 prefixEnd_6285699 := by exact prefixLift 6285699
  have htrace : WordTrace (prefixWord ++ tailWord_6285699) baseStart_6285699 baseEnd_6285699 := by
    simpa [prefixWord, tailWord_6285699, baseEnd_6285699] using wordTrace_append hprefix tailTrace_6285699
  have hstable : (prefixWord ++ tailWord_6285699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285699).length < 2 ^ (prefixWord ++ tailWord_6285699).sum := by decide
  have hdescent : baseEnd_6285699 < baseStart_6285699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285728 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 4]
def baseStart_6285728 : Nat := 118140960795 + 6285728 * 2 ^ 59
def prefixEnd_6285728 : Nat := 4983230072969 + 3 ^ 40 * 6285728 * 2
def baseEnd_6285728 : Nat := 3227599727424488293992469

theorem tailTrace_6285728 : CollatzResearch.WordTrace tailWord_6285728 prefixEnd_6285728 3227599727424488293992469 := by
  unfold tailWord_6285728
  simp only [CollatzResearch.WordTrace]
  refine ⟨114629667285944223860232919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152839556381258965146977225 114629667285944223860232919)
  ·
    refine ⟨171944500928916335790349379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114629667285944223860232919 171944500928916335790349379)
    ·
      refine ⟨257916751393374503685524069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171944500928916335790349379 257916751393374503685524069)
      ·
        refine ⟨48359390886257719441035763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257916751393374503685524069 48359390886257719441035763)
        ·
          refine ⟨72539086329386579161553645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48359390886257719441035763 72539086329386579161553645)
          ·
            refine ⟨27202157373519967185582617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72539086329386579161553645 27202157373519967185582617)
            ·
              refine ⟨20401618030139975389186963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27202157373519967185582617 20401618030139975389186963)
              ·
                refine ⟨30602427045209963083780445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20401618030139975389186963 30602427045209963083780445)
                ·
                  refine ⟨11475910141953736156417667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30602427045209963083780445 11475910141953736156417667)
                  ·
                    refine ⟨17213865212930604234626501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11475910141953736156417667 17213865212930604234626501)
                    ·
                      refine ⟨3227599727424488293992469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17213865212930604234626501 3227599727424488293992469)
                      ·
                        rfl

theorem cell23_6285728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_6285728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285728 prefixEnd_6285728 := by exact prefixLift 6285728
  have htrace : WordTrace (prefixWord ++ tailWord_6285728) baseStart_6285728 baseEnd_6285728 := by
    simpa [prefixWord, tailWord_6285728, baseEnd_6285728] using wordTrace_append hprefix tailTrace_6285728
  have hstable : (prefixWord ++ tailWord_6285728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285728).length < 2 ^ (prefixWord ++ tailWord_6285728).sum := by decide
  have hdescent : baseEnd_6285728 < baseStart_6285728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285745 : List Nat := [1, 2, 2, 4, 1, 3, 1, 3, 1, 1, 4]
def baseStart_6285745 : Nat := 118140960795 + 6285745 * 2 ^ 59
def prefixEnd_6285745 : Nat := 4983230072969 + 3 ^ 40 * 6285745 * 2
def baseEnd_6285745 : Nat := 3227608456595614727479891

theorem tailTrace_6285745 : CollatzResearch.WordTrace tailWord_6285745 prefixEnd_6285745 3227608456595614727479891 := by
  unfold tailWord_6285745
  simp only [CollatzResearch.WordTrace]
  refine ⟨229259954612826859623834689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152839969741884573082556459 229259954612826859623834689)
  ·
    refine ⟨171944965959620144717876017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229259954612826859623834689 171944965959620144717876017)
    ·
      refine ⟨128958724469715108538407013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171944965959620144717876017 128958724469715108538407013)
      ·
        refine ⟨24179760838071582850951315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128958724469715108538407013 24179760838071582850951315)
        ·
          refine ⟨36269641257107374276426973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24179760838071582850951315 36269641257107374276426973)
          ·
            refine ⟨13601115471415265353660115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36269641257107374276426973 13601115471415265353660115)
            ·
              refine ⟨20401673207122898030490173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13601115471415265353660115 20401673207122898030490173)
              ·
                refine ⟨7650627452671086761433815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20401673207122898030490173 7650627452671086761433815)
                ·
                  refine ⟨11475941179006630142150723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7650627452671086761433815 11475941179006630142150723)
                  ·
                    refine ⟨17213911768509945213226085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11475941179006630142150723 17213911768509945213226085)
                    ·
                      refine ⟨3227608456595614727479891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17213911768509945213226085 3227608456595614727479891)
                      ·
                        rfl

theorem cell23_6285745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_6285745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285745 prefixEnd_6285745 := by exact prefixLift 6285745
  have htrace : WordTrace (prefixWord ++ tailWord_6285745) baseStart_6285745 baseEnd_6285745 := by
    simpa [prefixWord, tailWord_6285745, baseEnd_6285745] using wordTrace_append hprefix tailTrace_6285745
  have hstable : (prefixWord ++ tailWord_6285745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285745).length < 2 ^ (prefixWord ++ tailWord_6285745).sum := by decide
  have hdescent : baseEnd_6285745 < baseStart_6285745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285751 : List Nat := [1, 1, 3, 1, 3, 4, 10]
def baseStart_6285751 : Nat := 118140960795 + 6285751 * 2 ^ 59
def prefixEnd_6285751 : Nat := 4983230072969 + 3 ^ 40 * 6285751 * 2
def baseEnd_6285751 : Nat := 39847056018265946963023

theorem tailTrace_6285751 : CollatzResearch.WordTrace tailWord_6285751 prefixEnd_6285751 39847056018265946963023 := by
  unfold tailWord_6285751
  simp only [CollatzResearch.WordTrace]
  refine ⟨229260173450805122648553107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152840115633870081765702071 229260173450805122648553107)
  ·
    refine ⟨343890260176207683972829661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229260173450805122648553107 343890260176207683972829661)
    ·
      refine ⟨128958847566077881489811123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343890260176207683972829661 128958847566077881489811123)
      ·
        refine ⟨193438271349116822234716685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128958847566077881489811123 193438271349116822234716685)
        ·
          refine ⟨72539351755918808338018757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193438271349116822234716685 72539351755918808338018757)
          ·
            refine ⟨13601128454234776563378517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72539351755918808338018757 13601128454234776563378517)
            ·
              refine ⟨39847056018265946963023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13601128454234776563378517 39847056018265946963023)
              ·
                rfl

theorem cell23_6285751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 10].length) (baseStart_6285751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285751 prefixEnd_6285751 := by exact prefixLift 6285751
  have htrace : WordTrace (prefixWord ++ tailWord_6285751) baseStart_6285751 baseEnd_6285751 := by
    simpa [prefixWord, tailWord_6285751, baseEnd_6285751] using wordTrace_append hprefix tailTrace_6285751
  have hstable : (prefixWord ++ tailWord_6285751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285751).length < 2 ^ (prefixWord ++ tailWord_6285751).sum := by decide
  have hdescent : baseEnd_6285751 < baseStart_6285751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285758 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_6285758 : Nat := 118140960795 + 6285758 * 2 ^ 59
def prefixEnd_6285758 : Nat := 4983230072969 + 3 ^ 40 * 6285758 * 2
def baseEnd_6285758 : Nat := 3227615131844123176617331

theorem tailTrace_6285758 : CollatzResearch.WordTrace tailWord_6285758 prefixEnd_6285758 3227615131844123176617331 := by
  unfold tailWord_6285758
  simp only [CollatzResearch.WordTrace]
  refine ⟨28657553595222470355507241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152840285841186508562705285 28657553595222470355507241)
  ·
    refine ⟨21493165196416852766630431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28657553595222470355507241 21493165196416852766630431)
    ·
      refine ⟨32239747794625279149945647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21493165196416852766630431 32239747794625279149945647)
      ·
        refine ⟨48359621691937918724918471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32239747794625279149945647 48359621691937918724918471)
        ·
          refine ⟨72539432537906878087377707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48359621691937918724918471 72539432537906878087377707)
          ·
            refine ⟨108809148806860317131066561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72539432537906878087377707 108809148806860317131066561)
            ·
              refine ⟨81606861605145237848299921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108809148806860317131066561 81606861605145237848299921)
              ·
                refine ⟨61205146203858928386224941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81606861605145237848299921 61205146203858928386224941)
                ·
                  refine ⟨22951929826447098144834353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61205146203858928386224941 22951929826447098144834353)
                  ·
                    refine ⟨17213947369835323608625765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22951929826447098144834353 17213947369835323608625765)
                    ·
                      refine ⟨3227615131844123176617331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17213947369835323608625765 3227615131844123176617331)
                      ·
                        rfl

theorem cell23_6285758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_6285758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285758 prefixEnd_6285758 := by exact prefixLift 6285758
  have htrace : WordTrace (prefixWord ++ tailWord_6285758) baseStart_6285758 baseEnd_6285758 := by
    simpa [prefixWord, tailWord_6285758, baseEnd_6285758] using wordTrace_append hprefix tailTrace_6285758
  have hstable : (prefixWord ++ tailWord_6285758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285758).length < 2 ^ (prefixWord ++ tailWord_6285758).sum := by decide
  have hdescent : baseEnd_6285758 < baseStart_6285758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285772 : List Nat := [2, 2, 1, 4, 4, 1, 1, 1, 1, 6]
def baseStart_6285772 : Nat := 118140960795 + 6285772 * 2 ^ 59
def prefixEnd_6285772 : Nat := 4983230072969 + 3 ^ 40 * 6285772 * 2
def baseEnd_6285772 : Nat := 1075874106857762040614089

theorem tailTrace_6285772 : CollatzResearch.WordTrace tailWord_6285772 prefixEnd_6285772 1075874106857762040614089 := by
  unfold tailWord_6285772
  simp only [CollatzResearch.WordTrace]
  refine ⟨114630469691864521617533785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152840626255819362156711713 114630469691864521617533785)
  ·
    refine ⟨85972852268898391213150339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114630469691864521617533785 85972852268898391213150339)
    ·
      refine ⟨128959278403347586819725509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85972852268898391213150339 128959278403347586819725509)
      ·
        refine ⟨24179864700627672528698533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128959278403347586819725509 24179864700627672528698533)
        ·
          refine ⟨4533724631367688599130975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24179864700627672528698533 4533724631367688599130975)
          ·
            refine ⟨6800586947051532898696463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4533724631367688599130975 6800586947051532898696463)
            ·
              refine ⟨10200880420577299348044695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6800586947051532898696463 10200880420577299348044695)
              ·
                refine ⟨15301320630865949022067043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10200880420577299348044695 15301320630865949022067043)
                ·
                  refine ⟨22951980946298923533100565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15301320630865949022067043 22951980946298923533100565)
                  ·
                    refine ⟨1075874106857762040614089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22951980946298923533100565 1075874106857762040614089)
                    ·
                      rfl

theorem cell23_6285772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 1, 6].length) (baseStart_6285772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285772 prefixEnd_6285772 := by exact prefixLift 6285772
  have htrace : WordTrace (prefixWord ++ tailWord_6285772) baseStart_6285772 baseEnd_6285772 := by
    simpa [prefixWord, tailWord_6285772, baseEnd_6285772] using wordTrace_append hprefix tailTrace_6285772
  have hstable : (prefixWord ++ tailWord_6285772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285772).length < 2 ^ (prefixWord ++ tailWord_6285772).sum := by decide
  have hdescent : baseEnd_6285772 < baseStart_6285772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285813 : List Nat := [1, 3, 5, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_6285813 : Nat := 118140960795 + 6285813 * 2 ^ 59
def prefixEnd_6285813 : Nat := 4983230072969 + 3 ^ 40 * 6285813 * 2
def baseEnd_6285813 : Nat := 3227643373280120461429579

theorem tailTrace_6285813 : CollatzResearch.WordTrace tailWord_6285813 prefixEnd_6285813 3227643373280120461429579 := by
  unfold tailWord_6285813
  simp only [CollatzResearch.WordTrace]
  refine ⟨229262434776580507237310093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152841623184387004824873395 229262434776580507237310093)
  ·
    refine ⟨85973413041217690213991285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229262434776580507237310093 85973413041217690213991285)
    ·
      refine ⟨8060007472614158457561683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85973413041217690213991285 8060007472614158457561683)
      ·
        refine ⟨12090011208921237686342525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8060007472614158457561683 12090011208921237686342525)
        ·
          refine ⟨4533754203345464132378447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12090011208921237686342525 4533754203345464132378447)
          ·
            refine ⟨6800631305018196198567671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4533754203345464132378447 6800631305018196198567671)
            ·
              refine ⟨10200946957527294297851507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6800631305018196198567671 10200946957527294297851507)
              ·
                refine ⟨15301420436290941446777261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10200946957527294297851507 15301420436290941446777261)
                ·
                  refine ⟨5738032663609103042541473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15301420436290941446777261 5738032663609103042541473)
                  ·
                    refine ⟨4303524497706827281906105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5738032663609103042541473 4303524497706827281906105)
                    ·
                      refine ⟨3227643373280120461429579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4303524497706827281906105 3227643373280120461429579)
                      ·
                        rfl

theorem cell23_6285813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_6285813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285813 prefixEnd_6285813 := by exact prefixLift 6285813
  have htrace : WordTrace (prefixWord ++ tailWord_6285813) baseStart_6285813 baseEnd_6285813 := by
    simpa [prefixWord, tailWord_6285813, baseEnd_6285813] using wordTrace_append hprefix tailTrace_6285813
  have hstable : (prefixWord ++ tailWord_6285813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285813).length < 2 ^ (prefixWord ++ tailWord_6285813).sum := by decide
  have hdescent : baseEnd_6285813 < baseStart_6285813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285852 : List Nat := [2, 2, 3, 1, 2, 3, 1, 2, 1, 4, 2]
def baseStart_6285852 : Nat := 118140960795 + 6285852 * 2 ^ 59
def prefixEnd_6285852 : Nat := 4983230072969 + 3 ^ 40 * 6285852 * 2
def baseEnd_6285852 : Nat := 3227663399025645808841899

theorem tailTrace_6285852 : CollatzResearch.WordTrace tailWord_6285852 prefixEnd_6285852 3227663399025645808841899 := by
  unfold tailWord_6285852
  simp only [CollatzResearch.WordTrace]
  refine ⟨114631928611719608448989905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152842571482292811265319873 114631928611719608448989905)
  ·
    refine ⟨85973946458789706336742429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114631928611719608448989905 85973946458789706336742429)
    ·
      refine ⟨32240229922046139876278411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85973946458789706336742429 32240229922046139876278411)
      ·
        refine ⟨48360344883069209814417617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32240229922046139876278411 48360344883069209814417617)
        ·
          refine ⟨36270258662301907360813213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48360344883069209814417617 36270258662301907360813213)
          ·
            refine ⟨13601346998363215260304955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36270258662301907360813213 13601346998363215260304955)
            ·
              refine ⟨20402020497544822890457433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13601346998363215260304955 20402020497544822890457433)
              ·
                refine ⟨15301515373158617167843075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20402020497544822890457433 15301515373158617167843075)
                ·
                  refine ⟨22952273059737925751764613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15301515373158617167843075 22952273059737925751764613)
                  ·
                    refine ⟨4303551198700861078455865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22952273059737925751764613 4303551198700861078455865)
                    ·
                      refine ⟨3227663399025645808841899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4303551198700861078455865 3227663399025645808841899)
                      ·
                        rfl

theorem cell23_6285852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_6285852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285852 prefixEnd_6285852 := by exact prefixLift 6285852
  have htrace : WordTrace (prefixWord ++ tailWord_6285852) baseStart_6285852 baseEnd_6285852 := by
    simpa [prefixWord, tailWord_6285852, baseEnd_6285852] using wordTrace_append hprefix tailTrace_6285852
  have hstable : (prefixWord ++ tailWord_6285852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285852).length < 2 ^ (prefixWord ++ tailWord_6285852).sum := by decide
  have hdescent : baseEnd_6285852 < baseStart_6285852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285856 : List Nat := [2, 1, 1, 6, 2, 1, 3, 1, 1, 3, 2]
def baseStart_6285856 : Nat := 118140960795 + 6285856 * 2 ^ 59
def prefixEnd_6285856 : Nat := 4983230072969 + 3 ^ 40 * 6285856 * 2
def baseEnd_6285856 : Nat := 3227665452948263793191881

theorem tailTrace_6285856 : CollatzResearch.WordTrace tailWord_6285856 prefixEnd_6285856 3227665452948263793191881 := by
  unfold tailWord_6285856
  simp only [CollatzResearch.WordTrace]
  refine ⟨114632001557712362790562711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152842668743616483720750281 114632001557712362790562711)
  ·
    refine ⟨171948002336568544185844067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114632001557712362790562711 171948002336568544185844067)
    ·
      refine ⟨257922003504852816278766101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171948002336568544185844067 257922003504852816278766101)
      ·
        refine ⟨12090093914289975763067161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 257922003504852816278766101 12090093914289975763067161)
        ·
          refine ⟨9067570435717481822300371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12090093914289975763067161 9067570435717481822300371)
          ·
            refine ⟨13601355653576222733450557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9067570435717481822300371 13601355653576222733450557)
            ·
              refine ⟨5100508370091083525043959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13601355653576222733450557 5100508370091083525043959)
              ·
                refine ⟨7650762555136625287565939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5100508370091083525043959 7650762555136625287565939)
                ·
                  refine ⟨11476143832704937931348909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7650762555136625287565939 11476143832704937931348909)
                  ·
                    refine ⟨4303553937264351724255841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11476143832704937931348909 4303553937264351724255841)
                    ·
                      refine ⟨3227665452948263793191881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4303553937264351724255841 3227665452948263793191881)
                      ·
                        rfl

theorem cell23_6285856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_6285856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285856 prefixEnd_6285856 := by exact prefixLift 6285856
  have htrace : WordTrace (prefixWord ++ tailWord_6285856) baseStart_6285856 baseEnd_6285856 := by
    simpa [prefixWord, tailWord_6285856, baseEnd_6285856] using wordTrace_append hprefix tailTrace_6285856
  have hstable : (prefixWord ++ tailWord_6285856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285856).length < 2 ^ (prefixWord ++ tailWord_6285856).sum := by decide
  have hdescent : baseEnd_6285856 < baseStart_6285856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285868 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 3]
def baseStart_6285868 : Nat := 118140960795 + 6285868 * 2 ^ 59
def prefixEnd_6285868 : Nat := 4983230072969 + 3 ^ 40 * 6285868 * 2
def baseEnd_6285868 : Nat := 3227671614716117746241825

theorem tailTrace_6285868 : CollatzResearch.WordTrace tailWord_6285868 prefixEnd_6285868 3227671614716117746241825 := by
  unfold tailWord_6285868
  simp only [CollatzResearch.WordTrace]
  refine ⟨114632220395690625815281129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152842960527587501087041505 114632220395690625815281129)
  ·
    refine ⟨85974165296767969361460847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114632220395690625815281129 85974165296767969361460847)
    ·
      refine ⟨128961247945151954042191271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85974165296767969361460847 128961247945151954042191271)
      ·
        refine ⟨193441871917727931063286907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128961247945151954042191271 193441871917727931063286907)
        ·
          refine ⟨290162807876591896594930361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193441871917727931063286907 290162807876591896594930361)
          ·
            refine ⟨217622105907443922446197771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290162807876591896594930361 217622105907443922446197771)
            ·
              refine ⟨326433158861165883669296657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217622105907443922446197771 326433158861165883669296657)
              ·
                refine ⟨244824869145874412751972493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326433158861165883669296657 244824869145874412751972493)
                ·
                  refine ⟨91809325929702904781989685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244824869145874412751972493 91809325929702904781989685)
                  ·
                    refine ⟨8607124305909647323311533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91809325929702904781989685 8607124305909647323311533)
                    ·
                      refine ⟨3227671614716117746241825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8607124305909647323311533 3227671614716117746241825)
                      ·
                        rfl

theorem cell23_6285868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_6285868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285868 prefixEnd_6285868 := by exact prefixLift 6285868
  have htrace : WordTrace (prefixWord ++ tailWord_6285868) baseStart_6285868 baseEnd_6285868 := by
    simpa [prefixWord, tailWord_6285868, baseEnd_6285868] using wordTrace_append hprefix tailTrace_6285868
  have hstable : (prefixWord ++ tailWord_6285868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285868).length < 2 ^ (prefixWord ++ tailWord_6285868).sum := by decide
  have hdescent : baseEnd_6285868 < baseStart_6285868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285875 : List Nat := [1, 1, 1, 2, 4, 2, 3, 4, 5]
def baseStart_6285875 : Nat := 118140960795 + 6285875 * 2 ^ 59
def prefixEnd_6285875 : Nat := 4983230072969 + 3 ^ 40 * 6285875 * 2
def baseEnd_6285875 : Nat := 358630578786744357650477

theorem tailTrace_6285875 : CollatzResearch.WordTrace tailWord_6285875 prefixEnd_6285875 358630578786744357650477 := by
  unfold tailWord_6285875
  simp only [CollatzResearch.WordTrace]
  refine ⟨229264696102355891826067079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152843130734903927884044719 229264696102355891826067079)
  ·
    refine ⟨343897044153533837739100619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229264696102355891826067079 343897044153533837739100619)
    ·
      refine ⟨515845566230300756608650929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343897044153533837739100619 515845566230300756608650929)
      ·
        refine ⟨386884174672725567456488197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 515845566230300756608650929 386884174672725567456488197)
        ·
          refine ⟨72540782751136043898091537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 386884174672725567456488197 72540782751136043898091537)
          ·
            refine ⟨54405587063352032923568653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72540782751136043898091537 54405587063352032923568653)
            ·
              refine ⟨20402095148757012346338245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54405587063352032923568653 20402095148757012346338245)
              ·
                refine ⟨3825392840391939814938421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20402095148757012346338245 3825392840391939814938421)
                ·
                  refine ⟨358630578786744357650477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3825392840391939814938421 358630578786744357650477)
                  ·
                    rfl

theorem cell23_6285875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 5].length) (baseStart_6285875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285875 prefixEnd_6285875 := by exact prefixLift 6285875
  have htrace : WordTrace (prefixWord ++ tailWord_6285875) baseStart_6285875 baseEnd_6285875 := by
    simpa [prefixWord, tailWord_6285875, baseEnd_6285875] using wordTrace_append hprefix tailTrace_6285875
  have hstable : (prefixWord ++ tailWord_6285875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285875).length < 2 ^ (prefixWord ++ tailWord_6285875).sum := by decide
  have hdescent : baseEnd_6285875 < baseStart_6285875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285885 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 1, 5, 3]
def baseStart_6285885 : Nat := 118140960795 + 6285885 * 2 ^ 59
def prefixEnd_6285885 : Nat := 4983230072969 + 3 ^ 40 * 6285885 * 2
def baseEnd_6285885 : Nat := 3227680343887244179729247

theorem tailTrace_6285885 : CollatzResearch.WordTrace tailWord_6285885 prefixEnd_6285885 3227680343887244179729247 := by
  unfold tailWord_6285885
  simp only [CollatzResearch.WordTrace]
  refine ⟨229265060832319663533931109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152843373888213109022620739 229265060832319663533931109)
  ·
    refine ⟨42987198906059936912612083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229265060832319663533931109 42987198906059936912612083)
    ·
      refine ⟨64480798359089905368918125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42987198906059936912612083 64480798359089905368918125)
      ·
        refine ⟨24180299384658714513344297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64480798359089905368918125 24180299384658714513344297)
        ·
          refine ⟨18135224538494035885008223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24180299384658714513344297 18135224538494035885008223)
          ·
            refine ⟨27202836807741053827512335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18135224538494035885008223 27202836807741053827512335)
            ·
              refine ⟨40804255211611580741268503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27202836807741053827512335 40804255211611580741268503)
              ·
                refine ⟨61206382817417371111902755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40804255211611580741268503 61206382817417371111902755)
                ·
                  refine ⟨91809574226126056667854133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61206382817417371111902755 91809574226126056667854133)
                  ·
                    refine ⟨8607147583699317812611325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91809574226126056667854133 8607147583699317812611325)
                    ·
                      refine ⟨3227680343887244179729247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8607147583699317812611325 3227680343887244179729247)
                      ·
                        rfl

theorem cell23_6285885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_6285885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285885 prefixEnd_6285885 := by exact prefixLift 6285885
  have htrace : WordTrace (prefixWord ++ tailWord_6285885) baseStart_6285885 baseEnd_6285885 := by
    simpa [prefixWord, tailWord_6285885, baseEnd_6285885] using wordTrace_append hprefix tailTrace_6285885
  have hstable : (prefixWord ++ tailWord_6285885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285885).length < 2 ^ (prefixWord ++ tailWord_6285885).sum := by decide
  have hdescent : baseEnd_6285885 < baseStart_6285885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285886 : List Nat := [4, 2, 1, 4, 1, 1, 2, 1, 1, 4, 2]
def baseStart_6285886 : Nat := 118140960795 + 6285886 * 2 ^ 59
def prefixEnd_6285886 : Nat := 4983230072969 + 3 ^ 40 * 6285886 * 2
def baseEnd_6285886 : Nat := 3227680857367898675816743

theorem tailTrace_6285886 : CollatzResearch.WordTrace tailWord_6285886 prefixEnd_6285886 3227680857367898675816743 := by
  unfold tailWord_6285886
  simp only [CollatzResearch.WordTrace]
  refine ⟨28658137163164505088089689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152843398203544027136478341 28658137163164505088089689)
  ·
    refine ⟨21493602872373378816067267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28658137163164505088089689 21493602872373378816067267)
    ·
      refine ⟨32240404308560068224100901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21493602872373378816067267 32240404308560068224100901)
      ·
        refine ⟨6045075807855012792018919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32240404308560068224100901 6045075807855012792018919)
        ·
          refine ⟨9067613711782519188028379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6045075807855012792018919 9067613711782519188028379)
          ·
            refine ⟨13601420567673778782042569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9067613711782519188028379 13601420567673778782042569)
            ·
              refine ⟨10201065425755334086531927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13601420567673778782042569 10201065425755334086531927)
              ·
                refine ⟨15301598138633001129797891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10201065425755334086531927 15301598138633001129797891)
                ·
                  refine ⟨22952397207949501694696837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15301598138633001129797891 22952397207949501694696837)
                  ·
                    refine ⟨4303574476490531567755657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22952397207949501694696837 4303574476490531567755657)
                    ·
                      refine ⟨3227680857367898675816743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4303574476490531567755657 3227680857367898675816743)
                      ·
                        rfl

theorem cell23_6285886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_6285886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285886 prefixEnd_6285886 := by exact prefixLift 6285886
  have htrace : WordTrace (prefixWord ++ tailWord_6285886) baseStart_6285886 baseEnd_6285886 := by
    simpa [prefixWord, tailWord_6285886, baseEnd_6285886] using wordTrace_append hprefix tailTrace_6285886
  have hstable : (prefixWord ++ tailWord_6285886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285886).length < 2 ^ (prefixWord ++ tailWord_6285886).sum := by decide
  have hdescent : baseEnd_6285886 < baseStart_6285886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285888 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 4, 5]
def baseStart_6285888 : Nat := 118140960795 + 6285888 * 2 ^ 59
def prefixEnd_6285888 : Nat := 4983230072969 + 3 ^ 40 * 6285888 * 2
def baseEnd_6285888 : Nat := 1075893961443069222663911

theorem tailTrace_6285888 : CollatzResearch.WordTrace tailWord_6285888 prefixEnd_6285888 1075893961443069222663911 := by
  unfold tailWord_6285888
  simp only [CollatzResearch.WordTrace]
  refine ⟨114632585125654397523145159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152843446834205863364193545 114632585125654397523145159)
  ·
    refine ⟨171948877688481596284717739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114632585125654397523145159 171948877688481596284717739)
    ·
      refine ⟨257923316532722394427076609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171948877688481596284717739 257923316532722394427076609)
      ·
        refine ⟨193442487399541795820307457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257923316532722394427076609 193442487399541795820307457)
        ·
          refine ⟨145081865549656346865230593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193442487399541795820307457 145081865549656346865230593)
          ·
            refine ⟨108811399162242260148922945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145081865549656346865230593 108811399162242260148922945)
            ·
              refine ⟨81608549371681695111692209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108811399162242260148922945 81608549371681695111692209)
              ·
                refine ⟨61206412028761271333769157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81608549371681695111692209 61206412028761271333769157)
                ·
                  refine ⟨11476202255392738375081717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61206412028761271333769157 11476202255392738375081717)
                  ·
                    refine ⟨1075893961443069222663911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11476202255392738375081717 1075893961443069222663911)
                    ·
                      rfl

theorem cell23_6285888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 4, 5].length) (baseStart_6285888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285888 prefixEnd_6285888 := by exact prefixLift 6285888
  have htrace : WordTrace (prefixWord ++ tailWord_6285888) baseStart_6285888 baseEnd_6285888 := by
    simpa [prefixWord, tailWord_6285888, baseEnd_6285888] using wordTrace_append hprefix tailTrace_6285888
  have hstable : (prefixWord ++ tailWord_6285888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285888).length < 2 ^ (prefixWord ++ tailWord_6285888).sum := by decide
  have hdescent : baseEnd_6285888 < baseStart_6285888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285905 : List Nat := [1, 2, 2, 1, 3, 3, 3, 1, 2, 5]
def baseStart_6285905 : Nat := 118140960795 + 6285905 * 2 ^ 59
def prefixEnd_6285905 : Nat := 4983230072969 + 3 ^ 40 * 6285905 * 2
def baseEnd_6285905 : Nat := 1075896871166778033826385

theorem tailTrace_6285905 : CollatzResearch.WordTrace tailWord_6285905 prefixEnd_6285905 1075896871166778033826385 := by
  unfold tailWord_6285905
  simp only [CollatzResearch.WordTrace]
  refine ⟨229265790292247206949659169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152843860194831471299772779 229265790292247206949659169)
  ·
    refine ⟨171949342719185405212244377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229265790292247206949659169 171949342719185405212244377)
    ·
      refine ⟨128962007039389053909183283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171949342719185405212244377 128962007039389053909183283)
      ·
        refine ⟨193443010559083580863774925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128962007039389053909183283 193443010559083580863774925)
        ·
          refine ⟨72541128959656342823915597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193443010559083580863774925 72541128959656342823915597)
          ·
            refine ⟨27202923359871128558968349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72541128959656342823915597 27202923359871128558968349)
            ·
              refine ⟨10201096259951673209613131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27202923359871128558968349 10201096259951673209613131)
              ·
                refine ⟨15301644389927509814419697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10201096259951673209613131 15301644389927509814419697)
                ·
                  refine ⟨11476233292445632360814773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15301644389927509814419697 11476233292445632360814773)
                  ·
                    refine ⟨1075896871166778033826385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11476233292445632360814773 1075896871166778033826385)
                    ·
                      rfl

theorem cell23_6285905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_6285905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285905 prefixEnd_6285905 := by exact prefixLift 6285905
  have htrace : WordTrace (prefixWord ++ tailWord_6285905) baseStart_6285905 baseEnd_6285905 := by
    simpa [prefixWord, tailWord_6285905, baseEnd_6285905] using wordTrace_append hprefix tailTrace_6285905
  have hstable : (prefixWord ++ tailWord_6285905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285905).length < 2 ^ (prefixWord ++ tailWord_6285905).sum := by decide
  have hdescent : baseEnd_6285905 < baseStart_6285905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285935 : List Nat := [1, 1, 2, 1, 3, 2, 3, 3, 3, 4]
def baseStart_6285935 : Nat := 118140960795 + 6285935 * 2 ^ 59
def prefixEnd_6285935 : Nat := 4983230072969 + 3 ^ 40 * 6285935 * 2
def baseEnd_6285935 : Nat := 1075902005973322994701339

theorem tailTrace_6285935 : CollatzResearch.WordTrace tailWord_6285935 prefixEnd_6285935 1075902005973322994701339 := by
  unfold tailWord_6285935
  simp only [CollatzResearch.WordTrace]
  refine ⟨229266884482138522073251259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152844589654759014715500839 229266884482138522073251259)
  ·
    refine ⟨343900326723207783109876889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229266884482138522073251259 343900326723207783109876889)
    ·
      refine ⟨257925245042405837332407667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343900326723207783109876889 257925245042405837332407667)
      ·
        refine ⟨386887867563608755998611501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257925245042405837332407667 386887867563608755998611501)
        ·
          refine ⟨145082950336353283499479313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 386887867563608755998611501 145082950336353283499479313)
          ·
            refine ⟨108812212752264962624609485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145082950336353283499479313 108812212752264962624609485)
            ·
              refine ⟨40804579782099360984228557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108812212752264962624609485 40804579782099360984228557)
              ·
                refine ⟨15301717418287260369085709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40804579782099360984228557 15301717418287260369085709)
                ·
                  refine ⟨5738144031857722638407141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15301717418287260369085709 5738144031857722638407141)
                  ·
                    refine ⟨1075902005973322994701339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5738144031857722638407141 1075902005973322994701339)
                    ·
                      rfl

theorem cell23_6285935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 4].length) (baseStart_6285935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285935 prefixEnd_6285935 := by exact prefixLift 6285935
  have htrace : WordTrace (prefixWord ++ tailWord_6285935) baseStart_6285935 baseEnd_6285935 := by
    simpa [prefixWord, tailWord_6285935, baseEnd_6285935] using wordTrace_append hprefix tailTrace_6285935
  have hstable : (prefixWord ++ tailWord_6285935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285935).length < 2 ^ (prefixWord ++ tailWord_6285935).sum := by decide
  have hdescent : baseEnd_6285935 < baseStart_6285935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285945 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 1, 4, 3]
def baseStart_6285945 : Nat := 118140960795 + 6285945 * 2 ^ 59
def prefixEnd_6285945 : Nat := 4983230072969 + 3 ^ 40 * 6285945 * 2
def baseEnd_6285945 : Nat := 3227711152726513944978971

theorem tailTrace_6285945 : CollatzResearch.WordTrace tailWord_6285945 prefixEnd_6285945 3227711152726513944978971 := by
  unfold tailWord_6285945
  simp only [CollatzResearch.WordTrace]
  refine ⟨229267249212102293781115289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152844832808068195854076859 229267249212102293781115289)
  ·
    refine ⟨171950436909076720335836467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229267249212102293781115289 171950436909076720335836467)
    ·
      refine ⟨257925655363615080503754701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171950436909076720335836467 257925655363615080503754701)
      ·
        refine ⟨96722120761355655188908013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257925655363615080503754701 96722120761355655188908013)
        ·
          refine ⟨36270795285508370695840505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96722120761355655188908013 36270795285508370695840505)
          ·
            refine ⟨27203096464131278021880379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36270795285508370695840505 27203096464131278021880379)
            ·
              refine ⟨40804644696196917032820569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27203096464131278021880379 40804644696196917032820569)
              ·
                refine ⟨30603483522147687774615427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40804644696196917032820569 30603483522147687774615427)
                ·
                  refine ⟨45905225283221531661923141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30603483522147687774615427 45905225283221531661923141)
                  ·
                    refine ⟨8607229740604037186610589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45905225283221531661923141 8607229740604037186610589)
                    ·
                      refine ⟨3227711152726513944978971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8607229740604037186610589 3227711152726513944978971)
                      ·
                        rfl

theorem cell23_6285945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_6285945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285945 prefixEnd_6285945 := by exact prefixLift 6285945
  have htrace : WordTrace (prefixWord ++ tailWord_6285945) baseStart_6285945 baseEnd_6285945 := by
    simpa [prefixWord, tailWord_6285945, baseEnd_6285945] using wordTrace_append hprefix tailTrace_6285945
  have hstable : (prefixWord ++ tailWord_6285945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285945).length < 2 ^ (prefixWord ++ tailWord_6285945).sum := by decide
  have hdescent : baseEnd_6285945 < baseStart_6285945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6285982 : List Nat := [4, 3, 1, 1, 1, 1, 2, 4, 6]
def baseStart_6285982 : Nat := 118140960795 + 6285982 * 2 ^ 59
def prefixEnd_6285982 : Nat := 4983230072969 + 3 ^ 40 * 6285982 * 2
def baseEnd_6285982 : Nat := 358636683501192255579589

theorem tailTrace_6285982 : CollatzResearch.WordTrace tailWord_6285982 prefixEnd_6285982 358636683501192255579589 := by
  unfold tailWord_6285982
  simp only [CollatzResearch.WordTrace]
  refine ⟨28658574839121031137526525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152845732475312166066808133 28658574839121031137526525)
  ·
    refine ⟨10746965564670386676572447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28658574839121031137526525 10746965564670386676572447)
    ·
      refine ⟨16120448347005580014858671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10746965564670386676572447 16120448347005580014858671)
      ·
        refine ⟨24180672520508370022288007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16120448347005580014858671 24180672520508370022288007)
        ·
          refine ⟨36271008780762555033432011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24180672520508370022288007 36271008780762555033432011)
          ·
            refine ⟨54406513171143832550148017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36271008780762555033432011 54406513171143832550148017)
            ·
              refine ⟨40804884878357874412611013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54406513171143832550148017 40804884878357874412611013)
              ·
                refine ⟨7650915914692101452364565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40804884878357874412611013 7650915914692101452364565)
                ·
                  refine ⟨358636683501192255579589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7650915914692101452364565 358636683501192255579589)
                  ·
                    rfl

theorem cell23_6285982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_6285982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6285982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6285982 prefixEnd_6285982 := by exact prefixLift 6285982
  have htrace : WordTrace (prefixWord ++ tailWord_6285982) baseStart_6285982 baseEnd_6285982 := by
    simpa [prefixWord, tailWord_6285982, baseEnd_6285982] using wordTrace_append hprefix tailTrace_6285982
  have hstable : (prefixWord ++ tailWord_6285982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6285982).length < 2 ^ (prefixWord ++ tailWord_6285982).sum := by decide
  have hdescent : baseEnd_6285982 < baseStart_6285982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6285982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286002 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2]
def baseStart_6286002 : Nat := 118140960795 + 6286002 * 2 ^ 59
def prefixEnd_6286002 : Nat := 4983230072969 + 3 ^ 40 * 6286002 * 2
def baseEnd_6286002 : Nat := 3227740421123820221966209

theorem tailTrace_6286002 : CollatzResearch.WordTrace tailWord_6286002 prefixEnd_6286002 3227740421123820221966209 := by
  unfold tailWord_6286002
  simp only [CollatzResearch.WordTrace]
  refine ⟨57317332043223948128985065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152846218781930528343960173 57317332043223948128985065)
  ·
    refine ⟨42987999032417961096738799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57317332043223948128985065 42987999032417961096738799)
    ·
      refine ⟨64481998548626941645108199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42987999032417961096738799 64481998548626941645108199)
      ·
        refine ⟨96722997822940412467662299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64481998548626941645108199 96722997822940412467662299)
        ·
          refine ⟨145084496734410618701493449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96722997822940412467662299 145084496734410618701493449)
          ·
            refine ⟨108813372550807964026120087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145084496734410618701493449 108813372550807964026120087)
            ·
              refine ⟨163220058826211946039180131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108813372550807964026120087 163220058826211946039180131)
              ·
                refine ⟨244830088239317919058770197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163220058826211946039180131 244830088239317919058770197)
                ·
                  refine ⟨11476410386218027455879853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 244830088239317919058770197 11476410386218027455879853)
                  ·
                    refine ⟨4303653894831760295954945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11476410386218027455879853 4303653894831760295954945)
                    ·
                      refine ⟨3227740421123820221966209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4303653894831760295954945 3227740421123820221966209)
                      ·
                        rfl

theorem cell23_6286002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_6286002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286002 prefixEnd_6286002 := by exact prefixLift 6286002
  have htrace : WordTrace (prefixWord ++ tailWord_6286002) baseStart_6286002 baseEnd_6286002 := by
    simpa [prefixWord, tailWord_6286002, baseEnd_6286002] using wordTrace_append hprefix tailTrace_6286002
  have hstable : (prefixWord ++ tailWord_6286002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286002).length < 2 ^ (prefixWord ++ tailWord_6286002).sum := by decide
  have hdescent : baseEnd_6286002 < baseStart_6286002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286052 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 3, 2, 3]
def baseStart_6286052 : Nat := 118140960795 + 6286052 * 2 ^ 59
def prefixEnd_6286052 : Nat := 4983230072969 + 3 ^ 40 * 6286052 * 2
def baseEnd_6286052 : Nat := 3227766095156545026340979

theorem tailTrace_6286052 : CollatzResearch.WordTrace tailWord_6286052 prefixEnd_6286052 3227766095156545026340979 := by
  unfold tailWord_6286052
  simp only [CollatzResearch.WordTrace]
  refine ⟨114635575911357325527630205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152847434548476434036840273 114635575911357325527630205)
  ·
    refine ⟨42988340966758997072861327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114635575911357325527630205 42988340966758997072861327)
    ·
      refine ⟨64482511450138495609291991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42988340966758997072861327 64482511450138495609291991)
      ·
        refine ⟨96723767175207743413937987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64482511450138495609291991 96723767175207743413937987)
        ·
          refine ⟨145085650762811615120906981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96723767175207743413937987 145085650762811615120906981)
          ·
            refine ⟨27203559518027177835170059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145085650762811615120906981 27203559518027177835170059)
            ·
              refine ⟨40805339277040766752755089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27203559518027177835170059 40805339277040766752755089)
              ·
                refine ⟨30604004457780575064566317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40805339277040766752755089 30604004457780575064566317)
                ·
                  refine ⟨11476501671667715649212369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30604004457780575064566317 11476501671667715649212369)
                  ·
                    refine ⟨8607376253750786736909277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11476501671667715649212369 8607376253750786736909277)
                    ·
                      refine ⟨3227766095156545026340979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8607376253750786736909277 3227766095156545026340979)
                      ·
                        rfl

theorem cell23_6286052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_6286052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286052 prefixEnd_6286052 := by exact prefixLift 6286052
  have htrace : WordTrace (prefixWord ++ tailWord_6286052) baseStart_6286052 baseEnd_6286052 := by
    simpa [prefixWord, tailWord_6286052, baseEnd_6286052] using wordTrace_append hprefix tailTrace_6286052
  have hstable : (prefixWord ++ tailWord_6286052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286052).length < 2 ^ (prefixWord ++ tailWord_6286052).sum := by decide
  have hdescent : baseEnd_6286052 < baseStart_6286052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286062 : List Nat := [4, 1, 2, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_6286062 : Nat := 118140960795 + 6286062 * 2 ^ 59
def prefixEnd_6286062 : Nat := 4983230072969 + 3 ^ 40 * 6286062 * 2
def baseEnd_6286062 : Nat := 3227771229963089987215933

theorem tailTrace_6286062 : CollatzResearch.WordTrace tailWord_6286062 prefixEnd_6286062 3227771229963089987215933 := by
  unfold tailWord_6286062
  simp only [CollatzResearch.WordTrace]
  refine ⟨28658939569084802845390555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152847677701785615175416293 28658939569084802845390555)
  ·
    refine ⟨42988409353627204268085833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28658939569084802845390555 42988409353627204268085833)
    ·
      refine ⟨32241307015220403201064375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42988409353627204268085833 32241307015220403201064375)
      ·
        refine ⟨48361960522830604801596563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32241307015220403201064375 48361960522830604801596563)
        ·
          refine ⟨72542940784245907202394845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48361960522830604801596563 72542940784245907202394845)
          ·
            refine ⟨27203602794092215200898067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72542940784245907202394845 27203602794092215200898067)
            ·
              refine ⟨40805404191138322801347101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27203602794092215200898067 40805404191138322801347101)
              ·
                refine ⟨15302026571676871050505163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40805404191138322801347101 15302026571676871050505163)
                ·
                  refine ⟨22953039857515306575757745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15302026571676871050505163 22953039857515306575757745)
                  ·
                    refine ⟨17214779893136479931818309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22953039857515306575757745 17214779893136479931818309)
                    ·
                      refine ⟨3227771229963089987215933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17214779893136479931818309 3227771229963089987215933)
                      ·
                        rfl

theorem cell23_6286062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_6286062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286062 prefixEnd_6286062 := by exact prefixLift 6286062
  have htrace : WordTrace (prefixWord ++ tailWord_6286062) baseStart_6286062 baseEnd_6286062 := by
    simpa [prefixWord, tailWord_6286062, baseEnd_6286062] using wordTrace_append hprefix tailTrace_6286062
  have hstable : (prefixWord ++ tailWord_6286062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286062).length < 2 ^ (prefixWord ++ tailWord_6286062).sum := by decide
  have hdescent : baseEnd_6286062 < baseStart_6286062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286066 : List Nat := [3, 2, 1, 3, 1, 3, 1, 2, 3, 2, 2]
def baseStart_6286066 : Nat := 118140960795 + 6286066 * 2 ^ 59
def prefixEnd_6286066 : Nat := 4983230072969 + 3 ^ 40 * 6286066 * 2
def baseEnd_6286066 : Nat := 3227773283885707971565915

theorem tailTrace_6286066 : CollatzResearch.WordTrace tailWord_6286066 prefixEnd_6286066 3227773283885707971565915 := by
  unfold tailWord_6286066
  simp only [CollatzResearch.WordTrace]
  refine ⟨57317915611165982861567513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152847774963109287630846701 57317915611165982861567513)
  ·
    refine ⟨42988436708374487146175635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57317915611165982861567513 42988436708374487146175635)
    ·
      refine ⟨64482655062561730719263453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42988436708374487146175635 64482655062561730719263453)
      ·
        refine ⟨24180995648460649019723795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64482655062561730719263453 24180995648460649019723795)
        ·
          refine ⟨36271493472690973529585693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24180995648460649019723795 36271493472690973529585693)
          ·
            refine ⟨13601810052259115073594635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36271493472690973529585693 13601810052259115073594635)
            ·
              refine ⟨20402715078388672610391953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13601810052259115073594635 20402715078388672610391953)
              ·
                refine ⟨15302036308791504457793965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20402715078388672610391953 15302036308791504457793965)
                ·
                  refine ⟨5738263615796814171672737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15302036308791504457793965 5738263615796814171672737)
                  ·
                    refine ⟨4303697711847610628754553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5738263615796814171672737 4303697711847610628754553)
                    ·
                      refine ⟨3227773283885707971565915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4303697711847610628754553 3227773283885707971565915)
                      ·
                        rfl

theorem cell23_6286066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_6286066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286066 prefixEnd_6286066 := by exact prefixLift 6286066
  have htrace : WordTrace (prefixWord ++ tailWord_6286066) baseStart_6286066 baseEnd_6286066 := by
    simpa [prefixWord, tailWord_6286066, baseEnd_6286066] using wordTrace_append hprefix tailTrace_6286066
  have hstable : (prefixWord ++ tailWord_6286066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286066).length < 2 ^ (prefixWord ++ tailWord_6286066).sum := by decide
  have hdescent : baseEnd_6286066 < baseStart_6286066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286105 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 2, 3, 4]
def baseStart_6286105 : Nat := 118140960795 + 6286105 * 2 ^ 59
def prefixEnd_6286105 : Nat := 4983230072969 + 3 ^ 40 * 6286105 * 2
def baseEnd_6286105 : Nat := 3227793309631233318978235

theorem tailTrace_6286105 : CollatzResearch.WordTrace tailWord_6286105 prefixEnd_6286105 3227793309631233318978235 := by
  unfold tailWord_6286105
  simp only [CollatzResearch.WordTrace]
  refine ⟨229273084891522641106939769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152848723261015094071293179 229273084891522641106939769)
  ·
    refine ⟨171954813668641980830204827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229273084891522641106939769 171954813668641980830204827)
    ·
      refine ⟨257932220502962971245307241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171954813668641980830204827 257932220502962971245307241)
      ·
        refine ⟨193449165377222228433980431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257932220502962971245307241 193449165377222228433980431)
        ·
          refine ⟨290173748065833342650970647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193449165377222228433980431 290173748065833342650970647)
          ·
            refine ⟨435260622098750013976455971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290173748065833342650970647 435260622098750013976455971)
            ·
              refine ⟨652890933148125020964683957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435260622098750013976455971 652890933148125020964683957)
              ·
                refine ⟨61208524982636720715439121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 652890933148125020964683957 61208524982636720715439121)
                ·
                  refine ⟨45906393736977540536579341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61208524982636720715439121 45906393736977540536579341)
                  ·
                    refine ⟨17214897651366577701217253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45906393736977540536579341 17214897651366577701217253)
                    ·
                      refine ⟨3227793309631233318978235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17214897651366577701217253 3227793309631233318978235)
                      ·
                        rfl

theorem cell23_6286105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_6286105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286105 prefixEnd_6286105 := by exact prefixLift 6286105
  have htrace : WordTrace (prefixWord ++ tailWord_6286105) baseStart_6286105 baseEnd_6286105 := by
    simpa [prefixWord, tailWord_6286105, baseEnd_6286105] using wordTrace_append hprefix tailTrace_6286105
  have hstable : (prefixWord ++ tailWord_6286105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286105).length < 2 ^ (prefixWord ++ tailWord_6286105).sum := by decide
  have hdescent : baseEnd_6286105 < baseStart_6286105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286116 : List Nat := [2, 3, 1, 3, 3, 2, 1, 1, 1, 3, 3]
def baseStart_6286116 : Nat := 118140960795 + 6286116 * 2 ^ 59
def prefixEnd_6286116 : Nat := 4983230072969 + 3 ^ 40 * 6286116 * 2
def baseEnd_6286116 : Nat := 3227798957918432775940685

theorem tailTrace_6286116 : CollatzResearch.WordTrace tailWord_6286116 prefixEnd_6286116 3227798957918432775940685 := by
  unfold tailWord_6286116
  simp only [CollatzResearch.WordTrace]
  refine ⟨114636743047241394992795101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152848990729655193323726801 114636743047241394992795101)
  ·
    refine ⟨42988778642715523122298163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114636743047241394992795101 42988778642715523122298163)
    ·
      refine ⟨64483167964073284683447245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42988778642715523122298163 64483167964073284683447245)
      ·
        refine ⟨24181187986527481756292717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64483167964073284683447245 24181187986527481756292717)
        ·
          refine ⟨9067945494947805658609769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24181187986527481756292717 9067945494947805658609769)
          ·
            refine ⟨6800959121210854243957327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9067945494947805658609769 6800959121210854243957327)
            ·
              refine ⟨10201438681816281365935991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6800959121210854243957327 10201438681816281365935991)
              ·
                refine ⟨15302158022724422048903987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10201438681816281365935991 15302158022724422048903987)
                ·
                  refine ⟨22953237034086633073355981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15302158022724422048903987 22953237034086633073355981)
                  ·
                    refine ⟨8607463887782487402508493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22953237034086633073355981 8607463887782487402508493)
                    ·
                      refine ⟨3227798957918432775940685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8607463887782487402508493 3227798957918432775940685)
                      ·
                        rfl

theorem cell23_6286116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_6286116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286116 prefixEnd_6286116 := by exact prefixLift 6286116
  have htrace : WordTrace (prefixWord ++ tailWord_6286116) baseStart_6286116 baseEnd_6286116 := by
    simpa [prefixWord, tailWord_6286116, baseEnd_6286116] using wordTrace_append hprefix tailTrace_6286116
  have hstable : (prefixWord ++ tailWord_6286116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286116).length < 2 ^ (prefixWord ++ tailWord_6286116).sum := by decide
  have hdescent : baseEnd_6286116 < baseStart_6286116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286134 : List Nat := [5, 1, 2, 2, 3, 1, 1, 3, 1, 2, 2]
def baseStart_6286134 : Nat := 118140960795 + 6286134 * 2 ^ 59
def prefixEnd_6286134 : Nat := 4983230072969 + 3 ^ 40 * 6286134 * 2
def baseEnd_6286134 : Nat := 3227808200570213705515603

theorem tailTrace_6286134 : CollatzResearch.WordTrace tailWord_6286134 prefixEnd_6286134 3227808200570213705515603 := by
  unfold tailWord_6286134
  simp only [CollatzResearch.WordTrace]
  refine ⟨14329633913026098691234091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152849428405611719373163637 14329633913026098691234091)
  ·
    refine ⟨21494450869539148036851137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14329633913026098691234091 21494450869539148036851137)
    ·
      refine ⟨16120838152154361027638353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21494450869539148036851137 16120838152154361027638353)
      ·
        refine ⟨12090628614115770770728765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16120838152154361027638353 12090628614115770770728765)
        ·
          refine ⟨4533985730293414039023287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12090628614115770770728765 4533985730293414039023287)
          ·
            refine ⟨6800978595440121058534931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4533985730293414039023287 6800978595440121058534931)
            ·
              refine ⟨10201467893160181587802397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6800978595440121058534931 10201467893160181587802397)
              ·
                refine ⟨3825550459935068095425899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10201467893160181587802397 3825550459935068095425899)
                ·
                  refine ⟨5738325689902602143138849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3825550459935068095425899 5738325689902602143138849)
                  ·
                    refine ⟨4303744267426951607354137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5738325689902602143138849 4303744267426951607354137)
                    ·
                      refine ⟨3227808200570213705515603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4303744267426951607354137 3227808200570213705515603)
                      ·
                        rfl

theorem cell23_6286134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_6286134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286134 prefixEnd_6286134 := by exact prefixLift 6286134
  have htrace : WordTrace (prefixWord ++ tailWord_6286134) baseStart_6286134 baseEnd_6286134 := by
    simpa [prefixWord, tailWord_6286134, baseEnd_6286134] using wordTrace_append hprefix tailTrace_6286134
  have hstable : (prefixWord ++ tailWord_6286134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286134).length < 2 ^ (prefixWord ++ tailWord_6286134).sum := by decide
  have hdescent : baseEnd_6286134 < baseStart_6286134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286156 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 4, 2, 2]
def baseStart_6286156 : Nat := 118140960795 + 6286156 * 2 ^ 59
def prefixEnd_6286156 : Nat := 4983230072969 + 3 ^ 40 * 6286156 * 2
def baseEnd_6286156 : Nat := 3227819497144612619440501

theorem tailTrace_6286156 : CollatzResearch.WordTrace tailWord_6286156 prefixEnd_6286156 3227819497144612619440501 := by
  unfold tailWord_6286156
  simp only [CollatzResearch.WordTrace]
  refine ⟨114637472507168938408523161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152849963342891917878030881 114637472507168938408523161)
  ·
    refine ⟨85978104380376703806392371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114637472507168938408523161 85978104380376703806392371)
    ·
      refine ⟨128967156570565055709588557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85978104380376703806392371 128967156570565055709588557)
      ·
        refine ⟨48362683713961895891095709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128967156570565055709588557 48362683713961895891095709)
        ·
          refine ⟨18136006392735710959160891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48362683713961895891095709 18136006392735710959160891)
          ·
            refine ⟨27204009589103566438741337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18136006392735710959160891 27204009589103566438741337)
            ·
              refine ⟨20403007191827674829056003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27204009589103566438741337 20403007191827674829056003)
              ·
                refine ⟨30604510787741512243584005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20403007191827674829056003 30604510787741512243584005)
                ·
                  refine ⟨5738345772701533545672001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30604510787741512243584005 5738345772701533545672001)
                  ·
                    refine ⟨4303759329526150159254001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5738345772701533545672001 4303759329526150159254001)
                    ·
                      refine ⟨3227819497144612619440501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4303759329526150159254001 3227819497144612619440501)
                      ·
                        rfl

theorem cell23_6286156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_6286156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286156 prefixEnd_6286156 := by exact prefixLift 6286156
  have htrace : WordTrace (prefixWord ++ tailWord_6286156) baseStart_6286156 baseEnd_6286156 := by
    simpa [prefixWord, tailWord_6286156, baseEnd_6286156] using wordTrace_append hprefix tailTrace_6286156
  have hstable : (prefixWord ++ tailWord_6286156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286156).length < 2 ^ (prefixWord ++ tailWord_6286156).sum := by decide
  have hdescent : baseEnd_6286156 < baseStart_6286156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286192 : List Nat := [2, 1, 1, 1, 4, 1, 3, 3, 2, 5]
def baseStart_6286192 : Nat := 118140960795 + 6286192 * 2 ^ 59
def prefixEnd_6286192 : Nat := 4983230072969 + 3 ^ 40 * 6286192 * 2
def baseEnd_6286192 : Nat := 1075945994149391492863445

theorem tailTrace_6286192 : CollatzResearch.WordTrace tailWord_6286192 prefixEnd_6286192 1075945994149391492863445 := by
  unfold tailWord_6286192
  simp only [CollatzResearch.WordTrace]
  refine ⟨114638129021103727482678415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152850838694804969976904553 114638129021103727482678415)
  ·
    refine ⟨171957193531655591224017623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114638129021103727482678415 171957193531655591224017623)
    ·
      refine ⟨257935790297483386836026435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171957193531655591224017623 257935790297483386836026435)
      ·
        refine ⟨386903685446225080254039653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257935790297483386836026435 386903685446225080254039653)
        ·
          refine ⟨72544441021167202547632435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 386903685446225080254039653 72544441021167202547632435)
          ·
            refine ⟨108816661531750803821448653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72544441021167202547632435 108816661531750803821448653)
            ·
              refine ⟨40806248074406551433043245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108816661531750803821448653 40806248074406551433043245)
              ·
                refine ⟨15302343027902456787391217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40806248074406551433043245 15302343027902456787391217)
                ·
                  refine ⟨11476757270926842590543413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15302343027902456787391217 11476757270926842590543413)
                  ·
                    refine ⟨1075945994149391492863445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11476757270926842590543413 1075945994149391492863445)
                    ·
                      rfl

theorem cell23_6286192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 2, 5].length) (baseStart_6286192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286192 prefixEnd_6286192 := by exact prefixLift 6286192
  have htrace : WordTrace (prefixWord ++ tailWord_6286192) baseStart_6286192 baseEnd_6286192 := by
    simpa [prefixWord, tailWord_6286192, baseEnd_6286192] using wordTrace_append hprefix tailTrace_6286192
  have hstable : (prefixWord ++ tailWord_6286192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286192).length < 2 ^ (prefixWord ++ tailWord_6286192).sum := by decide
  have hdescent : baseEnd_6286192 < baseStart_6286192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286212 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_6286212 : Nat := 118140960795 + 6286212 * 2 ^ 59
def prefixEnd_6286212 : Nat := 4983230072969 + 3 ^ 40 * 6286212 * 2
def baseEnd_6286212 : Nat := 3227848252061264400340243

theorem tailTrace_6286212 : CollatzResearch.WordTrace tailWord_6286212 prefixEnd_6286212 3227848252061264400340243 := by
  unfold tailWord_6286212
  simp only [CollatzResearch.WordTrace]
  refine ⟨114638493751067499190542445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152851325001423332254056593 114638493751067499190542445)
  ·
    refine ⟨42989435156650312196453417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114638493751067499190542445 42989435156650312196453417)
    ·
      refine ⟨32242076367487734147340063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42989435156650312196453417 32242076367487734147340063)
      ·
        refine ⟨48363114551231601221010095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32242076367487734147340063 48363114551231601221010095)
        ·
          refine ⟨72544671826847401831515143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48363114551231601221010095 72544671826847401831515143)
          ·
            refine ⟨108817007740271102747272715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72544671826847401831515143 108817007740271102747272715)
            ·
              refine ⟨163225511610406654120909073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108817007740271102747272715 163225511610406654120909073)
              ·
                refine ⟨122419133707804990590681805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163225511610406654120909073 122419133707804990590681805)
                ·
                  refine ⟨45907175140426871471505677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122419133707804990590681805 45907175140426871471505677)
                  ·
                    refine ⟨17215190677660076801814629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45907175140426871471505677 17215190677660076801814629)
                    ·
                      refine ⟨3227848252061264400340243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17215190677660076801814629 3227848252061264400340243)
                      ·
                        rfl

theorem cell23_6286212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_6286212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286212 prefixEnd_6286212 := by exact prefixLift 6286212
  have htrace : WordTrace (prefixWord ++ tailWord_6286212) baseStart_6286212 baseEnd_6286212 := by
    simpa [prefixWord, tailWord_6286212, baseEnd_6286212] using wordTrace_append hprefix tailTrace_6286212
  have hstable : (prefixWord ++ tailWord_6286212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286212).length < 2 ^ (prefixWord ++ tailWord_6286212).sum := by decide
  have hdescent : baseEnd_6286212 < baseStart_6286212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286229 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 1, 6, 2]
def baseStart_6286229 : Nat := 118140960795 + 6286229 * 2 ^ 59
def prefixEnd_6286229 : Nat := 4983230072969 + 3 ^ 40 * 6286229 * 2
def baseEnd_6286229 : Nat := 3227856981232390833827665

theorem tailTrace_6286229 : CollatzResearch.WordTrace tailWord_6286229 prefixEnd_6286229 3227856981232390833827665 := by
  unfold tailWord_6286229
  simp only [CollatzResearch.WordTrace]
  refine ⟨229277607543073410284453741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152851738362048940189635827 229277607543073410284453741)
  ·
    refine ⟨85979102828652528856670153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229277607543073410284453741 85979102828652528856670153)
    ·
      refine ⟨64484327121489396642502615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85979102828652528856670153 64484327121489396642502615)
      ·
        refine ⟨96726490682234094963753923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64484327121489396642502615 96726490682234094963753923)
        ·
          refine ⟨145089736023351142445630885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96726490682234094963753923 145089736023351142445630885)
          ·
            refine ⟨27204325504378339208555791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145089736023351142445630885 27204325504378339208555791)
            ·
              refine ⟨40806488256567508812833687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27204325504378339208555791 40806488256567508812833687)
              ·
                refine ⟨61209732384851263219250531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40806488256567508812833687 61209732384851263219250531)
                ·
                  refine ⟨91814598577276894828875797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61209732384851263219250531 91814598577276894828875797)
                  ·
                    refine ⟨4303809308309854445103553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91814598577276894828875797 4303809308309854445103553)
                    ·
                      refine ⟨3227856981232390833827665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4303809308309854445103553 3227856981232390833827665)
                      ·
                        rfl

theorem cell23_6286229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_6286229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286229 prefixEnd_6286229 := by exact prefixLift 6286229
  have htrace : WordTrace (prefixWord ++ tailWord_6286229) baseStart_6286229 baseEnd_6286229 := by
    simpa [prefixWord, tailWord_6286229, baseEnd_6286229] using wordTrace_append hprefix tailTrace_6286229
  have hstable : (prefixWord ++ tailWord_6286229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286229).length < 2 ^ (prefixWord ++ tailWord_6286229).sum := by decide
  have hdescent : baseEnd_6286229 < baseStart_6286229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286239 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 5, 4]
def baseStart_6286239 : Nat := 118140960795 + 6286239 * 2 ^ 59
def prefixEnd_6286239 : Nat := 4983230072969 + 3 ^ 40 * 6286239 * 2
def baseEnd_6286239 : Nat := 1075954038679645264900873

theorem tailTrace_6286239 : CollatzResearch.WordTrace tailWord_6286239 prefixEnd_6286239 1075954038679645264900873 := by
  unfold tailWord_6286239
  simp only [CollatzResearch.WordTrace]
  refine ⟨229277972273037181992317771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152851981515358121328211847 229277972273037181992317771)
  ·
    refine ⟨343916958409555772988476657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229277972273037181992317771 343916958409555772988476657)
    ·
      refine ⟨257937718807166829741357493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343916958409555772988476657 257937718807166829741357493)
      ·
        refine ⟨24181661138171890288252265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 257937718807166829741357493 24181661138171890288252265)
        ·
          refine ⟨18136245853628917716189199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24181661138171890288252265 18136245853628917716189199)
          ·
            refine ⟨27204368780443376574283799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18136245853628917716189199 27204368780443376574283799)
            ·
              refine ⟨40806553170665064861425699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27204368780443376574283799 40806553170665064861425699)
              ·
                refine ⟨61209829755997597292138549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40806553170665064861425699 61209829755997597292138549)
                ·
                  refine ⟨5738421539624774746137989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61209829755997597292138549 5738421539624774746137989)
                  ·
                    refine ⟨1075954038679645264900873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5738421539624774746137989 1075954038679645264900873)
                    ·
                      rfl

theorem cell23_6286239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 4].length) (baseStart_6286239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286239 prefixEnd_6286239 := by exact prefixLift 6286239
  have htrace : WordTrace (prefixWord ++ tailWord_6286239) baseStart_6286239 baseEnd_6286239 := by
    simpa [prefixWord, tailWord_6286239, baseEnd_6286239] using wordTrace_append hprefix tailTrace_6286239
  have hstable : (prefixWord ++ tailWord_6286239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286239).length < 2 ^ (prefixWord ++ tailWord_6286239).sum := by decide
  have hdescent : baseEnd_6286239 < baseStart_6286239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286269 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 8]
def baseStart_6286269 : Nat := 118140960795 + 6286269 * 2 ^ 59
def prefixEnd_6286269 : Nat := 4983230072969 + 3 ^ 40 * 6286269 * 2
def baseEnd_6286269 : Nat := 358653057828730075258609

theorem tailTrace_6286269 : CollatzResearch.WordTrace tailWord_6286269 prefixEnd_6286269 358653057828730075258609 := by
  unfold tailWord_6286269
  simp only [CollatzResearch.WordTrace]
  refine ⟨229279066462928497115909861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152852710975285664743939907 229279066462928497115909861)
  ·
    refine ⟨42989824961799093209233099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229279066462928497115909861 42989824961799093209233099)
    ·
      refine ⟨64484737442698639813849649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42989824961799093209233099 64484737442698639813849649)
      ·
        refine ⟨48363553082023979860387237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64484737442698639813849649 48363553082023979860387237)
        ·
          refine ⟨9068166202879496223822607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48363553082023979860387237 9068166202879496223822607)
          ·
            refine ⟨13602249304319244335733911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9068166202879496223822607 13602249304319244335733911)
            ·
              refine ⟨20403373956478866503600867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13602249304319244335733911 20403373956478866503600867)
              ·
                refine ⟨30605060934718299755401301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20403373956478866503600867 30605060934718299755401301)
                ·
                  refine ⟨358653057828730075258609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30605060934718299755401301 358653057828730075258609)
                  ·
                    rfl

theorem cell23_6286269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_6286269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286269 prefixEnd_6286269 := by exact prefixLift 6286269
  have htrace : WordTrace (prefixWord ++ tailWord_6286269) baseStart_6286269 baseEnd_6286269 := by
    simpa [prefixWord, tailWord_6286269, baseEnd_6286269] using wordTrace_append hprefix tailTrace_6286269
  have hstable : (prefixWord ++ tailWord_6286269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286269).length < 2 ^ (prefixWord ++ tailWord_6286269).sum := by decide
  have hdescent : baseEnd_6286269 < baseStart_6286269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286272 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 6]
def baseStart_6286272 : Nat := 118140960795 + 6286272 * 2 ^ 59
def prefixEnd_6286272 : Nat := 4983230072969 + 3 ^ 40 * 6286272 * 2
def baseEnd_6286272 : Nat := 3227879060900534165589967

theorem tailTrace_6286272 : CollatzResearch.WordTrace tailWord_6286272 prefixEnd_6286272 3227879060900534165589967 := by
  unfold tailWord_6286272
  simp only [CollatzResearch.WordTrace]
  refine ⟨114639587940958814314134535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152852783921278419085512713 114639587940958814314134535)
  ·
    refine ⟨171959381911438221471201803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114639587940958814314134535 171959381911438221471201803)
    ·
      refine ⟨257939072867157332206802705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171959381911438221471201803 257939072867157332206802705)
      ·
        refine ⟨193454304650367999155102029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257939072867157332206802705 193454304650367999155102029)
        ·
          refine ⟨72545364243887999683163261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193454304650367999155102029 72545364243887999683163261)
          ·
            refine ⟨27204511591457999881186223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72545364243887999683163261 27204511591457999881186223)
            ·
              refine ⟨40806767387186999821779335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27204511591457999881186223 40806767387186999821779335)
              ·
                refine ⟨61210151080780499732669003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40806767387186999821779335 61210151080780499732669003)
                ·
                  refine ⟨91815226621170749599003505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61210151080780499732669003 91815226621170749599003505)
                  ·
                    refine ⟨68861419965878062199252629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91815226621170749599003505 68861419965878062199252629)
                    ·
                      refine ⟨3227879060900534165589967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68861419965878062199252629 3227879060900534165589967)
                      ·
                        rfl

theorem cell23_6286272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_6286272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286272 prefixEnd_6286272 := by exact prefixLift 6286272
  have htrace : WordTrace (prefixWord ++ tailWord_6286272) baseStart_6286272 baseEnd_6286272 := by
    simpa [prefixWord, tailWord_6286272, baseEnd_6286272] using wordTrace_append hprefix tailTrace_6286272
  have hstable : (prefixWord ++ tailWord_6286272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286272).length < 2 ^ (prefixWord ++ tailWord_6286272).sum := by decide
  have hdescent : baseEnd_6286272 < baseStart_6286272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286286 : List Nat := [4, 1, 1, 1, 2, 4, 3, 1, 6]
def baseStart_6286286 : Nat := 118140960795 + 6286286 * 2 ^ 59
def prefixEnd_6286286 : Nat := 4983230072969 + 3 ^ 40 * 6286286 * 2
def baseEnd_6286286 : Nat := 358654027736633012312767

theorem tailTrace_6286286 : CollatzResearch.WordTrace tailWord_6286286 prefixEnd_6286286 358654027736633012312767 := by
  unfold tailWord_6286286
  simp only [CollatzResearch.WordTrace]
  refine ⟨28659960812983363627409839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152853124335911272679519141 28659960812983363627409839)
  ·
    refine ⟨42989941219475045441114759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28659960812983363627409839 42989941219475045441114759)
    ·
      refine ⟨64484911829212568161672139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42989941219475045441114759 64484911829212568161672139)
      ·
        refine ⟨96727367743818852242508209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64484911829212568161672139 96727367743818852242508209)
        ·
          refine ⟨72545525807864139181881157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96727367743818852242508209 72545525807864139181881157)
          ·
            refine ⟨13602286088974526096602717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72545525807864139181881157 13602286088974526096602717)
            ·
              refine ⟨5100857283365447286226019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13602286088974526096602717 5100857283365447286226019)
              ·
                refine ⟨7651285925048170929339029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5100857283365447286226019 7651285925048170929339029)
                ·
                  refine ⟨358654027736633012312767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7651285925048170929339029 358654027736633012312767)
                  ·
                    rfl

theorem cell23_6286286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_6286286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286286 prefixEnd_6286286 := by exact prefixLift 6286286
  have htrace : WordTrace (prefixWord ++ tailWord_6286286) baseStart_6286286 baseEnd_6286286 := by
    simpa [prefixWord, tailWord_6286286, baseEnd_6286286] using wordTrace_append hprefix tailTrace_6286286
  have hstable : (prefixWord ++ tailWord_6286286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286286).length < 2 ^ (prefixWord ++ tailWord_6286286).sum := by decide
  have hdescent : baseEnd_6286286 < baseStart_6286286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286289 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 3, 5, 2]
def baseStart_6286289 : Nat := 118140960795 + 6286289 * 2 ^ 59
def prefixEnd_6286289 : Nat := 4983230072969 + 3 ^ 40 * 6286289 * 2
def baseEnd_6286289 : Nat := 3227887790071660599077389

theorem tailTrace_6286289 : CollatzResearch.WordTrace tailWord_6286289 prefixEnd_6286289 3227887790071660599077389 := by
  unfold tailWord_6286289
  simp only [CollatzResearch.WordTrace]
  refine ⟨229279795922856040531637921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152853197281904027021091947 229279795922856040531637921)
  ·
    refine ⟨171959846942142030398728441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229279795922856040531637921 171959846942142030398728441)
    ·
      refine ⟨128969885206606522799046331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171959846942142030398728441 128969885206606522799046331)
      ·
        refine ⟨193454827809909784198569497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128969885206606522799046331 193454827809909784198569497)
        ·
          refine ⟨145091120857432338148927123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193454827809909784198569497 145091120857432338148927123)
          ·
            refine ⟨217636681286148507223390685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145091120857432338148927123 217636681286148507223390685)
            ·
              refine ⟨81613755482305690208771507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217636681286148507223390685 81613755482305690208771507)
              ·
                refine ⟨122420633223458535313157261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81613755482305690208771507 122420633223458535313157261)
                ·
                  refine ⟨45907737458796950742433973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122420633223458535313157261 45907737458796950742433973)
                  ·
                    refine ⟨4303850386762214132103185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45907737458796950742433973 4303850386762214132103185)
                    ·
                      refine ⟨3227887790071660599077389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4303850386762214132103185 3227887790071660599077389)
                      ·
                        rfl

theorem cell23_6286289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 5, 2].length) (baseStart_6286289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286289 prefixEnd_6286289 := by exact prefixLift 6286289
  have htrace : WordTrace (prefixWord ++ tailWord_6286289) baseStart_6286289 baseEnd_6286289 := by
    simpa [prefixWord, tailWord_6286289, baseEnd_6286289] using wordTrace_append hprefix tailTrace_6286289
  have hstable : (prefixWord ++ tailWord_6286289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286289).length < 2 ^ (prefixWord ++ tailWord_6286289).sum := by decide
  have hdescent : baseEnd_6286289 < baseStart_6286289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286296 : List Nat := [2, 1, 2, 2, 2, 3, 2, 2, 3, 1, 3]
def baseStart_6286296 : Nat := 118140960795 + 6286296 * 2 ^ 59
def prefixEnd_6286296 : Nat := 4983230072969 + 3 ^ 40 * 6286296 * 2
def baseEnd_6286296 : Nat := 3227891384436242071689857

theorem tailTrace_6286296 : CollatzResearch.WordTrace tailWord_6286296 prefixEnd_6286296 3227891384436242071689857 := by
  unfold tailWord_6286296
  simp only [CollatzResearch.WordTrace]
  refine ⟨114640025616915340363571371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152853367489220453818095161 114640025616915340363571371)
  ·
    refine ⟨171960038425373010545357057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114640025616915340363571371 171960038425373010545357057)
    ·
      refine ⟨128970028819029757909017793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171960038425373010545357057 128970028819029757909017793)
      ·
        refine ⟨96727521614272318431763345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128970028819029757909017793 96727521614272318431763345)
        ·
          refine ⟨72545641210704238823822509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96727521614272318431763345 72545641210704238823822509)
          ·
            refine ⟨27204615454014089558933441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72545641210704238823822509 27204615454014089558933441)
            ·
              refine ⟨20403461590510567169200081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27204615454014089558933441 20403461590510567169200081)
              ·
                refine ⟨15302596192882925376900061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20403461590510567169200081 15302596192882925376900061)
                ·
                  refine ⟨5738473572331097016337523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15302596192882925376900061 5738473572331097016337523)
                  ·
                    refine ⟨8607710358496645524506285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5738473572331097016337523 8607710358496645524506285)
                    ·
                      refine ⟨3227891384436242071689857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8607710358496645524506285 3227891384436242071689857)
                      ·
                        rfl

theorem cell23_6286296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_6286296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286296 prefixEnd_6286296 := by exact prefixLift 6286296
  have htrace : WordTrace (prefixWord ++ tailWord_6286296) baseStart_6286296 baseEnd_6286296 := by
    simpa [prefixWord, tailWord_6286296, baseEnd_6286296] using wordTrace_append hprefix tailTrace_6286296
  have hstable : (prefixWord ++ tailWord_6286296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286296).length < 2 ^ (prefixWord ++ tailWord_6286296).sum := by decide
  have hdescent : baseEnd_6286296 < baseStart_6286296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286324 : List Nat := [2, 6, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_6286324 : Nat := 118140960795 + 6286324 * 2 ^ 59
def prefixEnd_6286324 : Nat := 4983230072969 + 3 ^ 40 * 6286324 * 2
def baseEnd_6286324 : Nat := 1075968587298189320713243

theorem tailTrace_6286324 : CollatzResearch.WordTrace tailWord_6286324 prefixEnd_6286324 1075968587298189320713243 := by
  unfold tailWord_6286324
  simp only [CollatzResearch.WordTrace]
  refine ⟨114640536238864620754581013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152854048318486161006108017 114640536238864620754581013)
  ·
    refine ⟨5373775136196779097870985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 114640536238864620754581013 5373775136196779097870985)
    ·
      refine ⟨4030331352147584323403239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5373775136196779097870985 4030331352147584323403239)
      ·
        refine ⟨6045497028221376485104859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4030331352147584323403239 6045497028221376485104859)
        ·
          refine ⟨9068245542332064727657289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6045497028221376485104859 9068245542332064727657289)
          ·
            refine ⟨6801184156749048545742967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9068245542332064727657289 6801184156749048545742967)
            ·
              refine ⟨10201776235123572818614451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6801184156749048545742967 10201776235123572818614451)
              ·
                refine ⟨15302664352685359227921677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10201776235123572818614451 15302664352685359227921677)
                ·
                  refine ⟨5738499132257009710470629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15302664352685359227921677 5738499132257009710470629)
                  ·
                    refine ⟨1075968587298189320713243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5738499132257009710470629 1075968587298189320713243)
                    ·
                      rfl

theorem cell23_6286324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_6286324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286324 prefixEnd_6286324 := by exact prefixLift 6286324
  have htrace : WordTrace (prefixWord ++ tailWord_6286324) baseStart_6286324 baseEnd_6286324 := by
    simpa [prefixWord, tailWord_6286324, baseEnd_6286324] using wordTrace_append hprefix tailTrace_6286324
  have hstable : (prefixWord ++ tailWord_6286324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286324).length < 2 ^ (prefixWord ++ tailWord_6286324).sum := by decide
  have hdescent : baseEnd_6286324 < baseStart_6286324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286329 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 4, 4]
def baseStart_6286329 : Nat := 118140960795 + 6286329 * 2 ^ 59
def prefixEnd_6286329 : Nat := 4983230072969 + 3 ^ 40 * 6286329 * 2
def baseEnd_6286329 : Nat := 1075969443099280147525735

theorem tailTrace_6286329 : CollatzResearch.WordTrace tailWord_6286329 prefixEnd_6286329 1075969443099280147525735 := by
  unfold tailWord_6286329
  simp only [CollatzResearch.WordTrace]
  refine ⟨229281254842711127363094041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152854169895140751575396027 229281254842711127363094041)
  ·
    refine ⟨171960941132033345522320531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229281254842711127363094041 171960941132033345522320531)
    ·
      refine ⟨257941411698050018283480797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171960941132033345522320531 257941411698050018283480797)
      ·
        refine ⟨96728029386768756856305299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257941411698050018283480797 96728029386768756856305299)
        ·
          refine ⟨145092044080153135284457949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96728029386768756856305299 145092044080153135284457949)
          ·
            refine ⟨54409516530057425731671731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145092044080153135284457949 54409516530057425731671731)
            ·
              refine ⟨81614274795086138597507597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54409516530057425731671731 81614274795086138597507597)
              ·
                refine ⟨30605353048157301974065349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81614274795086138597507597 30605353048157301974065349)
                ·
                  refine ⟨5738503696529494120137253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30605353048157301974065349 5738503696529494120137253)
                  ·
                    refine ⟨1075969443099280147525735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5738503696529494120137253 1075969443099280147525735)
                    ·
                      rfl

theorem cell23_6286329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 4].length) (baseStart_6286329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286329 prefixEnd_6286329 := by exact prefixLift 6286329
  have htrace : WordTrace (prefixWord ++ tailWord_6286329) baseStart_6286329 baseEnd_6286329 := by
    simpa [prefixWord, tailWord_6286329, baseEnd_6286329] using wordTrace_append hprefix tailTrace_6286329
  have hstable : (prefixWord ++ tailWord_6286329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286329).length < 2 ^ (prefixWord ++ tailWord_6286329).sum := by decide
  have hdescent : baseEnd_6286329 < baseStart_6286329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286359 : List Nat := [1, 1, 3, 5, 1, 1, 2, 9]
def baseStart_6286359 : Nat := 118140960795 + 6286359 * 2 ^ 59
def prefixEnd_6286359 : Nat := 4983230072969 + 3 ^ 40 * 6286359 * 2
def baseEnd_6286359 : Nat := 119552730878425012044521

theorem tailTrace_6286359 : CollatzResearch.WordTrace tailWord_6286359 prefixEnd_6286359 119552730878425012044521 := by
  unfold tailWord_6286359
  simp only [CollatzResearch.WordTrace]
  refine ⟨229282349032602442486686131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152854899355068294991124087 229282349032602442486686131)
  ·
    refine ⟨343923523548903663730029197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229282349032602442486686131 343923523548903663730029197)
    ·
      refine ⟨128971321330838873898760949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343923523548903663730029197 128971321330838873898760949)
      ·
        refine ⟨12091061374766144428008839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128971321330838873898760949 12091061374766144428008839)
        ·
          refine ⟨18136592062149216642013259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12091061374766144428008839 18136592062149216642013259)
          ·
            refine ⟨27204888093223824963019889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18136592062149216642013259 27204888093223824963019889)
            ·
              refine ⟨20403666069917868722264917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27204888093223824963019889 20403666069917868722264917)
              ·
                refine ⟨119552730878425012044521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20403666069917868722264917 119552730878425012044521)
                ·
                  rfl

theorem cell23_6286359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 9].length) (baseStart_6286359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286359 prefixEnd_6286359 := by exact prefixLift 6286359
  have htrace : WordTrace (prefixWord ++ tailWord_6286359) baseStart_6286359 baseEnd_6286359 := by
    simpa [prefixWord, tailWord_6286359, baseEnd_6286359] using wordTrace_append hprefix tailTrace_6286359
  have hstable : (prefixWord ++ tailWord_6286359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286359).length < 2 ^ (prefixWord ++ tailWord_6286359).sum := by decide
  have hdescent : baseEnd_6286359 < baseStart_6286359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286373 : List Nat := [1, 3, 1, 2, 2, 2, 5, 1, 1, 2, 3]
def baseStart_6286373 : Nat := 118140960795 + 6286373 * 2 ^ 59
def prefixEnd_6286373 : Nat := 4983230072969 + 3 ^ 40 * 6286373 * 2
def baseEnd_6286373 : Nat := 3227930922446638270427003

theorem tailTrace_6286373 : CollatzResearch.WordTrace tailWord_6286373 prefixEnd_6286373 3227930922446638270427003 := by
  unfold tailWord_6286373
  simp only [CollatzResearch.WordTrace]
  refine ⟨229282859654551722877695773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152855239769701148585130515 229282859654551722877695773)
  ·
    refine ⟨85981072370456896079135915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229282859654551722877695773 85981072370456896079135915)
    ·
      refine ⟨128971608555685344118703873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85981072370456896079135915 128971608555685344118703873)
      ·
        refine ⟨96728706416764008089027905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128971608555685344118703873 96728706416764008089027905)
        ·
          refine ⟨72546529812573006066770929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96728706416764008089027905 72546529812573006066770929)
          ·
            refine ⟨54409897359429754550078197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72546529812573006066770929 54409897359429754550078197)
            ·
              refine ⟨5100927877446539489069831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54409897359429754550078197 5100927877446539489069831)
              ·
                refine ⟨7651391816169809233604747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5100927877446539489069831 7651391816169809233604747)
                ·
                  refine ⟨11477087724254713850407121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7651391816169809233604747 11477087724254713850407121)
                  ·
                    refine ⟨8607815793191035387805341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11477087724254713850407121 8607815793191035387805341)
                    ·
                      refine ⟨3227930922446638270427003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8607815793191035387805341 3227930922446638270427003)
                      ·
                        rfl

theorem cell23_6286373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_6286373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286373 prefixEnd_6286373 := by exact prefixLift 6286373
  have htrace : WordTrace (prefixWord ++ tailWord_6286373) baseStart_6286373 baseEnd_6286373 := by
    simpa [prefixWord, tailWord_6286373, baseEnd_6286373] using wordTrace_append hprefix tailTrace_6286373
  have hstable : (prefixWord ++ tailWord_6286373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286373).length < 2 ^ (prefixWord ++ tailWord_6286373).sum := by decide
  have hdescent : baseEnd_6286373 < baseStart_6286373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286426 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2]
def baseStart_6286426 : Nat := 118140960795 + 6286426 * 2 ^ 59
def prefixEnd_6286426 : Nat := 4983230072969 + 3 ^ 40 * 6286426 * 2
def baseEnd_6286426 : Nat := 3227958136921326563064259

theorem tailTrace_6286426 : CollatzResearch.WordTrace tailWord_6286426 prefixEnd_6286426 3227958136921326563064259 := by
  unfold tailWord_6286426
  simp only [CollatzResearch.WordTrace]
  refine ⟨57321198180839928232343783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152856528482239808619583421 57321198180839928232343783)
  ·
    refine ⟨85981797271259892348515675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57321198180839928232343783 85981797271259892348515675)
    ·
      refine ⟨128972695906889838522773513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85981797271259892348515675 128972695906889838522773513)
      ·
        refine ⟨96729521930167378892080135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128972695906889838522773513 96729521930167378892080135)
        ·
          refine ⟨145094282895251068338120203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96729521930167378892080135 145094282895251068338120203)
          ·
            refine ⟨217641424342876602507180305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145094282895251068338120203 217641424342876602507180305)
            ·
              refine ⟨163231068257157451880385229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217641424342876602507180305 163231068257157451880385229)
              ·
                refine ⟨61211650596434044455144461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163231068257157451880385229 61211650596434044455144461)
                ·
                  refine ⟨22954368973662766670679173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61211650596434044455144461 22954368973662766670679173)
                  ·
                    refine ⟨4303944182561768750752345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22954368973662766670679173 4303944182561768750752345)
                    ·
                      refine ⟨3227958136921326563064259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4303944182561768750752345 3227958136921326563064259)
                      ·
                        rfl

theorem cell23_6286426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_6286426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286426 prefixEnd_6286426 := by exact prefixLift 6286426
  have htrace : WordTrace (prefixWord ++ tailWord_6286426) baseStart_6286426 baseEnd_6286426 := by
    simpa [prefixWord, tailWord_6286426, baseEnd_6286426] using wordTrace_append hprefix tailTrace_6286426
  have hstable : (prefixWord ++ tailWord_6286426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286426).length < 2 ^ (prefixWord ++ tailWord_6286426).sum := by decide
  have hdescent : baseEnd_6286426 < baseStart_6286426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286496 : List Nat := [2, 1, 1, 4, 2, 1, 3, 2, 2, 5]
def baseStart_6286496 : Nat := 118140960795 + 6286496 * 2 ^ 59
def prefixEnd_6286496 : Nat := 4983230072969 + 3 ^ 40 * 6286496 * 2
def baseEnd_6286496 : Nat := 1075998026855713763062979

theorem tailTrace_6286496 : CollatzResearch.WordTrace tailWord_6286496 prefixEnd_6286496 1075998026855713763062979 := by
  unfold tailWord_6286496
  simp only [CollatzResearch.WordTrace]
  refine ⟨114643672916553057442211671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152858230555404076589615561 114643672916553057442211671)
  ·
    refine ⟨171965509374829586163317507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114643672916553057442211671 171965509374829586163317507)
    ·
      refine ⟨257948264062244379244976261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171965509374829586163317507 257948264062244379244976261)
      ·
        refine ⟨48365299511670821108433049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257948264062244379244976261 48365299511670821108433049)
        ·
          refine ⟨36273974633753115831324787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48365299511670821108433049 36273974633753115831324787)
          ·
            refine ⟨54410961950629673746987181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36273974633753115831324787 54410961950629673746987181)
            ·
              refine ⟨20404110731486127655120193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54410961950629673746987181 20404110731486127655120193)
              ·
                refine ⟨15303083048614595741340145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20404110731486127655120193 15303083048614595741340145)
                ·
                  refine ⟨11477312286460946806005109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15303083048614595741340145 11477312286460946806005109)
                  ·
                    refine ⟨1075998026855713763062979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11477312286460946806005109 1075998026855713763062979)
                    ·
                      rfl

theorem cell23_6286496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 2, 5].length) (baseStart_6286496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286496 prefixEnd_6286496 := by exact prefixLift 6286496
  have htrace : WordTrace (prefixWord ++ tailWord_6286496) baseStart_6286496 baseEnd_6286496 := by
    simpa [prefixWord, tailWord_6286496, baseEnd_6286496] using wordTrace_append hprefix tailTrace_6286496
  have hstable : (prefixWord ++ tailWord_6286496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286496).length < 2 ^ (prefixWord ++ tailWord_6286496).sum := by decide
  have hdescent : baseEnd_6286496 < baseStart_6286496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286500 : List Nat := [2, 3, 1, 2, 3, 2, 3, 2, 5]
def baseStart_6286500 : Nat := 118140960795 + 6286500 * 2 ^ 59
def prefixEnd_6286500 : Nat := 4983230072969 + 3 ^ 40 * 6286500 * 2
def baseEnd_6286500 : Nat := 358666237165528808170991

theorem tailTrace_6286500 : CollatzResearch.WordTrace tailWord_6286500 prefixEnd_6286500 358666237165528808170991 := by
  unfold tailWord_6286500
  simp only [CollatzResearch.WordTrace]
  refine ⟨114643745862545811783784477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152858327816727749045045969 114643745862545811783784477)
  ·
    refine ⟨42991404698454679418919179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114643745862545811783784477 42991404698454679418919179)
    ·
      refine ⟨64487107047682019128378769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42991404698454679418919179 64487107047682019128378769)
      ·
        refine ⟨48365330285761514346284077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64487107047682019128378769 48365330285761514346284077)
        ·
          refine ⟨18136998857160567879856529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48365330285761514346284077 18136998857160567879856529)
          ·
            refine ⟨13602749142870425909892397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18136998857160567879856529 13602749142870425909892397)
            ·
              refine ⟨5101030928576409716209649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13602749142870425909892397 5101030928576409716209649)
              ·
                refine ⟨3825773196432307287157237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5101030928576409716209649 3825773196432307287157237)
                ·
                  refine ⟨358666237165528808170991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3825773196432307287157237 358666237165528808170991)
                  ·
                    rfl

theorem cell23_6286500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_6286500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286500 prefixEnd_6286500 := by exact prefixLift 6286500
  have htrace : WordTrace (prefixWord ++ tailWord_6286500) baseStart_6286500 baseEnd_6286500 := by
    simpa [prefixWord, tailWord_6286500, baseEnd_6286500] using wordTrace_append hprefix tailTrace_6286500
  have hstable : (prefixWord ++ tailWord_6286500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286500).length < 2 ^ (prefixWord ++ tailWord_6286500).sum := by decide
  have hdescent : baseEnd_6286500 < baseStart_6286500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286536 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 1, 4, 3]
def baseStart_6286536 : Nat := 118140960795 + 6286536 * 2 ^ 59
def prefixEnd_6286536 : Nat := 4983230072969 + 3 ^ 40 * 6286536 * 2
def baseEnd_6286536 : Nat := 3228014619793321132688753

theorem tailTrace_6286536 : CollatzResearch.WordTrace tailWord_6286536 prefixEnd_6286536 3228014619793321132688753 := by
  unfold tailWord_6286536
  simp only [CollatzResearch.WordTrace]
  refine ⟨114644402376480600857939731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152859203168640801143919641 114644402376480600857939731)
  ·
    refine ⟨171966603564720901286909597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114644402376480600857939731 171966603564720901286909597)
    ·
      refine ⟨64487476336770337982591099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171966603564720901286909597 64487476336770337982591099)
      ·
        refine ⟨96731214505155506973886649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64487476336770337982591099 96731214505155506973886649)
        ·
          refine ⟨72548410878866630230414987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96731214505155506973886649 72548410878866630230414987)
          ·
            refine ⟨108822616318299945345622481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72548410878866630230414987 108822616318299945345622481)
            ·
              refine ⟨81616962238724959009216861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108822616318299945345622481 81616962238724959009216861)
              ·
                refine ⟨30606360839521859628456323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81616962238724959009216861 30606360839521859628456323)
                ·
                  refine ⟨45909541259282789442684485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30606360839521859628456323 45909541259282789442684485)
                  ·
                    refine ⟨8608038986115523020503341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45909541259282789442684485 8608038986115523020503341)
                    ·
                      refine ⟨3228014619793321132688753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8608038986115523020503341 3228014619793321132688753)
                      ·
                        rfl

theorem cell23_6286536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_6286536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286536 prefixEnd_6286536 := by exact prefixLift 6286536
  have htrace : WordTrace (prefixWord ++ tailWord_6286536) baseStart_6286536 baseEnd_6286536 := by
    simpa [prefixWord, tailWord_6286536, baseEnd_6286536] using wordTrace_append hprefix tailTrace_6286536
  have hstable : (prefixWord ++ tailWord_6286536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286536).length < 2 ^ (prefixWord ++ tailWord_6286536).sum := by decide
  have hdescent : baseEnd_6286536 < baseStart_6286536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286539 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 8]
def baseStart_6286539 : Nat := 118140960795 + 6286539 * 2 ^ 59
def prefixEnd_6286539 : Nat := 4983230072969 + 3 ^ 40 * 6286539 * 2
def baseEnd_6286539 : Nat := 358668462248364957883471

theorem tailTrace_6286539 : CollatzResearch.WordTrace tailWord_6286539 prefixEnd_6286539 358668462248364957883471 := by
  unfold tailWord_6286539
  simp only [CollatzResearch.WordTrace]
  refine ⟨229288914171950333228238671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152859276114633555485492447 229288914171950333228238671)
  ·
    refine ⟨343933371257925499842358007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229288914171950333228238671 343933371257925499842358007)
    ·
      refine ⟨515900056886888249763537011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343933371257925499842358007 515900056886888249763537011)
      ·
        refine ⟨773850085330332374645305517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515900056886888249763537011 773850085330332374645305517)
        ·
          refine ⟨290193781998874640491989569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 773850085330332374645305517 290193781998874640491989569)
          ·
            refine ⟨217645336499155980368992177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290193781998874640491989569 217645336499155980368992177)
            ·
              refine ⟨163234002374366985276744133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217645336499155980368992177 163234002374366985276744133)
              ·
                refine ⟨30606375445193809739389525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163234002374366985276744133 30606375445193809739389525)
                ·
                  refine ⟨358668462248364957883471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30606375445193809739389525 358668462248364957883471)
                  ·
                    rfl

theorem cell23_6286539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 8].length) (baseStart_6286539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286539 prefixEnd_6286539 := by exact prefixLift 6286539
  have htrace : WordTrace (prefixWord ++ tailWord_6286539) baseStart_6286539 baseEnd_6286539 := by
    simpa [prefixWord, tailWord_6286539, baseEnd_6286539] using wordTrace_append hprefix tailTrace_6286539
  have hstable : (prefixWord ++ tailWord_6286539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286539).length < 2 ^ (prefixWord ++ tailWord_6286539).sum := by decide
  have hdescent : baseEnd_6286539 < baseStart_6286539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286546 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_6286546 : Nat := 118140960795 + 6286546 * 2 ^ 59
def prefixEnd_6286546 : Nat := 4983230072969 + 3 ^ 40 * 6286546 * 2
def baseEnd_6286546 : Nat := 3228019754599866093563707

theorem tailTrace_6286546 : CollatzResearch.WordTrace tailWord_6286546 prefixEnd_6286546 3228019754599866093563707 := by
  unfold tailWord_6286546
  simp only [CollatzResearch.WordTrace]
  refine ⟨57322292370731243355935873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152859446321949982282495661 57322292370731243355935873)
  ·
    refine ⟨42991719278048432516951905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57322292370731243355935873 42991719278048432516951905)
    ·
      refine ⟨32243789458536324387713929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42991719278048432516951905 32243789458536324387713929)
      ·
        refine ⟨24182842093902243290785447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32243789458536324387713929 24182842093902243290785447)
        ·
          refine ⟨36274263140853364936178171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24182842093902243290785447 36274263140853364936178171)
          ·
            refine ⟨54411394711280047404267257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36274263140853364936178171 54411394711280047404267257)
            ·
              refine ⟨40808546033460035553200443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54411394711280047404267257 40808546033460035553200443)
              ·
                refine ⟨61212819050190053329800665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40808546033460035553200443 61212819050190053329800665)
                ·
                  refine ⟨45909614287642539997350499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61212819050190053329800665 45909614287642539997350499)
                  ·
                    refine ⟨68864421431463809996025749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45909614287642539997350499 68864421431463809996025749)
                    ·
                      refine ⟨3228019754599866093563707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68864421431463809996025749 3228019754599866093563707)
                      ·
                        rfl

theorem cell23_6286546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_6286546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286546 prefixEnd_6286546 := by exact prefixLift 6286546
  have htrace : WordTrace (prefixWord ++ tailWord_6286546) baseStart_6286546 baseEnd_6286546 := by
    simpa [prefixWord, tailWord_6286546, baseEnd_6286546] using wordTrace_append hprefix tailTrace_6286546
  have hstable : (prefixWord ++ tailWord_6286546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286546).length < 2 ^ (prefixWord ++ tailWord_6286546).sum := by decide
  have hdescent : baseEnd_6286546 < baseStart_6286546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286560 : List Nat := [2, 1, 1, 3, 1, 5, 1, 4, 1, 4]
def baseStart_6286560 : Nat := 118140960795 + 6286560 * 2 ^ 59
def prefixEnd_6286560 : Nat := 4983230072969 + 3 ^ 40 * 6286560 * 2
def baseEnd_6286560 : Nat := 1076008981109676346262881

theorem tailTrace_6286560 : CollatzResearch.WordTrace tailWord_6286560 prefixEnd_6286560 1076008981109676346262881 := by
  unfold tailWord_6286560
  simp only [CollatzResearch.WordTrace]
  refine ⟨114644840052437126907376567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152859786736582835876502089 114644840052437126907376567)
  ·
    refine ⟨171967260078655690361064851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114644840052437126907376567 171967260078655690361064851)
    ·
      refine ⟨257950890117983535541597277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171967260078655690361064851 257950890117983535541597277)
      ·
        refine ⟨96731583794243825828098979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257950890117983535541597277 96731583794243825828098979)
        ·
          refine ⟨145097375691365738742148469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96731583794243825828098979 145097375691365738742148469)
          ·
            refine ⟨13602878971065538007076419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 145097375691365738742148469 13602878971065538007076419)
            ·
              refine ⟨20404318456598307010614629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13602878971065538007076419 20404318456598307010614629)
              ·
                refine ⟨3825809710612182564490243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20404318456598307010614629 3825809710612182564490243)
                ·
                  refine ⟨5738714565918273846735365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3825809710612182564490243 5738714565918273846735365)
                  ·
                    refine ⟨1076008981109676346262881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5738714565918273846735365 1076008981109676346262881)
                    ·
                      rfl

theorem cell23_6286560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 1, 4].length) (baseStart_6286560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286560 prefixEnd_6286560 := by exact prefixLift 6286560
  have htrace : WordTrace (prefixWord ++ tailWord_6286560) baseStart_6286560 baseEnd_6286560 := by
    simpa [prefixWord, tailWord_6286560, baseEnd_6286560] using wordTrace_append hprefix tailTrace_6286560
  have hstable : (prefixWord ++ tailWord_6286560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286560).length < 2 ^ (prefixWord ++ tailWord_6286560).sum := by decide
  have hdescent : baseEnd_6286560 < baseStart_6286560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286569 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 1, 11]
def baseStart_6286569 : Nat := 118140960795 + 6286569 * 2 ^ 59
def prefixEnd_6286569 : Nat := 4983230072969 + 3 ^ 40 * 6286569 * 2
def baseEnd_6286569 : Nat := 1076010521551639834525367

theorem tailTrace_6286569 : CollatzResearch.WordTrace tailWord_6286569 prefixEnd_6286569 1076010521551639834525367 := by
  unfold tailWord_6286569
  simp only [CollatzResearch.WordTrace]
  refine ⟨229290008361841648351830761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152860005574561098901220507 229290008361841648351830761)
  ·
    refine ⟨171967506271381236263873071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229290008361841648351830761 171967506271381236263873071)
    ·
      refine ⟨257951259407071854395809607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171967506271381236263873071 257951259407071854395809607)
      ·
        refine ⟨386926889110607781593714411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257951259407071854395809607 386926889110607781593714411)
        ·
          refine ⟨580390333665911672390571617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386926889110607781593714411 580390333665911672390571617)
          ·
            refine ⟨435292750249433754292928713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 580390333665911672390571617 435292750249433754292928713)
            ·
              refine ⟨326469562687075315719696535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435292750249433754292928713 326469562687075315719696535)
              ·
                refine ⟨489704344030612973579544803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326469562687075315719696535 489704344030612973579544803)
                ·
                  refine ⟨734556516045919460369317205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489704344030612973579544803 734556516045919460369317205)
                  ·
                    refine ⟨1076010521551639834525367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 734556516045919460369317205 1076010521551639834525367)
                    ·
                      rfl

theorem cell23_6286569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 11].length) (baseStart_6286569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286569 prefixEnd_6286569 := by exact prefixLift 6286569
  have htrace : WordTrace (prefixWord ++ tailWord_6286569) baseStart_6286569 baseEnd_6286569 := by
    simpa [prefixWord, tailWord_6286569, baseEnd_6286569] using wordTrace_append hprefix tailTrace_6286569
  have hstable : (prefixWord ++ tailWord_6286569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286569).length < 2 ^ (prefixWord ++ tailWord_6286569).sum := by decide
  have hdescent : baseEnd_6286569 < baseStart_6286569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286573 : List Nat := [1, 5, 1, 2, 2, 1, 2, 3, 6]
def baseStart_6286573 : Nat := 118140960795 + 6286573 * 2 ^ 59
def prefixEnd_6286573 : Nat := 4983230072969 + 3 ^ 40 * 6286573 * 2
def baseEnd_6286573 : Nat := 358670402064170831991787

theorem tailTrace_6286573 : CollatzResearch.WordTrace tailWord_6286573 prefixEnd_6286573 358670402064170831991787 := by
  unfold tailWord_6286573
  simp only [CollatzResearch.WordTrace]
  refine ⟨229290154253827157034976373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152860102835884771356650915 229290154253827157034976373)
  ·
    refine ⟨21495951961296295972029035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229290154253827157034976373 21495951961296295972029035)
    ·
      refine ⟨32243927941944443958043553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21495951961296295972029035 32243927941944443958043553)
      ·
        refine ⟨24182945956458332968532665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32243927941944443958043553 24182945956458332968532665)
        ·
          refine ⟨18137209467343749726399499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24182945956458332968532665 18137209467343749726399499)
          ·
            refine ⟨27205814201015624589599249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18137209467343749726399499 27205814201015624589599249)
            ·
              refine ⟨20404360650761718442199437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27205814201015624589599249 20404360650761718442199437)
              ·
                refine ⟨7651635244035644415824789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20404360650761718442199437 7651635244035644415824789)
                ·
                  refine ⟨358670402064170831991787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7651635244035644415824789 358670402064170831991787)
                  ·
                    rfl

theorem cell23_6286573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_6286573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286573 prefixEnd_6286573 := by exact prefixLift 6286573
  have htrace : WordTrace (prefixWord ++ tailWord_6286573) baseStart_6286573 baseEnd_6286573 := by
    simpa [prefixWord, tailWord_6286573, baseEnd_6286573] using wordTrace_append hprefix tailTrace_6286573
  have hstable : (prefixWord ++ tailWord_6286573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286573).length < 2 ^ (prefixWord ++ tailWord_6286573).sum := by decide
  have hdescent : baseEnd_6286573 < baseStart_6286573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286583 : List Nat := [1, 1, 3, 1, 1, 1, 2, 6, 3, 1, 3]
def baseStart_6286583 : Nat := 118140960795 + 6286583 * 2 ^ 59
def prefixEnd_6286583 : Nat := 4983230072969 + 3 ^ 40 * 6286583 * 2
def baseEnd_6286583 : Nat := 3228038753384082448801037

theorem tailTrace_6286583 : CollatzResearch.WordTrace tailWord_6286583 prefixEnd_6286583 3228038753384082448801037 := by
  unfold tailWord_6286583
  simp only [CollatzResearch.WordTrace]
  refine ⟨229290518983790928742840403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152860345989193952495226935 229290518983790928742840403)
  ·
    refine ⟨343935778475686393114260605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229290518983790928742840403 343935778475686393114260605)
    ·
      refine ⟨128975916928382397417847727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343935778475686393114260605 128975916928382397417847727)
      ·
        refine ⟨193463875392573596126771591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128975916928382397417847727 193463875392573596126771591)
        ·
          refine ⟨290195813088860394190157387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193463875392573596126771591 290195813088860394190157387)
          ·
            refine ⟨435293719633290591285236081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290195813088860394190157387 435293719633290591285236081)
            ·
              refine ⟨326470289724967943463927061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435293719633290591285236081 326470289724967943463927061)
              ·
                refine ⟨15303294830857872349871581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 326470289724967943463927061 15303294830857872349871581)
                ·
                  refine ⟨5738735561571702131201843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15303294830857872349871581 5738735561571702131201843)
                  ·
                    refine ⟨8608103342357553196802765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5738735561571702131201843 8608103342357553196802765)
                    ·
                      refine ⟨3228038753384082448801037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8608103342357553196802765 3228038753384082448801037)
                      ·
                        rfl

theorem cell23_6286583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 1, 3].length) (baseStart_6286583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286583 prefixEnd_6286583 := by exact prefixLift 6286583
  have htrace : WordTrace (prefixWord ++ tailWord_6286583) baseStart_6286583 baseEnd_6286583 := by
    simpa [prefixWord, tailWord_6286583, baseEnd_6286583] using wordTrace_append hprefix tailTrace_6286583
  have hstable : (prefixWord ++ tailWord_6286583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286583).length < 2 ^ (prefixWord ++ tailWord_6286583).sum := by decide
  have hdescent : baseEnd_6286583 < baseStart_6286583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286586 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 3, 5]
def baseStart_6286586 : Nat := 118140960795 + 6286586 * 2 ^ 59
def prefixEnd_6286586 : Nat := 4983230072969 + 3 ^ 40 * 6286586 * 2
def baseEnd_6286586 : Nat := 1076013431275348645687841

theorem tailTrace_6286586 : CollatzResearch.WordTrace tailWord_6286586 prefixEnd_6286586 1076013431275348645687841 := by
  unfold tailWord_6286586
  simp only [CollatzResearch.WordTrace]
  refine ⟨57322657100695015063799903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152860418935186706836799741 57322657100695015063799903)
  ·
    refine ⟨85983985651042522595699855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57322657100695015063799903 85983985651042522595699855)
    ·
      refine ⟨128975978476563783893549783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85983985651042522595699855 128975978476563783893549783)
      ·
        refine ⟨193463967714845675840324675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128975978476563783893549783 193463967714845675840324675)
        ·
          refine ⟨290195951572268513760487013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193463967714845675840324675 290195951572268513760487013)
          ·
            refine ⟨54411740919800346330091315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 290195951572268513760487013 54411740919800346330091315)
            ·
              refine ⟨81617611379700519495136973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54411740919800346330091315 81617611379700519495136973)
              ·
                refine ⟨30606604267387694810676365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81617611379700519495136973 30606604267387694810676365)
                ·
                  refine ⟨11477476600270385554003637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30606604267387694810676365 11477476600270385554003637)
                  ·
                    refine ⟨1076013431275348645687841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11477476600270385554003637 1076013431275348645687841)
                    ·
                      rfl

theorem cell23_6286586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_6286586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286586 prefixEnd_6286586 := by exact prefixLift 6286586
  have htrace : WordTrace (prefixWord ++ tailWord_6286586) baseStart_6286586 baseEnd_6286586 := by
    simpa [prefixWord, tailWord_6286586, baseEnd_6286586] using wordTrace_append hprefix tailTrace_6286586
  have hstable : (prefixWord ++ tailWord_6286586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286586).length < 2 ^ (prefixWord ++ tailWord_6286586).sum := by decide
  have hdescent : baseEnd_6286586 < baseStart_6286586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286594 : List Nat := [3, 4, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_6286594 : Nat := 118140960795 + 6286594 * 2 ^ 59
def prefixEnd_6286594 : Nat := 4983230072969 + 3 ^ 40 * 6286594 * 2
def baseEnd_6286594 : Nat := 1076014800557093968587829

theorem tailTrace_6286594 : CollatzResearch.WordTrace tailWord_6286594 prefixEnd_6286594 1076014800557093968587829 := by
  unfold tailWord_6286594
  simp only [CollatzResearch.WordTrace]
  refine ⟨57322730046687769405372709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152860613457834051747660557 57322730046687769405372709)
  ·
    refine ⟨10748011883753956763507383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57322730046687769405372709 10748011883753956763507383)
    ·
      refine ⟨16122017825630935145261075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10748011883753956763507383 16122017825630935145261075)
      ·
        refine ⟨24183026738446402717891613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16122017825630935145261075 24183026738446402717891613)
        ·
          refine ⟨9068635026917401019209355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24183026738446402717891613 9068635026917401019209355)
          ·
            refine ⟨13602952540376101528814033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9068635026917401019209355 13602952540376101528814033)
            ·
              refine ⟨10202214405282076146610525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13602952540376101528814033 10202214405282076146610525)
              ·
                refine ⟨3825830401980778554978947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10202214405282076146610525 3825830401980778554978947)
                ·
                  refine ⟨5738745602971167832468421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3825830401980778554978947 5738745602971167832468421)
                  ·
                    refine ⟨1076014800557093968587829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5738745602971167832468421 1076014800557093968587829)
                    ·
                      rfl

theorem cell23_6286594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_6286594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286594 prefixEnd_6286594 := by exact prefixLift 6286594
  have htrace : WordTrace (prefixWord ++ tailWord_6286594) baseStart_6286594 baseEnd_6286594 := by
    simpa [prefixWord, tailWord_6286594, baseEnd_6286594] using wordTrace_append hprefix tailTrace_6286594
  have hstable : (prefixWord ++ tailWord_6286594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286594).length < 2 ^ (prefixWord ++ tailWord_6286594).sum := by decide
  have hdescent : baseEnd_6286594 < baseStart_6286594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286603 : List Nat := [1, 1, 1, 1, 5, 4, 1, 3, 1, 5]
def baseStart_6286603 : Nat := 118140960795 + 6286603 * 2 ^ 59
def prefixEnd_6286603 : Nat := 4983230072969 + 3 ^ 40 * 6286603 * 2
def baseEnd_6286603 : Nat := 1076016340999057456850315

theorem tailTrace_6286603 : CollatzResearch.WordTrace tailWord_6286603 prefixEnd_6286603 1076016340999057456850315 := by
  unfold tailWord_6286603
  simp only [CollatzResearch.WordTrace]
  refine ⟨229291248443718472158568463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152860832295812314772378975 229291248443718472158568463)
  ·
    refine ⟨343936872665577708237852695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229291248443718472158568463 343936872665577708237852695)
    ·
      refine ⟨515905308998366562356779043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343936872665577708237852695 515905308998366562356779043)
      ·
        refine ⟨773857963497549843535168565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515905308998366562356779043 773857963497549843535168565)
        ·
          refine ⟨72549184077895297831422053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 773857963497549843535168565 72549184077895297831422053)
          ·
            refine ⟨13602972014605368343391635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72549184077895297831422053 13602972014605368343391635)
            ·
              refine ⟨20404458021908052515087453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13602972014605368343391635 20404458021908052515087453)
              ·
                refine ⟨7651671758215519693157795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20404458021908052515087453 7651671758215519693157795)
                ·
                  refine ⟨11477507637323279539736693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7651671758215519693157795 11477507637323279539736693)
                  ·
                    refine ⟨1076016340999057456850315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11477507637323279539736693 1076016340999057456850315)
                    ·
                      rfl

theorem cell23_6286603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 5].length) (baseStart_6286603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286603 prefixEnd_6286603 := by exact prefixLift 6286603
  have htrace : WordTrace (prefixWord ++ tailWord_6286603) baseStart_6286603 baseEnd_6286603 := by
    simpa [prefixWord, tailWord_6286603, baseEnd_6286603] using wordTrace_append hprefix tailTrace_6286603
  have hstable : (prefixWord ++ tailWord_6286603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286603).length < 2 ^ (prefixWord ++ tailWord_6286603).sum := by decide
  have hdescent : baseEnd_6286603 < baseStart_6286603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286637 : List Nat := [1, 5, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_6286637 : Nat := 118140960795 + 6286637 * 2 ^ 59
def prefixEnd_6286637 : Nat := 4983230072969 + 3 ^ 40 * 6286637 * 2
def baseEnd_6286637 : Nat := 1076022160446475079175263

theorem tailTrace_6286637 : CollatzResearch.WordTrace tailWord_6286637 prefixEnd_6286637 1076022160446475079175263 := by
  unfold tailWord_6286637
  simp only [CollatzResearch.WordTrace]
  refine ⟨229292488525595295965306165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152861659017063530643537443 229292488525595295965306165)
  ·
    refine ⟨21496170799274558996747453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229292488525595295965306165 21496170799274558996747453)
    ·
      refine ⟨8061064049727959623780295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21496170799274558996747453 8061064049727959623780295)
      ·
        refine ⟨12091596074591939435670443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8061064049727959623780295 12091596074591939435670443)
        ·
          refine ⟨18137394111887909153505665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12091596074591939435670443 18137394111887909153505665)
          ·
            refine ⟨13603045583915931865129249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18137394111887909153505665 13603045583915931865129249)
            ·
              refine ⟨10202284187936948898846937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13603045583915931865129249 10202284187936948898846937)
              ·
                refine ⟨7651713140952711674135203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10202284187936948898846937 7651713140952711674135203)
                ·
                  refine ⟨11477569711429067511202805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7651713140952711674135203 11477569711429067511202805)
                  ·
                    refine ⟨1076022160446475079175263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11477569711429067511202805 1076022160446475079175263)
                    ·
                      rfl

theorem cell23_6286637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_6286637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286637 prefixEnd_6286637 := by exact prefixLift 6286637
  have htrace : WordTrace (prefixWord ++ tailWord_6286637) baseStart_6286637 baseEnd_6286637 := by
    simpa [prefixWord, tailWord_6286637, baseEnd_6286637] using wordTrace_append hprefix tailTrace_6286637
  have hstable : (prefixWord ++ tailWord_6286637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286637).length < 2 ^ (prefixWord ++ tailWord_6286637).sum := by decide
  have hdescent : baseEnd_6286637 < baseStart_6286637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286640 : List Nat := [2, 1, 1, 1, 2, 2, 3, 4, 3, 2, 2]
def baseStart_6286640 : Nat := 118140960795 + 6286640 * 2 ^ 59
def prefixEnd_6286640 : Nat := 4983230072969 + 3 ^ 40 * 6286640 * 2
def baseEnd_6286640 : Nat := 3228068021781388725788275

theorem tailTrace_6286640 : CollatzResearch.WordTrace tailWord_6286640 prefixEnd_6286640 3228068021781388725788275 := by
  unfold tailWord_6286640
  simp only [CollatzResearch.WordTrace]
  refine ⟨114646298972292213738832687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152861731963056284985110249 114646298972292213738832687)
  ·
    refine ⟨171969448458438320608249031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114646298972292213738832687 171969448458438320608249031)
    ·
      refine ⟨257954172687657480912373547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171969448458438320608249031 257954172687657480912373547)
      ·
        refine ⟨386931259031486221368560321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257954172687657480912373547 386931259031486221368560321)
        ·
          refine ⟨290198444273614666026420241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386931259031486221368560321 290198444273614666026420241)
          ·
            refine ⟨217648833205210999519815181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290198444273614666026420241 217648833205210999519815181)
            ·
              refine ⟨81618312451954124819930693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217648833205210999519815181 81618312451954124819930693)
              ·
                refine ⟨15303433584741398403737005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81618312451954124819930693 15303433584741398403737005)
                ·
                  refine ⟨5738787594278024401401377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15303433584741398403737005 5738787594278024401401377)
                  ·
                    refine ⟨4304090695708518301051033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5738787594278024401401377 4304090695708518301051033)
                    ·
                      refine ⟨3228068021781388725788275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4304090695708518301051033 3228068021781388725788275)
                      ·
                        rfl

theorem cell23_6286640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 3, 2, 2].length) (baseStart_6286640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286640 prefixEnd_6286640 := by exact prefixLift 6286640
  have htrace : WordTrace (prefixWord ++ tailWord_6286640) baseStart_6286640 baseEnd_6286640 := by
    simpa [prefixWord, tailWord_6286640, baseEnd_6286640] using wordTrace_append hprefix tailTrace_6286640
  have hstable : (prefixWord ++ tailWord_6286640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286640).length < 2 ^ (prefixWord ++ tailWord_6286640).sum := by decide
  have hdescent : baseEnd_6286640 < baseStart_6286640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286660 : List Nat := [2, 3, 4, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_6286660 : Nat := 118140960795 + 6286660 * 2 ^ 59
def prefixEnd_6286660 : Nat := 4983230072969 + 3 ^ 40 * 6286660 * 2
def baseEnd_6286660 : Nat := 3228078291394478647538183

theorem tailTrace_6286660 : CollatzResearch.WordTrace tailWord_6286660 prefixEnd_6286660 3228078291394478647538183 := by
  unfold tailWord_6286660
  simp only [CollatzResearch.WordTrace]
  refine ⟨114646663702255985446696717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152862218269674647262262289 114646663702255985446696717)
  ·
    refine ⟨42992498888345994542511269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114646663702255985446696717 42992498888345994542511269)
    ·
      refine ⟨8061093541564873976720863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42992498888345994542511269 8061093541564873976720863)
      ·
        refine ⟨12091640312347310965081295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8061093541564873976720863 12091640312347310965081295)
        ·
          refine ⟨18137460468520966447621943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12091640312347310965081295 18137460468520966447621943)
          ·
            refine ⟨27206190702781449671432915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18137460468520966447621943 27206190702781449671432915)
            ·
              refine ⟨40809286054172174507149373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27206190702781449671432915 40809286054172174507149373)
              ·
                refine ⟨15303482270314565440181015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40809286054172174507149373 15303482270314565440181015)
                ·
                  refine ⟨22955223405471848160271523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15303482270314565440181015 22955223405471848160271523)
                  ·
                    refine ⟨34432835108207772240407285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22955223405471848160271523 34432835108207772240407285)
                    ·
                      refine ⟨3228078291394478647538183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34432835108207772240407285 3228078291394478647538183)
                      ·
                        rfl

theorem cell23_6286660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_6286660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286660 prefixEnd_6286660 := by exact prefixLift 6286660
  have htrace : WordTrace (prefixWord ++ tailWord_6286660) baseStart_6286660 baseEnd_6286660 := by
    simpa [prefixWord, tailWord_6286660, baseEnd_6286660] using wordTrace_append hprefix tailTrace_6286660
  have hstable : (prefixWord ++ tailWord_6286660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286660).length < 2 ^ (prefixWord ++ tailWord_6286660).sum := by decide
  have hdescent : baseEnd_6286660 < baseStart_6286660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286690 : List Nat := [3, 3, 2, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_6286690 : Nat := 118140960795 + 6286690 * 2 ^ 59
def prefixEnd_6286690 : Nat := 4983230072969 + 3 ^ 40 * 6286690 * 2
def baseEnd_6286690 : Nat := 3228093695814113530163045

theorem tailTrace_6286690 : CollatzResearch.WordTrace tailWord_6286690 prefixEnd_6286690 3228093695814113530163045 := by
  unfold tailWord_6286690
  simp only [CollatzResearch.WordTrace]
  refine ⟨57323605398600821504246381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152862947729602190677990349 57323605398600821504246381)
  ·
    refine ⟨21496352024475308064092393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57323605398600821504246381 21496352024475308064092393)
    ·
      refine ⟨16122264018356481048069295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21496352024475308064092393 16122264018356481048069295)
      ·
        refine ⟨24183396027534721572103943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16122264018356481048069295 24183396027534721572103943)
        ·
          refine ⟨36275094041302082358155915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24183396027534721572103943 36275094041302082358155915)
          ·
            refine ⟨54412641061953123537233873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36275094041302082358155915 54412641061953123537233873)
            ·
              refine ⟨40809480796464842652925405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54412641061953123537233873 40809480796464842652925405)
              ·
                refine ⟨15303555298674315994847027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40809480796464842652925405 15303555298674315994847027)
                ·
                  refine ⟨22955332948011473992270541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15303555298674315994847027 22955332948011473992270541)
                  ·
                    refine ⟨8608249855504302747101453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22955332948011473992270541 8608249855504302747101453)
                    ·
                      refine ⟨3228093695814113530163045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8608249855504302747101453 3228093695814113530163045)
                      ·
                        rfl

theorem cell23_6286690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_6286690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286690 prefixEnd_6286690 := by exact prefixLift 6286690
  have htrace : WordTrace (prefixWord ++ tailWord_6286690) baseStart_6286690 baseEnd_6286690 := by
    simpa [prefixWord, tailWord_6286690, baseEnd_6286690] using wordTrace_append hprefix tailTrace_6286690
  have hstable : (prefixWord ++ tailWord_6286690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286690).length < 2 ^ (prefixWord ++ tailWord_6286690).sum := by decide
  have hdescent : baseEnd_6286690 < baseStart_6286690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286740 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_6286740 : Nat := 118140960795 + 6286740 * 2 ^ 59
def prefixEnd_6286740 : Nat := 4983230072969 + 3 ^ 40 * 6286740 * 2
def baseEnd_6286740 : Nat := 1076039789948946111512605

theorem tailTrace_6286740 : CollatzResearch.WordTrace tailWord_6286740 prefixEnd_6286740 1076039789948946111512605 := by
  unfold tailWord_6286740
  simp only [CollatzResearch.WordTrace]
  refine ⟨114648122622111072278152837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152864163496148096370870449 114648122622111072278152837)
  ·
    refine ⟨21496522991645826052153657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114648122622111072278152837 21496522991645826052153657)
    ·
      refine ⟨16122392243734369539115243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21496522991645826052153657 16122392243734369539115243)
      ·
        refine ⟨24183588365601554308672865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16122392243734369539115243 24183588365601554308672865)
        ·
          refine ⟨18137691274201165731504649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24183588365601554308672865 18137691274201165731504649)
          ·
            refine ⟨13603268455650874298628487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18137691274201165731504649 13603268455650874298628487)
            ·
              refine ⟨20404902683476311447942731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13603268455650874298628487 20404902683476311447942731)
              ·
                refine ⟨30607354025214467171914097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20404902683476311447942731 30607354025214467171914097)
                ·
                  refine ⟨22955515518910850378935573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30607354025214467171914097 22955515518910850378935573)
                  ·
                    refine ⟨1076039789948946111512605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22955515518910850378935573 1076039789948946111512605)
                    ·
                      rfl

theorem cell23_6286740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_6286740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286740 prefixEnd_6286740 := by exact prefixLift 6286740
  have htrace : WordTrace (prefixWord ++ tailWord_6286740) baseStart_6286740 baseEnd_6286740 := by
    simpa [prefixWord, tailWord_6286740, baseEnd_6286740] using wordTrace_append hprefix tailTrace_6286740
  have hstable : (prefixWord ++ tailWord_6286740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286740).length < 2 ^ (prefixWord ++ tailWord_6286740).sum := by decide
  have hdescent : baseEnd_6286740 < baseStart_6286740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
