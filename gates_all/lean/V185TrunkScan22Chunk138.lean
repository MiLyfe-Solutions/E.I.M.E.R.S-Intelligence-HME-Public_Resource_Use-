import V185TrunkScan22Chunk137

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1236749 : List Nat := [1, 7, 2, 1, 1, 1, 3, 6]
def baseStart_1236749 : Nat := 118140960795 + 1236749 * 2 ^ 59
def prefixEnd_1236749 : Nat := 4983230072969 + 3 ^ 40 * 1236749 * 2
def baseEnd_1236749 : Nat := 47040495256850885003689

theorem tailTrace_1236749 : CollatzResearch.WordTrace tailWord_1236749 prefixEnd_1236749 47040495256850885003689 := by
  unfold tailWord_1236749
  simp only [CollatzResearch.WordTrace]
  refine ⟨45107941796477067758233301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30071961197651378505488867 45107941796477067758233301)
  ·
    refine ⟨1057217385854931275583593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 45107941796477067758233301 1057217385854931275583593)
    ·
      refine ⟨792913039391198456687695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1057217385854931275583593 792913039391198456687695)
      ·
        refine ⟨1189369559086797685031543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 792913039391198456687695 1189369559086797685031543)
        ·
          refine ⟨1784054338630196527547315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1189369559086797685031543 1784054338630196527547315)
          ·
            refine ⟨2676081507945294791320973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1784054338630196527547315 2676081507945294791320973)
            ·
              refine ⟨1003530565479485546745365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2676081507945294791320973 1003530565479485546745365)
              ·
                refine ⟨47040495256850885003689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1003530565479485546745365 47040495256850885003689)
                ·
                  rfl

theorem cell22_1236749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 6].length) (baseStart_1236749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236749 prefixEnd_1236749 := by exact prefixLift 1236749
  have htrace : WordTrace (prefixWord ++ tailWord_1236749) baseStart_1236749 baseEnd_1236749 := by
    simpa [prefixWord, tailWord_1236749, baseEnd_1236749] using wordTrace_append hprefix tailTrace_1236749
  have hstable : (prefixWord ++ tailWord_1236749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236749).length < 2 ^ (prefixWord ++ tailWord_1236749).sum := by decide
  have hdescent : baseEnd_1236749 < baseStart_1236749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236773 : List Nat := [1, 3, 1, 2, 3, 3, 1, 3, 1, 4]
def baseStart_1236773 : Nat := 118140960795 + 1236773 * 2 ^ 59
def prefixEnd_1236773 : Nat := 4983230072969 + 3 ^ 40 * 1236773 * 2
def baseEnd_1236773 : Nat := 423372673002129902433127

theorem tailTrace_1236773 : CollatzResearch.WordTrace tailWord_1236773 prefixEnd_1236773 423372673002129902433127 := by
  unfold tailWord_1236773
  simp only [CollatzResearch.WordTrace]
  refine ⟨45108817148390119857106973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30072544765593413238071315 45108817148390119857106973)
  ·
    refine ⟨16915806430646294946415115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45108817148390119857106973 16915806430646294946415115)
    ·
      refine ⟨25373709645969442419622673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16915806430646294946415115 25373709645969442419622673)
      ·
        refine ⟨19030282234477081814717005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25373709645969442419622673 19030282234477081814717005)
        ·
          refine ⟨7136355837928905680518877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19030282234477081814717005 7136355837928905680518877)
          ·
            refine ⟨2676133439223339630194579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7136355837928905680518877 2676133439223339630194579)
            ·
              refine ⟨4014200158835009445291869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2676133439223339630194579 4014200158835009445291869)
              ·
                refine ⟨1505325059563128541984451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4014200158835009445291869 1505325059563128541984451)
                ·
                  refine ⟨2257987589344692812976677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1505325059563128541984451 2257987589344692812976677)
                  ·
                    refine ⟨423372673002129902433127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2257987589344692812976677 423372673002129902433127)
                    ·
                      rfl

theorem cell22_1236773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_1236773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236773 prefixEnd_1236773 := by exact prefixLift 1236773
  have htrace : WordTrace (prefixWord ++ tailWord_1236773) baseStart_1236773 baseEnd_1236773 := by
    simpa [prefixWord, tailWord_1236773, baseEnd_1236773] using wordTrace_append hprefix tailTrace_1236773
  have hstable : (prefixWord ++ tailWord_1236773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236773).length < 2 ^ (prefixWord ++ tailWord_1236773).sum := by decide
  have hdescent : baseEnd_1236773 < baseStart_1236773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236788 : List Nat := [2, 5, 1, 1, 2, 1, 1, 3, 6]
def baseStart_1236788 : Nat := 118140960795 + 1236788 * 2 ^ 59
def prefixEnd_1236788 : Nat := 4983230072969 + 3 ^ 40 * 1236788 * 2
def baseEnd_1236788 : Nat := 141125935936224954436027

theorem tailTrace_1236788 : CollatzResearch.WordTrace tailWord_1236788 prefixEnd_1236788 141125935936224954436027 := by
  unfold tailWord_1236788
  simp only [CollatzResearch.WordTrace]
  refine ⟨22554682121667888709451509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30072909495557184945935345 22554682121667888709451509)
  ·
    refine ⟨2114501448906364566511079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22554682121667888709451509 2114501448906364566511079)
    ·
      refine ⟨3171752173359546849766619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2114501448906364566511079 3171752173359546849766619)
      ·
        refine ⟨4757628260039320274649929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3171752173359546849766619 4757628260039320274649929)
        ·
          refine ⟨3568221195029490205987447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4757628260039320274649929 3568221195029490205987447)
          ·
            refine ⟨5352331792544235308981171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3568221195029490205987447 5352331792544235308981171)
            ·
              refine ⟨8028497688816352963471757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5352331792544235308981171 8028497688816352963471757)
              ·
                refine ⟨3010686633306132361301909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8028497688816352963471757 3010686633306132361301909)
                ·
                  refine ⟨141125935936224954436027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3010686633306132361301909 141125935936224954436027)
                  ·
                    rfl

theorem cell22_1236788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_1236788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236788 prefixEnd_1236788 := by exact prefixLift 1236788
  have htrace : WordTrace (prefixWord ++ tailWord_1236788) baseStart_1236788 baseEnd_1236788 := by
    simpa [prefixWord, tailWord_1236788, baseEnd_1236788] using wordTrace_append hprefix tailTrace_1236788
  have hstable : (prefixWord ++ tailWord_1236788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236788).length < 2 ^ (prefixWord ++ tailWord_1236788).sum := by decide
  have hdescent : baseEnd_1236788 < baseStart_1236788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236803 : List Nat := [1, 1, 1, 3, 1, 7, 1, 1, 1, 5]
def baseStart_1236803 : Nat := 118140960795 + 1236803 * 2 ^ 59
def prefixEnd_1236803 : Nat := 4983230072969 + 3 ^ 40 * 1236803 * 2
def baseEnd_1236803 : Nat := 423382942615219824183035

theorem tailTrace_1236803 : CollatzResearch.WordTrace tailWord_1236803 prefixEnd_1236803 423382942615219824183035 := by
  unfold tailWord_1236803
  simp only [CollatzResearch.WordTrace]
  refine ⟨45109911338281434980699063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30073274225520956653799375 45109911338281434980699063)
  ·
    refine ⟨67664867007422152471048595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45109911338281434980699063 67664867007422152471048595)
    ·
      refine ⟨101497300511133228706572893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67664867007422152471048595 101497300511133228706572893)
      ·
        refine ⟨38061487691674960764964835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101497300511133228706572893 38061487691674960764964835)
        ·
          refine ⟨57092231537512441147447253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38061487691674960764964835 57092231537512441147447253)
          ·
            refine ⟨1338099176660447839393295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 57092231537512441147447253 1338099176660447839393295)
            ·
              refine ⟨2007148764990671759089943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338099176660447839393295 2007148764990671759089943)
              ·
                refine ⟨3010723147486007638634915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2007148764990671759089943 3010723147486007638634915)
                ·
                  refine ⟨4516084721229011457952373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3010723147486007638634915 4516084721229011457952373)
                  ·
                    refine ⟨423382942615219824183035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4516084721229011457952373 423382942615219824183035)
                    ·
                      rfl

theorem cell22_1236803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 5].length) (baseStart_1236803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236803 prefixEnd_1236803 := by exact prefixLift 1236803
  have htrace : WordTrace (prefixWord ++ tailWord_1236803) baseStart_1236803 baseEnd_1236803 := by
    simpa [prefixWord, tailWord_1236803, baseEnd_1236803] using wordTrace_append hprefix tailTrace_1236803
  have hstable : (prefixWord ++ tailWord_1236803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236803).length < 2 ^ (prefixWord ++ tailWord_1236803).sum := by decide
  have hdescent : baseEnd_1236803 < baseStart_1236803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236876 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 4, 5]
def baseStart_1236876 : Nat := 118140960795 + 1236876 * 2 ^ 59
def prefixEnd_1236876 : Nat := 4983230072969 + 3 ^ 40 * 1236876 * 2
def baseEnd_1236876 : Nat := 423407932007071967107811

theorem tailTrace_1236876 : CollatzResearch.WordTrace tailWord_1236876 prefixEnd_1236876 423407932007071967107811 := by
  unfold tailWord_1236876
  simp only [CollatzResearch.WordTrace]
  refine ⟨22556286933508484224053241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30075049244677978965404321 22556286933508484224053241)
  ·
    refine ⟨16917215200131363168039931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22556286933508484224053241 16917215200131363168039931)
    ·
      refine ⟨25375822800197044752059897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16917215200131363168039931 25375822800197044752059897)
      ·
        refine ⟨19031867100147783564044923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25375822800197044752059897 19031867100147783564044923)
        ·
          refine ⟨28547800650221675346067385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19031867100147783564044923 28547800650221675346067385)
          ·
            refine ⟨21410850487666256509550539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28547800650221675346067385 21410850487666256509550539)
            ·
              refine ⟨32116275731499384764325809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21410850487666256509550539 32116275731499384764325809)
              ·
                refine ⟨24087206798624538573244357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32116275731499384764325809 24087206798624538573244357)
                ·
                  refine ⟨4516351274742100982483317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24087206798624538573244357 4516351274742100982483317)
                  ·
                    refine ⟨423407932007071967107811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4516351274742100982483317 423407932007071967107811)
                    ·
                      rfl

theorem cell22_1236876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_1236876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236876 prefixEnd_1236876 := by exact prefixLift 1236876
  have htrace : WordTrace (prefixWord ++ tailWord_1236876) baseStart_1236876 baseEnd_1236876 := by
    simpa [prefixWord, tailWord_1236876, baseEnd_1236876] using wordTrace_append hprefix tailTrace_1236876
  have hstable : (prefixWord ++ tailWord_1236876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236876).length < 2 ^ (prefixWord ++ tailWord_1236876).sum := by decide
  have hdescent : baseEnd_1236876 < baseStart_1236876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236895 : List Nat := [1, 1, 2, 5, 3, 1, 2, 2, 5]
def baseStart_1236895 : Nat := 118140960795 + 1236895 * 2 ^ 59
def prefixEnd_1236895 : Nat := 4983230072969 + 3 ^ 40 * 1236895 * 2
def baseEnd_1236895 : Nat := 141138145365120750294251

theorem tailTrace_1236895 : CollatzResearch.WordTrace tailWord_1236895 prefixEnd_1236895 141138145365120750294251 := by
  unfold tailWord_1236895
  simp only [CollatzResearch.WordTrace]
  refine ⟨45113266853948134693048139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30075511235965423128698759 45113266853948134693048139)
  ·
    refine ⟨67669900280922202039572209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45113266853948134693048139 67669900280922202039572209)
    ·
      refine ⟨50752425210691651529679157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67669900280922202039572209 50752425210691651529679157)
      ·
        refine ⟨4758039863502342330907421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50752425210691651529679157 4758039863502342330907421)
        ·
          refine ⟨1784264948813378374090283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4758039863502342330907421 1784264948813378374090283)
          ·
            refine ⟨2676397423220067561135425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1784264948813378374090283 2676397423220067561135425)
            ·
              refine ⟨2007298067415050670851569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2676397423220067561135425 2007298067415050670851569)
              ·
                refine ⟨1505473550561288003138677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2007298067415050670851569 1505473550561288003138677)
                ·
                  refine ⟨141138145365120750294251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1505473550561288003138677 141138145365120750294251)
                  ·
                    rfl

theorem cell22_1236895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 5].length) (baseStart_1236895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236895 prefixEnd_1236895 := by exact prefixLift 1236895
  have htrace : WordTrace (prefixWord ++ tailWord_1236895) baseStart_1236895 baseEnd_1236895 := by
    simpa [prefixWord, tailWord_1236895, baseEnd_1236895] using wordTrace_append hprefix tailTrace_1236895
  have hstable : (prefixWord ++ tailWord_1236895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236895).length < 2 ^ (prefixWord ++ tailWord_1236895).sum := by decide
  have hdescent : baseEnd_1236895 < baseStart_1236895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236938 : List Nat := [3, 1, 2, 1, 2, 1, 4, 2, 1, 5]
def baseStart_1236938 : Nat := 118140960795 + 1236938 * 2 ^ 59
def prefixEnd_1236938 : Nat := 4983230072969 + 3 ^ 40 * 1236938 * 2
def baseEnd_1236938 : Nat := 423429155874124472057621

theorem tailTrace_1236938 : CollatzResearch.WordTrace tailWord_1236938 prefixEnd_1236938 423429155874124472057621 := by
  unfold tailWord_1236938
  simp only [CollatzResearch.WordTrace]
  refine ⟨11278708798198088259215867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30076556795194902024575645 11278708798198088259215867)
  ·
    refine ⟨16918063197297132388823801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11278708798198088259215867 16918063197297132388823801)
    ·
      refine ⟨12688547397972849291617851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16918063197297132388823801 12688547397972849291617851)
      ·
        refine ⟨19032821096959273937426777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12688547397972849291617851 19032821096959273937426777)
        ·
          refine ⟨14274615822719455453070083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19032821096959273937426777 14274615822719455453070083)
          ·
            refine ⟨21411923734079183179605125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14274615822719455453070083 21411923734079183179605125)
            ·
              refine ⟨4014735700139846846175961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21411923734079183179605125 4014735700139846846175961)
              ·
                refine ⟨3011051775104885134631971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4014735700139846846175961 3011051775104885134631971)
                ·
                  refine ⟨4516577662657327701947957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3011051775104885134631971 4516577662657327701947957)
                  ·
                    refine ⟨423429155874124472057621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4516577662657327701947957 423429155874124472057621)
                    ·
                      rfl

theorem cell22_1236938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_1236938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236938 prefixEnd_1236938 := by exact prefixLift 1236938
  have htrace : WordTrace (prefixWord ++ tailWord_1236938) baseStart_1236938 baseEnd_1236938 := by
    simpa [prefixWord, tailWord_1236938, baseEnd_1236938] using wordTrace_append hprefix tailTrace_1236938
  have hstable : (prefixWord ++ tailWord_1236938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236938).length < 2 ^ (prefixWord ++ tailWord_1236938).sum := by decide
  have hdescent : baseEnd_1236938 < baseStart_1236938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236940 : List Nat := [2, 2, 1, 4, 1, 2, 1, 5, 4]
def baseStart_1236940 : Nat := 118140960795 + 1236940 * 2 ^ 59
def prefixEnd_1236940 : Nat := 4983230072969 + 3 ^ 40 * 1236940 * 2
def baseEnd_1236940 : Nat := 141143280171665711169205

theorem tailTrace_1236940 : CollatzResearch.WordTrace tailWord_1236940 prefixEnd_1236940 141143280171665711169205 := by
  unfold tailWord_1236940
  simp only [CollatzResearch.WordTrace]
  refine ⟨22557454069392553689218137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30076605425856738252290849 22557454069392553689218137)
  ·
    refine ⟨16918090552044415266913603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22557454069392553689218137 16918090552044415266913603)
    ·
      refine ⟨25377135828066622900370405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16918090552044415266913603 25377135828066622900370405)
      ·
        refine ⟨4758212967762491793819451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25377135828066622900370405 4758212967762491793819451)
        ·
          refine ⟨7137319451643737690729177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4758212967762491793819451 7137319451643737690729177)
          ·
            refine ⟨5352989588732803268046883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7137319451643737690729177 5352989588732803268046883)
            ·
              refine ⟨8029484383099204902070325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5352989588732803268046883 8029484383099204902070325)
              ·
                refine ⟨752764160915550459569093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8029484383099204902070325 752764160915550459569093)
                ·
                  refine ⟨141143280171665711169205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 752764160915550459569093 141143280171665711169205)
                  ·
                    rfl

theorem cell22_1236940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 4].length) (baseStart_1236940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236940 prefixEnd_1236940 := by exact prefixLift 1236940
  have htrace : WordTrace (prefixWord ++ tailWord_1236940) baseStart_1236940 baseEnd_1236940 := by
    simpa [prefixWord, tailWord_1236940, baseEnd_1236940] using wordTrace_append hprefix tailTrace_1236940
  have hstable : (prefixWord ++ tailWord_1236940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236940).length < 2 ^ (prefixWord ++ tailWord_1236940).sum := by decide
  have hdescent : baseEnd_1236940 < baseStart_1236940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236951 : List Nat := [1, 1, 3, 2, 1, 1, 13]
def baseStart_1236951 : Nat := 118140960795 + 1236951 * 2 ^ 59
def prefixEnd_1236951 : Nat := 4983230072969 + 3 ^ 40 * 1236951 * 2
def baseEnd_1236951 : Nat := 15682726149622102647503

theorem tailTrace_1236951 : CollatzResearch.WordTrace tailWord_1236951 prefixEnd_1236951 15682726149622102647503 := by
  unfold tailWord_1236951
  simp only [CollatzResearch.WordTrace]
  refine ⟨45115309341745256257086707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30076872894496837504724471 45115309341745256257086707)
  ·
    refine ⟨67672964012617884385630061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45115309341745256257086707 67672964012617884385630061)
    ·
      refine ⟨25377361504731706644611273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67672964012617884385630061 25377361504731706644611273)
      ·
        refine ⟨19033021128548779983458455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25377361504731706644611273 19033021128548779983458455)
        ·
          refine ⟨28549531692823169975187683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19033021128548779983458455 28549531692823169975187683)
          ·
            refine ⟨42824297539234754962781525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28549531692823169975187683 42824297539234754962781525)
            ·
              refine ⟨15682726149622102647503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 42824297539234754962781525 15682726149622102647503)
              ·
                rfl

theorem cell22_1236951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 13].length) (baseStart_1236951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236951 prefixEnd_1236951 := by exact prefixLift 1236951
  have htrace : WordTrace (prefixWord ++ tailWord_1236951) baseStart_1236951 baseEnd_1236951 := by
    simpa [prefixWord, tailWord_1236951, baseEnd_1236951] using wordTrace_append hprefix tailTrace_1236951
  have hstable : (prefixWord ++ tailWord_1236951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236951).length < 2 ^ (prefixWord ++ tailWord_1236951).sum := by decide
  have hdescent : baseEnd_1236951 < baseStart_1236951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236985 : List Nat := [1, 2, 1, 3, 1, 6, 2, 6]
def baseStart_1236985 : Nat := 118140960795 + 1236985 * 2 ^ 59
def prefixEnd_1236985 : Nat := 4983230072969 + 3 ^ 40 * 1236985 * 2
def baseEnd_1236985 : Nat := 47049471659403557348053

theorem tailTrace_1236985 : CollatzResearch.WordTrace tailWord_1236985 prefixEnd_1236985 47049471659403557348053 := by
  unfold tailWord_1236985
  simp only [CollatzResearch.WordTrace]
  refine ⟨45116549423622080063824409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30077699615748053375882939 45116549423622080063824409)
  ·
    refine ⟨33837412067716560047868307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45116549423622080063824409 33837412067716560047868307)
    ·
      refine ⟨50756118101574840071802461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33837412067716560047868307 50756118101574840071802461)
      ·
        refine ⟨19033544288090565026925923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50756118101574840071802461 19033544288090565026925923)
        ·
          refine ⟨28550316432135847540388885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19033544288090565026925923 28550316432135847540388885)
          ·
            refine ⟨1338296082756367853455729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28550316432135847540388885 1338296082756367853455729)
            ·
              refine ⟨1003722062067275890091797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1338296082756367853455729 1003722062067275890091797)
              ·
                refine ⟨47049471659403557348053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1003722062067275890091797 47049471659403557348053)
                ·
                  rfl

theorem cell22_1236985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 6].length) (baseStart_1236985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236985 prefixEnd_1236985 := by exact prefixLift 1236985
  have htrace : WordTrace (prefixWord ++ tailWord_1236985) baseStart_1236985 baseEnd_1236985 := by
    simpa [prefixWord, tailWord_1236985, baseEnd_1236985] using wordTrace_append hprefix tailTrace_1236985
  have hstable : (prefixWord ++ tailWord_1236985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236985).length < 2 ^ (prefixWord ++ tailWord_1236985).sum := by decide
  have hdescent : baseEnd_1236985 < baseStart_1236985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237062 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1237062 : Nat := 118140960795 + 1237062 * 2 ^ 59
def prefixEnd_1237062 : Nat := 4983230072969 + 3 ^ 40 * 1237062 * 2
def baseEnd_1237062 : Nat := 423471603608229481957241

theorem tailTrace_1237062 : CollatzResearch.WordTrace tailWord_1237062 prefixEnd_1237062 423471603608229481957241 := by
  unfold tailWord_1237062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1409979932635722569199295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30079571896228748142918293 1409979932635722569199295)
  ·
    refine ⟨2114969898953583853798943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1409979932635722569199295 2114969898953583853798943)
    ·
      refine ⟨3172454848430375780698415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2114969898953583853798943 3172454848430375780698415)
      ·
        refine ⟨4758682272645563671047623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3172454848430375780698415 4758682272645563671047623)
        ·
          refine ⟨7138023408968345506571435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4758682272645563671047623 7138023408968345506571435)
          ·
            refine ⟨10707035113452518259857153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7138023408968345506571435 10707035113452518259857153)
            ·
              refine ⟨8030276335089388694892865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10707035113452518259857153 8030276335089388694892865)
              ·
                refine ⟨6022707251317041521169649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8030276335089388694892865 6022707251317041521169649)
                ·
                  refine ⟨4517030438487781140877237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6022707251317041521169649 4517030438487781140877237)
                  ·
                    refine ⟨423471603608229481957241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4517030438487781140877237 423471603608229481957241)
                    ·
                      rfl

theorem cell22_1237062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1237062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237062 prefixEnd_1237062 := by exact prefixLift 1237062
  have htrace : WordTrace (prefixWord ++ tailWord_1237062) baseStart_1237062 baseEnd_1237062 := by
    simpa [prefixWord, tailWord_1237062, baseEnd_1237062] using wordTrace_append hprefix tailTrace_1237062
  have hstable : (prefixWord ++ tailWord_1237062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237062).length < 2 ^ (prefixWord ++ tailWord_1237062).sum := by decide
  have hdescent : baseEnd_1237062 < baseStart_1237062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237073 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 5, 5]
def baseStart_1237073 : Nat := 118140960795 + 1237073 * 2 ^ 59
def prefixEnd_1237073 : Nat := 4983230072969 + 3 ^ 40 * 1237073 * 2
def baseEnd_1237073 : Nat := 423475369133029119932207

theorem tailTrace_1237073 : CollatzResearch.WordTrace tailWord_1237073 prefixEnd_1237073 423475369133029119932207 := by
  unfold tailWord_1237073
  simp only [CollatzResearch.WordTrace]
  refine ⟨45119759047303271093027873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30079839364868847395351915 45119759047303271093027873)
  ·
    refine ⟨33839819285477453319770905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45119759047303271093027873 33839819285477453319770905)
    ·
      refine ⟨25379864464108089989828179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33839819285477453319770905 25379864464108089989828179)
      ·
        refine ⟨38069796696162134984742269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25379864464108089989828179 38069796696162134984742269)
        ·
          refine ⟨14276173761060800619278351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38069796696162134984742269 14276173761060800619278351)
          ·
            refine ⟨21414260641591200928917527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14276173761060800619278351 21414260641591200928917527)
            ·
              refine ⟨32121390962386801393376291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21414260641591200928917527 32121390962386801393376291)
              ·
                refine ⟨48182086443580202090064437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32121390962386801393376291 48182086443580202090064437)
                ·
                  refine ⟨4517070604085643945943541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48182086443580202090064437 4517070604085643945943541)
                  ·
                    refine ⟨423475369133029119932207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4517070604085643945943541 423475369133029119932207)
                    ·
                      rfl

theorem cell22_1237073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_1237073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237073 prefixEnd_1237073 := by exact prefixLift 1237073
  have htrace : WordTrace (prefixWord ++ tailWord_1237073) baseStart_1237073 baseEnd_1237073 := by
    simpa [prefixWord, tailWord_1237073, baseEnd_1237073] using wordTrace_append hprefix tailTrace_1237073
  have hstable : (prefixWord ++ tailWord_1237073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237073).length < 2 ^ (prefixWord ++ tailWord_1237073).sum := by decide
  have hdescent : baseEnd_1237073 < baseStart_1237073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237152 : List Nat := [2, 1, 1, 4, 2, 2, 2, 2, 3, 3]
def baseStart_1237152 : Nat := 118140960795 + 1237152 * 2 ^ 59
def prefixEnd_1237152 : Nat := 4983230072969 + 3 ^ 40 * 1237152 * 2
def baseEnd_1237152 : Nat := 423502412447499247206965

theorem tailTrace_1237152 : CollatzResearch.WordTrace tailWord_1237152 prefixEnd_1237152 423502412447499247206965 := by
  unfold tailWord_1237152
  simp only [CollatzResearch.WordTrace]
  refine ⟨22561320207008533792576855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30081760276011378390102473 22561320207008533792576855)
  ·
    refine ⟨33841980310512800688865283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22561320207008533792576855 33841980310512800688865283)
    ·
      refine ⟨50762970465769201033297925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33841980310512800688865283 50762970465769201033297925)
      ·
        refine ⟨9518056962331725193743361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50762970465769201033297925 9518056962331725193743361)
        ·
          refine ⟨7138542721748793895307521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9518056962331725193743361 7138542721748793895307521)
          ·
            refine ⟨5353907041311595421480641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7138542721748793895307521 5353907041311595421480641)
            ·
              refine ⟨4015430280983696566110481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5353907041311595421480641 4015430280983696566110481)
              ·
                refine ⟨3011572710737772424582861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4015430280983696566110481 3011572710737772424582861)
                ·
                  refine ⟨1129339766526664659218573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3011572710737772424582861 1129339766526664659218573)
                  ·
                    refine ⟨423502412447499247206965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1129339766526664659218573 423502412447499247206965)
                    ·
                      rfl

theorem cell22_1237152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 3, 3].length) (baseStart_1237152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237152 prefixEnd_1237152 := by exact prefixLift 1237152
  have htrace : WordTrace (prefixWord ++ tailWord_1237152) baseStart_1237152 baseEnd_1237152 := by
    simpa [prefixWord, tailWord_1237152, baseEnd_1237152] using wordTrace_append hprefix tailTrace_1237152
  have hstable : (prefixWord ++ tailWord_1237152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237152).length < 2 ^ (prefixWord ++ tailWord_1237152).sum := by decide
  have hdescent : baseEnd_1237152 < baseStart_1237152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237154 : List Nat := [3, 3, 1, 3, 1, 3, 2, 6]
def baseStart_1237154 : Nat := 118140960795 + 1237154 * 2 ^ 59
def prefixEnd_1237154 : Nat := 4983230072969 + 3 ^ 40 * 1237154 * 2
def baseEnd_1237154 : Nat := 47055899676485767628551

theorem tailTrace_1237154 : CollatzResearch.WordTrace tailWord_1237154 prefixEnd_1237154 47055899676485767628551 := by
  unfold tailWord_1237154
  simp only [CollatzResearch.WordTrace]
  refine ⟨11280678340002455481681629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30081808906673214617817677 11280678340002455481681629)
  ·
    refine ⟨4230254377500920805630611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11280678340002455481681629 4230254377500920805630611)
    ·
      refine ⟨6345381566251381208445917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4230254377500920805630611 6345381566251381208445917)
      ·
        refine ⟨2379518087344267953167219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6345381566251381208445917 2379518087344267953167219)
        ·
          refine ⟨3569277131016401929750829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2379518087344267953167219 3569277131016401929750829)
          ·
            refine ⟨1338478924131150723656561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3569277131016401929750829 1338478924131150723656561)
            ·
              refine ⟨1003859193098363042742421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1338478924131150723656561 1003859193098363042742421)
              ·
                refine ⟨47055899676485767628551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1003859193098363042742421 47055899676485767628551)
                ·
                  rfl

theorem cell22_1237154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 6].length) (baseStart_1237154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237154 prefixEnd_1237154 := by exact prefixLift 1237154
  have htrace : WordTrace (prefixWord ++ tailWord_1237154) baseStart_1237154 baseEnd_1237154 := by
    simpa [prefixWord, tailWord_1237154, baseEnd_1237154] using wordTrace_append hprefix tailTrace_1237154
  have hstable : (prefixWord ++ tailWord_1237154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237154).length < 2 ^ (prefixWord ++ tailWord_1237154).sum := by decide
  have hdescent : baseEnd_1237154 < baseStart_1237154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237195 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 3, 4]
def baseStart_1237195 : Nat := 118140960795 + 1237195 * 2 ^ 59
def prefixEnd_1237195 : Nat := 4983230072969 + 3 ^ 40 * 1237195 * 2
def baseEnd_1237195 : Nat := 423517132226261468381833

theorem tailTrace_1237195 : CollatzResearch.WordTrace tailWord_1237195 prefixEnd_1237195 423517132226261468381833 := by
  unfold tailWord_1237195
  simp only [CollatzResearch.WordTrace]
  refine ⟨45124208752861285928969039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30082805835240857285979359 45124208752861285928969039)
  ·
    refine ⟨67686313129291928893453559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45124208752861285928969039 67686313129291928893453559)
    ·
      refine ⟨101529469693937893340180339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67686313129291928893453559 101529469693937893340180339)
      ·
        refine ⟨152294204540906840010270509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101529469693937893340180339 152294204540906840010270509)
        ·
          refine ⟨57110326702840065003851441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152294204540906840010270509 57110326702840065003851441)
          ·
            refine ⟨42832745027130048752888581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57110326702840065003851441 42832745027130048752888581)
            ·
              refine ⟨8031139692586884141166609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42832745027130048752888581 8031139692586884141166609)
              ·
                refine ⟨6023354769440163105874957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8031139692586884141166609 6023354769440163105874957)
                ·
                  refine ⟨2258758038540061164703109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6023354769440163105874957 2258758038540061164703109)
                  ·
                    refine ⟨423517132226261468381833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2258758038540061164703109 423517132226261468381833)
                    ·
                      rfl

theorem cell22_1237195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 4].length) (baseStart_1237195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237195 prefixEnd_1237195 := by exact prefixLift 1237195
  have htrace : WordTrace (prefixWord ++ tailWord_1237195) baseStart_1237195 baseEnd_1237195 := by
    simpa [prefixWord, tailWord_1237195, baseEnd_1237195] using wordTrace_append hprefix tailTrace_1237195
  have hstable : (prefixWord ++ tailWord_1237195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237195).length < 2 ^ (prefixWord ++ tailWord_1237195).sum := by decide
  have hdescent : baseEnd_1237195 < baseStart_1237195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237210 : List Nat := [3, 1, 1, 2, 2, 1, 2, 4, 6]
def baseStart_1237210 : Nat := 118140960795 + 1237210 * 2 ^ 59
def prefixEnd_1237210 : Nat := 4983230072969 + 3 ^ 40 * 1237210 * 2
def baseEnd_1237210 : Nat := 141174089010935476418929

theorem tailTrace_1237210 : CollatzResearch.WordTrace tailWord_1237210 prefixEnd_1237210 141174089010935476418929 := by
  unfold tailWord_1237210
  simp only [CollatzResearch.WordTrace]
  refine ⟨11281188961951735872691271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30083170565204628993843389 11281188961951735872691271)
  ·
    refine ⟨16921783442927603809036907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11281188961951735872691271 16921783442927603809036907)
    ·
      refine ⟨25382675164391405713555361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16921783442927603809036907 25382675164391405713555361)
      ·
        refine ⟨19037006373293554285166521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25382675164391405713555361 19037006373293554285166521)
        ·
          refine ⟨14277754779970165713874891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19037006373293554285166521 14277754779970165713874891)
          ·
            refine ⟨21416632169955248570812337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14277754779970165713874891 21416632169955248570812337)
            ·
              refine ⟨16062474127466436428109253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21416632169955248570812337 16062474127466436428109253)
              ·
                refine ⟨3011713898899956830270485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16062474127466436428109253 3011713898899956830270485)
                ·
                  refine ⟨141174089010935476418929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3011713898899956830270485 141174089010935476418929)
                  ·
                    rfl

theorem cell22_1237210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_1237210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237210 prefixEnd_1237210 := by exact prefixLift 1237210
  have htrace : WordTrace (prefixWord ++ tailWord_1237210) baseStart_1237210 baseEnd_1237210 := by
    simpa [prefixWord, tailWord_1237210, baseEnd_1237210] using wordTrace_append hprefix tailTrace_1237210
  have hstable : (prefixWord ++ tailWord_1237210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237210).length < 2 ^ (prefixWord ++ tailWord_1237210).sum := by decide
  have hdescent : baseEnd_1237210 < baseStart_1237210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237225 : List Nat := [1, 2, 1, 1, 1, 2, 2, 6, 1, 5]
def baseStart_1237225 : Nat := 118140960795 + 1237225 * 2 ^ 59
def prefixEnd_1237225 : Nat := 4983230072969 + 3 ^ 40 * 1237225 * 2
def baseEnd_1237225 : Nat := 423527401839351390131741

theorem tailTrace_1237225 : CollatzResearch.WordTrace tailWord_1237225 prefixEnd_1237225 423527401839351390131741 := by
  unfold tailWord_1237225
  simp only [CollatzResearch.WordTrace]
  refine ⟨45125302942752601052561129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30083535295168400701707419 45125302942752601052561129)
  ·
    refine ⟨33843977207064450789420847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45125302942752601052561129 33843977207064450789420847)
    ·
      refine ⟨50765965810596676184131271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33843977207064450789420847 50765965810596676184131271)
      ·
        refine ⟨76148948715895014276196907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50765965810596676184131271 76148948715895014276196907)
        ·
          refine ⟨114223423073842521414295361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76148948715895014276196907 114223423073842521414295361)
          ·
            refine ⟨85667567305381891060721521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114223423073842521414295361 85667567305381891060721521)
            ·
              refine ⟨64250675479036418295541141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85667567305381891060721521 64250675479036418295541141)
              ·
                refine ⟨3011750413079832107603491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64250675479036418295541141 3011750413079832107603491)
                ·
                  refine ⟨4517625619619748161405237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3011750413079832107603491 4517625619619748161405237)
                  ·
                    refine ⟨423527401839351390131741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4517625619619748161405237 423527401839351390131741)
                    ·
                      rfl

theorem cell22_1237225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 5].length) (baseStart_1237225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237225 prefixEnd_1237225 := by exact prefixLift 1237225
  have htrace : WordTrace (prefixWord ++ tailWord_1237225) baseStart_1237225 baseEnd_1237225 := by
    simpa [prefixWord, tailWord_1237225, baseEnd_1237225] using wordTrace_append hprefix tailTrace_1237225
  have hstable : (prefixWord ++ tailWord_1237225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237225).length < 2 ^ (prefixWord ++ tailWord_1237225).sum := by decide
  have hdescent : baseEnd_1237225 < baseStart_1237225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237227 : List Nat := [1, 1, 1, 1, 2, 5, 2, 5, 4]
def baseStart_1237227 : Nat := 118140960795 + 1237227 * 2 ^ 59
def prefixEnd_1237227 : Nat := 4983230072969 + 3 ^ 40 * 1237227 * 2
def baseEnd_1237227 : Nat := 141176028826741350527245

theorem tailTrace_1237227 : CollatzResearch.WordTrace tailWord_1237227 prefixEnd_1237227 141176028826741350527245 := by
  unfold tailWord_1237227
  simp only [CollatzResearch.WordTrace]
  refine ⟨45125375888745355394133935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30083583925830236929422623 45125375888745355394133935)
  ·
    refine ⟨67688063833118033091200903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45125375888745355394133935 67688063833118033091200903)
    ·
      refine ⟨101532095749677049636801355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67688063833118033091200903 101532095749677049636801355)
      ·
        refine ⟨152298143624515574455202033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101532095749677049636801355 152298143624515574455202033)
        ·
          refine ⟨114223607718386680841401525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152298143624515574455202033 114223607718386680841401525)
          ·
            refine ⟨10708463223598751328881393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114223607718386680841401525 10708463223598751328881393)
            ·
              refine ⟨8031347417699063496661045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10708463223598751328881393 8031347417699063496661045)
              ·
                refine ⟨752938820409287202811973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8031347417699063496661045 752938820409287202811973)
                ·
                  refine ⟨141176028826741350527245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 752938820409287202811973 141176028826741350527245)
                  ·
                    rfl

theorem cell22_1237227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 4].length) (baseStart_1237227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237227 prefixEnd_1237227 := by exact prefixLift 1237227
  have htrace : WordTrace (prefixWord ++ tailWord_1237227) baseStart_1237227 baseEnd_1237227 := by
    simpa [prefixWord, tailWord_1237227, baseEnd_1237227] using wordTrace_append hprefix tailTrace_1237227
  have hstable : (prefixWord ++ tailWord_1237227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237227).length < 2 ^ (prefixWord ++ tailWord_1237227).sum := by decide
  have hdescent : baseEnd_1237227 < baseStart_1237227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237244 : List Nat := [2, 2, 2, 1, 4, 2, 1, 4, 4]
def baseStart_1237244 : Nat := 118140960795 + 1237244 * 2 ^ 59
def prefixEnd_1237244 : Nat := 4983230072969 + 3 ^ 40 * 1237244 * 2
def baseEnd_1237244 : Nat := 141177968642547224635561

theorem tailTrace_1237244 : CollatzResearch.WordTrace tailWord_1237244 prefixEnd_1237244 141177968642547224635561 := by
  unfold tailWord_1237244
  simp only [CollatzResearch.WordTrace]
  refine ⟨22562997964841883648751393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30083997286455844865001857 22562997964841883648751393)
  ·
    refine ⟨16922248473631412736563545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22562997964841883648751393 16922248473631412736563545)
    ·
      refine ⟨12691686355223559552422659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16922248473631412736563545 12691686355223559552422659)
      ·
        refine ⟨19037529532835339328633989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12691686355223559552422659 19037529532835339328633989)
        ·
          refine ⟨3569536787406626124118873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19037529532835339328633989 3569536787406626124118873)
          ·
            refine ⟨2677152590554969593089155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3569536787406626124118873 2677152590554969593089155)
            ·
              refine ⟨4015728885832454389633733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2677152590554969593089155 4015728885832454389633733)
              ·
                refine ⟨752949166093585198056325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4015728885832454389633733 752949166093585198056325)
                ·
                  refine ⟨141177968642547224635561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 752949166093585198056325 141177968642547224635561)
                  ·
                    rfl

theorem cell22_1237244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 4].length) (baseStart_1237244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237244 prefixEnd_1237244 := by exact prefixLift 1237244
  have htrace : WordTrace (prefixWord ++ tailWord_1237244) baseStart_1237244 baseEnd_1237244 := by
    simpa [prefixWord, tailWord_1237244, baseEnd_1237244] using wordTrace_append hprefix tailTrace_1237244
  have hstable : (prefixWord ++ tailWord_1237244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237244).length < 2 ^ (prefixWord ++ tailWord_1237244).sum := by decide
  have hdescent : baseEnd_1237244 < baseStart_1237244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237272 : List Nat := [2, 1, 2, 3, 1, 2, 5, 6]
def baseStart_1237272 : Nat := 118140960795 + 1237272 * 2 ^ 59
def prefixEnd_1237272 : Nat := 4983230072969 + 3 ^ 40 * 1237272 * 2
def baseEnd_1237272 : Nat := 47060387877762103800733

theorem tailTrace_1237272 : CollatzResearch.WordTrace tailWord_1237272 prefixEnd_1237272 47060387877762103800733 := by
  unfold tailWord_1237272
  simp only [CollatzResearch.WordTrace]
  refine ⟨22563508586791164039761035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30084678115721552053014713 22563508586791164039761035)
  ·
    refine ⟨33845262880186746059641553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22563508586791164039761035 33845262880186746059641553)
    ·
      refine ⟨25383947160140059544731165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33845262880186746059641553 25383947160140059544731165)
      ·
        refine ⟨9518980185052522329274187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25383947160140059544731165 9518980185052522329274187)
        ·
          refine ⟨14278470277578783493911281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9518980185052522329274187 14278470277578783493911281)
          ·
            refine ⟨10708852708184087620433461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14278470277578783493911281 10708852708184087620433461)
            ·
              refine ⟨1003954941392258214415637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10708852708184087620433461 1003954941392258214415637)
              ·
                refine ⟨47060387877762103800733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1003954941392258214415637 47060387877762103800733)
                ·
                  rfl

theorem cell22_1237272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 6].length) (baseStart_1237272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237272 prefixEnd_1237272 := by exact prefixLift 1237272
  have htrace : WordTrace (prefixWord ++ tailWord_1237272) baseStart_1237272 baseEnd_1237272 := by
    simpa [prefixWord, tailWord_1237272, baseEnd_1237272] using wordTrace_append hprefix tailTrace_1237272
  have hstable : (prefixWord ++ tailWord_1237272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237272).length < 2 ^ (prefixWord ++ tailWord_1237272).sum := by decide
  have hdescent : baseEnd_1237272 < baseStart_1237272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237278 : List Nat := [4, 3, 2, 1, 1, 2, 2, 3, 4]
def baseStart_1237278 : Nat := 118140960795 + 1237278 * 2 ^ 59
def prefixEnd_1237278 : Nat := 4983230072969 + 3 ^ 40 * 1237278 * 2
def baseEnd_1237278 : Nat := 141181848274158972852193

theorem tailTrace_1237278 : CollatzResearch.WordTrace tailWord_1237278 prefixEnd_1237278 141181848274158972852193 := by
  unfold tailWord_1237278
  simp only [CollatzResearch.WordTrace]
  refine ⟨5640904501445073888030061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30084824007707060736160325 5640904501445073888030061)
  ·
    refine ⟨2115339188041902708011273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5640904501445073888030061 2115339188041902708011273)
    ·
      refine ⟨1586504391031427031008455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2115339188041902708011273 1586504391031427031008455)
      ·
        refine ⟨2379756586547140546512683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1586504391031427031008455 2379756586547140546512683)
        ·
          refine ⟨3569634879820710819769025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2379756586547140546512683 3569634879820710819769025)
          ·
            refine ⟨2677226159865533114826769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3569634879820710819769025 2677226159865533114826769)
            ·
              refine ⟨2007919619899149836120077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2677226159865533114826769 2007919619899149836120077)
              ·
                refine ⟨752969857462181188545029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2007919619899149836120077 752969857462181188545029)
                ·
                  refine ⟨141181848274158972852193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 752969857462181188545029 141181848274158972852193)
                  ·
                    rfl

theorem cell22_1237278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_1237278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237278 prefixEnd_1237278 := by exact prefixLift 1237278
  have htrace : WordTrace (prefixWord ++ tailWord_1237278) baseStart_1237278 baseEnd_1237278 := by
    simpa [prefixWord, tailWord_1237278, baseEnd_1237278] using wordTrace_append hprefix tailTrace_1237278
  have hstable : (prefixWord ++ tailWord_1237278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237278).length < 2 ^ (prefixWord ++ tailWord_1237278).sum := by decide
  have hdescent : baseEnd_1237278 < baseStart_1237278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237411 : List Nat := [1, 1, 1, 4, 1, 5, 2, 2, 2, 3]
def baseStart_1237411 : Nat := 118140960795 + 1237411 * 2 ^ 59
def prefixEnd_1237411 : Nat := 4983230072969 + 3 ^ 40 * 1237411 * 2
def baseEnd_1237411 : Nat := 423591073440508904981171

theorem tailTrace_1237411 : CollatzResearch.WordTrace tailWord_1237411 prefixEnd_1237411 423591073440508904981171 := by
  unfold tailWord_1237411
  simp only [CollatzResearch.WordTrace]
  refine ⟨45132086920078754818832087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30088057946719169879221391 45132086920078754818832087)
  ·
    refine ⟨67698130380118132228248131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45132086920078754818832087 67698130380118132228248131)
    ·
      refine ⟨101547195570177198342372197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67698130380118132228248131 101547195570177198342372197)
      ·
        refine ⟨19040099169408224689194787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101547195570177198342372197 19040099169408224689194787)
        ·
          refine ⟨28560148754112337033792181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19040099169408224689194787 28560148754112337033792181)
          ·
            refine ⟨2677513945698031596918017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28560148754112337033792181 2677513945698031596918017)
            ·
              refine ⟨2008135459273523697688513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2677513945698031596918017 2008135459273523697688513)
              ·
                refine ⟨1506101594455142773266385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2008135459273523697688513 1506101594455142773266385)
                ·
                  refine ⟨1129576195841357079949789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1506101594455142773266385 1129576195841357079949789)
                  ·
                    refine ⟨423591073440508904981171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1129576195841357079949789 423591073440508904981171)
                    ·
                      rfl

theorem cell22_1237411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 3].length) (baseStart_1237411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237411 prefixEnd_1237411 := by exact prefixLift 1237411
  have htrace : WordTrace (prefixWord ++ tailWord_1237411) baseStart_1237411 baseEnd_1237411 := by
    simpa [prefixWord, tailWord_1237411, baseEnd_1237411] using wordTrace_append hprefix tailTrace_1237411
  have hstable : (prefixWord ++ tailWord_1237411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237411).length < 2 ^ (prefixWord ++ tailWord_1237411).sum := by decide
  have hdescent : baseEnd_1237411 < baseStart_1237411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237469 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 7]
def baseStart_1237469 : Nat := 118140960795 + 1237469 * 2 ^ 59
def prefixEnd_1237469 : Nat := 4983230072969 + 3 ^ 40 * 1237469 * 2
def baseEnd_1237469 : Nat := 141203642675272029010331

theorem tailTrace_1237469 : CollatzResearch.WordTrace tailWord_1237469 prefixEnd_1237469 141203642675272029010331 := by
  unfold tailWord_1237469
  simp only [CollatzResearch.WordTrace]
  refine ⟨45134202353868630724443461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30089468235912420482962307 45134202353868630724443461)
  ·
    refine ⟨8462662941350368260833149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45134202353868630724443461 8462662941350368260833149)
    ·
      refine ⟨3173498603006388097812431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8462662941350368260833149 3173498603006388097812431)
      ·
        refine ⟨4760247904509582146718647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3173498603006388097812431 4760247904509582146718647)
        ·
          refine ⟨7140371856764373220077971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4760247904509582146718647 7140371856764373220077971)
          ·
            refine ⟨10710557785146559830116957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7140371856764373220077971 10710557785146559830116957)
            ·
              refine ⟨4016459169429959936293859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10710557785146559830116957 4016459169429959936293859)
              ·
                refine ⟨6024688754144939904440789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4016459169429959936293859 6024688754144939904440789)
                ·
                  refine ⟨141203642675272029010331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6024688754144939904440789 141203642675272029010331)
                  ·
                    rfl

theorem cell22_1237469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_1237469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237469 prefixEnd_1237469 := by exact prefixLift 1237469
  have htrace : WordTrace (prefixWord ++ tailWord_1237469) baseStart_1237469 baseEnd_1237469 := by
    simpa [prefixWord, tailWord_1237469, baseEnd_1237469] using wordTrace_append hprefix tailTrace_1237469
  have hstable : (prefixWord ++ tailWord_1237469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237469).length < 2 ^ (prefixWord ++ tailWord_1237469).sum := by decide
  have hdescent : baseEnd_1237469 < baseStart_1237469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237516 : List Nat := [2, 2, 1, 2, 4, 1, 2, 3, 1, 4]
def baseStart_1237516 : Nat := 118140960795 + 1237516 * 2 ^ 59
def prefixEnd_1237516 : Nat := 4983230072969 + 3 ^ 40 * 1237516 * 2
def baseEnd_1237516 : Nat := 423627017086323631105849

theorem tailTrace_1237516 : CollatzResearch.WordTrace tailWord_1237516 prefixEnd_1237516 423627017086323631105849 := by
  unfold tailWord_1237516
  simp only [CollatzResearch.WordTrace]
  refine ⟨22567958292349178875702201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30090611056465571834269601 22567958292349178875702201)
  ·
    refine ⟨16925968719261884156776651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22567958292349178875702201 16925968719261884156776651)
    ·
      refine ⟨25388953078892826235164977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16925968719261884156776651 25388953078892826235164977)
      ·
        refine ⟨19041714809169619676373733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25388953078892826235164977 19041714809169619676373733)
        ·
          refine ⟨3570321526719303689320075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19041714809169619676373733 3570321526719303689320075)
          ·
            refine ⟨5355482290078955533980113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3570321526719303689320075 5355482290078955533980113)
            ·
              refine ⟨4016611717559216650485085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5355482290078955533980113 4016611717559216650485085)
              ·
                refine ⟨1506229394084706243931907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4016611717559216650485085 1506229394084706243931907)
                ·
                  refine ⟨2259344091127059365897861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1506229394084706243931907 2259344091127059365897861)
                  ·
                    refine ⟨423627017086323631105849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2259344091127059365897861 423627017086323631105849)
                    ·
                      rfl

theorem cell22_1237516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_1237516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237516 prefixEnd_1237516 := by exact prefixLift 1237516
  have htrace : WordTrace (prefixWord ++ tailWord_1237516) baseStart_1237516 baseEnd_1237516 := by
    simpa [prefixWord, tailWord_1237516, baseEnd_1237516] using wordTrace_append hprefix tailTrace_1237516
  have hstable : (prefixWord ++ tailWord_1237516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237516).length < 2 ^ (prefixWord ++ tailWord_1237516).sum := by decide
  have hdescent : baseEnd_1237516 < baseStart_1237516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237550 : List Nat := [4, 1, 3, 1, 3, 2, 1, 2, 1, 4]
def baseStart_1237550 : Nat := 118140960795 + 1237550 * 2 ^ 59
def prefixEnd_1237550 : Nat := 4983230072969 + 3 ^ 40 * 1237550 * 2
def baseEnd_1237550 : Nat := 423638655981158875755745

theorem tailTrace_1237550 : CollatzResearch.WordTrace tailWord_1237550 prefixEnd_1237550 423638655981158875755745 := by
  unfold tailWord_1237550
  simp only [CollatzResearch.WordTrace]
  refine ⟨5642144583321897694767763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30091437777716787705428069 5642144583321897694767763)
  ·
    refine ⟨8463216874982846542151645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5642144583321897694767763 8463216874982846542151645)
    ·
      refine ⟨3173706328118567453306867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8463216874982846542151645 3173706328118567453306867)
      ·
        refine ⟨4760559492177851179960301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3173706328118567453306867 4760559492177851179960301)
        ·
          refine ⟨1785209809566694192485113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4760559492177851179960301 1785209809566694192485113)
          ·
            refine ⟨1338907357175020644363835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1785209809566694192485113 1338907357175020644363835)
            ·
              refine ⟨2008361035762530966545753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338907357175020644363835 2008361035762530966545753)
              ·
                refine ⟨1506270776821898224909315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2008361035762530966545753 1506270776821898224909315)
                ·
                  refine ⟨2259406165232847337363973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1506270776821898224909315 2259406165232847337363973)
                  ·
                    refine ⟨423638655981158875755745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2259406165232847337363973 423638655981158875755745)
                    ·
                      rfl

theorem cell22_1237550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_1237550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237550 prefixEnd_1237550 := by exact prefixLift 1237550
  have htrace : WordTrace (prefixWord ++ tailWord_1237550) baseStart_1237550 baseEnd_1237550 := by
    simpa [prefixWord, tailWord_1237550, baseEnd_1237550] using wordTrace_append hprefix tailTrace_1237550
  have hstable : (prefixWord ++ tailWord_1237550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237550).length < 2 ^ (prefixWord ++ tailWord_1237550).sum := by decide
  have hdescent : baseEnd_1237550 < baseStart_1237550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237561 : List Nat := [1, 2, 1, 5, 1, 1, 4, 1, 2, 4]
def baseStart_1237561 : Nat := 118140960795 + 1237561 * 2 ^ 59
def prefixEnd_1237561 : Nat := 4983230072969 + 3 ^ 40 * 1237561 * 2
def baseEnd_1237561 : Nat := 423642421505958513730711

theorem tailTrace_1237561 : CollatzResearch.WordTrace tailWord_1237561 prefixEnd_1237561 423642421505958513730711 := by
  unfold tailWord_1237561
  simp only [CollatzResearch.WordTrace]
  refine ⟨45137557869535330436792537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30091705246356886957861691 45137557869535330436792537)
  ·
    refine ⟨33853168402151497827594403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45137557869535330436792537 33853168402151497827594403)
    ·
      refine ⟨50779752603227246741391605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33853168402151497827594403 50779752603227246741391605)
      ·
        refine ⟨4760601806552554382005463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50779752603227246741391605 4760601806552554382005463)
        ·
          refine ⟨7140902709828831573008195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4760601806552554382005463 7140902709828831573008195)
          ·
            refine ⟨10711354064743247359512293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7140902709828831573008195 10711354064743247359512293)
            ·
              refine ⟨2008378887139358879908555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10711354064743247359512293 2008378887139358879908555)
              ·
                refine ⟨3012568330709038319862833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008378887139358879908555 3012568330709038319862833)
                ·
                  refine ⟨2259426248031778739897125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3012568330709038319862833 2259426248031778739897125)
                  ·
                    refine ⟨423642421505958513730711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2259426248031778739897125 423642421505958513730711)
                    ·
                      rfl

theorem cell22_1237561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 4].length) (baseStart_1237561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237561 prefixEnd_1237561 := by exact prefixLift 1237561
  have htrace : WordTrace (prefixWord ++ tailWord_1237561) baseStart_1237561 baseEnd_1237561 := by
    simpa [prefixWord, tailWord_1237561, baseEnd_1237561] using wordTrace_append hprefix tailTrace_1237561
  have hstable : (prefixWord ++ tailWord_1237561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237561).length < 2 ^ (prefixWord ++ tailWord_1237561).sum := by decide
  have hdescent : baseEnd_1237561 < baseStart_1237561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237589 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 2, 6]
def baseStart_1237589 : Nat := 118140960795 + 1237589 * 2 ^ 59
def prefixEnd_1237589 : Nat := 4983230072969 + 3 ^ 40 * 1237589 * 2
def baseEnd_1237589 : Nat := 423652006478175774030625

theorem tailTrace_1237589 : CollatzResearch.WordTrace tailWord_1237589 prefixEnd_1237589 423652006478175774030625 := by
  unfold tailWord_1237589
  simp only [CollatzResearch.WordTrace]
  refine ⟨45138579113433891218811821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30092386075622594145874547 45138579113433891218811821)
  ·
    refine ⟨16926967167537709207054433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45138579113433891218811821 16926967167537709207054433)
    ·
      refine ⟨12695225375653281905290825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16926967167537709207054433 12695225375653281905290825)
      ·
        refine ⟨9521419031739961428968119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12695225375653281905290825 9521419031739961428968119)
        ·
          refine ⟨14282128547609942143452179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9521419031739961428968119 14282128547609942143452179)
          ·
            refine ⟨21423192821414913215178269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14282128547609942143452179 21423192821414913215178269)
            ·
              refine ⟨8033697308030592455691851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21423192821414913215178269 8033697308030592455691851)
              ·
                refine ⟨12050545962045888683537777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8033697308030592455691851 12050545962045888683537777)
                ·
                  refine ⟨9037909471534416512653333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12050545962045888683537777 9037909471534416512653333)
                  ·
                    refine ⟨423652006478175774030625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9037909471534416512653333 423652006478175774030625)
                    ·
                      rfl

theorem cell22_1237589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_1237589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237589 prefixEnd_1237589 := by exact prefixLift 1237589
  have htrace : WordTrace (prefixWord ++ tailWord_1237589) baseStart_1237589 baseEnd_1237589 := by
    simpa [prefixWord, tailWord_1237589, baseEnd_1237589] using wordTrace_append hprefix tailTrace_1237589
  have hstable : (prefixWord ++ tailWord_1237589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237589).length < 2 ^ (prefixWord ++ tailWord_1237589).sum := by decide
  have hdescent : baseEnd_1237589 < baseStart_1237589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237591 : List Nat := [1, 1, 3, 2, 2, 2, 2, 3, 3, 3]
def baseStart_1237591 : Nat := 118140960795 + 1237591 * 2 ^ 59
def prefixEnd_1237591 : Nat := 4983230072969 + 3 ^ 40 * 1237591 * 2
def baseEnd_1237591 : Nat := 423652691119048435480619

theorem tailTrace_1237591 : CollatzResearch.WordTrace tailWord_1237591 prefixEnd_1237591 423652691119048435480619 := by
  unfold tailWord_1237591
  simp only [CollatzResearch.WordTrace]
  refine ⟨45138652059426645560384627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30092434706284430373589751 45138652059426645560384627)
  ·
    refine ⟨67707978089139968340576941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45138652059426645560384627 67707978089139968340576941)
    ·
      refine ⟨25390491783427488127716353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67707978089139968340576941 25390491783427488127716353)
      ·
        refine ⟨19042868837570616095787265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25390491783427488127716353 19042868837570616095787265)
        ·
          refine ⟨14282151628177962071840449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19042868837570616095787265 14282151628177962071840449)
          ·
            refine ⟨10711613721133471553880337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14282151628177962071840449 10711613721133471553880337)
            ·
              refine ⟨8033710290850103665410253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10711613721133471553880337 8033710290850103665410253)
              ·
                refine ⟨3012641359068788874528845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8033710290850103665410253 3012641359068788874528845)
                ·
                  refine ⟨1129740509650795827948317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3012641359068788874528845 1129740509650795827948317)
                  ·
                    refine ⟨423652691119048435480619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1129740509650795827948317 423652691119048435480619)
                    ·
                      rfl

theorem cell22_1237591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_1237591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237591 prefixEnd_1237591 := by exact prefixLift 1237591
  have htrace : WordTrace (prefixWord ++ tailWord_1237591) baseStart_1237591 baseEnd_1237591 := by
    simpa [prefixWord, tailWord_1237591, baseEnd_1237591] using wordTrace_append hprefix tailTrace_1237591
  have hstable : (prefixWord ++ tailWord_1237591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237591).length < 2 ^ (prefixWord ++ tailWord_1237591).sum := by decide
  have hdescent : baseEnd_1237591 < baseStart_1237591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237625 : List Nat := [1, 2, 1, 3, 3, 3, 2, 3, 1, 3]
def baseStart_1237625 : Nat := 118140960795 + 1237625 * 2 ^ 59
def prefixEnd_1237625 : Nat := 4983230072969 + 3 ^ 40 * 1237625 * 2
def baseEnd_1237625 : Nat := 423664330013883680130515

theorem tailTrace_1237625 : CollatzResearch.WordTrace tailWord_1237625 prefixEnd_1237625 423664330013883680130515 := by
  unfold tailWord_1237625
  simp only [CollatzResearch.WordTrace]
  refine ⟨45139892141303469367122329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30093261427535646244748219 45139892141303469367122329)
  ·
    refine ⟨33854919105977602025341747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45139892141303469367122329 33854919105977602025341747)
    ·
      refine ⟨50782378658966403038012621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33854919105977602025341747 50782378658966403038012621)
      ·
        refine ⟨19043391997112401139254733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50782378658966403038012621 19043391997112401139254733)
        ·
          refine ⟨7141271998917150427220525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19043391997112401139254733 7141271998917150427220525)
          ·
            refine ⟨2677976999593931410207697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7141271998917150427220525 2677976999593931410207697)
            ·
              refine ⟨2008482749695448557655773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2677976999593931410207697 2008482749695448557655773)
              ·
                refine ⟨753181031135793209120915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2008482749695448557655773 753181031135793209120915)
                ·
                  refine ⟨1129771546703689813681373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 753181031135793209120915 1129771546703689813681373)
                  ·
                    refine ⟨423664330013883680130515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1129771546703689813681373 423664330013883680130515)
                    ·
                      rfl

theorem cell22_1237625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 1, 3].length) (baseStart_1237625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237625 prefixEnd_1237625 := by exact prefixLift 1237625
  have htrace : WordTrace (prefixWord ++ tailWord_1237625) baseStart_1237625 baseEnd_1237625 := by
    simpa [prefixWord, tailWord_1237625, baseEnd_1237625] using wordTrace_append hprefix tailTrace_1237625
  have hstable : (prefixWord ++ tailWord_1237625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237625).length < 2 ^ (prefixWord ++ tailWord_1237625).sum := by decide
  have hdescent : baseEnd_1237625 < baseStart_1237625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237636 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_1237636 : Nat := 118140960795 + 1237636 * 2 ^ 59
def prefixEnd_1237636 : Nat := 4983230072969 + 3 ^ 40 * 1237636 * 2
def baseEnd_1237636 : Nat := 423668095538683318105481

theorem tailTrace_1237636 : CollatzResearch.WordTrace tailWord_1237636 prefixEnd_1237636 423668095538683318105481 := by
  unfold tailWord_1237636
  simp only [CollatzResearch.WordTrace]
  refine ⟨22570146672131809122886381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30093528896175745497181841 22570146672131809122886381)
  ·
    refine ⟨8463805002049428421082393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22570146672131809122886381 8463805002049428421082393)
    ·
      refine ⟨6347853751537071315811795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8463805002049428421082393 6347853751537071315811795)
      ·
        refine ⟨9521780627305606973717693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6347853751537071315811795 9521780627305606973717693)
        ·
          refine ⟨3570667735239602615144135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9521780627305606973717693 3570667735239602615144135)
          ·
            refine ⟨5356001602859403922716203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3570667735239602615144135 5356001602859403922716203)
            ·
              refine ⟨8034002404289105884074305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5356001602859403922716203 8034002404289105884074305)
              ·
                refine ⟨6025501803216829413055729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8034002404289105884074305 6025501803216829413055729)
                ·
                  refine ⟨4519126352412622059791797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6025501803216829413055729 4519126352412622059791797)
                  ·
                    refine ⟨423668095538683318105481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4519126352412622059791797 423668095538683318105481)
                    ·
                      rfl

theorem cell22_1237636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_1237636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237636 prefixEnd_1237636 := by exact prefixLift 1237636
  have htrace : WordTrace (prefixWord ++ tailWord_1237636) baseStart_1237636 baseEnd_1237636 := by
    simpa [prefixWord, tailWord_1237636, baseEnd_1237636] using wordTrace_append hprefix tailTrace_1237636
  have hstable : (prefixWord ++ tailWord_1237636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237636).length < 2 ^ (prefixWord ++ tailWord_1237636).sum := by decide
  have hdescent : baseEnd_1237636 < baseStart_1237636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237668 : List Nat := [2, 3, 1, 2, 2, 1, 4, 2, 1, 4]
def baseStart_1237668 : Nat := 118140960795 + 1237668 * 2 ^ 59
def prefixEnd_1237668 : Nat := 4983230072969 + 3 ^ 40 * 1237668 * 2
def baseEnd_1237668 : Nat := 423679049792645901305383

theorem tailTrace_1237668 : CollatzResearch.WordTrace tailWord_1237668 prefixEnd_1237668 423679049792645901305383 := by
  unfold tailWord_1237668
  simp only [CollatzResearch.WordTrace]
  refine ⟨22570730240073843855468829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30094306986765125140625105 22570730240073843855468829)
  ·
    refine ⟨8464023840027691445800811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22570730240073843855468829 8464023840027691445800811)
    ·
      refine ⟨12696035760041537168701217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8464023840027691445800811 12696035760041537168701217)
      ·
        refine ⟨9522026820031152876525913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12696035760041537168701217 9522026820031152876525913)
        ·
          refine ⟨7141520115023364657394435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9522026820031152876525913 7141520115023364657394435)
          ·
            refine ⟨10712280172535046986091653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7141520115023364657394435 10712280172535046986091653)
            ·
              refine ⟨2008552532350321309892185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10712280172535046986091653 2008552532350321309892185)
              ·
                refine ⟨1506414399262740982419139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2008552532350321309892185 1506414399262740982419139)
                ·
                  refine ⟨2259621598894111473628709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1506414399262740982419139 2259621598894111473628709)
                  ·
                    refine ⟨423679049792645901305383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2259621598894111473628709 423679049792645901305383)
                    ·
                      rfl

theorem cell22_1237668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_1237668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237668 prefixEnd_1237668 := by exact prefixLift 1237668
  have htrace : WordTrace (prefixWord ++ tailWord_1237668) baseStart_1237668 baseEnd_1237668 := by
    simpa [prefixWord, tailWord_1237668, baseEnd_1237668] using wordTrace_append hprefix tailTrace_1237668
  have hstable : (prefixWord ++ tailWord_1237668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237668).length < 2 ^ (prefixWord ++ tailWord_1237668).sum := by decide
  have hdescent : baseEnd_1237668 < baseStart_1237668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237683 : List Nat := [1, 1, 1, 2, 3, 4, 3, 3, 4]
def baseStart_1237683 : Nat := 118140960795 + 1237683 * 2 ^ 59
def prefixEnd_1237683 : Nat := 4983230072969 + 3 ^ 40 * 1237683 * 2
def baseEnd_1237683 : Nat := 141228061533063620726779

theorem tailTrace_1237683 : CollatzResearch.WordTrace tailWord_1237683 prefixEnd_1237683 141228061533063620726779 := by
  unfold tailWord_1237683
  simp only [CollatzResearch.WordTrace]
  refine ⟨45142007575093345272733703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30094671716728896848489135 45142007575093345272733703)
  ·
    refine ⟨67713011362640017909100555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45142007575093345272733703 67713011362640017909100555)
    ·
      refine ⟨101569517043960026863650833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67713011362640017909100555 101569517043960026863650833)
      ·
        refine ⟨76177137782970020147738125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101569517043960026863650833 76177137782970020147738125)
        ·
          refine ⟨28566426668613757555401797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76177137782970020147738125 28566426668613757555401797)
          ·
            refine ⟨5356205000365079541637837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28566426668613757555401797 5356205000365079541637837)
            ·
              refine ⟨2008576875136904828114189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5356205000365079541637837 2008576875136904828114189)
              ·
                refine ⟨753216328176339310542821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2008576875136904828114189 753216328176339310542821)
                ·
                  refine ⟨141228061533063620726779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 753216328176339310542821 141228061533063620726779)
                  ·
                    rfl

theorem cell22_1237683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 4].length) (baseStart_1237683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237683 prefixEnd_1237683 := by exact prefixLift 1237683
  have htrace : WordTrace (prefixWord ++ tailWord_1237683) baseStart_1237683 baseEnd_1237683 := by
    simpa [prefixWord, tailWord_1237683, baseEnd_1237683] using wordTrace_append hprefix tailTrace_1237683
  have hstable : (prefixWord ++ tailWord_1237683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237683).length < 2 ^ (prefixWord ++ tailWord_1237683).sum := by decide
  have hdescent : baseEnd_1237683 < baseStart_1237683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237696 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 4, 4]
def baseStart_1237696 : Nat := 118140960795 + 1237696 * 2 ^ 59
def prefixEnd_1237696 : Nat := 4983230072969 + 3 ^ 40 * 1237696 * 2
def baseEnd_1237696 : Nat := 423688634764863161605297

theorem tailTrace_1237696 : CollatzResearch.WordTrace tailWord_1237696 prefixEnd_1237696 423688634764863161605297 := by
  unfold tailWord_1237696
  simp only [CollatzResearch.WordTrace]
  refine ⟨22571240862023124246478471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30094987816030832328637961 22571240862023124246478471)
  ·
    refine ⟨33856861293034686369717707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22571240862023124246478471 33856861293034686369717707)
    ·
      refine ⟨50785291939552029554576561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33856861293034686369717707 50785291939552029554576561)
      ·
        refine ⟨38088968954664022165932421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50785291939552029554576561 38088968954664022165932421)
        ·
          refine ⟨7141681678999504156112329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38088968954664022165932421 7141681678999504156112329)
          ·
            refine ⟨5356261259249628117084247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7141681678999504156112329 5356261259249628117084247)
            ·
              refine ⟨8034391888874442175626371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5356261259249628117084247 8034391888874442175626371)
              ·
                refine ⟨12051587833311663263439557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8034391888874442175626371 12051587833311663263439557)
                ·
                  refine ⟨2259672718745936861894917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12051587833311663263439557 2259672718745936861894917)
                  ·
                    refine ⟨423688634764863161605297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2259672718745936861894917 423688634764863161605297)
                    ·
                      rfl

theorem cell22_1237696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 4, 4].length) (baseStart_1237696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237696 prefixEnd_1237696 := by exact prefixLift 1237696
  have htrace : WordTrace (prefixWord ++ tailWord_1237696) baseStart_1237696 baseEnd_1237696 := by
    simpa [prefixWord, tailWord_1237696, baseEnd_1237696] using wordTrace_append hprefix tailTrace_1237696
  have hstable : (prefixWord ++ tailWord_1237696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237696).length < 2 ^ (prefixWord ++ tailWord_1237696).sum := by decide
  have hdescent : baseEnd_1237696 < baseStart_1237696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237758 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_1237758 : Nat := 118140960795 + 1237758 * 2 ^ 59
def prefixEnd_1237758 : Nat := 4983230072969 + 3 ^ 40 * 1237758 * 2
def baseEnd_1237758 : Nat := 423709858631915666555107

theorem tailTrace_1237758 : CollatzResearch.WordTrace tailWord_1237758 prefixEnd_1237758 423709858631915666555107 := by
  unfold tailWord_1237758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5643092881227704135214241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30096495366547755387809285 5643092881227704135214241)
  ·
    refine ⟨4232319660920778101410681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5643092881227704135214241 4232319660920778101410681)
    ·
      refine ⟨3174239745690583576058011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4232319660920778101410681 3174239745690583576058011)
      ·
        refine ⟨4761359618535875364087017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3174239745690583576058011 4761359618535875364087017)
        ·
          refine ⟨3571019713901906523065263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4761359618535875364087017 3571019713901906523065263)
          ·
            refine ⟨5356529570852859784597895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3571019713901906523065263 5356529570852859784597895)
            ·
              refine ⟨8034794356279289676896843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5356529570852859784597895 8034794356279289676896843)
              ·
                refine ⟨12052191534418934515345265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8034794356279289676896843 12052191534418934515345265)
                ·
                  refine ⟨9039143650814200886508949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12052191534418934515345265 9039143650814200886508949)
                  ·
                    refine ⟨423709858631915666555107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9039143650814200886508949 423709858631915666555107)
                    ·
                      rfl

theorem cell22_1237758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_1237758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237758 prefixEnd_1237758 := by exact prefixLift 1237758
  have htrace : WordTrace (prefixWord ++ tailWord_1237758) baseStart_1237758 baseEnd_1237758 := by
    simpa [prefixWord, tailWord_1237758, baseEnd_1237758] using wordTrace_append hprefix tailTrace_1237758
  have hstable : (prefixWord ++ tailWord_1237758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237758).length < 2 ^ (prefixWord ++ tailWord_1237758).sum := by decide
  have hdescent : baseEnd_1237758 < baseStart_1237758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237833 : List Nat := [1, 2, 1, 1, 2, 5, 3, 1, 1, 5]
def baseStart_1237833 : Nat := 118140960795 + 1237833 * 2 ^ 59
def prefixEnd_1237833 : Nat := 4983230072969 + 3 ^ 40 * 1237833 * 2
def baseEnd_1237833 : Nat := 423735532664640470929877

theorem tailTrace_1237833 : CollatzResearch.WordTrace tailWord_1237833 prefixEnd_1237833 423735532664640470929877 := by
  unfold tailWord_1237833
  simp only [CollatzResearch.WordTrace]
  refine ⟨45147478524549920890694153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30098319016366613927129435 45147478524549920890694153)
  ·
    refine ⟨33860608893412440668020615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45147478524549920890694153 33860608893412440668020615)
    ·
      refine ⟨50790913340118661002030923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33860608893412440668020615 50790913340118661002030923)
      ·
        refine ⟨76186370010177991503046385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50790913340118661002030923 76186370010177991503046385)
        ·
          refine ⟨57139777507633493627284789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76186370010177991503046385 57139777507633493627284789)
          ·
            refine ⟨5356854141340640027557949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57139777507633493627284789 5356854141340640027557949)
            ·
              refine ⟨2008820303002740010334231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5356854141340640027557949 2008820303002740010334231)
              ·
                refine ⟨3013230454504110015501347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008820303002740010334231 3013230454504110015501347)
                ·
                  refine ⟨4519845681756165023252021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3013230454504110015501347 4519845681756165023252021)
                  ·
                    refine ⟨423735532664640470929877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4519845681756165023252021 423735532664640470929877)
                    ·
                      rfl

theorem cell22_1237833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 5].length) (baseStart_1237833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237833 prefixEnd_1237833 := by exact prefixLift 1237833
  have htrace : WordTrace (prefixWord ++ tailWord_1237833) baseStart_1237833 baseEnd_1237833 := by
    simpa [prefixWord, tailWord_1237833, baseEnd_1237833] using wordTrace_append hprefix tailTrace_1237833
  have hstable : (prefixWord ++ tailWord_1237833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237833).length < 2 ^ (prefixWord ++ tailWord_1237833).sum := by decide
  have hdescent : baseEnd_1237833 < baseStart_1237833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237852 : List Nat := [2, 2, 4, 2, 1, 1, 3, 3, 4]
def baseStart_1237852 : Nat := 118140960795 + 1237852 * 2 ^ 59
def prefixEnd_1237852 : Nat := 4983230072969 + 3 ^ 40 * 1237852 * 2
def baseEnd_1237852 : Nat := 141247345584310251568273

theorem tailTrace_1237852 : CollatzResearch.WordTrace tailWord_1237852 prefixEnd_1237852 141247345584310251568273 := by
  unfold tailWord_1237852
  simp only [CollatzResearch.WordTrace]
  refine ⟨22574085755740543567817905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30098781007654058090423873 22574085755740543567817905)
  ·
    refine ⟨16930564316805407675863429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22574085755740543567817905 16930564316805407675863429)
    ·
      refine ⟨3174480809401013939224393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16930564316805407675863429 3174480809401013939224393)
      ·
        refine ⟨2380860607050760454418295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3174480809401013939224393 2380860607050760454418295)
        ·
          refine ⟨3571290910576140681627443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2380860607050760454418295 3571290910576140681627443)
          ·
            refine ⟨5356936365864211022441165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3571290910576140681627443 5356936365864211022441165)
            ·
              refine ⟨2008851137199079133415437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5356936365864211022441165 2008851137199079133415437)
              ·
                refine ⟨753319176449654675030789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2008851137199079133415437 753319176449654675030789)
                ·
                  refine ⟨141247345584310251568273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 753319176449654675030789 141247345584310251568273)
                  ·
                    rfl

theorem cell22_1237852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 4].length) (baseStart_1237852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237852 prefixEnd_1237852 := by exact prefixLift 1237852
  have htrace : WordTrace (prefixWord ++ tailWord_1237852) baseStart_1237852 baseEnd_1237852 := by
    simpa [prefixWord, tailWord_1237852, baseEnd_1237852] using wordTrace_append hprefix tailTrace_1237852
  have hstable : (prefixWord ++ tailWord_1237852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237852).length < 2 ^ (prefixWord ++ tailWord_1237852).sum := by decide
  have hdescent : baseEnd_1237852 < baseStart_1237852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237863 : List Nat := [1, 1, 5, 1, 2, 4, 8]
def baseStart_1237863 : Nat := 118140960795 + 1237863 * 2 ^ 59
def prefixEnd_1237863 : Nat := 4983230072969 + 3 ^ 40 * 1237863 * 2
def baseEnd_1237863 : Nat := 15694288973249273802955

theorem tailTrace_1237863 : CollatzResearch.WordTrace tailWord_1237863 prefixEnd_1237863 15694288973249273802955 := by
  unfold tailWord_1237863
  simp only [CollatzResearch.WordTrace]
  refine ⟨45148572714441236014286243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30099048476294157342857495 45148572714441236014286243)
  ·
    refine ⟨67722859071661854021429365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45148572714441236014286243 67722859071661854021429365)
    ·
      refine ⟨6349018037968298814509003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67722859071661854021429365 6349018037968298814509003)
      ·
        refine ⟨9523527056952448221763505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6349018037968298814509003 9523527056952448221763505)
        ·
          refine ⟨7142645292714336166322629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9523527056952448221763505 7142645292714336166322629)
          ·
            refine ⟨1339245992383938031185493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7142645292714336166322629 1339245992383938031185493)
            ·
              refine ⟨15694288973249273802955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1339245992383938031185493 15694288973249273802955)
              ·
                rfl

theorem cell22_1237863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 8].length) (baseStart_1237863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237863 prefixEnd_1237863 := by exact prefixLift 1237863
  have htrace : WordTrace (prefixWord ++ tailWord_1237863) baseStart_1237863 baseEnd_1237863 := by
    simpa [prefixWord, tailWord_1237863, baseEnd_1237863] using wordTrace_append hprefix tailTrace_1237863
  have hstable : (prefixWord ++ tailWord_1237863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237863).length < 2 ^ (prefixWord ++ tailWord_1237863).sum := by decide
  have hdescent : baseEnd_1237863 < baseStart_1237863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237972 : List Nat := [2, 4, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_1237972 : Nat := 118140960795 + 1237972 * 2 ^ 59
def prefixEnd_1237972 : Nat := 4983230072969 + 3 ^ 40 * 1237972 * 2
def baseEnd_1237972 : Nat := 423783115205290441704451

theorem tailTrace_1237972 : CollatzResearch.WordTrace tailWord_1237972 prefixEnd_1237972 423783115205290441704451 := by
  unfold tailWord_1237972
  simp only [CollatzResearch.WordTrace]
  refine ⟨22576274135523173815002085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30101698847364231753336113 22576274135523173815002085)
  ·
    refine ⟨4233051400410595090312891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22576274135523173815002085 4233051400410595090312891)
    ·
      refine ⟨6349577100615892635469337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4233051400410595090312891 6349577100615892635469337)
      ·
        refine ⟨4762182825461919476602003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6349577100615892635469337 4762182825461919476602003)
        ·
          refine ⟨7143274238192879214903005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4762182825461919476602003 7143274238192879214903005)
          ·
            refine ⟨2678727839322329705588627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7143274238192879214903005 2678727839322329705588627)
            ·
              refine ⟨4018091758983494558382941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2678727839322329705588627 4018091758983494558382941)
              ·
                refine ⟨1506784409618810459393603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4018091758983494558382941 1506784409618810459393603)
                ·
                  refine ⟨2260176614428215689090405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1506784409618810459393603 2260176614428215689090405)
                  ·
                    refine ⟨423783115205290441704451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2260176614428215689090405 423783115205290441704451)
                    ·
                      rfl

theorem cell22_1237972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_1237972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1237972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1237972 prefixEnd_1237972 := by exact prefixLift 1237972
  have htrace : WordTrace (prefixWord ++ tailWord_1237972) baseStart_1237972 baseEnd_1237972 := by
    simpa [prefixWord, tailWord_1237972, baseEnd_1237972] using wordTrace_append hprefix tailTrace_1237972
  have hstable : (prefixWord ++ tailWord_1237972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237972).length < 2 ^ (prefixWord ++ tailWord_1237972).sum := by decide
  have hdescent : baseEnd_1237972 < baseStart_1237972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238013 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_1238013 : Nat := 118140960795 + 1238013 * 2 ^ 59
def prefixEnd_1238013 : Nat := 4983230072969 + 3 ^ 40 * 1238013 * 2
def baseEnd_1238013 : Nat := 423797150343180001429325

theorem tailTrace_1238013 : CollatzResearch.WordTrace tailWord_1238013 prefixEnd_1238013 423797150343180001429325 := by
  unfold tailWord_1238013
  simp only [CollatzResearch.WordTrace]
  refine ⟨45154043663897811632246693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30102695775931874421497795 45154043663897811632246693)
  ·
    refine ⟨8466383186980839681046255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45154043663897811632246693 8466383186980839681046255)
    ·
      refine ⟨12699574780471259521569383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8466383186980839681046255 12699574780471259521569383)
      ·
        refine ⟨19049362170706889282354075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12699574780471259521569383 19049362170706889282354075)
        ·
          refine ⟨28574043256060333923531113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19049362170706889282354075 28574043256060333923531113)
          ·
            refine ⟨21430532442045250442648335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28574043256060333923531113 21430532442045250442648335)
            ·
              refine ⟨32145798663067875663972503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21430532442045250442648335 32145798663067875663972503)
              ·
                refine ⟨48218697994601813495958755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32145798663067875663972503 48218697994601813495958755)
                ·
                  refine ⟨72328046991902720243938133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48218697994601813495958755 72328046991902720243938133)
                  ·
                    refine ⟨423797150343180001429325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 72328046991902720243938133 423797150343180001429325)
                    ·
                      rfl

theorem cell22_1238013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_1238013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238013 prefixEnd_1238013 := by exact prefixLift 1238013
  have htrace : WordTrace (prefixWord ++ tailWord_1238013) baseStart_1238013 baseEnd_1238013 := by
    simpa [prefixWord, tailWord_1238013, baseEnd_1238013] using wordTrace_append hprefix tailTrace_1238013
  have hstable : (prefixWord ++ tailWord_1238013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238013).length < 2 ^ (prefixWord ++ tailWord_1238013).sum := by decide
  have hdescent : baseEnd_1238013 < baseStart_1238013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238047 : List Nat := [1, 1, 2, 4, 1, 3, 3, 1, 3, 3]
def baseStart_1238047 : Nat := 118140960795 + 1238047 * 2 ^ 59
def prefixEnd_1238047 : Nat := 4983230072969 + 3 ^ 40 * 1238047 * 2
def baseEnd_1238047 : Nat := 423808789238015246079221

theorem tailTrace_1238047 : CollatzResearch.WordTrace tailWord_1238047 prefixEnd_1238047 423808789238015246079221 := by
  unfold tailWord_1238047
  simp only [CollatzResearch.WordTrace]
  refine ⟨45155283745774635438984395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30103522497183090292656263 45155283745774635438984395)
  ·
    refine ⟨67732925618661953158476593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45155283745774635438984395 67732925618661953158476593)
    ·
      refine ⟨50799694213996464868857445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67732925618661953158476593 50799694213996464868857445)
      ·
        refine ⟨9524942665124337162910771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50799694213996464868857445 9524942665124337162910771)
        ·
          refine ⟨14287413997686505744366157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9524942665124337162910771 14287413997686505744366157)
          ·
            refine ⟨5357780249132439654137309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14287413997686505744366157 5357780249132439654137309)
            ·
              refine ⟨2009167593424664870301491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5357780249132439654137309 2009167593424664870301491)
              ·
                refine ⟨3013751390136997305452237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009167593424664870301491 3013751390136997305452237)
                ·
                  refine ⟨1130156771301373989544589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3013751390136997305452237 1130156771301373989544589)
                  ·
                    refine ⟨423808789238015246079221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1130156771301373989544589 423808789238015246079221)
                    ·
                      rfl

theorem cell22_1238047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 3].length) (baseStart_1238047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238047 prefixEnd_1238047 := by exact prefixLift 1238047
  have htrace : WordTrace (prefixWord ++ tailWord_1238047) baseStart_1238047 baseEnd_1238047 := by
    simpa [prefixWord, tailWord_1238047, baseEnd_1238047] using wordTrace_append hprefix tailTrace_1238047
  have hstable : (prefixWord ++ tailWord_1238047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238047).length < 2 ^ (prefixWord ++ tailWord_1238047).sum := by decide
  have hdescent : baseEnd_1238047 < baseStart_1238047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238060 : List Nat := [2, 2, 1, 1, 1, 2, 5, 3, 5]
def baseStart_1238060 : Nat := 118140960795 + 1238060 * 2 ^ 59
def prefixEnd_1238060 : Nat := 4983230072969 + 3 ^ 40 * 1238060 * 2
def baseEnd_1238060 : Nat := 141271079801229181834727

theorem tailTrace_1238060 : CollatzResearch.WordTrace tailWord_1238060 prefixEnd_1238060 141271079801229181834727 := by
  unfold tailWord_1238060
  simp only [CollatzResearch.WordTrace]
  refine ⟨22577878947363769329603817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30103838596485025772805089 22577878947363769329603817)
  ·
    refine ⟨16933409210522826997202863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22577878947363769329603817 16933409210522826997202863)
    ·
      refine ⟨25400113815784240495804295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16933409210522826997202863 25400113815784240495804295)
      ·
        refine ⟨38100170723676360743706443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25400113815784240495804295 38100170723676360743706443)
        ·
          refine ⟨57150256085514541115559665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38100170723676360743706443 57150256085514541115559665)
          ·
            refine ⟨42862692064135905836669749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57150256085514541115559665 42862692064135905836669749)
            ·
              refine ⟨4018377381012741172187789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42862692064135905836669749 4018377381012741172187789)
              ·
                refine ⟨1506891517879777939570421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4018377381012741172187789 1506891517879777939570421)
                ·
                  refine ⟨141271079801229181834727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1506891517879777939570421 141271079801229181834727)
                  ·
                    rfl

theorem cell22_1238060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_1238060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238060 prefixEnd_1238060 := by exact prefixLift 1238060
  have htrace : WordTrace (prefixWord ++ tailWord_1238060) baseStart_1238060 baseEnd_1238060 := by
    simpa [prefixWord, tailWord_1238060, baseEnd_1238060] using wordTrace_append hprefix tailTrace_1238060
  have hstable : (prefixWord ++ tailWord_1238060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238060).length < 2 ^ (prefixWord ++ tailWord_1238060).sum := by decide
  have hdescent : baseEnd_1238060 < baseStart_1238060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238098 : List Nat := [3, 2, 2, 1, 3, 3, 2, 2, 1, 3]
def baseStart_1238098 : Nat := 118140960795 + 1238098 * 2 ^ 59
def prefixEnd_1238098 : Nat := 4983230072969 + 3 ^ 40 * 1238098 * 2
def baseEnd_1238098 : Nat := 423826247580268113054065

theorem tailTrace_1238098 : CollatzResearch.WordTrace tailWord_1238098 prefixEnd_1238098 423826247580268113054065 := by
  unfold tailWord_1238098
  simp only [CollatzResearch.WordTrace]
  refine ⟨11289285967147467787272737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30104762579059914099393965 11289285967147467787272737)
  ·
    refine ⟨8466964475360600840454553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11289285967147467787272737 8466964475360600840454553)
    ·
      refine ⟨6350223356520450630340915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8466964475360600840454553 6350223356520450630340915)
      ·
        refine ⟨9525335034780675945511373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6350223356520450630340915 9525335034780675945511373)
        ·
          refine ⟨3572000638042753479566765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9525335034780675945511373 3572000638042753479566765)
          ·
            refine ⟨1339500239266032554837537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3572000638042753479566765 1339500239266032554837537)
            ·
              refine ⟨1004625179449524416128153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1339500239266032554837537 1004625179449524416128153)
              ·
                refine ⟨753468884587143312096115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1004625179449524416128153 753468884587143312096115)
                ·
                  refine ⟨1130203326880714968144173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 753468884587143312096115 1130203326880714968144173)
                  ·
                    refine ⟨423826247580268113054065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1130203326880714968144173 423826247580268113054065)
                    ·
                      rfl

theorem cell22_1238098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_1238098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238098 prefixEnd_1238098 := by exact prefixLift 1238098
  have htrace : WordTrace (prefixWord ++ tailWord_1238098) baseStart_1238098 baseEnd_1238098 := by
    simpa [prefixWord, tailWord_1238098, baseEnd_1238098] using wordTrace_append hprefix tailTrace_1238098
  have hstable : (prefixWord ++ tailWord_1238098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238098).length < 2 ^ (prefixWord ++ tailWord_1238098).sum := by decide
  have hdescent : baseEnd_1238098 < baseStart_1238098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238109 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1238109 : Nat := 118140960795 + 1238109 * 2 ^ 59
def prefixEnd_1238109 : Nat := 4983230072969 + 3 ^ 40 * 1238109 * 2
def baseEnd_1238109 : Nat := 423830013105067751029031

theorem tailTrace_1238109 : CollatzResearch.WordTrace tailWord_1238109 prefixEnd_1238109 423830013105067751029031 := by
  unfold tailWord_1238109
  simp only [CollatzResearch.WordTrace]
  refine ⟨45157545071550020027741381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30105030047700013351827587 45157545071550020027741381)
  ·
    refine ⟨8467039700915628755201509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45157545071550020027741381 8467039700915628755201509)
    ·
      refine ⟨1587569943921680391600283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8467039700915628755201509 1587569943921680391600283)
      ·
        refine ⟨2381354915882520587400425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1587569943921680391600283 2381354915882520587400425)
        ·
          refine ⟨1786016186911890440550319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2381354915882520587400425 1786016186911890440550319)
          ·
            refine ⟨2679024280367835660825479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786016186911890440550319 2679024280367835660825479)
            ·
              refine ⟨4018536420551753491238219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2679024280367835660825479 4018536420551753491238219)
              ·
                refine ⟨6027804630827630236857329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4018536420551753491238219 6027804630827630236857329)
                ·
                  refine ⟨4520853473120722677642997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6027804630827630236857329 4520853473120722677642997)
                  ·
                    refine ⟨423830013105067751029031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4520853473120722677642997 423830013105067751029031)
                    ·
                      rfl

theorem cell22_1238109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1238109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238109 prefixEnd_1238109 := by exact prefixLift 1238109
  have htrace : WordTrace (prefixWord ++ tailWord_1238109) baseStart_1238109 baseEnd_1238109 := by
    simpa [prefixWord, tailWord_1238109, baseEnd_1238109] using wordTrace_append hprefix tailTrace_1238109
  have hstable : (prefixWord ++ tailWord_1238109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238109).length < 2 ^ (prefixWord ++ tailWord_1238109).sum := by decide
  have hdescent : baseEnd_1238109 < baseStart_1238109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238122 : List Nat := [3, 1, 3, 2, 2, 2, 1, 2, 6]
def baseStart_1238122 : Nat := 118140960795 + 1238122 * 2 ^ 59
def prefixEnd_1238122 : Nat := 4983230072969 + 3 ^ 40 * 1238122 * 2
def baseEnd_1238122 : Nat := 141278154423580016817997

theorem tailTrace_1238122 : CollatzResearch.WordTrace tailWord_1238122 prefixEnd_1238122 141278154423580016817997 := by
  unfold tailWord_1238122
  simp only [CollatzResearch.WordTrace]
  refine ⟨11289504805125730811991155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30105346147001948831976413 11289504805125730811991155)
  ·
    refine ⟨16934257207688596217986733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11289504805125730811991155 16934257207688596217986733)
    ·
      refine ⟨6350346452883223581745025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16934257207688596217986733 6350346452883223581745025)
      ·
        refine ⟨4762759839662417686308769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6350346452883223581745025 4762759839662417686308769)
        ·
          refine ⟨3572069879746813264731577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4762759839662417686308769 3572069879746813264731577)
          ·
            refine ⟨2679052409810109948548683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3572069879746813264731577 2679052409810109948548683)
            ·
              refine ⟨4018578614715164922823025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2679052409810109948548683 4018578614715164922823025)
              ·
                refine ⟨3013933961036373692117269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4018578614715164922823025 3013933961036373692117269)
                ·
                  refine ⟨141278154423580016817997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3013933961036373692117269 141278154423580016817997)
                  ·
                    rfl

theorem cell22_1238122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_1238122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238122 prefixEnd_1238122 := by exact prefixLift 1238122
  have htrace : WordTrace (prefixWord ++ tailWord_1238122) baseStart_1238122 baseEnd_1238122 := by
    simpa [prefixWord, tailWord_1238122, baseEnd_1238122] using wordTrace_append hprefix tailTrace_1238122
  have hstable : (prefixWord ++ tailWord_1238122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238122).length < 2 ^ (prefixWord ++ tailWord_1238122).sum := by decide
  have hdescent : baseEnd_1238122 < baseStart_1238122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238135 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 1, 6]
def baseStart_1238135 : Nat := 118140960795 + 1238135 * 2 ^ 59
def prefixEnd_1238135 : Nat := 4983230072969 + 3 ^ 40 * 1238135 * 2
def baseEnd_1238135 : Nat := 423838913436412349878951

theorem tailTrace_1238135 : CollatzResearch.WordTrace tailWord_1238135 prefixEnd_1238135 423838913436412349878951 := by
  unfold tailWord_1238135
  simp only [CollatzResearch.WordTrace]
  refine ⟨45158493369455826468187859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30105662246303884312125239 45158493369455826468187859)
  ·
    refine ⟨67737740054183739702281789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45158493369455826468187859 67737740054183739702281789)
    ·
      refine ⟨25401652520318902388355671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67737740054183739702281789 25401652520318902388355671)
      ·
        refine ⟨38102478780478353582533507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25401652520318902388355671 38102478780478353582533507)
        ·
          refine ⟨57153718170717530373800261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38102478780478353582533507 57153718170717530373800261)
          ·
            refine ⟨10716322157009536945087549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57153718170717530373800261 10716322157009536945087549)
            ·
              refine ⟨4018620808878576354407831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10716322157009536945087549 4018620808878576354407831)
              ·
                refine ⟨6027931213317864531611747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4018620808878576354407831 6027931213317864531611747)
                ·
                  refine ⟨9041896819976796797417621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6027931213317864531611747 9041896819976796797417621)
                  ·
                    refine ⟨423838913436412349878951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9041896819976796797417621 423838913436412349878951)
                    ·
                      rfl

theorem cell22_1238135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_1238135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238135 prefixEnd_1238135 := by exact prefixLift 1238135
  have htrace : WordTrace (prefixWord ++ tailWord_1238135) baseStart_1238135 baseEnd_1238135 := by
    simpa [prefixWord, tailWord_1238135, baseEnd_1238135] using wordTrace_append hprefix tailTrace_1238135
  have hstable : (prefixWord ++ tailWord_1238135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238135).length < 2 ^ (prefixWord ++ tailWord_1238135).sum := by decide
  have hdescent : baseEnd_1238135 < baseStart_1238135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238195 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 7]
def baseStart_1238195 : Nat := 118140960795 + 1238195 * 2 ^ 59
def prefixEnd_1238195 : Nat := 4983230072969 + 3 ^ 40 * 1238195 * 2
def baseEnd_1238195 : Nat := 141286484220864064459589

theorem tailTrace_1238195 : CollatzResearch.WordTrace tailWord_1238195 prefixEnd_1238195 141286484220864064459589 := by
  unfold tailWord_1238195
  simp only [CollatzResearch.WordTrace]
  refine ⟨45160681749238456715372039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30107121166158971143581359 45160681749238456715372039)
  ·
    refine ⟨67741022623857685073058059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45160681749238456715372039 67741022623857685073058059)
    ·
      refine ⟨101611533935786527609587089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67741022623857685073058059 101611533935786527609587089)
      ·
        refine ⟨76208650451839895707190317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101611533935786527609587089 76208650451839895707190317)
        ·
          refine ⟨28578243919439960890196369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76208650451839895707190317 28578243919439960890196369)
          ·
            refine ⟨21433682939579970667647277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28578243919439960890196369 21433682939579970667647277)
            ·
              refine ⟨8037631102342489000367729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21433682939579970667647277 8037631102342489000367729)
              ·
                refine ⟨6028223326756866750275797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8037631102342489000367729 6028223326756866750275797)
                ·
                  refine ⟨141286484220864064459589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6028223326756866750275797 141286484220864064459589)
                  ·
                    rfl

theorem cell22_1238195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 7].length) (baseStart_1238195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238195 prefixEnd_1238195 := by exact prefixLift 1238195
  have htrace : WordTrace (prefixWord ++ tailWord_1238195) baseStart_1238195 baseEnd_1238195 := by
    simpa [prefixWord, tailWord_1238195, baseEnd_1238195] using wordTrace_append hprefix tailTrace_1238195
  have hstable : (prefixWord ++ tailWord_1238195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238195).length < 2 ^ (prefixWord ++ tailWord_1238195).sum := by decide
  have hdescent : baseEnd_1238195 < baseStart_1238195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238225 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 2, 8]
def baseStart_1238225 : Nat := 118140960795 + 1238225 * 2 ^ 59
def prefixEnd_1238225 : Nat := 4983230072969 + 3 ^ 40 * 1238225 * 2
def baseEnd_1238225 : Nat := 423869722275682115128675

theorem tailTrace_1238225 : CollatzResearch.WordTrace tailWord_1238225 prefixEnd_1238225 423869722275682115128675 := by
  unfold tailWord_1238225
  simp only [CollatzResearch.WordTrace]
  refine ⟨45161775939129771838964129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30107850626086514559309419 45161775939129771838964129)
  ·
    refine ⟨33871331954347328879223097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45161775939129771838964129 33871331954347328879223097)
    ·
      refine ⟨25403498965760496659417323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33871331954347328879223097 25403498965760496659417323)
      ·
        refine ⟨38105248448640744989125985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25403498965760496659417323 38105248448640744989125985)
        ·
          refine ⟨28578936336480558741844489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38105248448640744989125985 28578936336480558741844489)
          ·
            refine ⟨21434202252360419056383367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28578936336480558741844489 21434202252360419056383367)
            ·
              refine ⟨32151303378540628584575051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21434202252360419056383367 32151303378540628584575051)
              ·
                refine ⟨48226955067810942876862577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32151303378540628584575051 48226955067810942876862577)
                ·
                  refine ⟨36170216300858207157646933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48226955067810942876862577 36170216300858207157646933)
                  ·
                    refine ⟨423869722275682115128675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36170216300858207157646933 423869722275682115128675)
                    ·
                      rfl

theorem cell22_1238225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_1238225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238225 prefixEnd_1238225 := by exact prefixLift 1238225
  have htrace : WordTrace (prefixWord ++ tailWord_1238225) baseStart_1238225 baseEnd_1238225 := by
    simpa [prefixWord, tailWord_1238225, baseEnd_1238225] using wordTrace_append hprefix tailTrace_1238225
  have hstable : (prefixWord ++ tailWord_1238225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238225).length < 2 ^ (prefixWord ++ tailWord_1238225).sum := by decide
  have hdescent : baseEnd_1238225 < baseStart_1238225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238229 : List Nat := [1, 3, 2, 4, 1, 2, 1, 3, 5]
def baseStart_1238229 : Nat := 118140960795 + 1238229 * 2 ^ 59
def prefixEnd_1238229 : Nat := 4983230072969 + 3 ^ 40 * 1238229 * 2
def baseEnd_1238229 : Nat := 141290363852475812676221

theorem tailTrace_1238229 : CollatzResearch.WordTrace tailWord_1238229 prefixEnd_1238229 141290363852475812676221 := by
  unfold tailWord_1238229
  simp only [CollatzResearch.WordTrace]
  refine ⟨45161921831115280522109741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30107947887410187014739827 45161921831115280522109741)
  ·
    refine ⟨16935720686668230195791153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45161921831115280522109741 16935720686668230195791153)
    ·
      refine ⟨12701790515001172646843365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16935720686668230195791153 12701790515001172646843365)
      ·
        refine ⟨2381585721562719871283131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12701790515001172646843365 2381585721562719871283131)
        ·
          refine ⟨3572378582344079806924697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2381585721562719871283131 3572378582344079806924697)
          ·
            refine ⟨2679283936758059855193523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3572378582344079806924697 2679283936758059855193523)
            ·
              refine ⟨4018925905137089782790285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2679283936758059855193523 4018925905137089782790285)
              ·
                refine ⟨1507097214426408668546357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4018925905137089782790285 1507097214426408668546357)
                ·
                  refine ⟨141290363852475812676221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1507097214426408668546357 141290363852475812676221)
                  ·
                    rfl

theorem cell22_1238229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_1238229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238229 prefixEnd_1238229 := by exact prefixLift 1238229
  have htrace : WordTrace (prefixWord ++ tailWord_1238229) baseStart_1238229 baseEnd_1238229 := by
    simpa [prefixWord, tailWord_1238229, baseEnd_1238229] using wordTrace_append hprefix tailTrace_1238229
  have hstable : (prefixWord ++ tailWord_1238229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238229).length < 2 ^ (prefixWord ++ tailWord_1238229).sum := by decide
  have hdescent : baseEnd_1238229 < baseStart_1238229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238289 : List Nat := [1, 2, 2, 1, 1, 4, 1, 5, 2, 3]
def baseStart_1238289 : Nat := 118140960795 + 1238289 * 2 ^ 59
def prefixEnd_1238289 : Nat := 4983230072969 + 3 ^ 40 * 1238289 * 2
def baseEnd_1238289 : Nat := 423891630783607281528479

theorem tailTrace_1238289 : CollatzResearch.WordTrace tailWord_1238289 prefixEnd_1238289 423891630783607281528479 := by
  unfold tailWord_1238289
  simp only [CollatzResearch.WordTrace]
  refine ⟨45164110210897910769293921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30109406807265273846195947 45164110210897910769293921)
  ·
    refine ⟨33873082658173433076970441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45164110210897910769293921 33873082658173433076970441)
    ·
      refine ⟨25404811993630074807727831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33873082658173433076970441 25404811993630074807727831)
      ·
        refine ⟨38107217990445112211591747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25404811993630074807727831 38107217990445112211591747)
        ·
          refine ⟨57160826985667668317387621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38107217990445112211591747 57160826985667668317387621)
          ·
            refine ⟨10717655059812687809510179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57160826985667668317387621 10717655059812687809510179)
            ·
              refine ⟨16076482589719031714265269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10717655059812687809510179 16076482589719031714265269)
              ·
                refine ⟨1507170242786159223212369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16076482589719031714265269 1507170242786159223212369)
                ·
                  refine ⟨1130377682089619417409277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1507170242786159223212369 1130377682089619417409277)
                  ·
                    refine ⟨423891630783607281528479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1130377682089619417409277 423891630783607281528479)
                    ·
                      rfl

theorem cell22_1238289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_1238289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238289 prefixEnd_1238289 := by exact prefixLift 1238289
  have htrace : WordTrace (prefixWord ++ tailWord_1238289) baseStart_1238289 baseEnd_1238289 := by
    simpa [prefixWord, tailWord_1238289, baseEnd_1238289] using wordTrace_append hprefix tailTrace_1238289
  have hstable : (prefixWord ++ tailWord_1238289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238289).length < 2 ^ (prefixWord ++ tailWord_1238289).sum := by decide
  have hdescent : baseEnd_1238289 < baseStart_1238289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238304 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 1, 6]
def baseStart_1238304 : Nat := 118140960795 + 1238304 * 2 ^ 59
def prefixEnd_1238304 : Nat := 4983230072969 + 3 ^ 40 * 1238304 * 2
def baseEnd_1238304 : Nat := 423896765590152242403433

theorem tailTrace_1238304 : CollatzResearch.WordTrace tailWord_1238304 prefixEnd_1238304 423896765590152242403433 := by
  unfold tailWord_1238304
  simp only [CollatzResearch.WordTrace]
  refine ⟨22582328652921784165544983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30109771537229045554059977 22582328652921784165544983)
  ·
    refine ⟨33873492979382676248317475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22582328652921784165544983 33873492979382676248317475)
    ·
      refine ⟨50810239469074014372476213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33873492979382676248317475 50810239469074014372476213)
      ·
        refine ⟨4763459950225688847419645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50810239469074014372476213 4763459950225688847419645)
        ·
          refine ⟨1786297481334633317782367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4763459950225688847419645 1786297481334633317782367)
          ·
            refine ⟨2679446222001949976673551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786297481334633317782367 2679446222001949976673551)
            ·
              refine ⟨4019169333002924965010327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2679446222001949976673551 4019169333002924965010327)
              ·
                refine ⟨6028753999504387447515491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4019169333002924965010327 6028753999504387447515491)
                ·
                  refine ⟨9043130999256581171273237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6028753999504387447515491 9043130999256581171273237)
                  ·
                    refine ⟨423896765590152242403433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9043130999256581171273237 423896765590152242403433)
                    ·
                      rfl

theorem cell22_1238304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 1, 6].length) (baseStart_1238304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238304 prefixEnd_1238304 := by exact prefixLift 1238304
  have htrace : WordTrace (prefixWord ++ tailWord_1238304) baseStart_1238304 baseEnd_1238304 := by
    simpa [prefixWord, tailWord_1238304, baseEnd_1238304] using wordTrace_append hprefix tailTrace_1238304
  have hstable : (prefixWord ++ tailWord_1238304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238304).length < 2 ^ (prefixWord ++ tailWord_1238304).sum := by decide
  have hdescent : baseEnd_1238304 < baseStart_1238304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238340 : List Nat := [2, 3, 4, 1, 1, 2, 3, 1, 2, 3]
def baseStart_1238340 : Nat := 118140960795 + 1238340 * 2 ^ 59
def prefixEnd_1238340 : Nat := 4983230072969 + 3 ^ 40 * 1238340 * 2
def baseEnd_1238340 : Nat := 423909089125860148503323

theorem tailTrace_1238340 : CollatzResearch.WordTrace tailWord_1238340 prefixEnd_1238340 423909089125860148503323 := by
  unfold tailWord_1238340
  simp only [CollatzResearch.WordTrace]
  refine ⟨22582985166856573239700237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30110646889142097652933649 22582985166856573239700237)
  ·
    refine ⟨8468619437571214964887589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22582985166856573239700237 8468619437571214964887589)
    ·
      refine ⟨1587866144544602805916423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8468619437571214964887589 1587866144544602805916423)
      ·
        refine ⟨2381799216816904208874635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1587866144544602805916423 2381799216816904208874635)
        ·
          refine ⟨3572698825225356313311953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2381799216816904208874635 3572698825225356313311953)
          ·
            refine ⟨2679524118919017234983965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3572698825225356313311953 2679524118919017234983965)
            ·
              refine ⟨1004821544594631463118987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2679524118919017234983965 1004821544594631463118987)
              ·
                refine ⟨1507232316891947194678481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1004821544594631463118987 1507232316891947194678481)
                ·
                  refine ⟨1130424237668960396008861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1507232316891947194678481 1130424237668960396008861)
                  ·
                    refine ⟨423909089125860148503323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1130424237668960396008861 423909089125860148503323)
                    ·
                      rfl

theorem cell22_1238340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_1238340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238340 prefixEnd_1238340 := by exact prefixLift 1238340
  have htrace : WordTrace (prefixWord ++ tailWord_1238340) baseStart_1238340 baseEnd_1238340 := by
    simpa [prefixWord, tailWord_1238340, baseEnd_1238340] using wordTrace_append hprefix tailTrace_1238340
  have hstable : (prefixWord ++ tailWord_1238340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238340).length < 2 ^ (prefixWord ++ tailWord_1238340).sum := by decide
  have hdescent : baseEnd_1238340 < baseStart_1238340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238362 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 1, 7]
def baseStart_1238362 : Nat := 118140960795 + 1238362 * 2 ^ 59
def prefixEnd_1238362 : Nat := 4983230072969 + 3 ^ 40 * 1238362 * 2
def baseEnd_1238362 : Nat := 423916620175459424453255

theorem tailTrace_1238362 : CollatzResearch.WordTrace tailWord_1238362 prefixEnd_1238362 423916620175459424453255 := by
  unfold tailWord_1238362
  simp only [CollatzResearch.WordTrace]
  refine ⟨11291693184908361059175335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30111181826422296157800893 11291693184908361059175335)
  ·
    refine ⟨16937539777362541588763003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11291693184908361059175335 16937539777362541588763003)
    ·
      refine ⟨25406309666043812383144505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16937539777362541588763003 25406309666043812383144505)
      ·
        refine ⟨19054732249532859287358379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25406309666043812383144505 19054732249532859287358379)
        ·
          refine ⟨28582098374299288931037569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19054732249532859287358379 28582098374299288931037569)
          ·
            refine ⟨21436573780724466698278177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28582098374299288931037569 21436573780724466698278177)
            ·
              refine ⟨16077430335543350023708633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21436573780724466698278177 16077430335543350023708633)
              ·
                refine ⟨12058072751657512517781475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16077430335543350023708633 12058072751657512517781475)
                ·
                  refine ⟨18087109127486268776672213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12058072751657512517781475 18087109127486268776672213)
                  ·
                    refine ⟨423916620175459424453255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18087109127486268776672213 423916620175459424453255)
                    ·
                      rfl

theorem cell22_1238362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_1238362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238362 prefixEnd_1238362 := by exact prefixLift 1238362
  have htrace : WordTrace (prefixWord ++ tailWord_1238362) baseStart_1238362 baseEnd_1238362 := by
    simpa [prefixWord, tailWord_1238362, baseEnd_1238362] using wordTrace_append hprefix tailTrace_1238362
  have hstable : (prefixWord ++ tailWord_1238362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238362).length < 2 ^ (prefixWord ++ tailWord_1238362).sum := by decide
  have hdescent : baseEnd_1238362 < baseStart_1238362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238368 : List Nat := [2, 1, 1, 3, 4, 1, 3, 3, 1, 3]
def baseStart_1238368 : Nat := 118140960795 + 1238368 * 2 ^ 59
def prefixEnd_1238368 : Nat := 4983230072969 + 3 ^ 40 * 1238368 * 2
def baseEnd_1238368 : Nat := 423918674098077408803237

theorem tailTrace_1238368 : CollatzResearch.WordTrace tailWord_1238368 prefixEnd_1238368 423918674098077408803237 := by
  unfold tailWord_1238368
  simp only [CollatzResearch.WordTrace]
  refine ⟨22583495788805853630709879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30111327718407804840946505 22583495788805853630709879)
  ·
    refine ⟨33875243683208780446064819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22583495788805853630709879 33875243683208780446064819)
    ·
      refine ⟨50812865524813170669097229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33875243683208780446064819 50812865524813170669097229)
      ·
        refine ⟨19054824571804939000911461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50812865524813170669097229 19054824571804939000911461)
        ·
          refine ⟨3572779607213426062670899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19054824571804939000911461 3572779607213426062670899)
          ·
            refine ⟨5359169410820139094006349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3572779607213426062670899 5359169410820139094006349)
            ·
              refine ⟨2009688529057552160252381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5359169410820139094006349 2009688529057552160252381)
              ·
                refine ⟨753633198396582060094643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2009688529057552160252381 753633198396582060094643)
                ·
                  refine ⟨1130449797594873090141965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 753633198396582060094643 1130449797594873090141965)
                  ·
                    refine ⟨423918674098077408803237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1130449797594873090141965 423918674098077408803237)
                    ·
                      rfl

theorem cell22_1238368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 1, 3].length) (baseStart_1238368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238368 prefixEnd_1238368 := by exact prefixLift 1238368
  have htrace : WordTrace (prefixWord ++ tailWord_1238368) baseStart_1238368 baseEnd_1238368 := by
    simpa [prefixWord, tailWord_1238368, baseEnd_1238368] using wordTrace_append hprefix tailTrace_1238368
  have hstable : (prefixWord ++ tailWord_1238368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238368).length < 2 ^ (prefixWord ++ tailWord_1238368).sum := by decide
  have hdescent : baseEnd_1238368 < baseStart_1238368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238426 : List Nat := [3, 1, 1, 4, 1, 1, 2, 5, 4]
def baseStart_1238426 : Nat := 118140960795 + 1238426 * 2 ^ 59
def prefixEnd_1238426 : Nat := 4983230072969 + 3 ^ 40 * 1238426 * 2
def baseEnd_1238426 : Nat := 141312842894461530284353

theorem tailTrace_1238426 : CollatzResearch.WordTrace tailWord_1238426 prefixEnd_1238426 141312842894461530284353 := by
  unfold tailWord_1238426
  simp only [CollatzResearch.WordTrace]
  refine ⟨11292276752850395791757783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30112738007601055444687421 11292276752850395791757783)
  ·
    refine ⟨16938415129275593687636675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11292276752850395791757783 16938415129275593687636675)
    ·
      refine ⟨25407622693913390531455013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16938415129275593687636675 25407622693913390531455013)
      ·
        refine ⟨4763929255108760724647815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25407622693913390531455013 4763929255108760724647815)
        ·
          refine ⟨7145893882663141086971723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4763929255108760724647815 7145893882663141086971723)
          ·
            refine ⟨10718840823994711630457585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7145893882663141086971723 10718840823994711630457585)
            ·
              refine ⟨8039130617996033722843189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10718840823994711630457585 8039130617996033722843189)
              ·
                refine ⟨753668495437128161516549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8039130617996033722843189 753668495437128161516549)
                ·
                  refine ⟨141312842894461530284353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 753668495437128161516549 141312842894461530284353)
                  ·
                    rfl

theorem cell22_1238426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 4].length) (baseStart_1238426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238426 prefixEnd_1238426 := by exact prefixLift 1238426
  have htrace : WordTrace (prefixWord ++ tailWord_1238426) baseStart_1238426 baseEnd_1238426 := by
    simpa [prefixWord, tailWord_1238426, baseEnd_1238426] using wordTrace_append hprefix tailTrace_1238426
  have hstable : (prefixWord ++ tailWord_1238426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238426).length < 2 ^ (prefixWord ++ tailWord_1238426).sum := by decide
  have hdescent : baseEnd_1238426 < baseStart_1238426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238503 : List Nat := [1, 1, 5, 2, 1, 3, 2, 1, 3, 3]
def baseStart_1238503 : Nat := 118140960795 + 1238503 * 2 ^ 59
def prefixEnd_1238503 : Nat := 4983230072969 + 3 ^ 40 * 1238503 * 2
def baseEnd_1238503 : Nat := 423964887356982056677823

theorem tailTrace_1238503 : CollatzResearch.WordTrace tailWord_1238503 prefixEnd_1238503 423964887356982056677823 := by
  unfold tailWord_1238503
  simp only [CollatzResearch.WordTrace]
  refine ⟨45171915432122625317584163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30114610288081750211722775 45171915432122625317584163)
  ·
    refine ⟨67757873148183937976376245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45171915432122625317584163 67757873148183937976376245)
    ·
      refine ⟨6352300607642244185285273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67757873148183937976376245 6352300607642244185285273)
      ·
        refine ⟨4764225455731683138963955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6352300607642244185285273 4764225455731683138963955)
        ·
          refine ⟨7146338183597524708445933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4764225455731683138963955 7146338183597524708445933)
          ·
            refine ⟨2679876818849071765667225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7146338183597524708445933 2679876818849071765667225)
            ·
              refine ⟨2009907614136803824250419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2679876818849071765667225 2009907614136803824250419)
              ·
                refine ⟨3014861421205205736375629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009907614136803824250419 3014861421205205736375629)
                ·
                  refine ⟨1130573032951952151140861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3014861421205205736375629 1130573032951952151140861)
                  ·
                    refine ⟨423964887356982056677823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1130573032951952151140861 423964887356982056677823)
                    ·
                      rfl

theorem cell22_1238503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_1238503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238503 prefixEnd_1238503 := by exact prefixLift 1238503
  have htrace : WordTrace (prefixWord ++ tailWord_1238503) baseStart_1238503 baseEnd_1238503 := by
    simpa [prefixWord, tailWord_1238503, baseEnd_1238503] using wordTrace_append hprefix tailTrace_1238503
  have hstable : (prefixWord ++ tailWord_1238503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238503).length < 2 ^ (prefixWord ++ tailWord_1238503).sum := by decide
  have hdescent : baseEnd_1238503 < baseStart_1238503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238561 : List Nat := [1, 2, 3, 2, 2, 2, 3, 1, 6]
def baseStart_1238561 : Nat := 118140960795 + 1238561 * 2 ^ 59
def prefixEnd_1238561 : Nat := 4983230072969 + 3 ^ 40 * 1238561 * 2
def baseEnd_1238561 : Nat := 141328247314096412909215

theorem tailTrace_1238561 : CollatzResearch.WordTrace tailWord_1238561 prefixEnd_1238561 141328247314096412909215 := by
  unfold tailWord_1238561
  simp only [CollatzResearch.WordTrace]
  refine ⟨45174030865912501223195537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30116020577275000815463691 45174030865912501223195537)
  ·
    refine ⟨33880523149434375917396653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45174030865912501223195537 33880523149434375917396653)
    ·
      refine ⟨12705196181037890969023745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33880523149434375917396653 12705196181037890969023745)
      ·
        refine ⟨9528897135778418226767809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12705196181037890969023745 9528897135778418226767809)
        ·
          refine ⟨7146672851833813670075857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9528897135778418226767809 7146672851833813670075857)
          ·
            refine ⟨5360004638875360252556893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7146672851833813670075857 5360004638875360252556893)
            ·
              refine ⟨2010001739578260094708835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5360004638875360252556893 2010001739578260094708835)
              ·
                refine ⟨3015002609367390142063253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2010001739578260094708835 3015002609367390142063253)
                ·
                  refine ⟨141328247314096412909215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3015002609367390142063253 141328247314096412909215)
                  ·
                    rfl

theorem cell22_1238561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 6].length) (baseStart_1238561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238561 prefixEnd_1238561 := by exact prefixLift 1238561
  have htrace : WordTrace (prefixWord ++ tailWord_1238561) baseStart_1238561 baseEnd_1238561 := by
    simpa [prefixWord, tailWord_1238561, baseEnd_1238561] using wordTrace_append hprefix tailTrace_1238561
  have hstable : (prefixWord ++ tailWord_1238561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238561).length < 2 ^ (prefixWord ++ tailWord_1238561).sum := by decide
  have hdescent : baseEnd_1238561 < baseStart_1238561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238591 : List Nat := [1, 1, 2, 2, 3, 3, 1, 3, 2, 4]
def baseStart_1238591 : Nat := 118140960795 + 1238591 * 2 ^ 59
def prefixEnd_1238591 : Nat := 4983230072969 + 3 ^ 40 * 1238591 * 2
def baseEnd_1238591 : Nat := 423995011555379160477553

theorem tailTrace_1238591 : CollatzResearch.WordTrace tailWord_1238591 prefixEnd_1238591 423995011555379160477553 := by
  unfold tailWord_1238591
  simp only [CollatzResearch.WordTrace]
  refine ⟨45175125055803816346787627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30116750037202544231191751 45175125055803816346787627)
  ·
    refine ⟨67762687583705724520181441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45175125055803816346787627 67762687583705724520181441)
    ·
      refine ⟨50822015687779293390136081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67762687583705724520181441 50822015687779293390136081)
      ·
        refine ⟨38116511765834470042602061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50822015687779293390136081 38116511765834470042602061)
        ·
          refine ⟨14293691912187926265975773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38116511765834470042602061 14293691912187926265975773)
          ·
            refine ⟨5360134467070472349740915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14293691912187926265975773 5360134467070472349740915)
            ·
              refine ⟨8040201700605708524611373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5360134467070472349740915 8040201700605708524611373)
              ·
                refine ⟨3015075637727140696729265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8040201700605708524611373 3015075637727140696729265)
                ·
                  refine ⟨2261306728295355522546949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3015075637727140696729265 2261306728295355522546949)
                  ·
                    refine ⟨423995011555379160477553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2261306728295355522546949 423995011555379160477553)
                    ·
                      rfl

theorem cell22_1238591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 4].length) (baseStart_1238591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238591 prefixEnd_1238591 := by exact prefixLift 1238591
  have htrace : WordTrace (prefixWord ++ tailWord_1238591) baseStart_1238591 baseEnd_1238591 := by
    simpa [prefixWord, tailWord_1238591, baseEnd_1238591] using wordTrace_append hprefix tailTrace_1238591
  have hstable : (prefixWord ++ tailWord_1238591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238591).length < 2 ^ (prefixWord ++ tailWord_1238591).sum := by decide
  have hdescent : baseEnd_1238591 < baseStart_1238591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238610 : List Nat := [3, 2, 2, 1, 2, 3, 2, 2, 2, 3]
def baseStart_1238610 : Nat := 118140960795 + 1238610 * 2 ^ 59
def prefixEnd_1238610 : Nat := 4983230072969 + 3 ^ 40 * 1238610 * 2
def baseEnd_1238610 : Nat := 424001515643669444252495

theorem tailTrace_1238610 : CollatzResearch.WordTrace tailWord_1238610 prefixEnd_1238610 424001515643669444252495 := by
  unfold tailWord_1238610
  simp only [CollatzResearch.WordTrace]
  refine ⟨11293954510683745647932321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30117212028489988394486189 11293954510683745647932321)
  ·
    refine ⟨8470465883012809235949241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11293954510683745647932321 8470465883012809235949241)
    ·
      refine ⟨6352849412259606926961931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8470465883012809235949241 6352849412259606926961931)
      ·
        refine ⟨9529274118389410390442897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6352849412259606926961931 9529274118389410390442897)
        ·
          refine ⟨7146955588792057792832173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9529274118389410390442897 7146955588792057792832173)
          ·
            refine ⟨2680108345797021672312065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7146955588792057792832173 2680108345797021672312065)
            ·
              refine ⟨2010081259347766254234049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2680108345797021672312065 2010081259347766254234049)
              ·
                refine ⟨1507560944510824690675537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2010081259347766254234049 1507560944510824690675537)
                ·
                  refine ⟨1130670708383118518006653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1507560944510824690675537 1130670708383118518006653)
                  ·
                    refine ⟨424001515643669444252495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1130670708383118518006653 424001515643669444252495)
                    ·
                      rfl

theorem cell22_1238610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_1238610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238610 prefixEnd_1238610 := by exact prefixLift 1238610
  have htrace : WordTrace (prefixWord ++ tailWord_1238610) baseStart_1238610 baseEnd_1238610 := by
    simpa [prefixWord, tailWord_1238610, baseEnd_1238610] using wordTrace_append hprefix tailTrace_1238610
  have hstable : (prefixWord ++ tailWord_1238610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238610).length < 2 ^ (prefixWord ++ tailWord_1238610).sum := by decide
  have hdescent : baseEnd_1238610 < baseStart_1238610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238681 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 3, 4]
def baseStart_1238681 : Nat := 118140960795 + 1238681 * 2 ^ 59
def prefixEnd_1238681 : Nat := 4983230072969 + 3 ^ 40 * 1238681 * 2
def baseEnd_1238681 : Nat := 424025820394648925727277

theorem tailTrace_1238681 : CollatzResearch.WordTrace tailWord_1238681 prefixEnd_1238681 424025820394648925727277 := by
  unfold tailWord_1238681
  simp only [CollatzResearch.WordTrace]
  refine ⟨45178407625477761717563897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30118938416985174478375931 45178407625477761717563897)
  ·
    refine ⟨33883805719108321288172923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45178407625477761717563897 33883805719108321288172923)
    ·
      refine ⟨50825708578662481932259385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33883805719108321288172923 50825708578662481932259385)
      ·
        refine ⟨38119281433996861449194539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50825708578662481932259385 38119281433996861449194539)
        ·
          refine ⟨57178922150995292173791809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38119281433996861449194539 57178922150995292173791809)
          ·
            refine ⟨42884191613246469130343857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57178922150995292173791809 42884191613246469130343857)
            ·
              refine ⟨32163143709934851847757893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42884191613246469130343857 32163143709934851847757893)
              ·
                refine ⟨6030589445612784721454605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32163143709934851847757893 6030589445612784721454605)
                ·
                  refine ⟨2261471042104794270545477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6030589445612784721454605 2261471042104794270545477)
                  ·
                    refine ⟨424025820394648925727277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2261471042104794270545477 424025820394648925727277)
                    ·
                      rfl

theorem cell22_1238681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 4].length) (baseStart_1238681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238681 prefixEnd_1238681 := by exact prefixLift 1238681
  have htrace : WordTrace (prefixWord ++ tailWord_1238681) baseStart_1238681 baseEnd_1238681 := by
    simpa [prefixWord, tailWord_1238681, baseEnd_1238681] using wordTrace_append hprefix tailTrace_1238681
  have hstable : (prefixWord ++ tailWord_1238681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238681).length < 2 ^ (prefixWord ++ tailWord_1238681).sum := by decide
  have hdescent : baseEnd_1238681 < baseStart_1238681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238728 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 4, 3]
def baseStart_1238728 : Nat := 118140960795 + 1238728 * 2 ^ 59
def prefixEnd_1238728 : Nat := 4983230072969 + 3 ^ 40 * 1238728 * 2
def baseEnd_1238728 : Nat := 424041909455156469802133

theorem tailTrace_1238728 : CollatzResearch.WordTrace tailWord_1238728 prefixEnd_1238728 424041909455156469802133 := by
  unfold tailWord_1238728
  simp only [CollatzResearch.WordTrace]
  refine ⟨22590060928153744372262419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30120081237538325829683225 22590060928153744372262419)
  ·
    refine ⟨33885091392230616558393629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22590060928153744372262419 33885091392230616558393629)
    ·
      refine ⟨12706909272086481209397611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33885091392230616558393629 12706909272086481209397611)
      ·
        refine ⟨19060363908129721814096417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12706909272086481209397611 19060363908129721814096417)
        ·
          refine ⟨14295272931097291360572313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19060363908129721814096417 14295272931097291360572313)
          ·
            refine ⟨10721454698322968520429235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14295272931097291360572313 10721454698322968520429235)
            ·
              refine ⟨16082182047484452780643853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10721454698322968520429235 16082182047484452780643853)
              ·
                refine ⟨6030818267806669792741445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16082182047484452780643853 6030818267806669792741445)
                ·
                  refine ⟨1130778425213750586139021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6030818267806669792741445 1130778425213750586139021)
                  ·
                    refine ⟨424041909455156469802133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1130778425213750586139021 424041909455156469802133)
                    ·
                      rfl

theorem cell22_1238728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_1238728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238728 prefixEnd_1238728 := by exact prefixLift 1238728
  have htrace : WordTrace (prefixWord ++ tailWord_1238728) baseStart_1238728 baseEnd_1238728 := by
    simpa [prefixWord, tailWord_1238728, baseEnd_1238728] using wordTrace_append hprefix tailTrace_1238728
  have hstable : (prefixWord ++ tailWord_1238728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238728).length < 2 ^ (prefixWord ++ tailWord_1238728).sum := by decide
  have hdescent : baseEnd_1238728 < baseStart_1238728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238730 : List Nat := [3, 1, 2, 1, 5, 2, 1, 1, 6]
def baseStart_1238730 : Nat := 118140960795 + 1238730 * 2 ^ 59
def prefixEnd_1238730 : Nat := 4983230072969 + 3 ^ 40 * 1238730 * 2
def baseEnd_1238730 : Nat := 141347531365343043750709

theorem tailTrace_1238730 : CollatzResearch.WordTrace tailWord_1238730 prefixEnd_1238730 141347531365343043750709 := by
  unfold tailWord_1238730
  simp only [CollatzResearch.WordTrace]
  refine ⟨11295048700575060771524411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30120129868200162057398429 11295048700575060771524411)
  ·
    refine ⟨16942573050862591157286617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11295048700575060771524411 16942573050862591157286617)
    ·
      refine ⟨12706929788146943367964963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16942573050862591157286617 12706929788146943367964963)
      ·
        refine ⟨19060394682220415051947445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12706929788146943367964963 19060394682220415051947445)
        ·
          refine ⟨1786912001458163911120073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19060394682220415051947445 1786912001458163911120073)
          ·
            refine ⟨1340184001093622933340055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1786912001458163911120073 1340184001093622933340055)
            ·
              refine ⟨2010276001640434400010083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1340184001093622933340055 2010276001640434400010083)
              ·
                refine ⟨3015414002460651600015125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2010276001640434400010083 3015414002460651600015125)
                ·
                  refine ⟨141347531365343043750709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3015414002460651600015125 141347531365343043750709)
                  ·
                    rfl

theorem cell22_1238730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_1238730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238730 prefixEnd_1238730 := by exact prefixLift 1238730
  have htrace : WordTrace (prefixWord ++ tailWord_1238730) baseStart_1238730 baseEnd_1238730 := by
    simpa [prefixWord, tailWord_1238730, baseEnd_1238730] using wordTrace_append hprefix tailTrace_1238730
  have hstable : (prefixWord ++ tailWord_1238730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238730).length < 2 ^ (prefixWord ++ tailWord_1238730).sum := by decide
  have hdescent : baseEnd_1238730 < baseStart_1238730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238745 : List Nat := [1, 2, 1, 2, 3, 4, 1, 3, 2, 3]
def baseStart_1238745 : Nat := 118140960795 + 1238745 * 2 ^ 59
def prefixEnd_1238745 : Nat := 4983230072969 + 3 ^ 40 * 1238745 * 2
def baseEnd_1238745 : Nat := 424047728902574092127081

theorem tailTrace_1238745 : CollatzResearch.WordTrace tailWord_1238745 prefixEnd_1238745 424047728902574092127081 := by
  unfold tailWord_1238745
  simp only [CollatzResearch.WordTrace]
  refine ⟨45180741897245900647893689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30120494598163933765262459 45180741897245900647893689)
  ·
    refine ⟨33885556422934425485920267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45180741897245900647893689 33885556422934425485920267)
    ·
      refine ⟨50828334634401638228880401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33885556422934425485920267 50828334634401638228880401)
      ·
        refine ⟨38121250975801228671660301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50828334634401638228880401 38121250975801228671660301)
        ·
          refine ⟨14295469115925460751872613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38121250975801228671660301 14295469115925460751872613)
          ·
            refine ⟨2680400459236023890976115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14295469115925460751872613 2680400459236023890976115)
            ·
              refine ⟨4020600688854035836464173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2680400459236023890976115 4020600688854035836464173)
              ·
                refine ⟨1507725258320263438674065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4020600688854035836464173 1507725258320263438674065)
                ·
                  refine ⟨1130793943740197579005549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1507725258320263438674065 1130793943740197579005549)
                  ·
                    refine ⟨424047728902574092127081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1130793943740197579005549 424047728902574092127081)
                    ·
                      rfl

theorem cell22_1238745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 3].length) (baseStart_1238745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238745 prefixEnd_1238745 := by exact prefixLift 1238745
  have htrace : WordTrace (prefixWord ++ tailWord_1238745) baseStart_1238745 baseEnd_1238745 := by
    simpa [prefixWord, tailWord_1238745, baseEnd_1238745] using wordTrace_append hprefix tailTrace_1238745
  have hstable : (prefixWord ++ tailWord_1238745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238745).length < 2 ^ (prefixWord ++ tailWord_1238745).sum := by decide
  have hdescent : baseEnd_1238745 < baseStart_1238745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238749 : List Nat := [1, 4, 3, 3, 1, 2, 1, 2, 1, 4]
def baseStart_1238749 : Nat := 118140960795 + 1238749 * 2 ^ 59
def prefixEnd_1238749 : Nat := 4983230072969 + 3 ^ 40 * 1238749 * 2
def baseEnd_1238749 : Nat := 424049098184319415027069

theorem tailTrace_1238749 : CollatzResearch.WordTrace tailWord_1238749 prefixEnd_1238749 424049098184319415027069 := by
  unfold tailWord_1238749
  simp only [CollatzResearch.WordTrace]
  refine ⟨45180887789231409331039301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30120591859487606220692867 45180887789231409331039301)
  ·
    refine ⟨8471416460480889249569869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45180887789231409331039301 8471416460480889249569869)
    ·
      refine ⟨3176781172680333468588701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8471416460480889249569869 3176781172680333468588701)
      ·
        refine ⟨1191292939755125050720763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3176781172680333468588701 1191292939755125050720763)
        ·
          refine ⟨1786939409632687576081145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1191292939755125050720763 1786939409632687576081145)
          ·
            refine ⟨1340204557224515682060859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1786939409632687576081145 1340204557224515682060859)
            ·
              refine ⟨2010306835836773523091289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1340204557224515682060859 2010306835836773523091289)
              ·
                refine ⟨1507730126877580142318467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2010306835836773523091289 1507730126877580142318467)
                ·
                  refine ⟨2261595190316370213477701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1507730126877580142318467 2261595190316370213477701)
                  ·
                    refine ⟨424049098184319415027069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2261595190316370213477701 424049098184319415027069)
                    ·
                      rfl

theorem cell22_1238749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_1238749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238749 prefixEnd_1238749 := by exact prefixLift 1238749
  have htrace : WordTrace (prefixWord ++ tailWord_1238749) baseStart_1238749 baseEnd_1238749 := by
    simpa [prefixWord, tailWord_1238749, baseEnd_1238749] using wordTrace_append hprefix tailTrace_1238749
  have hstable : (prefixWord ++ tailWord_1238749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238749).length < 2 ^ (prefixWord ++ tailWord_1238749).sum := by decide
  have hdescent : baseEnd_1238749 < baseStart_1238749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238760 : List Nat := [2, 1, 4, 1, 3, 2, 2, 1, 2, 4]
def baseStart_1238760 : Nat := 118140960795 + 1238760 * 2 ^ 59
def prefixEnd_1238760 : Nat := 4983230072969 + 3 ^ 40 * 1238760 * 2
def baseEnd_1238760 : Nat := 424052863709119053002035

theorem tailTrace_1238760 : CollatzResearch.WordTrace tailWord_1238760 prefixEnd_1238760 424052863709119053002035 := by
  unfold tailWord_1238760
  simp only [CollatzResearch.WordTrace]
  refine ⟨22590644496095779104844867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30120859328127705473126489 22590644496095779104844867)
  ·
    refine ⟨33885966744143668657267301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22590644496095779104844867 33885966744143668657267301)
    ·
      refine ⟨6353618764526937873237619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33885966744143668657267301 6353618764526937873237619)
      ·
        refine ⟨9530428146790406809856429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6353618764526937873237619 9530428146790406809856429)
        ·
          refine ⟨3573910555046402553696161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9530428146790406809856429 3573910555046402553696161)
          ·
            refine ⟨2680432916284801915272121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3573910555046402553696161 2680432916284801915272121)
            ·
              refine ⟨2010324687213601436454091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2680432916284801915272121 2010324687213601436454091)
              ·
                refine ⟨3015487030820402154681137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2010324687213601436454091 3015487030820402154681137)
                ·
                  refine ⟨2261615273115301616010853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3015487030820402154681137 2261615273115301616010853)
                  ·
                    refine ⟨424052863709119053002035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2261615273115301616010853 424052863709119053002035)
                    ·
                      rfl

theorem cell22_1238760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_1238760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238760 prefixEnd_1238760 := by exact prefixLift 1238760
  have htrace : WordTrace (prefixWord ++ tailWord_1238760) baseStart_1238760 baseEnd_1238760 := by
    simpa [prefixWord, tailWord_1238760, baseEnd_1238760] using wordTrace_append hprefix tailTrace_1238760
  have hstable : (prefixWord ++ tailWord_1238760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238760).length < 2 ^ (prefixWord ++ tailWord_1238760).sum := by decide
  have hdescent : baseEnd_1238760 < baseStart_1238760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238788 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_1238788 : Nat := 118140960795 + 1238788 * 2 ^ 59
def prefixEnd_1238788 : Nat := 4983230072969 + 3 ^ 40 * 1238788 * 2
def baseEnd_1238788 : Nat := 424062448681336313301949

theorem tailTrace_1238788 : CollatzResearch.WordTrace tailWord_1238788 prefixEnd_1238788 424062448681336313301949 := by
  unfold tailWord_1238788
  simp only [CollatzResearch.WordTrace]
  refine ⟨22591155118045059495854509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30121540157393412661139345 22591155118045059495854509)
  ·
    refine ⟨8471683169266897310945441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22591155118045059495854509 8471683169266897310945441)
    ·
      refine ⟨6353762376950172983209081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8471683169266897310945441 6353762376950172983209081)
      ·
        refine ⟨4765321782712629737406811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6353762376950172983209081 4765321782712629737406811)
        ·
          refine ⟨7147982674068944606110217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4765321782712629737406811 7147982674068944606110217)
          ·
            refine ⟨5360987005551708454582663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7147982674068944606110217 5360987005551708454582663)
            ·
              refine ⟨8041480508327562681873995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5360987005551708454582663 8041480508327562681873995)
              ·
                refine ⟨12062220762491344022810993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8041480508327562681873995 12062220762491344022810993)
                ·
                  refine ⟨9046665571868508017108245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12062220762491344022810993 9046665571868508017108245)
                  ·
                    refine ⟨424062448681336313301949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9046665571868508017108245 424062448681336313301949)
                    ·
                      rfl

theorem cell22_1238788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_1238788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238788 prefixEnd_1238788 := by exact prefixLift 1238788
  have htrace : WordTrace (prefixWord ++ tailWord_1238788) baseStart_1238788 baseEnd_1238788 := by
    simpa [prefixWord, tailWord_1238788, baseEnd_1238788] using wordTrace_append hprefix tailTrace_1238788
  have hstable : (prefixWord ++ tailWord_1238788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238788).length < 2 ^ (prefixWord ++ tailWord_1238788).sum := by decide
  have hdescent : baseEnd_1238788 < baseStart_1238788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238818 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_1238818 : Nat := 118140960795 + 1238818 * 2 ^ 59
def prefixEnd_1238818 : Nat := 4983230072969 + 3 ^ 40 * 1238818 * 2
def baseEnd_1238818 : Nat := 424072718294426235051857

theorem tailTrace_1238818 : CollatzResearch.WordTrace tailWord_1238818 prefixEnd_1238818 424072718294426235051857 := by
  unfold tailWord_1238818
  simp only [CollatzResearch.WordTrace]
  refine ⟨11295851106495358528825277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30122269617320956076867405 11295851106495358528825277)
  ·
    refine ⟨4235944164935759448309479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11295851106495358528825277 4235944164935759448309479)
    ·
      refine ⟨6353916247403639172464219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4235944164935759448309479 6353916247403639172464219)
      ·
        refine ⟨9530874371105458758696329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6353916247403639172464219 9530874371105458758696329)
        ·
          refine ⟨7148155778329094069022247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9530874371105458758696329 7148155778329094069022247)
          ·
            refine ⟨10722233667493641103533371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7148155778329094069022247 10722233667493641103533371)
            ·
              refine ⟨16083350501240461655300057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10722233667493641103533371 16083350501240461655300057)
              ·
                refine ⟨12062512875930346241475043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16083350501240461655300057 12062512875930346241475043)
                ·
                  refine ⟨18093769313895519362212565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12062512875930346241475043 18093769313895519362212565)
                  ·
                    refine ⟨424072718294426235051857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18093769313895519362212565 424072718294426235051857)
                    ·
                      rfl

theorem cell22_1238818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_1238818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238818 prefixEnd_1238818 := by exact prefixLift 1238818
  have htrace : WordTrace (prefixWord ++ tailWord_1238818) baseStart_1238818 baseEnd_1238818 := by
    simpa [prefixWord, tailWord_1238818, baseEnd_1238818] using wordTrace_append hprefix tailTrace_1238818
  have hstable : (prefixWord ++ tailWord_1238818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238818).length < 2 ^ (prefixWord ++ tailWord_1238818).sum := by decide
  have hdescent : baseEnd_1238818 < baseStart_1238818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238824 : List Nat := [2, 1, 5, 1, 1, 3, 2, 3, 1, 3]
def baseStart_1238824 : Nat := 118140960795 + 1238824 * 2 ^ 59
def prefixEnd_1238824 : Nat := 4983230072969 + 3 ^ 40 * 1238824 * 2
def baseEnd_1238824 : Nat := 424074772217044219401839

theorem tailTrace_1238824 : CollatzResearch.WordTrace tailWord_1238824 prefixEnd_1238824 424074772217044219401839 := by
  unfold tailWord_1238824
  simp only [CollatzResearch.WordTrace]
  refine ⟨22591811631979848570009763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30122415509306464760013017 22591811631979848570009763)
  ·
    refine ⟨33887717447969772855014645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22591811631979848570009763 33887717447969772855014645)
    ·
      refine ⟨3176973510747166205157623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33887717447969772855014645 3176973510747166205157623)
      ·
        refine ⟨4765460266120749307736435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3176973510747166205157623 4765460266120749307736435)
        ·
          refine ⟨7148190399181123961604653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4765460266120749307736435 7148190399181123961604653)
          ·
            refine ⟨2680571399692921485601745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7148190399181123961604653 2680571399692921485601745)
            ·
              refine ⟨2010428549769691114201309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2680571399692921485601745 2010428549769691114201309)
              ·
                refine ⟨753910706163634167825491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2010428549769691114201309 753910706163634167825491)
                ·
                  refine ⟨1130866059245451251738237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 753910706163634167825491 1130866059245451251738237)
                  ·
                    refine ⟨424074772217044219401839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1130866059245451251738237 424074772217044219401839)
                    ·
                      rfl

theorem cell22_1238824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_1238824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238824 prefixEnd_1238824 := by exact prefixLift 1238824
  have htrace : WordTrace (prefixWord ++ tailWord_1238824) baseStart_1238824 baseEnd_1238824 := by
    simpa [prefixWord, tailWord_1238824, baseEnd_1238824] using wordTrace_append hprefix tailTrace_1238824
  have hstable : (prefixWord ++ tailWord_1238824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238824).length < 2 ^ (prefixWord ++ tailWord_1238824).sum := by decide
  have hdescent : baseEnd_1238824 < baseStart_1238824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238837 : List Nat := [1, 3, 3, 1, 4, 2, 1, 2, 5]
def baseStart_1238837 : Nat := 118140960795 + 1238837 * 2 ^ 59
def prefixEnd_1238837 : Nat := 4983230072969 + 3 ^ 40 * 1238837 * 2
def baseEnd_1238837 : Nat := 141359740794238839608933

theorem tailTrace_1238837 : CollatzResearch.WordTrace tailWord_1238837 prefixEnd_1238837 141359740794238839608933 := by
  unfold tailWord_1238837
  simp only [CollatzResearch.WordTrace]
  refine ⟨45184097412912600360242765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30122731608608400240161843 45184097412912600360242765)
  ·
    refine ⟨16944036529842225135091037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45184097412912600360242765 16944036529842225135091037)
    ·
      refine ⟨6354013698690834425659139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16944036529842225135091037 6354013698690834425659139)
      ·
        refine ⟨9531020548036251638488709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6354013698690834425659139 9531020548036251638488709)
        ·
          refine ⟨1787066352756797182216633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9531020548036251638488709 1787066352756797182216633)
          ·
            refine ⟨1340299764567597886662475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1787066352756797182216633 1340299764567597886662475)
            ·
              refine ⟨2010449646851396829993713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1340299764567597886662475 2010449646851396829993713)
              ·
                refine ⟨1507837235138547622495285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2010449646851396829993713 1507837235138547622495285)
                ·
                  refine ⟨141359740794238839608933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1507837235138547622495285 141359740794238839608933)
                  ·
                    rfl

theorem cell22_1238837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_1238837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238837 prefixEnd_1238837 := by exact prefixLift 1238837
  have htrace : WordTrace (prefixWord ++ tailWord_1238837) baseStart_1238837 baseEnd_1238837 := by
    simpa [prefixWord, tailWord_1238837, baseEnd_1238837] using wordTrace_append hprefix tailTrace_1238837
  have hstable : (prefixWord ++ tailWord_1238837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238837).length < 2 ^ (prefixWord ++ tailWord_1238837).sum := by decide
  have hdescent : baseEnd_1238837 < baseStart_1238837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238880 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 4, 3]
def baseStart_1238880 : Nat := 118140960795 + 1238880 * 2 ^ 59
def prefixEnd_1238880 : Nat := 4983230072969 + 3 ^ 40 * 1238880 * 2
def baseEnd_1238880 : Nat := 424093942161478740001667

theorem tailTrace_1238880 : CollatzResearch.WordTrace tailWord_1238880 prefixEnd_1238880 424093942161478740001667 := by
  unfold tailWord_1238880
  simp only [CollatzResearch.WordTrace]
  refine ⟨22592832875878409352029047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30123777167837879136038729 22592832875878409352029047)
  ·
    refine ⟨33889249313817614028043571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22592832875878409352029047 33889249313817614028043571)
    ·
      refine ⟨50833873970726421042065357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33889249313817614028043571 50833873970726421042065357)
      ·
        refine ⟨19062702739022407890774509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50833873970726421042065357 19062702739022407890774509)
        ·
          refine ⟨7148513527133402959040441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19062702739022407890774509 7148513527133402959040441)
          ·
            refine ⟨5361385145350052219280331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7148513527133402959040441 5361385145350052219280331)
            ·
              refine ⟨8042077718025078328920497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5361385145350052219280331 8042077718025078328920497)
              ·
                refine ⟨6031558288518808746690373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8042077718025078328920497 6031558288518808746690373)
                ·
                  refine ⟨1130917179097276640004445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6031558288518808746690373 1130917179097276640004445)
                  ·
                    refine ⟨424093942161478740001667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1130917179097276640004445 424093942161478740001667)
                    ·
                      rfl

theorem cell22_1238880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 4, 3].length) (baseStart_1238880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238880 prefixEnd_1238880 := by exact prefixLift 1238880
  have htrace : WordTrace (prefixWord ++ tailWord_1238880) baseStart_1238880 baseEnd_1238880 := by
    simpa [prefixWord, tailWord_1238880, baseEnd_1238880] using wordTrace_append hprefix tailTrace_1238880
  have hstable : (prefixWord ++ tailWord_1238880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238880).length < 2 ^ (prefixWord ++ tailWord_1238880).sum := by decide
  have hdescent : baseEnd_1238880 < baseStart_1238880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238893 : List Nat := [1, 5, 1, 1, 1, 1, 12]
def baseStart_1238893 : Nat := 118140960795 + 1238893 * 2 ^ 59
def prefixEnd_1238893 : Nat := 4983230072969 + 3 ^ 40 * 1238893 * 2
def baseEnd_1238893 : Nat := 15707347863968557015801

theorem tailTrace_1238893 : CollatzResearch.WordTrace tailWord_1238893 prefixEnd_1238893 15707347863968557015801 := by
  unfold tailWord_1238893
  simp only [CollatzResearch.WordTrace]
  refine ⟨45186139900709721924281333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30124093267139814616187555 45186139900709721924281333)
  ·
    refine ⟨4236200615691536430401375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45186139900709721924281333 4236200615691536430401375)
    ·
      refine ⟨6354300923537304645602063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4236200615691536430401375 6354300923537304645602063)
      ·
        refine ⟨9531451385305956968403095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6354300923537304645602063 9531451385305956968403095)
        ·
          refine ⟨14297177077958935452604643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9531451385305956968403095 14297177077958935452604643)
          ·
            refine ⟨21445765616938403178906965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14297177077958935452604643 21445765616938403178906965)
            ·
              refine ⟨15707347863968557015801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 21445765616938403178906965 15707347863968557015801)
              ·
                rfl

theorem cell22_1238893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 12].length) (baseStart_1238893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1238893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1238893 prefixEnd_1238893 := by exact prefixLift 1238893
  have htrace : WordTrace (prefixWord ++ tailWord_1238893) baseStart_1238893 baseEnd_1238893 := by
    simpa [prefixWord, tailWord_1238893, baseEnd_1238893] using wordTrace_append hprefix tailTrace_1238893
  have hstable : (prefixWord ++ tailWord_1238893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238893).length < 2 ^ (prefixWord ++ tailWord_1238893).sum := by decide
  have hdescent : baseEnd_1238893 < baseStart_1238893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239032 : List Nat := [2, 1, 2, 1, 1, 3, 2, 5, 2, 3]
def baseStart_1239032 : Nat := 118140960795 + 1239032 * 2 ^ 59
def prefixEnd_1239032 : Nat := 4983230072969 + 3 ^ 40 * 1239032 * 2
def baseEnd_1239032 : Nat := 424145974867801010201201

theorem tailTrace_1239032 : CollatzResearch.WordTrace tailWord_1239032 prefixEnd_1239032 424145974867801010201201 := by
  unfold tailWord_1239032
  simp only [CollatzResearch.WordTrace]
  refine ⟨22595604823603074331795675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30127473098137432442394233 22595604823603074331795675)
  ·
    refine ⟨33893407235404611497693513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22595604823603074331795675 33893407235404611497693513)
    ·
      refine ⟨25420055426553458623270135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33893407235404611497693513 25420055426553458623270135)
      ·
        refine ⟨38130083139830187934905203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25420055426553458623270135 38130083139830187934905203)
        ·
          refine ⟨57195124709745281902357805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38130083139830187934905203 57195124709745281902357805)
          ·
            refine ⟨21448171766154480713384177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57195124709745281902357805 21448171766154480713384177)
            ·
              refine ⟨16086128824615860535038133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21448171766154480713384177 16086128824615860535038133)
              ·
                refine ⟨1508074577307736925159825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16086128824615860535038133 1508074577307736925159825)
                ·
                  refine ⟨1131055932980802693869869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1508074577307736925159825 1131055932980802693869869)
                  ·
                    refine ⟨424145974867801010201201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1131055932980802693869869 424145974867801010201201)
                    ·
                      rfl

theorem cell22_1239032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_1239032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239032 prefixEnd_1239032 := by exact prefixLift 1239032
  have htrace : WordTrace (prefixWord ++ tailWord_1239032) baseStart_1239032 baseEnd_1239032 := by
    simpa [prefixWord, tailWord_1239032, baseEnd_1239032] using wordTrace_append hprefix tailTrace_1239032
  have hstable : (prefixWord ++ tailWord_1239032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239032).length < 2 ^ (prefixWord ++ tailWord_1239032).sum := by decide
  have hdescent : baseEnd_1239032 < baseStart_1239032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239045 : List Nat := [1, 3, 1, 1, 2, 5, 1, 8]
def baseStart_1239045 : Nat := 118140960795 + 1239045 * 2 ^ 59
def prefixEnd_1239045 : Nat := 4983230072969 + 3 ^ 40 * 1239045 * 2
def baseEnd_1239045 : Nat := 47127825003719256625129

theorem tailTrace_1239045 : CollatzResearch.WordTrace tailWord_1239045 prefixEnd_1239045 47127825003719256625129 := by
  unfold tailWord_1239045
  simp only [CollatzResearch.WordTrace]
  refine ⟨45191683796159051883814589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30127789197439367922543059 45191683796159051883814589)
  ·
    refine ⟨16946881423559644456430471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45191683796159051883814589 16946881423559644456430471)
    ·
      refine ⟨25420322135339466684645707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16946881423559644456430471 25420322135339466684645707)
      ·
        refine ⟨38130483203009200026968561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25420322135339466684645707 38130483203009200026968561)
        ·
          refine ⟨28597862402256900020226421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38130483203009200026968561 28597862402256900020226421)
          ·
            refine ⟨2681049600211584376896227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28597862402256900020226421 2681049600211584376896227)
            ·
              refine ⟨4021574400317376565344341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2681049600211584376896227 4021574400317376565344341)
              ·
                refine ⟨47127825003719256625129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4021574400317376565344341 47127825003719256625129)
                ·
                  rfl

theorem cell22_1239045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 8].length) (baseStart_1239045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239045 prefixEnd_1239045 := by exact prefixLift 1239045
  have htrace : WordTrace (prefixWord ++ tailWord_1239045) baseStart_1239045 baseEnd_1239045 := by
    simpa [prefixWord, tailWord_1239045, baseEnd_1239045] using wordTrace_append hprefix tailTrace_1239045
  have hstable : (prefixWord ++ tailWord_1239045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239045).length < 2 ^ (prefixWord ++ tailWord_1239045).sum := by decide
  have hdescent : baseEnd_1239045 < baseStart_1239045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239075 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 2, 6]
def baseStart_1239075 : Nat := 118140960795 + 1239075 * 2 ^ 59
def prefixEnd_1239075 : Nat := 4983230072969 + 3 ^ 40 * 1239075 * 2
def baseEnd_1239075 : Nat := 424160694646563231376069

theorem tailTrace_1239075 : CollatzResearch.WordTrace tailWord_1239075 prefixEnd_1239075 424160694646563231376069 := by
  unfold tailWord_1239075
  simp only [CollatzResearch.WordTrace]
  refine ⟨45192777986050367007406679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30128518657366911338271119 45192777986050367007406679)
  ·
    refine ⟨67789166979075550511110019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45192777986050367007406679 67789166979075550511110019)
    ·
      refine ⟨101683750468613325766665029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67789166979075550511110019 101683750468613325766665029)
      ·
        refine ⟨19065703212864998581249693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101683750468613325766665029 19065703212864998581249693)
        ·
          refine ⟨7149638704824374467968635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19065703212864998581249693 7149638704824374467968635)
          ·
            refine ⟨10724458057236561701952953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7149638704824374467968635 10724458057236561701952953)
            ·
              refine ⟨8043343542927421276464715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10724458057236561701952953 8043343542927421276464715)
              ·
                refine ⟨12065015314391131914697073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8043343542927421276464715 12065015314391131914697073)
                ·
                  refine ⟨9048761485793348936022805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12065015314391131914697073 9048761485793348936022805)
                  ·
                    refine ⟨424160694646563231376069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9048761485793348936022805 424160694646563231376069)
                    ·
                      rfl

theorem cell22_1239075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 6].length) (baseStart_1239075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239075 prefixEnd_1239075 := by exact prefixLift 1239075
  have htrace : WordTrace (prefixWord ++ tailWord_1239075) baseStart_1239075 baseEnd_1239075 := by
    simpa [prefixWord, tailWord_1239075, baseEnd_1239075] using wordTrace_append hprefix tailTrace_1239075
  have hstable : (prefixWord ++ tailWord_1239075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239075).length < 2 ^ (prefixWord ++ tailWord_1239075).sum := by decide
  have hdescent : baseEnd_1239075 < baseStart_1239075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239079 : List Nat := [1, 1, 7, 1, 2, 1, 2, 7]
def baseStart_1239079 : Nat := 118140960795 + 1239079 * 2 ^ 59
def prefixEnd_1239079 : Nat := 4983230072969 + 3 ^ 40 * 1239079 * 2
def baseEnd_1239079 : Nat := 47129118214256506030673

theorem tailTrace_1239079 : CollatzResearch.WordTrace tailWord_1239079 prefixEnd_1239079 47129118214256506030673 := by
  unfold tailWord_1239079
  simp only [CollatzResearch.WordTrace]
  refine ⟨45192923878035875690552291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30128615918690583793701527 45192923878035875690552291)
  ·
    refine ⟨67789385817053813535828437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45192923878035875690552291 67789385817053813535828437)
    ·
      refine ⟨1588813730087198754745979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 67789385817053813535828437 1588813730087198754745979)
      ·
        refine ⟨2383220595130798132118969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1588813730087198754745979 2383220595130798132118969)
        ·
          refine ⟨1787415446348098599089227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2383220595130798132118969 1787415446348098599089227)
          ·
            refine ⟨2681123169522147898633841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1787415446348098599089227 2681123169522147898633841)
            ·
              refine ⟨2010842377141610923975381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2681123169522147898633841 2010842377141610923975381)
              ·
                refine ⟨47129118214256506030673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2010842377141610923975381 47129118214256506030673)
                ·
                  rfl

theorem cell22_1239079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 7].length) (baseStart_1239079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239079 prefixEnd_1239079 := by exact prefixLift 1239079
  have htrace : WordTrace (prefixWord ++ tailWord_1239079) baseStart_1239079 baseEnd_1239079 := by
    simpa [prefixWord, tailWord_1239079, baseEnd_1239079] using wordTrace_append hprefix tailTrace_1239079
  have hstable : (prefixWord ++ tailWord_1239079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239079).length < 2 ^ (prefixWord ++ tailWord_1239079).sum := by decide
  have hdescent : baseEnd_1239079 < baseStart_1239079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239094 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_1239094 : Nat := 118140960795 + 1239094 * 2 ^ 59
def prefixEnd_1239094 : Nat := 4983230072969 + 3 ^ 40 * 1239094 * 2
def baseEnd_1239094 : Nat := 424167198734853515151011

theorem tailTrace_1239094 : CollatzResearch.WordTrace tailWord_1239094 prefixEnd_1239094 424167198734853515151011 := by
  unfold tailWord_1239094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2824591935811345828271771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30128980648654355501565557 2824591935811345828271771)
  ·
    refine ⟨4236887903717018742407657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2824591935811345828271771 4236887903717018742407657)
    ·
      refine ⟨3177665927787764056805743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4236887903717018742407657 3177665927787764056805743)
      ·
        refine ⟨4766498891681646085208615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3177665927787764056805743 4766498891681646085208615)
        ·
          refine ⟨7149748337522469127812923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4766498891681646085208615 7149748337522469127812923)
          ·
            refine ⟨10724622506283703691719385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7149748337522469127812923 10724622506283703691719385)
            ·
              refine ⟨8043466879712777768789539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10724622506283703691719385 8043466879712777768789539)
              ·
                refine ⟨12065200319569166653184309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8043466879712777768789539 12065200319569166653184309)
                ·
                  refine ⟨1131112529959609373736029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12065200319569166653184309 1131112529959609373736029)
                  ·
                    refine ⟨424167198734853515151011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1131112529959609373736029 424167198734853515151011)
                    ·
                      rfl

theorem cell22_1239094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_1239094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239094 prefixEnd_1239094 := by exact prefixLift 1239094
  have htrace : WordTrace (prefixWord ++ tailWord_1239094) baseStart_1239094 baseEnd_1239094 := by
    simpa [prefixWord, tailWord_1239094, baseEnd_1239094] using wordTrace_append hprefix tailTrace_1239094
  have hstable : (prefixWord ++ tailWord_1239094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239094).length < 2 ^ (prefixWord ++ tailWord_1239094).sum := by decide
  have hdescent : baseEnd_1239094 < baseStart_1239094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239128 : List Nat := [2, 1, 2, 2, 1, 6, 2, 2, 1, 3]
def baseStart_1239128 : Nat := 118140960795 + 1239128 * 2 ^ 59
def prefixEnd_1239128 : Nat := 4983230072969 + 3 ^ 40 * 1239128 * 2
def baseEnd_1239128 : Nat := 424178837629688759800907

theorem tailTrace_1239128 : CollatzResearch.WordTrace tailWord_1239128 prefixEnd_1239128 424178837629688759800907 := by
  unfold tailWord_1239128
  simp only [CollatzResearch.WordTrace]
  refine ⟨22597355527429178529543019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30129807369905571372724025 22597355527429178529543019)
  ·
    refine ⟨33896033291143767794314529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22597355527429178529543019 33896033291143767794314529)
    ·
      refine ⟨25422024968357825845735897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33896033291143767794314529 25422024968357825845735897)
      ·
        refine ⟨19066518726268369384301923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25422024968357825845735897 19066518726268369384301923)
        ·
          refine ⟨28599778089402554076452885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19066518726268369384301923 28599778089402554076452885)
          ·
            refine ⟨1340614597940744722333729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28599778089402554076452885 1340614597940744722333729)
            ·
              refine ⟨1005460948455558541750297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1340614597940744722333729 1005460948455558541750297)
              ·
                refine ⟨754095711341668906312723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1005460948455558541750297 754095711341668906312723)
                ·
                  refine ⟨1131143567012503359469085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754095711341668906312723 1131143567012503359469085)
                  ·
                    refine ⟨424178837629688759800907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1131143567012503359469085 424178837629688759800907)
                    ·
                      rfl

theorem cell22_1239128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 1, 3].length) (baseStart_1239128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239128 prefixEnd_1239128 := by exact prefixLift 1239128
  have htrace : WordTrace (prefixWord ++ tailWord_1239128) baseStart_1239128 baseEnd_1239128 := by
    simpa [prefixWord, tailWord_1239128, baseEnd_1239128] using wordTrace_append hprefix tailTrace_1239128
  have hstable : (prefixWord ++ tailWord_1239128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239128).length < 2 ^ (prefixWord ++ tailWord_1239128).sum := by decide
  have hdescent : baseEnd_1239128 < baseStart_1239128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239152 : List Nat := [2, 1, 1, 1, 5, 3, 1, 2, 6]
def baseStart_1239152 : Nat := 118140960795 + 1239152 * 2 ^ 59
def prefixEnd_1239152 : Nat := 4983230072969 + 3 ^ 40 * 1239152 * 2
def baseEnd_1239152 : Nat := 141395684440053565733611

theorem tailTrace_1239152 : CollatzResearch.WordTrace tailWord_1239152 prefixEnd_1239152 141395684440053565733611 := by
  unfold tailWord_1239152
  simp only [CollatzResearch.WordTrace]
  refine ⟨22597793203385704578979855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30130390937847606105306473 22597793203385704578979855)
  ·
    refine ⟨33896689805078556868469783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22597793203385704578979855 33896689805078556868469783)
    ·
      refine ⟨50845034707617835302704675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33896689805078556868469783 50845034707617835302704675)
      ·
        refine ⟨76267552061426752954057013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50845034707617835302704675 76267552061426752954057013)
        ·
          refine ⟨7150083005758758089442845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76267552061426752954057013 7150083005758758089442845)
          ·
            refine ⟨2681281127159534283541067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7150083005758758089442845 2681281127159534283541067)
            ·
              refine ⟨4021921690739301425311601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2681281127159534283541067 4021921690739301425311601)
              ·
                refine ⟨3016441268054476068983701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4021921690739301425311601 3016441268054476068983701)
                ·
                  refine ⟨141395684440053565733611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3016441268054476068983701 141395684440053565733611)
                  ·
                    rfl

theorem cell22_1239152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 6].length) (baseStart_1239152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239152 prefixEnd_1239152 := by exact prefixLift 1239152
  have htrace : WordTrace (prefixWord ++ tailWord_1239152) baseStart_1239152 baseEnd_1239152 := by
    simpa [prefixWord, tailWord_1239152, baseEnd_1239152] using wordTrace_append hprefix tailTrace_1239152
  have hstable : (prefixWord ++ tailWord_1239152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239152).length < 2 ^ (prefixWord ++ tailWord_1239152).sum := by decide
  have hdescent : baseEnd_1239152 < baseStart_1239152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239171 : List Nat := [1, 1, 1, 3, 3, 5, 2, 1, 1, 4]
def baseStart_1239171 : Nat := 118140960795 + 1239171 * 2 ^ 59
def prefixEnd_1239171 : Nat := 4983230072969 + 3 ^ 40 * 1239171 * 2
def baseEnd_1239171 : Nat := 424193557408450980975775

theorem tailTrace_1239171 : CollatzResearch.WordTrace tailWord_1239171 prefixEnd_1239171 424193557408450980975775 := by
  unfold tailWord_1239171
  simp only [CollatzResearch.WordTrace]
  refine ⟨45196279393702575402901367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30130852929135050268600911 45196279393702575402901367)
  ·
    refine ⟨67794419090553863104352051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45196279393702575402901367 67794419090553863104352051)
    ·
      refine ⟨101691628635830794656528077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67794419090553863104352051 101691628635830794656528077)
      ·
        refine ⟨38134360738436547996198029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101691628635830794656528077 38134360738436547996198029)
        ·
          refine ⟨14300385276913705498574261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38134360738436547996198029 14300385276913705498574261)
          ·
            refine ⟨1340661119710659890491337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14300385276913705498574261 1340661119710659890491337)
            ·
              refine ⟨1005495839782994917868503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1340661119710659890491337 1005495839782994917868503)
              ·
                refine ⟨1508243759674492376802755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1005495839782994917868503 1508243759674492376802755)
                ·
                  refine ⟨2262365639511738565204133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508243759674492376802755 2262365639511738565204133)
                  ·
                    refine ⟨424193557408450980975775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2262365639511738565204133 424193557408450980975775)
                    ·
                      rfl

theorem cell22_1239171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 1, 4].length) (baseStart_1239171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239171 prefixEnd_1239171 := by exact prefixLift 1239171
  have htrace : WordTrace (prefixWord ++ tailWord_1239171) baseStart_1239171 baseEnd_1239171 := by
    simpa [prefixWord, tailWord_1239171, baseEnd_1239171] using wordTrace_append hprefix tailTrace_1239171
  have hstable : (prefixWord ++ tailWord_1239171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239171).length < 2 ^ (prefixWord ++ tailWord_1239171).sum := by decide
  have hdescent : baseEnd_1239171 < baseStart_1239171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239242 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 7]
def baseStart_1239242 : Nat := 118140960795 + 1239242 * 2 ^ 59
def prefixEnd_1239242 : Nat := 4983230072969 + 3 ^ 40 * 1239242 * 2
def baseEnd_1239242 : Nat := 141405954053143487483519

theorem tailTrace_1239242 : CollatzResearch.WordTrace tailWord_1239242 prefixEnd_1239242 141405954053143487483519 := by
  unfold tailWord_1239242
  simp only [CollatzResearch.WordTrace]
  refine ⟨11299717244111338632183995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30132579317630236352490653 11299717244111338632183995)
  ·
    refine ⟨16949575866167007948275993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11299717244111338632183995 16949575866167007948275993)
    ·
      refine ⟨12712181899625255961206995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16949575866167007948275993 12712181899625255961206995)
      ·
        refine ⟨19068272849437883941810493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12712181899625255961206995 19068272849437883941810493)
        ·
          refine ⟨7150602318539206478178935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19068272849437883941810493 7150602318539206478178935)
          ·
            refine ⟨10725903477808809717268403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7150602318539206478178935 10725903477808809717268403)
            ·
              refine ⟨16088855216713214575902605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10725903477808809717268403 16088855216713214575902605)
              ·
                refine ⟨6033320706267455465963477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16088855216713214575902605 6033320706267455465963477)
                ·
                  refine ⟨141405954053143487483519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6033320706267455465963477 141405954053143487483519)
                  ·
                    rfl

theorem cell22_1239242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_1239242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239242 prefixEnd_1239242 := by exact prefixLift 1239242
  have htrace : WordTrace (prefixWord ++ tailWord_1239242) baseStart_1239242 baseEnd_1239242 := by
    simpa [prefixWord, tailWord_1239242, baseEnd_1239242] using wordTrace_append hprefix tailTrace_1239242
  have hstable : (prefixWord ++ tailWord_1239242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239242).length < 2 ^ (prefixWord ++ tailWord_1239242).sum := by decide
  have hdescent : baseEnd_1239242 < baseStart_1239242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239246 : List Nat := [4, 1, 1, 1, 4, 1, 3, 1, 3, 3]
def baseStart_1239246 : Nat := 118140960795 + 1239246 * 2 ^ 59
def prefixEnd_1239246 : Nat := 4983230072969 + 3 ^ 40 * 1239246 * 2
def baseEnd_1239246 : Nat := 424219231441175785350545

theorem tailTrace_1239246 : CollatzResearch.WordTrace tailWord_1239246 prefixEnd_1239246 424219231441175785350545 := by
  unfold tailWord_1239246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5649876858553857901485199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30132676578953908807921061 5649876858553857901485199)
  ·
    refine ⟨8474815287830786852227799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5649876858553857901485199 8474815287830786852227799)
    ·
      refine ⟨12712222931746180278341699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8474815287830786852227799 12712222931746180278341699)
      ·
        refine ⟨19068334397619270417512549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12712222931746180278341699 19068334397619270417512549)
        ·
          refine ⟨3575312699553613203283603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19068334397619270417512549 3575312699553613203283603)
          ·
            refine ⟨5362969049330419804925405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3575312699553613203283603 5362969049330419804925405)
            ·
              refine ⟨2011113393498907426847027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5362969049330419804925405 2011113393498907426847027)
              ·
                refine ⟨3016670090248361140270541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2011113393498907426847027 3016670090248361140270541)
                ·
                  refine ⟨1131251283843135427601453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3016670090248361140270541 1131251283843135427601453)
                  ·
                    refine ⟨424219231441175785350545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1131251283843135427601453 424219231441175785350545)
                    ·
                      rfl

theorem cell22_1239246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_1239246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239246 prefixEnd_1239246 := by exact prefixLift 1239246
  have htrace : WordTrace (prefixWord ++ tailWord_1239246) baseStart_1239246 baseEnd_1239246 := by
    simpa [prefixWord, tailWord_1239246, baseEnd_1239246] using wordTrace_append hprefix tailTrace_1239246
  have hstable : (prefixWord ++ tailWord_1239246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239246).length < 2 ^ (prefixWord ++ tailWord_1239246).sum := by decide
  have hdescent : baseEnd_1239246 < baseStart_1239246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239257 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 2, 5]
def baseStart_1239257 : Nat := 118140960795 + 1239257 * 2 ^ 59
def prefixEnd_1239257 : Nat := 4983230072969 + 3 ^ 40 * 1239257 * 2
def baseEnd_1239257 : Nat := 424222996965975423325511

theorem tailTrace_1239257 : CollatzResearch.WordTrace tailWord_1239257 prefixEnd_1239257 424222996965975423325511 := by
  unfold tailWord_1239257
  simp only [CollatzResearch.WordTrace]
  refine ⟨45199416071391012090532025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30132944047594008060354683 45199416071391012090532025)
  ·
    refine ⟨33899562053543259067899019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45199416071391012090532025 33899562053543259067899019)
    ·
      refine ⟨50849343080314888601848529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33899562053543259067899019 50849343080314888601848529)
      ·
        refine ⟨38137007310236166451386397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50849343080314888601848529 38137007310236166451386397)
        ·
          refine ⟨14301377741338562419269899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38137007310236166451386397 14301377741338562419269899)
          ·
            refine ⟨21452066612007843628904849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14301377741338562419269899 21452066612007843628904849)
            ·
              refine ⟨16089049959005882721678637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21452066612007843628904849 16089049959005882721678637)
              ·
                refine ⟨6033393734627206020629489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16089049959005882721678637 6033393734627206020629489)
                ·
                  refine ⟨4525045300970404515472117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6033393734627206020629489 4525045300970404515472117)
                  ·
                    refine ⟨424222996965975423325511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4525045300970404515472117 424222996965975423325511)
                    ·
                      rfl

theorem cell22_1239257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_1239257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239257 prefixEnd_1239257 := by exact prefixLift 1239257
  have htrace : WordTrace (prefixWord ++ tailWord_1239257) baseStart_1239257 baseEnd_1239257 := by
    simpa [prefixWord, tailWord_1239257, baseEnd_1239257] using wordTrace_append hprefix tailTrace_1239257
  have hstable : (prefixWord ++ tailWord_1239257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239257).length < 2 ^ (prefixWord ++ tailWord_1239257).sum := by decide
  have hdescent : baseEnd_1239257 < baseStart_1239257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239319 : List Nat := [1, 1, 3, 4, 1, 2, 1, 3, 1, 5]
def baseStart_1239319 : Nat := 118140960795 + 1239319 * 2 ^ 59
def prefixEnd_1239319 : Nat := 4983230072969 + 3 ^ 40 * 1239319 * 2
def baseEnd_1239319 : Nat := 424244220833027928275321

theorem tailTrace_1239319 : CollatzResearch.WordTrace tailWord_1239319 prefixEnd_1239319 424244220833027928275321 := by
  unfold tailWord_1239319
  simp only [CollatzResearch.WordTrace]
  refine ⟨45201677397166396679289011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30134451598110931119526007 45201677397166396679289011)
  ·
    refine ⟨67802516095749595018933517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45201677397166396679289011 67802516095749595018933517)
    ·
      refine ⟨25425943535906098132100069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67802516095749595018933517 25425943535906098132100069)
      ·
        refine ⟨4767364412982393399768763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25425943535906098132100069 4767364412982393399768763)
        ·
          refine ⟨7151046619473590099653145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4767364412982393399768763 7151046619473590099653145)
          ·
            refine ⟨5363284964605192574739859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7151046619473590099653145 5363284964605192574739859)
            ·
              refine ⟨8044927446907788862109789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5363284964605192574739859 8044927446907788862109789)
              ·
                refine ⟨3016847792590420823291171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8044927446907788862109789 3016847792590420823291171)
                ·
                  refine ⟨4525271688885631234936757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3016847792590420823291171 4525271688885631234936757)
                  ·
                    refine ⟨424244220833027928275321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4525271688885631234936757 424244220833027928275321)
                    ·
                      rfl

theorem cell22_1239319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_1239319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239319 prefixEnd_1239319 := by exact prefixLift 1239319
  have htrace : WordTrace (prefixWord ++ tailWord_1239319) baseStart_1239319 baseEnd_1239319 := by
    simpa [prefixWord, tailWord_1239319, baseEnd_1239319] using wordTrace_append hprefix tailTrace_1239319
  have hstable : (prefixWord ++ tailWord_1239319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239319).length < 2 ^ (prefixWord ++ tailWord_1239319).sum := by decide
  have hdescent : baseEnd_1239319 < baseStart_1239319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239353 : List Nat := [1, 2, 1, 6, 1, 1, 3, 2, 2, 3]
def baseStart_1239353 : Nat := 118140960795 + 1239353 * 2 ^ 59
def prefixEnd_1239353 : Nat := 4983230072969 + 3 ^ 40 * 1239353 * 2
def baseEnd_1239353 : Nat := 424255859727863172925217

theorem tailTrace_1239353 : CollatzResearch.WordTrace tailWord_1239353 prefixEnd_1239353 424255859727863172925217 := by
  unfold tailWord_1239353
  simp only [CollatzResearch.WordTrace]
  refine ⟨45202917479043220486026713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30135278319362146990684475 45202917479043220486026713)
  ·
    refine ⟨33902188109282415364520035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45202917479043220486026713 33902188109282415364520035)
    ·
      refine ⟨50853282163923623046780053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33902188109282415364520035 50853282163923623046780053)
      ·
        refine ⟨2383747601433919830317815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50853282163923623046780053 2383747601433919830317815)
        ·
          refine ⟨3575621402150879745476723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2383747601433919830317815 3575621402150879745476723)
          ·
            refine ⟨5363432103226319618215085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3575621402150879745476723 5363432103226319618215085)
            ·
              refine ⟨2011287038709869856830657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5363432103226319618215085 2011287038709869856830657)
              ·
                refine ⟨1508465279032402392622993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2011287038709869856830657 1508465279032402392622993)
                ·
                  refine ⟨1131348959274301794467245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1508465279032402392622993 1131348959274301794467245)
                  ·
                    refine ⟨424255859727863172925217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1131348959274301794467245 424255859727863172925217)
                    ·
                      rfl

theorem cell22_1239353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 3].length) (baseStart_1239353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239353 prefixEnd_1239353 := by exact prefixLift 1239353
  have htrace : WordTrace (prefixWord ++ tailWord_1239353) baseStart_1239353 baseEnd_1239353 := by
    simpa [prefixWord, tailWord_1239353, baseEnd_1239353] using wordTrace_append hprefix tailTrace_1239353
  have hstable : (prefixWord ++ tailWord_1239353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239353).length < 2 ^ (prefixWord ++ tailWord_1239353).sum := by decide
  have hdescent : baseEnd_1239353 < baseStart_1239353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239473 : List Nat := [1, 2, 2, 4, 1, 3, 1, 4, 4]
def baseStart_1239473 : Nat := 118140960795 + 1239473 * 2 ^ 59
def prefixEnd_1239473 : Nat := 4983230072969 + 3 ^ 40 * 1239473 * 2
def baseEnd_1239473 : Nat := 141432312726740953308283

theorem tailTrace_1239473 : CollatzResearch.WordTrace tailWord_1239473 prefixEnd_1239473 141432312726740953308283 := by
  unfold tailWord_1239473
  simp only [CollatzResearch.WordTrace]
  refine ⟨45207294238608480980395073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30138196159072320653596715 45207294238608480980395073)
  ·
    refine ⟨33905470678956360735296305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45207294238608480980395073 33905470678956360735296305)
    ·
      refine ⟨25429103009217270551472229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33905470678956360735296305 25429103009217270551472229)
      ·
        refine ⟨4767956814228238228401043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25429103009217270551472229 4767956814228238228401043)
        ·
          refine ⟨7151935221342357342601565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4767956814228238228401043 7151935221342357342601565)
          ·
            refine ⟨2681975708003384003475587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7151935221342357342601565 2681975708003384003475587)
            ·
              refine ⟨4022963562005076005213381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2681975708003384003475587 4022963562005076005213381)
              ·
                refine ⟨754305667875951750977509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4022963562005076005213381 754305667875951750977509)
                ·
                  refine ⟨141432312726740953308283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 754305667875951750977509 141432312726740953308283)
                  ·
                    rfl

theorem cell22_1239473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 4].length) (baseStart_1239473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239473 prefixEnd_1239473 := by exact prefixLift 1239473
  have htrace : WordTrace (prefixWord ++ tailWord_1239473) baseStart_1239473 baseEnd_1239473 := by
    simpa [prefixWord, tailWord_1239473, baseEnd_1239473] using wordTrace_append hprefix tailTrace_1239473
  have hstable : (prefixWord ++ tailWord_1239473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239473).length < 2 ^ (prefixWord ++ tailWord_1239473).sum := by decide
  have hdescent : baseEnd_1239473 < baseStart_1239473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239486 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_1239486 : Nat := 118140960795 + 1239486 * 2 ^ 59
def prefixEnd_1239486 : Nat := 4983230072969 + 3 ^ 40 * 1239486 * 2
def baseEnd_1239486 : Nat := 424301388345895159349809

theorem tailTrace_1239486 : CollatzResearch.WordTrace tailWord_1239486 prefixEnd_1239486 424301388345895159349809 := by
  unfold tailWord_1239486
  simp only [CollatzResearch.WordTrace]
  refine ⟨5650971048445173025077289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30138512258374256133745541 5650971048445173025077289)
  ·
    refine ⟨4238228286333879768807967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5650971048445173025077289 4238228286333879768807967)
    ·
      refine ⟨6357342429500819653211951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4238228286333879768807967 6357342429500819653211951)
      ·
        refine ⟨9536013644251229479817927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6357342429500819653211951 9536013644251229479817927)
        ·
          refine ⟨14304020466376844219726891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9536013644251229479817927 14304020466376844219726891)
          ·
            refine ⟨21456030699565266329590337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14304020466376844219726891 21456030699565266329590337)
            ·
              refine ⟨16092023024673949747192753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21456030699565266329590337 16092023024673949747192753)
              ·
                refine ⟨12069017268505462310394565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16092023024673949747192753 12069017268505462310394565)
                ·
                  refine ⟨2262940737844774183198981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12069017268505462310394565 2262940737844774183198981)
                  ·
                    refine ⟨424301388345895159349809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2262940737844774183198981 424301388345895159349809)
                    ·
                      rfl

theorem cell22_1239486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_1239486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239486 prefixEnd_1239486 := by exact prefixLift 1239486
  have htrace : WordTrace (prefixWord ++ tailWord_1239486) baseStart_1239486 baseEnd_1239486 := by
    simpa [prefixWord, tailWord_1239486, baseEnd_1239486] using wordTrace_append hprefix tailTrace_1239486
  have hstable : (prefixWord ++ tailWord_1239486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239486).length < 2 ^ (prefixWord ++ tailWord_1239486).sum := by decide
  have hdescent : baseEnd_1239486 < baseStart_1239486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239522 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1239522 : Nat := 118140960795 + 1239522 * 2 ^ 59
def prefixEnd_1239522 : Nat := 4983230072969 + 3 ^ 40 * 1239522 * 2
def baseEnd_1239522 : Nat := 424313711881603065449699

theorem tailTrace_1239522 : CollatzResearch.WordTrace tailWord_1239522 prefixEnd_1239522 424313711881603065449699 := by
  unfold tailWord_1239522
  simp only [CollatzResearch.WordTrace]
  refine ⟨11302270353857740587232205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30139387610287308232619213 11302270353857740587232205)
  ·
    refine ⟨4238351382696652720212077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11302270353857740587232205 4238351382696652720212077)
    ·
      refine ⟨1589381768511244770079529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4238351382696652720212077 1589381768511244770079529)
      ·
        refine ⟨1192036326383433577559647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1589381768511244770079529 1192036326383433577559647)
        ·
          refine ⟨1788054489575150366339471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1192036326383433577559647 1788054489575150366339471)
          ·
            refine ⟨2682081734362725549509207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1788054489575150366339471 2682081734362725549509207)
            ·
              refine ⟨4023122601544088324263811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2682081734362725549509207 4023122601544088324263811)
              ·
                refine ⟨6034683902316132486395717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4023122601544088324263811 6034683902316132486395717)
                ·
                  refine ⟨1131503231684274841199197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6034683902316132486395717 1131503231684274841199197)
                  ·
                    refine ⟨424313711881603065449699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1131503231684274841199197 424313711881603065449699)
                    ·
                      rfl

theorem cell22_1239522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1239522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239522 prefixEnd_1239522 := by exact prefixLift 1239522
  have htrace : WordTrace (prefixWord ++ tailWord_1239522) baseStart_1239522 baseEnd_1239522 := by
    simpa [prefixWord, tailWord_1239522, baseEnd_1239522] using wordTrace_append hprefix tailTrace_1239522
  have hstable : (prefixWord ++ tailWord_1239522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239522).length < 2 ^ (prefixWord ++ tailWord_1239522).sum := by decide
  have hdescent : baseEnd_1239522 < baseStart_1239522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239584 : List Nat := [2, 1, 1, 6, 2, 1, 3, 2, 1, 3]
def baseStart_1239584 : Nat := 118140960795 + 1239584 * 2 ^ 59
def prefixEnd_1239584 : Nat := 4983230072969 + 3 ^ 40 * 1239584 * 2
def baseEnd_1239584 : Nat := 424334935748655570399509

theorem tailTrace_1239584 : CollatzResearch.WordTrace tailWord_1239584 prefixEnd_1239584 424334935748655570399509 := by
  unfold tailWord_1239584
  simp only [CollatzResearch.WordTrace]
  refine ⟨22605671370603173468842903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30140895160804231291790537 22605671370603173468842903)
  ·
    refine ⟨33908507055904760203264355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22605671370603173468842903 33908507055904760203264355)
    ·
      refine ⟨50862760583857140304896533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33908507055904760203264355 50862760583857140304896533)
      ·
        refine ⟨2384191902368303451792025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50862760583857140304896533 2384191902368303451792025)
        ·
          refine ⟨1788143926776227588844019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2384191902368303451792025 1788143926776227588844019)
          ·
            refine ⟨2682215890164341383266029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1788143926776227588844019 2682215890164341383266029)
            ·
              refine ⟨1005830958811628018724761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2682215890164341383266029 1005830958811628018724761)
              ·
                refine ⟨754373219108721014043571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1005830958811628018724761 754373219108721014043571)
                ·
                  refine ⟨1131559828663081521065357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754373219108721014043571 1131559828663081521065357)
                  ·
                    refine ⟨424334935748655570399509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1131559828663081521065357 424334935748655570399509)
                    ·
                      rfl

theorem cell22_1239584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 1, 3].length) (baseStart_1239584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239584 prefixEnd_1239584 := by exact prefixLift 1239584
  have htrace : WordTrace (prefixWord ++ tailWord_1239584) baseStart_1239584 baseEnd_1239584 := by
    simpa [prefixWord, tailWord_1239584, baseEnd_1239584] using wordTrace_append hprefix tailTrace_1239584
  have hstable : (prefixWord ++ tailWord_1239584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239584).length < 2 ^ (prefixWord ++ tailWord_1239584).sum := by decide
  have hdescent : baseEnd_1239584 < baseStart_1239584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239610 : List Nat := [3, 1, 1, 1, 3, 5, 1, 2, 1, 4]
def baseStart_1239610 : Nat := 118140960795 + 1239610 * 2 ^ 59
def prefixEnd_1239610 : Nat := 4983230072969 + 3 ^ 40 * 1239610 * 2
def baseEnd_1239610 : Nat := 424343836080000169249429

theorem tailTrace_1239610 : CollatzResearch.WordTrace tailWord_1239610 prefixEnd_1239610 424343836080000169249429 := by
  unfold tailWord_1239610
  simp only [CollatzResearch.WordTrace]
  refine ⟨11303072759778038344533071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30141527359408102252088189 11303072759778038344533071)
  ·
    refine ⟨16954609139667057516799607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11303072759778038344533071 16954609139667057516799607)
    ·
      refine ⟨25431913709500586275199411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16954609139667057516799607 25431913709500586275199411)
      ·
        refine ⟨38147870564250879412799117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25431913709500586275199411 38147870564250879412799117)
        ·
          refine ⟨14305451461594079779799669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38147870564250879412799117 14305451461594079779799669)
          ·
            refine ⟨1341136074524444979356219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14305451461594079779799669 1341136074524444979356219)
            ·
              refine ⟨2011704111786667469034329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1341136074524444979356219 2011704111786667469034329)
              ·
                refine ⟨1508778083840000601775747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2011704111786667469034329 1508778083840000601775747)
                ·
                  refine ⟨2263167125760000902663621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508778083840000601775747 2263167125760000902663621)
                  ·
                    refine ⟨424343836080000169249429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2263167125760000902663621 424343836080000169249429)
                    ·
                      rfl

theorem cell22_1239610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_1239610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239610 prefixEnd_1239610 := by exact prefixLift 1239610
  have htrace : WordTrace (prefixWord ++ tailWord_1239610) baseStart_1239610 baseEnd_1239610 := by
    simpa [prefixWord, tailWord_1239610, baseEnd_1239610] using wordTrace_append hprefix tailTrace_1239610
  have hstable : (prefixWord ++ tailWord_1239610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239610).length < 2 ^ (prefixWord ++ tailWord_1239610).sum := by decide
  have hdescent : baseEnd_1239610 < baseStart_1239610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239623 : List Nat := [1, 1, 4, 1, 4, 2, 1, 2, 1, 5]
def baseStart_1239623 : Nat := 118140960795 + 1239623 * 2 ^ 59
def prefixEnd_1239623 : Nat := 4983230072969 + 3 ^ 40 * 1239623 * 2
def baseEnd_1239623 : Nat := 424348286245672468674389

theorem tailTrace_1239623 : CollatzResearch.WordTrace tailWord_1239623 prefixEnd_1239623 424348286245672468674389 := by
  unfold tailWord_1239623
  simp only [CollatzResearch.WordTrace]
  refine ⟨45212765188065056598355523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30141843458710037732237015 45212765188065056598355523)
  ·
    refine ⟨67819147782097584897533285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45212765188065056598355523 67819147782097584897533285)
    ·
      refine ⟨12716090209143297168287491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67819147782097584897533285 12716090209143297168287491)
      ·
        refine ⟨19074135313714945752431237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12716090209143297168287491 19074135313714945752431237)
        ·
          refine ⟨3576400371321552328580857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19074135313714945752431237 3576400371321552328580857)
          ·
            refine ⟨2682300278491164246435643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3576400371321552328580857 2682300278491164246435643)
            ·
              refine ⟨4023450417736746369653465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2682300278491164246435643 4023450417736746369653465)
              ·
                refine ⟨3017587813302559777240099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4023450417736746369653465 3017587813302559777240099)
                ·
                  refine ⟨4526381719953839665860149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3017587813302559777240099 4526381719953839665860149)
                  ·
                    refine ⟨424348286245672468674389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4526381719953839665860149 424348286245672468674389)
                    ·
                      rfl

theorem cell22_1239623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_1239623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239623 prefixEnd_1239623 := by exact prefixLift 1239623
  have htrace : WordTrace (prefixWord ++ tailWord_1239623) baseStart_1239623 baseEnd_1239623 := by
    simpa [prefixWord, tailWord_1239623, baseEnd_1239623] using wordTrace_append hprefix tailTrace_1239623
  have hstable : (prefixWord ++ tailWord_1239623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239623).length < 2 ^ (prefixWord ++ tailWord_1239623).sum := by decide
  have hdescent : baseEnd_1239623 < baseStart_1239623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239636 : List Nat := [2, 4, 1, 1, 1, 13]
def baseStart_1239636 : Nat := 118140960795 + 1239636 * 2 ^ 59
def prefixEnd_1239636 : Nat := 4983230072969 + 3 ^ 40 * 1239636 * 2
def baseEnd_1239636 : Nat := 5238922671744997137029

theorem tailTrace_1239636 : CollatzResearch.WordTrace tailWord_1239636 prefixEnd_1239636 5238922671744997137029 := by
  unfold tailWord_1239636
  simp only [CollatzResearch.WordTrace]
  refine ⟨22606619668508979909289381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30142159558011973212385841 22606619668508979909289381)
  ·
    refine ⟨4238741187845433732991759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22606619668508979909289381 4238741187845433732991759)
    ·
      refine ⟨6358111781768150599487639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4238741187845433732991759 6358111781768150599487639)
      ·
        refine ⟨9537167672652225899231459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6358111781768150599487639 9537167672652225899231459)
        ·
          refine ⟨14305751508978338848847189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9537167672652225899231459 14305751508978338848847189)
          ·
            refine ⟨5238922671744997137029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 14305751508978338848847189 5238922671744997137029)
            ·
              rfl

theorem cell22_1239636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 13].length) (baseStart_1239636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239636 prefixEnd_1239636 := by exact prefixLift 1239636
  have htrace : WordTrace (prefixWord ++ tailWord_1239636) baseStart_1239636 baseEnd_1239636 := by
    simpa [prefixWord, tailWord_1239636, baseEnd_1239636] using wordTrace_append hprefix tailTrace_1239636
  have hstable : (prefixWord ++ tailWord_1239636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239636).length < 2 ^ (prefixWord ++ tailWord_1239636).sum := by decide
  have hdescent : baseEnd_1239636 < baseStart_1239636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239790 : List Nat := [4, 1, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_1239790 : Nat := 118140960795 + 1239790 * 2 ^ 59
def prefixEnd_1239790 : Nat := 4983230072969 + 3 ^ 40 * 1239790 * 2
def baseEnd_1239790 : Nat := 424405453758539699748877

theorem tailTrace_1239790 : CollatzResearch.WordTrace tailWord_1239790 prefixEnd_1239790 424405453758539699748877 := by
  unfold tailWord_1239790
  simp only [CollatzResearch.WordTrace]
  refine ⟨5652357022307505514960603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30145904118973362746456549 5652357022307505514960603)
  ·
    refine ⟨8478535533461258272440905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5652357022307505514960603 8478535533461258272440905)
    ·
      refine ⟨6358901650095943704330679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8478535533461258272440905 6358901650095943704330679)
      ·
        refine ⟨9538352475143915556496019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6358901650095943704330679 9538352475143915556496019)
        ·
          refine ⟨14307528712715873334744029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9538352475143915556496019 14307528712715873334744029)
          ·
            refine ⟨5365323267268452500529011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14307528712715873334744029 5365323267268452500529011)
            ·
              refine ⟨8047984900902678750793517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5365323267268452500529011 8047984900902678750793517)
              ·
                refine ⟨3017994337838504531547569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8047984900902678750793517 3017994337838504531547569)
                ·
                  refine ⟨2263495753378878398660677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3017994337838504531547569 2263495753378878398660677)
                  ·
                    refine ⟨424405453758539699748877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2263495753378878398660677 424405453758539699748877)
                    ·
                      rfl

theorem cell22_1239790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_1239790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239790 prefixEnd_1239790 := by exact prefixLift 1239790
  have htrace : WordTrace (prefixWord ++ tailWord_1239790) baseStart_1239790 baseEnd_1239790 := by
    simpa [prefixWord, tailWord_1239790, baseEnd_1239790] using wordTrace_append hprefix tailTrace_1239790
  have hstable : (prefixWord ++ tailWord_1239790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239790).length < 2 ^ (prefixWord ++ tailWord_1239790).sum := by decide
  have hdescent : baseEnd_1239790 < baseStart_1239790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239818 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 1, 8]
def baseStart_1239818 : Nat := 118140960795 + 1239818 * 2 ^ 59
def prefixEnd_1239818 : Nat := 4983230072969 + 3 ^ 40 * 1239818 * 2
def baseEnd_1239818 : Nat := 424415038730756960048791

theorem tailTrace_1239818 : CollatzResearch.WordTrace tailWord_1239818 prefixEnd_1239818 424415038730756960048791 := by
  unfold tailWord_1239818
  simp only [CollatzResearch.WordTrace]
  refine ⟨11304969355589651225426027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30146584948239069934469405 11304969355589651225426027)
  ·
    refine ⟨16957454033384476838139041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11304969355589651225426027 16957454033384476838139041)
    ·
      refine ⟨12718090525038357628604281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16957454033384476838139041 12718090525038357628604281)
      ·
        refine ⟨9538567893778768221453211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12718090525038357628604281 9538567893778768221453211)
        ·
          refine ⟨14307851840668152332179817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9538567893778768221453211 14307851840668152332179817)
          ·
            refine ⟨10730888880501114249134863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14307851840668152332179817 10730888880501114249134863)
            ·
              refine ⟨16096333320751671373702295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10730888880501114249134863 16096333320751671373702295)
              ·
                refine ⟨24144499981127507060553443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16096333320751671373702295 24144499981127507060553443)
                ·
                  refine ⟨36216749971691260590830165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24144499981127507060553443 36216749971691260590830165)
                  ·
                    refine ⟨424415038730756960048791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36216749971691260590830165 424415038730756960048791)
                    ·
                      rfl

theorem cell22_1239818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_1239818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239818 prefixEnd_1239818 := by exact prefixLift 1239818
  have htrace : WordTrace (prefixWord ++ tailWord_1239818) baseStart_1239818 baseEnd_1239818 := by
    simpa [prefixWord, tailWord_1239818, baseEnd_1239818] using wordTrace_append hprefix tailTrace_1239818
  have hstable : (prefixWord ++ tailWord_1239818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239818).length < 2 ^ (prefixWord ++ tailWord_1239818).sum := by decide
  have hdescent : baseEnd_1239818 < baseStart_1239818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239820 : List Nat := [2, 2, 1, 2, 2, 1, 1, 5, 3, 3]
def baseStart_1239820 : Nat := 118140960795 + 1239820 * 2 ^ 59
def prefixEnd_1239820 : Nat := 4983230072969 + 3 ^ 40 * 1239820 * 2
def baseEnd_1239820 : Nat := 424415723371629621498785

theorem tailTrace_1239820 : CollatzResearch.WordTrace tailWord_1239820 prefixEnd_1239820 424415723371629621498785 := by
  unfold tailWord_1239820
  simp only [CollatzResearch.WordTrace]
  refine ⟨22609975184175679621638457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30146633578900906162184609 22609975184175679621638457)
  ·
    refine ⟨16957481388131759716228843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22609975184175679621638457 16957481388131759716228843)
    ·
      refine ⟨25436222082197639574343265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16957481388131759716228843 25436222082197639574343265)
      ·
        refine ⟨19077166561648229680757449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25436222082197639574343265 19077166561648229680757449)
        ·
          refine ⟨14307874921236172260568087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19077166561648229680757449 14307874921236172260568087)
          ·
            refine ⟨21461812381854258390852131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14307874921236172260568087 21461812381854258390852131)
            ·
              refine ⟨32192718572781387586278197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21461812381854258390852131 32192718572781387586278197)
              ·
                refine ⟨3018067366198255086213581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32192718572781387586278197 3018067366198255086213581)
                ·
                  refine ⟨1131775262324345657330093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3018067366198255086213581 1131775262324345657330093)
                  ·
                    refine ⟨424415723371629621498785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1131775262324345657330093 424415723371629621498785)
                    ·
                      rfl

theorem cell22_1239820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_1239820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239820 prefixEnd_1239820 := by exact prefixLift 1239820
  have htrace : WordTrace (prefixWord ++ tailWord_1239820) baseStart_1239820 baseEnd_1239820 := by
    simpa [prefixWord, tailWord_1239820, baseEnd_1239820] using wordTrace_append hprefix tailTrace_1239820
  have hstable : (prefixWord ++ tailWord_1239820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239820).length < 2 ^ (prefixWord ++ tailWord_1239820).sum := by decide
  have hdescent : baseEnd_1239820 < baseStart_1239820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239895 : List Nat := [1, 1, 3, 2, 4, 1, 2, 2, 6]
def baseStart_1239895 : Nat := 118140960795 + 1239895 * 2 ^ 59
def prefixEnd_1239895 : Nat := 4983230072969 + 3 ^ 40 * 1239895 * 2
def baseEnd_1239895 : Nat := 141480465801451475291185

theorem tailTrace_1239895 : CollatzResearch.WordTrace tailWord_1239895 prefixEnd_1239895 141480465801451475291185 := by
  unfold tailWord_1239895
  simp only [CollatzResearch.WordTrace]
  refine ⟨45222685843079647052257139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30148457228719764701504759 45222685843079647052257139)
  ·
    refine ⟨67834028764619470578385709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45222685843079647052257139 67834028764619470578385709)
    ·
      refine ⟨25437760786732301466894641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67834028764619470578385709 25437760786732301466894641)
      ·
        refine ⟨19078320590049226100170981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25437760786732301466894641 19078320590049226100170981)
        ·
          refine ⟨3577185110634229893782059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19078320590049226100170981 3577185110634229893782059)
          ·
            refine ⟨5365777665951344840673089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3577185110634229893782059 5365777665951344840673089)
            ·
              refine ⟨4024333249463508630504817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5365777665951344840673089 4024333249463508630504817)
              ·
                refine ⟨3018249937097631472878613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4024333249463508630504817 3018249937097631472878613)
                ·
                  refine ⟨141480465801451475291185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3018249937097631472878613 141480465801451475291185)
                  ·
                    rfl

theorem cell22_1239895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 6].length) (baseStart_1239895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239895 prefixEnd_1239895 := by exact prefixLift 1239895
  have htrace : WordTrace (prefixWord ++ tailWord_1239895) baseStart_1239895 baseEnd_1239895 := by
    simpa [prefixWord, tailWord_1239895, baseEnd_1239895] using wordTrace_append hprefix tailTrace_1239895
  have hstable : (prefixWord ++ tailWord_1239895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239895).length < 2 ^ (prefixWord ++ tailWord_1239895).sum := by decide
  have hdescent : baseEnd_1239895 < baseStart_1239895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239897 : List Nat := [1, 2, 1, 2, 2, 5, 2, 2, 1, 4]
def baseStart_1239897 : Nat := 118140960795 + 1239897 * 2 ^ 59
def prefixEnd_1239897 : Nat := 4983230072969 + 3 ^ 40 * 1239897 * 2
def baseEnd_1239897 : Nat := 424442082045227087323549

theorem tailTrace_1239897 : CollatzResearch.WordTrace tailWord_1239897 prefixEnd_1239897 424442082045227087323549 := by
  unfold tailWord_1239897
  simp only [CollatzResearch.WordTrace]
  refine ⟨45222758789072401393829945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30148505859381600929219963 45222758789072401393829945)
  ·
    refine ⟨33917069091804301045372459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45222758789072401393829945 33917069091804301045372459)
    ·
      refine ⟨50875603637706451568058689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33917069091804301045372459 50875603637706451568058689)
      ·
        refine ⟨38156702728279838676044017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50875603637706451568058689 38156702728279838676044017)
        ·
          refine ⟨28617527046209879007033013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38156702728279838676044017 28617527046209879007033013)
          ·
            refine ⟨2682893160582176156909345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28617527046209879007033013 2682893160582176156909345)
            ·
              refine ⟨2012169870436632117682009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2682893160582176156909345 2012169870436632117682009)
              ·
                refine ⟨1509127402827474088261507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2012169870436632117682009 1509127402827474088261507)
                ·
                  refine ⟨2263691104241211132392261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509127402827474088261507 2263691104241211132392261)
                  ·
                    refine ⟨424442082045227087323549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2263691104241211132392261 424442082045227087323549)
                    ·
                      rfl

theorem cell22_1239897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 4].length) (baseStart_1239897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239897 prefixEnd_1239897 := by exact prefixLift 1239897
  have htrace : WordTrace (prefixWord ++ tailWord_1239897) baseStart_1239897 baseEnd_1239897 := by
    simpa [prefixWord, tailWord_1239897, baseEnd_1239897] using wordTrace_append hprefix tailTrace_1239897
  have hstable : (prefixWord ++ tailWord_1239897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239897).length < 2 ^ (prefixWord ++ tailWord_1239897).sum := by decide
  have hdescent : baseEnd_1239897 < baseStart_1239897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239923 : List Nat := [1, 1, 1, 2, 2, 1, 14]
def baseStart_1239923 : Nat := 118140960795 + 1239923 * 2 ^ 59
def prefixEnd_1239923 : Nat := 4983230072969 + 3 ^ 40 * 1239923 * 2
def baseEnd_1239923 : Nat := 15720406754687840228647

theorem tailTrace_1239923 : CollatzResearch.WordTrace tailWord_1239923 prefixEnd_1239923 15720406754687840228647 := by
  unfold tailWord_1239923
  simp only [CollatzResearch.WordTrace]
  refine ⟨45223707086978207834276423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30149138057985471889517615 45223707086978207834276423)
  ·
    refine ⟨67835560630467311751414635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45223707086978207834276423 67835560630467311751414635)
    ·
      refine ⟨101753340945700967627121953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67835560630467311751414635 101753340945700967627121953)
      ·
        refine ⟨76315005709275725720341465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101753340945700967627121953 76315005709275725720341465)
        ·
          refine ⟨57236254281956794290256099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76315005709275725720341465 57236254281956794290256099)
          ·
            refine ⟨85854381422935191435384149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57236254281956794290256099 85854381422935191435384149)
            ·
              refine ⟨15720406754687840228647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 85854381422935191435384149 15720406754687840228647)
              ·
                rfl

theorem cell22_1239923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 14].length) (baseStart_1239923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239923 prefixEnd_1239923 := by exact prefixLift 1239923
  have htrace : WordTrace (prefixWord ++ tailWord_1239923) baseStart_1239923 baseEnd_1239923 := by
    simpa [prefixWord, tailWord_1239923, baseEnd_1239923] using wordTrace_append hprefix tailTrace_1239923
  have hstable : (prefixWord ++ tailWord_1239923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239923).length < 2 ^ (prefixWord ++ tailWord_1239923).sum := by decide
  have hdescent : baseEnd_1239923 < baseStart_1239923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239929 : List Nat := [1, 2, 1, 3, 2, 4, 3, 2, 4]
def baseStart_1239929 : Nat := 118140960795 + 1239929 * 2 ^ 59
def prefixEnd_1239929 : Nat := 4983230072969 + 3 ^ 40 * 1239929 * 2
def baseEnd_1239929 : Nat := 141484345433063223507817

theorem tailTrace_1239929 : CollatzResearch.WordTrace tailWord_1239929 prefixEnd_1239929 141484345433063223507817 := by
  unfold tailWord_1239929
  simp only [CollatzResearch.WordTrace]
  refine ⟨45223925924956470858994841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30149283949970980572663227 45223925924956470858994841)
  ·
    refine ⟨33917944443717353144246131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45223925924956470858994841 33917944443717353144246131)
    ·
      refine ⟨50876916665576029716369197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33917944443717353144246131 50876916665576029716369197)
      ·
        refine ⟨19078843749591011143638449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50876916665576029716369197 19078843749591011143638449)
        ·
          refine ⟨14309132812193258357728837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19078843749591011143638449 14309132812193258357728837)
          ·
            refine ⟨2682962402286235942074157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14309132812193258357728837 2682962402286235942074157)
            ·
              refine ⟨1006110900857338478277809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2682962402286235942074157 1006110900857338478277809)
              ·
                refine ⟨754583175643003858708357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1006110900857338478277809 754583175643003858708357)
                ·
                  refine ⟨141484345433063223507817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 754583175643003858708357 141484345433063223507817)
                  ·
                    rfl

theorem cell22_1239929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 4].length) (baseStart_1239929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239929 prefixEnd_1239929 := by exact prefixLift 1239929
  have htrace : WordTrace (prefixWord ++ tailWord_1239929) baseStart_1239929 baseEnd_1239929 := by
    simpa [prefixWord, tailWord_1239929, baseEnd_1239929] using wordTrace_append hprefix tailTrace_1239929
  have hstable : (prefixWord ++ tailWord_1239929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239929).length < 2 ^ (prefixWord ++ tailWord_1239929).sum := by decide
  have hdescent : baseEnd_1239929 < baseStart_1239929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239944 : List Nat := [2, 1, 3, 3, 2, 2, 1, 3, 2, 3]
def baseStart_1239944 : Nat := 118140960795 + 1239944 * 2 ^ 59
def prefixEnd_1239944 : Nat := 4983230072969 + 3 ^ 40 * 1239944 * 2
def baseEnd_1239944 : Nat := 424458171105734631398405

theorem tailTrace_1239944 : CollatzResearch.WordTrace tailWord_1239944 prefixEnd_1239944 424458171105734631398405 := by
  unfold tailWord_1239944
  simp only [CollatzResearch.WordTrace]
  refine ⟨22612236509951064210395443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30149648679934752280527257 22612236509951064210395443)
  ·
    refine ⟨33918354764926596315593165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22612236509951064210395443 33918354764926596315593165)
    ·
      refine ⟨12719383036847473618347437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33918354764926596315593165 12719383036847473618347437)
      ·
        refine ⟨4769768638817802606880289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12719383036847473618347437 4769768638817802606880289)
        ·
          refine ⟨3577326479113351955160217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4769768638817802606880289 3577326479113351955160217)
          ·
            refine ⟨2682994859335013966370163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3577326479113351955160217 2682994859335013966370163)
            ·
              refine ⟨4024492289002520949555245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2682994859335013966370163 4024492289002520949555245)
              ·
                refine ⟨1509184608375945356083217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4024492289002520949555245 1509184608375945356083217)
                ·
                  refine ⟨1131888456281959017062413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1509184608375945356083217 1131888456281959017062413)
                  ·
                    refine ⟨424458171105734631398405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1131888456281959017062413 424458171105734631398405)
                    ·
                      rfl

theorem cell22_1239944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_1239944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1239944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1239944 prefixEnd_1239944 := by exact prefixLift 1239944
  have htrace : WordTrace (prefixWord ++ tailWord_1239944) baseStart_1239944 baseEnd_1239944 := by
    simpa [prefixWord, tailWord_1239944, baseEnd_1239944] using wordTrace_append hprefix tailTrace_1239944
  have hstable : (prefixWord ++ tailWord_1239944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239944).length < 2 ^ (prefixWord ++ tailWord_1239944).sum := by decide
  have hdescent : baseEnd_1239944 < baseStart_1239944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240000 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 1, 7]
def baseStart_1240000 : Nat := 118140960795 + 1240000 * 2 ^ 59
def prefixEnd_1240000 : Nat := 4983230072969 + 3 ^ 40 * 1240000 * 2
def baseEnd_1240000 : Nat := 424477341050169151998233

theorem tailTrace_1240000 : CollatzResearch.WordTrace tailWord_1240000 prefixEnd_1240000 424477341050169151998233 := by
  unfold tailWord_1240000
  simp only [CollatzResearch.WordTrace]
  refine ⟨22613257753849624992414727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30151010338466166656552969 22613257753849624992414727)
  ·
    refine ⟨33919886630774437488622091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22613257753849624992414727 33919886630774437488622091)
    ·
      refine ⟨50879829946161656232933137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33919886630774437488622091 50879829946161656232933137)
      ·
        refine ⟨38159872459621242174699853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50879829946161656232933137 38159872459621242174699853)
        ·
          refine ⟨14309952172357965815512445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38159872459621242174699853 14309952172357965815512445)
          ·
            refine ⟨5366232064634237180817167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14309952172357965815512445 5366232064634237180817167)
            ·
              refine ⟨8049348096951355771225751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5366232064634237180817167 8049348096951355771225751)
              ·
                refine ⟨12074022145427033656838627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8049348096951355771225751 12074022145427033656838627)
                ·
                  refine ⟨18111033218140550485257941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12074022145427033656838627 18111033218140550485257941)
                  ·
                    refine ⟨424477341050169151998233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18111033218140550485257941 424477341050169151998233)
                    ·
                      rfl

theorem cell22_1240000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_1240000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240000 prefixEnd_1240000 := by exact prefixLift 1240000
  have htrace : WordTrace (prefixWord ++ tailWord_1240000) baseStart_1240000 baseEnd_1240000 := by
    simpa [prefixWord, tailWord_1240000, baseEnd_1240000] using wordTrace_append hprefix tailTrace_1240000
  have hstable : (prefixWord ++ tailWord_1240000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240000).length < 2 ^ (prefixWord ++ tailWord_1240000).sum := by decide
  have hdescent : baseEnd_1240000 < baseStart_1240000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240034 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1240034 : Nat := 118140960795 + 1240034 * 2 ^ 59
def prefixEnd_1240034 : Nat := 4983230072969 + 3 ^ 40 * 1240034 * 2
def baseEnd_1240034 : Nat := 424488979945004396648129

theorem tailTrace_1240034 : CollatzResearch.WordTrace tailWord_1240034 prefixEnd_1240034 424488979945004396648129 := by
  unfold tailWord_1240034
  simp only [CollatzResearch.WordTrace]
  refine ⟨11306938897394018447891789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30151837059717382527711437 11306938897394018447891789)
  ·
    refine ⟨4240102086522756917959421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11306938897394018447891789 4240102086522756917959421)
    ·
      refine ⟨1590038282446033844234783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4240102086522756917959421 1590038282446033844234783)
      ·
        refine ⟨2385057423669050766352175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1590038282446033844234783 2385057423669050766352175)
        ·
          refine ⟨3577586135503576149528263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2385057423669050766352175 3577586135503576149528263)
          ·
            refine ⟨5366379203255364224292395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3577586135503576149528263 5366379203255364224292395)
            ·
              refine ⟨8049568804883046336438593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5366379203255364224292395 8049568804883046336438593)
              ·
                refine ⟨6037176603662284752328945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8049568804883046336438593 6037176603662284752328945)
                ·
                  refine ⟨4527882452746713564246709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6037176603662284752328945 4527882452746713564246709)
                  ·
                    refine ⟨424488979945004396648129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4527882452746713564246709 424488979945004396648129)
                    ·
                      rfl

theorem cell22_1240034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1240034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240034 prefixEnd_1240034 := by exact prefixLift 1240034
  have htrace : WordTrace (prefixWord ++ tailWord_1240034) baseStart_1240034 baseEnd_1240034 := by
    simpa [prefixWord, tailWord_1240034, baseEnd_1240034] using wordTrace_append hprefix tailTrace_1240034
  have hstable : (prefixWord ++ tailWord_1240034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240034).length < 2 ^ (prefixWord ++ tailWord_1240034).sum := by decide
  have hdescent : baseEnd_1240034 < baseStart_1240034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240047 : List Nat := [1, 1, 2, 1, 4, 4, 2, 1, 6]
def baseStart_1240047 : Nat := 118140960795 + 1240047 * 2 ^ 59
def prefixEnd_1240047 : Nat := 4983230072969 + 3 ^ 40 * 1240047 * 2
def baseEnd_1240047 : Nat := 141497810036892232024363

theorem tailTrace_1240047 : CollatzResearch.WordTrace tailWord_1240047 prefixEnd_1240047 141497810036892232024363 := by
  unfold tailWord_1240047
  simp only [CollatzResearch.WordTrace]
  refine ⟨45228229738528977011790395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30152153159019318007860263 45228229738528977011790395)
  ·
    refine ⟨67842344607793465517685593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45228229738528977011790395 67842344607793465517685593)
    ·
      refine ⟨50881758455845099138264195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67842344607793465517685593 50881758455845099138264195)
      ·
        refine ⟨76322637683767648707396293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50881758455845099138264195 76322637683767648707396293)
        ·
          refine ⟨14310494565706434132636805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76322637683767648707396293 14310494565706434132636805)
          ·
            refine ⟨2683217731069956399869401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14310494565706434132636805 2683217731069956399869401)
            ·
              refine ⟨2012413298302467299902051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2683217731069956399869401 2012413298302467299902051)
              ·
                refine ⟨3018619947453700949853077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2012413298302467299902051 3018619947453700949853077)
                ·
                  refine ⟨141497810036892232024363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3018619947453700949853077 141497810036892232024363)
                  ·
                    rfl

theorem cell22_1240047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 6].length) (baseStart_1240047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240047 prefixEnd_1240047 := by exact prefixLift 1240047
  have htrace : WordTrace (prefixWord ++ tailWord_1240047) baseStart_1240047 baseEnd_1240047 := by
    simpa [prefixWord, tailWord_1240047, baseEnd_1240047] using wordTrace_append hprefix tailTrace_1240047
  have hstable : (prefixWord ++ tailWord_1240047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240047).length < 2 ^ (prefixWord ++ tailWord_1240047).sum := by decide
  have hdescent : baseEnd_1240047 < baseStart_1240047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240053 : List Nat := [1, 3, 5, 2, 1, 1, 3, 1, 5]
def baseStart_1240053 : Nat := 118140960795 + 1240053 * 2 ^ 59
def prefixEnd_1240053 : Nat := 4983230072969 + 3 ^ 40 * 1240053 * 2
def baseEnd_1240053 : Nat := 141498494677764893474357

theorem tailTrace_1240053 : CollatzResearch.WordTrace tailWord_1240053 prefixEnd_1240053 141498494677764893474357 := by
  unfold tailWord_1240053
  simp only [CollatzResearch.WordTrace]
  refine ⟨45228448576507240036508813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30152299051004826691005875 45228448576507240036508813)
  ·
    refine ⟨16960668216190215013690805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45228448576507240036508813 16960668216190215013690805)
    ·
      refine ⟨1590062645267832657533513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16960668216190215013690805 1590062645267832657533513)
      ·
        refine ⟨1192546983950874493150135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1590062645267832657533513 1192546983950874493150135)
        ·
          refine ⟨1788820475926311739725203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1192546983950874493150135 1788820475926311739725203)
          ·
            refine ⟨2683230713889467609587805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1788820475926311739725203 2683230713889467609587805)
            ·
              refine ⟨1006211517708550353595427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2683230713889467609587805 1006211517708550353595427)
              ·
                refine ⟨1509317276562825530393141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1006211517708550353595427 1509317276562825530393141)
                ·
                  refine ⟨141498494677764893474357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1509317276562825530393141 141498494677764893474357)
                  ·
                    rfl

theorem cell22_1240053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 5].length) (baseStart_1240053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240053 prefixEnd_1240053 := by exact prefixLift 1240053
  have htrace : WordTrace (prefixWord ++ tailWord_1240053) baseStart_1240053 baseEnd_1240053 := by
    simpa [prefixWord, tailWord_1240053, baseEnd_1240053] using wordTrace_append hprefix tailTrace_1240053
  have hstable : (prefixWord ++ tailWord_1240053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240053).length < 2 ^ (prefixWord ++ tailWord_1240053).sum := by decide
  have hdescent : baseEnd_1240053 < baseStart_1240053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240152 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 2, 5]
def baseStart_1240152 : Nat := 118140960795 + 1240152 * 2 ^ 59
def prefixEnd_1240152 : Nat := 4983230072969 + 3 ^ 40 * 1240152 * 2
def baseEnd_1240152 : Nat := 424529373756491422197767

theorem tailTrace_1240152 : CollatzResearch.WordTrace tailWord_1240152 prefixEnd_1240152 424529373756491422197767 := by
  unfold tailWord_1240152
  simp only [CollatzResearch.WordTrace]
  refine ⟨22616029701574289972181355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30154706268765719962908473 22616029701574289972181355)
  ·
    refine ⟨33924044552361434958272033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22616029701574289972181355 33924044552361434958272033)
    ·
      refine ⟨25443033414271076218704025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33924044552361434958272033 25443033414271076218704025)
      ·
        refine ⟨19082275060703307164028019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25443033414271076218704025 19082275060703307164028019)
        ·
          refine ⟨28623412591054960746042029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19082275060703307164028019 28623412591054960746042029)
          ·
            refine ⟨10733779721645610279765761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28623412591054960746042029 10733779721645610279765761)
            ·
              refine ⟨8050334791234207709824321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10733779721645610279765761 8050334791234207709824321)
              ·
                refine ⟨6037751093425655782368241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8050334791234207709824321 6037751093425655782368241)
                ·
                  refine ⟨4528313320069241836776181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6037751093425655782368241 4528313320069241836776181)
                  ·
                    refine ⟨424529373756491422197767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4528313320069241836776181 424529373756491422197767)
                    ·
                      rfl

theorem cell22_1240152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_1240152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240152 prefixEnd_1240152 := by exact prefixLift 1240152
  have htrace : WordTrace (prefixWord ++ tailWord_1240152) baseStart_1240152 baseEnd_1240152 := by
    simpa [prefixWord, tailWord_1240152, baseEnd_1240152] using wordTrace_append hprefix tailTrace_1240152
  have hstable : (prefixWord ++ tailWord_1240152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240152).length < 2 ^ (prefixWord ++ tailWord_1240152).sum := by decide
  have hdescent : baseEnd_1240152 < baseStart_1240152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240201 : List Nat := [1, 2, 1, 1, 4, 3, 4, 1, 1, 4]
def baseStart_1240201 : Nat := 118140960795 + 1240201 * 2 ^ 59
def prefixEnd_1240201 : Nat := 4983230072969 + 3 ^ 40 * 1240201 * 2
def baseEnd_1240201 : Nat := 424546147457871627722617

theorem tailTrace_1240201 : CollatzResearch.WordTrace tailWord_1240201 prefixEnd_1240201 424546147457871627722617 := by
  unfold tailWord_1240201
  simp only [CollatzResearch.WordTrace]
  refine ⟨45233846579971061312896457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30155897719980707541930971 45233846579971061312896457)
  ·
    refine ⟨33925384934978295984672343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45233846579971061312896457 33925384934978295984672343)
    ·
      refine ⟨50888077402467443977008515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33925384934978295984672343 50888077402467443977008515)
      ·
        refine ⟨76332116103701165965512773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50888077402467443977008515 76332116103701165965512773)
        ·
          refine ⟨14312271769443968618533645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76332116103701165965512773 14312271769443968618533645)
          ·
            refine ⟨5367101913541488231950117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14312271769443968618533645 5367101913541488231950117)
            ·
              refine ⟨1006331608789029043490647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5367101913541488231950117 1006331608789029043490647)
              ·
                refine ⟨1509497413183543565235971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1006331608789029043490647 1509497413183543565235971)
                ·
                  refine ⟨2264246119775315347853957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509497413183543565235971 2264246119775315347853957)
                  ·
                    refine ⟨424546147457871627722617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2264246119775315347853957 424546147457871627722617)
                    ·
                      rfl

theorem cell22_1240201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 1, 4].length) (baseStart_1240201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240201 prefixEnd_1240201 := by exact prefixLift 1240201
  have htrace : WordTrace (prefixWord ++ tailWord_1240201) baseStart_1240201 baseEnd_1240201 := by
    simpa [prefixWord, tailWord_1240201, baseEnd_1240201] using wordTrace_append hprefix tailTrace_1240201
  have hstable : (prefixWord ++ tailWord_1240201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240201).length < 2 ^ (prefixWord ++ tailWord_1240201).sum := by decide
  have hdescent : baseEnd_1240201 < baseStart_1240201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240216 : List Nat := [2, 1, 2, 4, 2, 1, 2, 4, 4]
def baseStart_1240216 : Nat := 118140960795 + 1240216 * 2 ^ 59
def prefixEnd_1240216 : Nat := 4983230072969 + 3 ^ 40 * 1240216 * 2
def baseEnd_1240216 : Nat := 141517094088138862865857

theorem tailTrace_1240216 : CollatzResearch.WordTrace tailWord_1240216 prefixEnd_1240216 141517094088138862865857 := by
  unfold tailWord_1240216
  simp only [CollatzResearch.WordTrace]
  refine ⟨22617196837458359437346251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30156262449944479249795001 22617196837458359437346251)
  ·
    refine ⟨33925795256187539156019377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22617196837458359437346251 33925795256187539156019377)
    ·
      refine ⟨25444346442140654367014533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33925795256187539156019377 25444346442140654367014533)
      ·
        refine ⟨4770814957901372693815225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25444346442140654367014533 4770814957901372693815225)
        ·
          refine ⟨3578111218426029520361419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4770814957901372693815225 3578111218426029520361419)
          ·
            refine ⟨5367166827639044280542129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3578111218426029520361419 5367166827639044280542129)
            ·
              refine ⟨4025375120729283210406597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5367166827639044280542129 4025375120729283210406597)
              ·
                refine ⟨754757835136740601951237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4025375120729283210406597 754757835136740601951237)
                ·
                  refine ⟨141517094088138862865857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 754757835136740601951237 141517094088138862865857)
                  ·
                    rfl

theorem cell22_1240216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 4].length) (baseStart_1240216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240216 prefixEnd_1240216 := by exact prefixLift 1240216
  have htrace : WordTrace (prefixWord ++ tailWord_1240216) baseStart_1240216 baseEnd_1240216 := by
    simpa [prefixWord, tailWord_1240216, baseEnd_1240216] using wordTrace_append hprefix tailTrace_1240216
  have hstable : (prefixWord ++ tailWord_1240216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240216).length < 2 ^ (prefixWord ++ tailWord_1240216).sum := by decide
  have hdescent : baseEnd_1240216 < baseStart_1240216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240231 : List Nat := [1, 1, 6, 2, 1, 1, 3, 1, 1, 5]
def baseStart_1240231 : Nat := 118140960795 + 1240231 * 2 ^ 59
def prefixEnd_1240231 : Nat := 4983230072969 + 3 ^ 40 * 1240231 * 2
def baseEnd_1240231 : Nat := 424556417070961549472525

theorem tailTrace_1240231 : CollatzResearch.WordTrace tailWord_1240231 prefixEnd_1240231 424556417070961549472525 := by
  unfold tailWord_1240231
  simp only [CollatzResearch.WordTrace]
  refine ⟨45234940769862376436488547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30156627179908250957659031 45234940769862376436488547)
  ·
    refine ⟨67852411154793564654732821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45234940769862376436488547 67852411154793564654732821)
    ·
      refine ⟨3180581772880948343190601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 67852411154793564654732821 3180581772880948343190601)
      ·
        refine ⟨2385436329660711257392951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3180581772880948343190601 2385436329660711257392951)
        ·
          refine ⟨3578154494491066886089427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2385436329660711257392951 3578154494491066886089427)
          ·
            refine ⟨5367231741736600329134141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3578154494491066886089427 5367231741736600329134141)
            ·
              refine ⟨2012711903151225123425303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5367231741736600329134141 2012711903151225123425303)
              ·
                refine ⟨3019067854726837685137955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2012711903151225123425303 3019067854726837685137955)
                ·
                  refine ⟨4528601782090256527706933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3019067854726837685137955 4528601782090256527706933)
                  ·
                    refine ⟨424556417070961549472525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4528601782090256527706933 424556417070961549472525)
                    ·
                      rfl

theorem cell22_1240231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_1240231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240231 prefixEnd_1240231 := by exact prefixLift 1240231
  have htrace : WordTrace (prefixWord ++ tailWord_1240231) baseStart_1240231 baseEnd_1240231 := by
    simpa [prefixWord, tailWord_1240231, baseEnd_1240231] using wordTrace_append hprefix tailTrace_1240231
  have hstable : (prefixWord ++ tailWord_1240231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240231).length < 2 ^ (prefixWord ++ tailWord_1240231).sum := by decide
  have hdescent : baseEnd_1240231 < baseStart_1240231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240274 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_1240274 : Nat := 118140960795 + 1240274 * 2 ^ 59
def prefixEnd_1240274 : Nat := 4983230072969 + 3 ^ 40 * 1240274 * 2
def baseEnd_1240274 : Nat := 424571136849723770647393

theorem tailTrace_1240274 : CollatzResearch.WordTrace tailWord_1240274 prefixEnd_1240274 424571136849723770647393 := by
  unfold tailWord_1240274
  simp only [CollatzResearch.WordTrace]
  refine ⟨11309127277176648695075969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30157672739137729853535917 11309127277176648695075969)
  ·
    refine ⟨8481845457882486521306977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11309127277176648695075969 8481845457882486521306977)
    ·
      refine ⟨6361384093411864890980233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8481845457882486521306977 6361384093411864890980233)
      ·
        refine ⟨4771038070058898668235175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6361384093411864890980233 4771038070058898668235175)
        ·
          refine ⟨7156557105088348002352763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4771038070058898668235175 7156557105088348002352763)
          ·
            refine ⟨10734835657632522003529145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7156557105088348002352763 10734835657632522003529145)
            ·
              refine ⟨8051126743224391502646859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10734835657632522003529145 8051126743224391502646859)
              ·
                refine ⟨12076690114836587253970289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8051126743224391502646859 12076690114836587253970289)
                ·
                  refine ⟨9057517586127440440477717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12076690114836587253970289 9057517586127440440477717)
                  ·
                    refine ⟨424571136849723770647393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9057517586127440440477717 424571136849723770647393)
                    ·
                      rfl

theorem cell22_1240274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_1240274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240274 prefixEnd_1240274 := by exact prefixLift 1240274
  have htrace : WordTrace (prefixWord ++ tailWord_1240274) baseStart_1240274 baseEnd_1240274 := by
    simpa [prefixWord, tailWord_1240274, baseEnd_1240274] using wordTrace_append hprefix tailTrace_1240274
  have hstable : (prefixWord ++ tailWord_1240274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240274).length < 2 ^ (prefixWord ++ tailWord_1240274).sum := by decide
  have hdescent : baseEnd_1240274 < baseStart_1240274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240278 : List Nat := [5, 2, 1, 2, 2, 1, 2, 7]
def baseStart_1240278 : Nat := 118140960795 + 1240278 * 2 ^ 59
def prefixEnd_1240278 : Nat := 4983230072969 + 3 ^ 40 * 1240278 * 2
def baseEnd_1240278 : Nat := 47174722903496565949709

theorem tailTrace_1240278 : CollatzResearch.WordTrace tailWord_1240278 prefixEnd_1240278 47174722903496565949709 := by
  unfold tailWord_1240278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2827290937543256466465593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30157770000461402308966325 2827290937543256466465593)
  ·
    refine ⟨2120468203157442349849195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2827290937543256466465593 2120468203157442349849195)
    ·
      refine ⟨3180702304736163524773793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2120468203157442349849195 3180702304736163524773793)
      ·
        refine ⟨2385526728552122643580345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3180702304736163524773793 2385526728552122643580345)
        ·
          refine ⟨1789145046414091982685259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2385526728552122643580345 1789145046414091982685259)
          ·
            refine ⟨2683717569621137974027889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1789145046414091982685259 2683717569621137974027889)
            ·
              refine ⟨2012788177215853480520917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2683717569621137974027889 2012788177215853480520917)
              ·
                refine ⟨47174722903496565949709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2012788177215853480520917 47174722903496565949709)
                ·
                  rfl

theorem cell22_1240278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_1240278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240278 prefixEnd_1240278 := by exact prefixLift 1240278
  have htrace : WordTrace (prefixWord ++ tailWord_1240278) baseStart_1240278 baseEnd_1240278 := by
    simpa [prefixWord, tailWord_1240278, baseEnd_1240278] using wordTrace_append hprefix tailTrace_1240278
  have hstable : (prefixWord ++ tailWord_1240278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240278).length < 2 ^ (prefixWord ++ tailWord_1240278).sum := by decide
  have hdescent : baseEnd_1240278 < baseStart_1240278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240351 : List Nat := [1, 1, 2, 4, 4, 1, 1, 2, 6]
def baseStart_1240351 : Nat := 118140960795 + 1240351 * 2 ^ 59
def prefixEnd_1240351 : Nat := 4983230072969 + 3 ^ 40 * 1240351 * 2
def baseEnd_1240351 : Nat := 141532498507773745490719

theorem tailTrace_1240351 : CollatzResearch.WordTrace tailWord_1240351 prefixEnd_1240351 141532498507773745490719 := by
  unfold tailWord_1240351
  simp only [CollatzResearch.WordTrace]
  refine ⟨45239317529427636930856907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30159545019618424620571271 45239317529427636930856907)
  ·
    refine ⟨67858976294141455396285361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45239317529427636930856907 67858976294141455396285361)
    ·
      refine ⟨50894232220606091547214021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67858976294141455396285361 50894232220606091547214021)
      ·
        refine ⟨9542668541363642165102629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50894232220606091547214021 9542668541363642165102629)
        ·
          refine ⟨1789250351505682905956743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9542668541363642165102629 1789250351505682905956743)
          ·
            refine ⟨2683875527258524358935115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1789250351505682905956743 2683875527258524358935115)
            ·
              refine ⟨4025813290887786538402673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2683875527258524358935115 4025813290887786538402673)
              ·
                refine ⟨3019359968165839903802005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4025813290887786538402673 3019359968165839903802005)
                ·
                  refine ⟨141532498507773745490719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3019359968165839903802005 141532498507773745490719)
                  ·
                    rfl

theorem cell22_1240351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 6].length) (baseStart_1240351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240351 prefixEnd_1240351 := by exact prefixLift 1240351
  have htrace : WordTrace (prefixWord ++ tailWord_1240351) baseStart_1240351 baseEnd_1240351 := by
    simpa [prefixWord, tailWord_1240351, baseEnd_1240351] using wordTrace_append hprefix tailTrace_1240351
  have hstable : (prefixWord ++ tailWord_1240351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240351).length < 2 ^ (prefixWord ++ tailWord_1240351).sum := by decide
  have hdescent : baseEnd_1240351 < baseStart_1240351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240370 : List Nat := [3, 2, 1, 1, 4, 3, 2, 1, 1, 4]
def baseStart_1240370 : Nat := 118140960795 + 1240370 * 2 ^ 59
def prefixEnd_1240370 : Nat := 4983230072969 + 3 ^ 40 * 1240370 * 2
def baseEnd_1240370 : Nat := 424603999611611520247099

theorem tailTrace_1240370 : CollatzResearch.WordTrace tailWord_1240370 prefixEnd_1240370 424603999611611520247099 := by
  unfold tailWord_1240370
  simp only [CollatzResearch.WordTrace]
  refine ⟨11310002629089700793949641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30160007010905868783865709 11310002629089700793949641)
  ·
    refine ⟨8482501971817275595462231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11310002629089700793949641 8482501971817275595462231)
    ·
      refine ⟨12723752957725913393193347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8482501971817275595462231 12723752957725913393193347)
      ·
        refine ⟨19085629436588870089790021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12723752957725913393193347 19085629436588870089790021)
        ·
          refine ⟨3578555519360413141835629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19085629436588870089790021 3578555519360413141835629)
          ·
            refine ⟨1341958319760154928188361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3578555519360413141835629 1341958319760154928188361)
            ·
              refine ⟨1006468739820116196141271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1341958319760154928188361 1006468739820116196141271)
              ·
                refine ⟨1509703109730174294211907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1006468739820116196141271 1509703109730174294211907)
                ·
                  refine ⟨2264554664595261441317861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509703109730174294211907 2264554664595261441317861)
                  ·
                    refine ⟨424603999611611520247099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2264554664595261441317861 424603999611611520247099)
                    ·
                      rfl

theorem cell22_1240370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_1240370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240370 prefixEnd_1240370 := by exact prefixLift 1240370
  have htrace : WordTrace (prefixWord ++ tailWord_1240370) baseStart_1240370 baseEnd_1240370 := by
    simpa [prefixWord, tailWord_1240370, baseEnd_1240370] using wordTrace_append hprefix tailTrace_1240370
  have hstable : (prefixWord ++ tailWord_1240370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240370).length < 2 ^ (prefixWord ++ tailWord_1240370).sum := by decide
  have hdescent : baseEnd_1240370 < baseStart_1240370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240383 : List Nat := [1, 1, 2, 2, 4, 2, 3, 2, 2, 3]
def baseStart_1240383 : Nat := 118140960795 + 1240383 * 2 ^ 59
def prefixEnd_1240383 : Nat := 4983230072969 + 3 ^ 40 * 1240383 * 2
def baseEnd_1240383 : Nat := 424608449777283819672059

theorem tailTrace_1240383 : CollatzResearch.WordTrace tailWord_1240383 prefixEnd_1240383 424608449777283819672059 := by
  unfold tailWord_1240383
  simp only [CollatzResearch.WordTrace]
  refine ⟨45240484665311706396021803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30160323110207804264014535 45240484665311706396021803)
  ·
    refine ⟨67860726997967559594032705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45240484665311706396021803 67860726997967559594032705)
    ·
      refine ⟨50895545248475669695524529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67860726997967559594032705 50895545248475669695524529)
      ·
        refine ⟨38171658936356752271643397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50895545248475669695524529 38171658936356752271643397)
        ·
          refine ⟨7157186050566891050933137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38171658936356752271643397 7157186050566891050933137)
          ·
            refine ⟨5367889537925168288199853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7157186050566891050933137 5367889537925168288199853)
            ·
              refine ⟨2012958576721938108074945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5367889537925168288199853 2012958576721938108074945)
              ·
                refine ⟨1509718932541453581056209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2012958576721938108074945 1509718932541453581056209)
                ·
                  refine ⟨1132289199406090185792157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1509718932541453581056209 1132289199406090185792157)
                  ·
                    refine ⟨424608449777283819672059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1132289199406090185792157 424608449777283819672059)
                    ·
                      rfl

theorem cell22_1240383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 3].length) (baseStart_1240383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240383 prefixEnd_1240383 := by exact prefixLift 1240383
  have htrace : WordTrace (prefixWord ++ tailWord_1240383) baseStart_1240383 baseEnd_1240383 := by
    simpa [prefixWord, tailWord_1240383, baseEnd_1240383] using wordTrace_append hprefix tailTrace_1240383
  have hstable : (prefixWord ++ tailWord_1240383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240383).length < 2 ^ (prefixWord ++ tailWord_1240383).sum := by decide
  have hdescent : baseEnd_1240383 < baseStart_1240383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240409 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 2, 6]
def baseStart_1240409 : Nat := 118140960795 + 1240409 * 2 ^ 59
def prefixEnd_1240409 : Nat := 4983230072969 + 3 ^ 40 * 1240409 * 2
def baseEnd_1240409 : Nat := 424617350108628418521979

theorem tailTrace_1240409 : CollatzResearch.WordTrace tailWord_1240409 prefixEnd_1240409 424617350108628418521979 := by
  unfold tailWord_1240409
  simp only [CollatzResearch.WordTrace]
  refine ⟨45241432963217512836468281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30160955308811675224312187 45241432963217512836468281)
  ·
    refine ⟨33931074722413134627351211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45241432963217512836468281 33931074722413134627351211)
    ·
      refine ⟨50896612083619701941026817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33931074722413134627351211 50896612083619701941026817)
      ·
        refine ⟨38172459062714776455770113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50896612083619701941026817 38172459062714776455770113)
        ·
          refine ⟨28629344297036082341827585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38172459062714776455770113 28629344297036082341827585)
          ·
            refine ⟨21472008222777061756370689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28629344297036082341827585 21472008222777061756370689)
            ·
              refine ⟨16104006167082796317278017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21472008222777061756370689 16104006167082796317278017)
              ·
                refine ⟨12078004625312097237958513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16104006167082796317278017 12078004625312097237958513)
                ·
                  refine ⟨9058503468984072928468885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12078004625312097237958513 9058503468984072928468885)
                  ·
                    refine ⟨424617350108628418521979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9058503468984072928468885 424617350108628418521979)
                    ·
                      rfl

theorem cell22_1240409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_1240409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240409 prefixEnd_1240409 := by exact prefixLift 1240409
  have htrace : WordTrace (prefixWord ++ tailWord_1240409) baseStart_1240409 baseEnd_1240409 := by
    simpa [prefixWord, tailWord_1240409, baseEnd_1240409] using wordTrace_append hprefix tailTrace_1240409
  have hstable : (prefixWord ++ tailWord_1240409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240409).length < 2 ^ (prefixWord ++ tailWord_1240409).sum := by decide
  have hdescent : baseEnd_1240409 < baseStart_1240409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240430 : List Nat := [4, 1, 2, 4, 2, 1, 8]
def baseStart_1240430 : Nat := 118140960795 + 1240430 * 2 ^ 59
def prefixEnd_1240430 : Nat := 4983230072969 + 3 ^ 40 * 1240430 * 2
def baseEnd_1240430 : Nat := 15726834771770050509145

theorem tailTrace_1240430 : CollatzResearch.WordTrace tailWord_1240430 prefixEnd_1240430 15726834771770050509145 := by
  unfold tailWord_1240430
  simp only [CollatzResearch.WordTrace]
  refine ⟨5655274862017679177872843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30161465930760955615321829 5655274862017679177872843)
  ·
    refine ⟨8482912293026518766809265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5655274862017679177872843 8482912293026518766809265)
    ·
      refine ⟨6362184219769889075106949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8482912293026518766809265 6362184219769889075106949)
      ·
        refine ⟨1192909541206854201582553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6362184219769889075106949 1192909541206854201582553)
        ·
          refine ⟨894682155905140651186915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1192909541206854201582553 894682155905140651186915)
          ·
            refine ⟨1342023233857710976780373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894682155905140651186915 1342023233857710976780373)
            ·
              refine ⟨15726834771770050509145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1342023233857710976780373 15726834771770050509145)
              ·
                rfl

theorem cell22_1240430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 8].length) (baseStart_1240430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240430 prefixEnd_1240430 := by exact prefixLift 1240430
  have htrace : WordTrace (prefixWord ++ tailWord_1240430) baseStart_1240430 baseEnd_1240430 := by
    simpa [prefixWord, tailWord_1240430, baseEnd_1240430] using wordTrace_append hprefix tailTrace_1240430
  have hstable : (prefixWord ++ tailWord_1240430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240430).length < 2 ^ (prefixWord ++ tailWord_1240430).sum := by decide
  have hdescent : baseEnd_1240430 < baseStart_1240430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240503 : List Nat := [1, 1, 3, 1, 3, 2, 3, 4, 4]
def baseStart_1240503 : Nat := 118140960795 + 1240503 * 2 ^ 59
def prefixEnd_1240503 : Nat := 4983230072969 + 3 ^ 40 * 1240503 * 2
def baseEnd_1240503 : Nat := 141549842743214502223897

theorem tailTrace_1240503 : CollatzResearch.WordTrace tailWord_1240503 prefixEnd_1240503 141549842743214502223897 := by
  unfold tailWord_1240503
  simp only [CollatzResearch.WordTrace]
  refine ⟨45244861424876966890390163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30163240949917977926926775 45244861424876966890390163)
  ·
    refine ⟨67867292137315450335585245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45244861424876966890390163 67867292137315450335585245)
    ·
      refine ⟨25450234551493293875844467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67867292137315450335585245 25450234551493293875844467)
      ·
        refine ⟨38175351827239940813766701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25450234551493293875844467 38175351827239940813766701)
        ·
          refine ⟨14315756935214977805162513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38175351827239940813766701 14315756935214977805162513)
          ·
            refine ⟨10736817701411233353871885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14315756935214977805162513 10736817701411233353871885)
            ·
              refine ⟨4026306638029212507701957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10736817701411233353871885 4026306638029212507701957)
              ·
                refine ⟨754932494630477345194117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4026306638029212507701957 754932494630477345194117)
                ·
                  refine ⟨141549842743214502223897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 754932494630477345194117 141549842743214502223897)
                  ·
                    rfl

theorem cell22_1240503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 4].length) (baseStart_1240503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240503 prefixEnd_1240503 := by exact prefixLift 1240503
  have htrace : WordTrace (prefixWord ++ tailWord_1240503) baseStart_1240503 baseEnd_1240503 := by
    simpa [prefixWord, tailWord_1240503, baseEnd_1240503] using wordTrace_append hprefix tailTrace_1240503
  have hstable : (prefixWord ++ tailWord_1240503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240503).length < 2 ^ (prefixWord ++ tailWord_1240503).sum := by decide
  have hdescent : baseEnd_1240503 < baseStart_1240503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240597 : List Nat := [1, 3, 2, 1, 3, 2, 3, 3, 1, 3]
def baseStart_1240597 : Nat := 118140960795 + 1240597 * 2 ^ 59
def prefixEnd_1240597 : Nat := 4983230072969 + 3 ^ 40 * 1240597 * 2
def baseEnd_1240597 : Nat := 424681706350658594821403

theorem tailTrace_1240597 : CollatzResearch.WordTrace tailWord_1240597 prefixEnd_1240597 424681706350658594821403 := by
  unfold tailWord_1240597
  simp only [CollatzResearch.WordTrace]
  refine ⟨45248289886536420944312045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30165526591024280629541363 45248289886536420944312045)
  ·
    refine ⟨16968108707451157854117017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45248289886536420944312045 16968108707451157854117017)
    ·
      refine ⟨12726081530588368390587763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16968108707451157854117017 12726081530588368390587763)
      ·
        refine ⟨19089122295882552585881645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12726081530588368390587763 19089122295882552585881645)
        ·
          refine ⟨7158420860955957219705617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19089122295882552585881645 7158420860955957219705617)
          ·
            refine ⟨5368815645716967914779213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7158420860955957219705617 5368815645716967914779213)
            ·
              refine ⟨2013305867143862968042205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5368815645716967914779213 2013305867143862968042205)
              ·
                refine ⟨754989700178948613015827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2013305867143862968042205 754989700178948613015827)
                ·
                  refine ⟨1132484550268422919523741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754989700178948613015827 1132484550268422919523741)
                  ·
                    refine ⟨424681706350658594821403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1132484550268422919523741 424681706350658594821403)
                    ·
                      rfl

theorem cell22_1240597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_1240597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240597 prefixEnd_1240597 := by exact prefixLift 1240597
  have htrace : WordTrace (prefixWord ++ tailWord_1240597) baseStart_1240597 baseEnd_1240597 := by
    simpa [prefixWord, tailWord_1240597, baseEnd_1240597] using wordTrace_append hprefix tailTrace_1240597
  have hstable : (prefixWord ++ tailWord_1240597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240597).length < 2 ^ (prefixWord ++ tailWord_1240597).sum := by decide
  have hdescent : baseEnd_1240597 < baseStart_1240597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240766 : List Nat := [4, 2, 1, 1, 2, 4, 1, 3, 1, 3]
def baseStart_1240766 : Nat := 118140960795 + 1240766 * 2 ^ 59
def prefixEnd_1240766 : Nat := 4983230072969 + 3 ^ 40 * 1240766 * 2
def baseEnd_1240766 : Nat := 424739558504398487345885

theorem tailTrace_1240766 : CollatzResearch.WordTrace tailWord_1240766 prefixEnd_1240766 424739558504398487345885 := by
  unfold tailWord_1240766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5656806727865520350901769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30169635881949441871476101 5656806727865520350901769)
  ·
    refine ⟨4242605045899140263176327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5656806727865520350901769 4242605045899140263176327)
    ·
      refine ⟨6363907568848710394764491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4242605045899140263176327 6363907568848710394764491)
      ·
        refine ⟨9545861353273065592146737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6363907568848710394764491 9545861353273065592146737)
        ·
          refine ⟨7159396014954799194110053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9545861353273065592146737 7159396014954799194110053)
          ·
            refine ⟨1342386752804024848895635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7159396014954799194110053 1342386752804024848895635)
            ·
              refine ⟨2013580129206037273343453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1342386752804024848895635 2013580129206037273343453)
              ·
                refine ⟨755092548452263977503795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2013580129206037273343453 755092548452263977503795)
                ·
                  refine ⟨1132638822678395966255693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 755092548452263977503795 1132638822678395966255693)
                  ·
                    refine ⟨424739558504398487345885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1132638822678395966255693 424739558504398487345885)
                    ·
                      rfl

theorem cell22_1240766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_1240766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240766 prefixEnd_1240766 := by exact prefixLift 1240766
  have htrace : WordTrace (prefixWord ++ tailWord_1240766) baseStart_1240766 baseEnd_1240766 := by
    simpa [prefixWord, tailWord_1240766, baseEnd_1240766] using wordTrace_append hprefix tailTrace_1240766
  have hstable : (prefixWord ++ tailWord_1240766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240766).length < 2 ^ (prefixWord ++ tailWord_1240766).sum := by decide
  have hdescent : baseEnd_1240766 < baseStart_1240766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240775 : List Nat := [1, 1, 4, 1, 1, 1, 3, 5, 1, 4]
def baseStart_1240775 : Nat := 118140960795 + 1240775 * 2 ^ 59
def prefixEnd_1240775 : Nat := 4983230072969 + 3 ^ 40 * 1240775 * 2
def baseEnd_1240775 : Nat := 424742639388325463870857

theorem tailTrace_1240775 : CollatzResearch.WordTrace tailWord_1240775 prefixEnd_1240775 424742639388325463870857 := by
  unfold tailWord_1240775
  simp only [CollatzResearch.WordTrace]
  refine ⟨45254782079891557344291779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30169854719927704896194519 45254782079891557344291779)
  ·
    refine ⟨67882173119837336016437669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45254782079891557344291779 67882173119837336016437669)
    ·
      refine ⟨12727907459969500503082063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67882173119837336016437669 12727907459969500503082063)
      ·
        refine ⟨19091861189954250754623095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12727907459969500503082063 19091861189954250754623095)
        ·
          refine ⟨28637791784931376131934643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19091861189954250754623095 28637791784931376131934643)
          ·
            refine ⟨42956687677397064197901965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28637791784931376131934643 42956687677397064197901965)
            ·
              refine ⟨16108757879023899074213237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42956687677397064197901965 16108757879023899074213237)
              ·
                refine ⟨1510196051158490538207491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16108757879023899074213237 1510196051158490538207491)
                ·
                  refine ⟨2265294076737735807311237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1510196051158490538207491 2265294076737735807311237)
                  ·
                    refine ⟨424742639388325463870857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2265294076737735807311237 424742639388325463870857)
                    ·
                      rfl

theorem cell22_1240775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_1240775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240775 prefixEnd_1240775 := by exact prefixLift 1240775
  have htrace : WordTrace (prefixWord ++ tailWord_1240775) baseStart_1240775 baseEnd_1240775 := by
    simpa [prefixWord, tailWord_1240775, baseEnd_1240775] using wordTrace_append hprefix tailTrace_1240775
  have hstable : (prefixWord ++ tailWord_1240775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240775).length < 2 ^ (prefixWord ++ tailWord_1240775).sum := by decide
  have hdescent : baseEnd_1240775 < baseStart_1240775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240796 : List Nat := [2, 2, 5, 1, 2, 2, 2, 1, 5]
def baseStart_1240796 : Nat := 118140960795 + 1240796 * 2 ^ 59
def prefixEnd_1240796 : Nat := 4983230072969 + 3 ^ 40 * 1240796 * 2
def baseEnd_1240796 : Nat := 141583276039162803031931

theorem tailTrace_1240796 : CollatzResearch.WordTrace tailWord_1240796 prefixEnd_1240796 141583276039162803031931 := by
  unfold tailWord_1240796
  simp only [CollatzResearch.WordTrace]
  refine ⟨22627774006407738965403121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30170365341876985287204161 22627774006407738965403121)
  ·
    refine ⟨16970830504805804224052341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22627774006407738965403121 16970830504805804224052341)
    ·
      refine ⟨1591015359825544146004907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16970830504805804224052341 1591015359825544146004907)
      ·
        refine ⟨2386523039738316219007361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1591015359825544146004907 2386523039738316219007361)
        ·
          refine ⟨1789892279803737164255521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2386523039738316219007361 1789892279803737164255521)
          ·
            refine ⟨1342419209852802873191641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1789892279803737164255521 1342419209852802873191641)
            ·
              refine ⟨1006814407389602154893731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1342419209852802873191641 1006814407389602154893731)
              ·
                refine ⟨1510221611084403232340597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1006814407389602154893731 1510221611084403232340597)
                ·
                  refine ⟨141583276039162803031931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1510221611084403232340597 141583276039162803031931)
                  ·
                    rfl

theorem cell22_1240796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 5].length) (baseStart_1240796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240796 prefixEnd_1240796 := by exact prefixLift 1240796
  have htrace : WordTrace (prefixWord ++ tailWord_1240796) baseStart_1240796 baseEnd_1240796 := by
    simpa [prefixWord, tailWord_1240796, baseEnd_1240796] using wordTrace_append hprefix tailTrace_1240796
  have hstable : (prefixWord ++ tailWord_1240796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240796).length < 2 ^ (prefixWord ++ tailWord_1240796).sum := by decide
  have hdescent : baseEnd_1240796 < baseStart_1240796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240805 : List Nat := [1, 3, 1, 4, 1, 1, 2, 3, 1, 5]
def baseStart_1240805 : Nat := 118140960795 + 1240805 * 2 ^ 59
def prefixEnd_1240805 : Nat := 4983230072969 + 3 ^ 40 * 1240805 * 2
def baseEnd_1240805 : Nat := 424752909001415385620765

theorem tailTrace_1240805 : CollatzResearch.WordTrace tailWord_1240805 prefixEnd_1240805 424752909001415385620765 := by
  unfold tailWord_1240805
  simp only [CollatzResearch.WordTrace]
  refine ⟨45255876269782872467883869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30170584179855248311922579 45255876269782872467883869)
  ·
    refine ⟨16970953601168577175456451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45255876269782872467883869 16970953601168577175456451)
    ·
      refine ⟨25456430401752865763184677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16970953601168577175456451 25456430401752865763184677)
      ·
        refine ⟨4773080700328662330597127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25456430401752865763184677 4773080700328662330597127)
        ·
          refine ⟨7159621050492993495895691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4773080700328662330597127 7159621050492993495895691)
          ·
            refine ⟨10739431575739490243843537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7159621050492993495895691 10739431575739490243843537)
            ·
              refine ⟨8054573681804617682882653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10739431575739490243843537 8054573681804617682882653)
              ·
                refine ⟨3020465130676731631080995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8054573681804617682882653 3020465130676731631080995)
                ·
                  refine ⟨4530697696015097446621493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3020465130676731631080995 4530697696015097446621493)
                  ·
                    refine ⟨424752909001415385620765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4530697696015097446621493 424752909001415385620765)
                    ·
                      rfl

theorem cell22_1240805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_1240805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240805 prefixEnd_1240805 := by exact prefixLift 1240805
  have htrace : WordTrace (prefixWord ++ tailWord_1240805) baseStart_1240805 baseEnd_1240805 := by
    simpa [prefixWord, tailWord_1240805, baseEnd_1240805] using wordTrace_append hprefix tailTrace_1240805
  have hstable : (prefixWord ++ tailWord_1240805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240805).length < 2 ^ (prefixWord ++ tailWord_1240805).sum := by decide
  have hdescent : baseEnd_1240805 < baseStart_1240805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240822 : List Nat := [5, 1, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_1240822 : Nat := 118140960795 + 1240822 * 2 ^ 59
def prefixEnd_1240822 : Nat := 4983230072969 + 3 ^ 40 * 1240822 * 2
def baseEnd_1240822 : Nat := 424758728448833007945713

theorem tailTrace_1240822 : CollatzResearch.WordTrace tailWord_1240822 prefixEnd_1240822 424758728448833007945713 := by
  unfold tailWord_1240822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2828531019420080273203295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30170997540480856247501813 2828531019420080273203295)
  ·
    refine ⟨4242796529130120409804943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2828531019420080273203295 4242796529130120409804943)
    ·
      refine ⟨6364194793695180614707415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4242796529130120409804943 6364194793695180614707415)
      ·
        refine ⟨9546292190542770922061123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6364194793695180614707415 9546292190542770922061123)
        ·
          refine ⟨14319438285814156383091685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9546292190542770922061123 14319438285814156383091685)
          ·
            refine ⟨2684894678590154321829691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14319438285814156383091685 2684894678590154321829691)
            ·
              refine ⟨4027342017885231482744537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2684894678590154321829691 4027342017885231482744537)
              ·
                refine ⟨3020506513413923612058403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4027342017885231482744537 3020506513413923612058403)
                ·
                  refine ⟨4530759770120885418087605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3020506513413923612058403 4530759770120885418087605)
                  ·
                    refine ⟨424758728448833007945713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4530759770120885418087605 424758728448833007945713)
                    ·
                      rfl

theorem cell22_1240822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_1240822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240822 prefixEnd_1240822 := by exact prefixLift 1240822
  have htrace : WordTrace (prefixWord ++ tailWord_1240822) baseStart_1240822 baseEnd_1240822 := by
    simpa [prefixWord, tailWord_1240822, baseEnd_1240822] using wordTrace_append hprefix tailTrace_1240822
  have hstable : (prefixWord ++ tailWord_1240822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240822).length < 2 ^ (prefixWord ++ tailWord_1240822).sum := by decide
  have hdescent : baseEnd_1240822 < baseStart_1240822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240914 : List Nat := [3, 2, 2, 1, 1, 4, 3, 1, 5]
def baseStart_1240914 : Nat := 118140960795 + 1240914 * 2 ^ 59
def prefixEnd_1240914 : Nat := 4983230072969 + 3 ^ 40 * 1240914 * 2
def baseEnd_1240914 : Nat := 141596740642991811548477

theorem tailTrace_1240914 : CollatzResearch.WordTrace tailWord_1240914 prefixEnd_1240914 141596740642991811548477 := by
  unfold tailWord_1240914
  simp only [CollatzResearch.WordTrace]
  refine ⟨11314962956596996020900449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30173234550925322722401197 11314962956596996020900449)
  ·
    refine ⟨8486222217447747015675337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11314962956596996020900449 8486222217447747015675337)
    ·
      refine ⟨6364666663085810261756503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8486222217447747015675337 6364666663085810261756503)
      ·
        refine ⟨9546999994628715392634755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6364666663085810261756503 9546999994628715392634755)
        ·
          refine ⟨14320499991943073088952133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9546999994628715392634755 14320499991943073088952133)
          ·
            refine ⟨2685093748489326204178525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14320499991943073088952133 2685093748489326204178525)
            ·
              refine ⟨1006910155683497326566947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2685093748489326204178525 1006910155683497326566947)
              ·
                refine ⟨1510365233525245989850421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1006910155683497326566947 1510365233525245989850421)
                ·
                  refine ⟨141596740642991811548477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1510365233525245989850421 141596740642991811548477)
                  ·
                    rfl

theorem cell22_1240914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_1240914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240914 prefixEnd_1240914 := by exact prefixLift 1240914
  have htrace : WordTrace (prefixWord ++ tailWord_1240914) baseStart_1240914 baseEnd_1240914 := by
    simpa [prefixWord, tailWord_1240914, baseEnd_1240914] using wordTrace_append hprefix tailTrace_1240914
  have hstable : (prefixWord ++ tailWord_1240914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240914).length < 2 ^ (prefixWord ++ tailWord_1240914).sum := by decide
  have hdescent : baseEnd_1240914 < baseStart_1240914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240927 : List Nat := [1, 1, 2, 3, 1, 4, 1, 4, 1, 4]
def baseStart_1240927 : Nat := 118140960795 + 1240927 * 2 ^ 59
def prefixEnd_1240927 : Nat := 4983230072969 + 3 ^ 40 * 1240927 * 2
def baseEnd_1240927 : Nat := 424794672094647734070391

theorem tailTrace_1240927 : CollatzResearch.WordTrace tailWord_1240927 prefixEnd_1240927 424794672094647734070391 := by
  unfold tailWord_1240927
  simp only [CollatzResearch.WordTrace]
  refine ⟨45260325975340887303825035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30173550650227258202550023 45260325975340887303825035)
  ·
    refine ⟨67890488963011330955737553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45260325975340887303825035 67890488963011330955737553)
    ·
      refine ⟨50917866722258498216803165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67890488963011330955737553 50917866722258498216803165)
      ·
        refine ⟨19094200020846936831301187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50917866722258498216803165 19094200020846936831301187)
        ·
          refine ⟨28641300031270405246951781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19094200020846936831301187 28641300031270405246951781)
          ·
            refine ⟨5370243755863200983803459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28641300031270405246951781 5370243755863200983803459)
            ·
              refine ⟨8055365633794801475705189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5370243755863200983803459 8055365633794801475705189)
              ·
                refine ⟨1510381056336525276694723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8055365633794801475705189 1510381056336525276694723)
                ·
                  refine ⟨2265571584504787915042085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1510381056336525276694723 2265571584504787915042085)
                  ·
                    refine ⟨424794672094647734070391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2265571584504787915042085 424794672094647734070391)
                    ·
                      rfl

theorem cell22_1240927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 4].length) (baseStart_1240927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240927 prefixEnd_1240927 := by exact prefixLift 1240927
  have htrace : WordTrace (prefixWord ++ tailWord_1240927) baseStart_1240927 baseEnd_1240927 := by
    simpa [prefixWord, tailWord_1240927, baseEnd_1240927] using wordTrace_append hprefix tailTrace_1240927
  have hstable : (prefixWord ++ tailWord_1240927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240927).length < 2 ^ (prefixWord ++ tailWord_1240927).sum := by decide
  have hdescent : baseEnd_1240927 < baseStart_1240927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240985 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 2, 7]
def baseStart_1240985 : Nat := 118140960795 + 1240985 * 2 ^ 59
def prefixEnd_1240985 : Nat := 4983230072969 + 3 ^ 40 * 1240985 * 2
def baseEnd_1240985 : Nat := 424814526679954916120213

theorem tailTrace_1240985 : CollatzResearch.WordTrace tailWord_1240985 prefixEnd_1240985 424814526679954916120213 := by
  unfold tailWord_1240985
  simp only [CollatzResearch.WordTrace]
  refine ⟨45262441409130763209436409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30174960939420508806290939 45262441409130763209436409)
  ·
    refine ⟨33946831056848072407077307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45262441409130763209436409 33946831056848072407077307)
    ·
      refine ⟨50920246585272108610615961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33946831056848072407077307 50920246585272108610615961)
      ·
        refine ⟨38190184938954081457961971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50920246585272108610615961 38190184938954081457961971)
        ·
          refine ⟨57285277408431122186942957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38190184938954081457961971 57285277408431122186942957)
          ·
            refine ⟨21481979028161670820103609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57285277408431122186942957 21481979028161670820103609)
            ·
              refine ⟨16111484271121253115077707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21481979028161670820103609 16111484271121253115077707)
              ·
                refine ⟨24167226406681879672616561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16111484271121253115077707 24167226406681879672616561)
                ·
                  refine ⟨18125419805011409754462421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24167226406681879672616561 18125419805011409754462421)
                  ·
                    refine ⟨424814526679954916120213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18125419805011409754462421 424814526679954916120213)
                    ·
                      rfl

theorem cell22_1240985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_1240985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240985 prefixEnd_1240985 := by exact prefixLift 1240985
  have htrace : WordTrace (prefixWord ++ tailWord_1240985) baseStart_1240985 baseEnd_1240985 := by
    simpa [prefixWord, tailWord_1240985, baseEnd_1240985] using wordTrace_append hprefix tailTrace_1240985
  have hstable : (prefixWord ++ tailWord_1240985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240985).length < 2 ^ (prefixWord ++ tailWord_1240985).sum := by decide
  have hdescent : baseEnd_1240985 < baseStart_1240985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240989 : List Nat := [1, 4, 2, 1, 2, 3, 2, 1, 2, 4]
def baseStart_1240989 : Nat := 118140960795 + 1240989 * 2 ^ 59
def prefixEnd_1240989 : Nat := 4983230072969 + 3 ^ 40 * 1240989 * 2
def baseEnd_1240989 : Nat := 424815895961700239020201

theorem tailTrace_1240989 : CollatzResearch.WordTrace tailWord_1240989 prefixEnd_1240989 424815895961700239020201 := by
  unfold tailWord_1240989
  simp only [CollatzResearch.WordTrace]
  refine ⟨45262587301116271892582021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30175058200744181261721347 45262587301116271892582021)
  ·
    refine ⟨8486735118959300979859129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45262587301116271892582021 8486735118959300979859129)
    ·
      refine ⟨6365051339219475734894347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8486735118959300979859129 6365051339219475734894347)
      ·
        refine ⟨9547577008829213602341521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6365051339219475734894347 9547577008829213602341521)
        ·
          refine ⟨7160682756621910201756141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9547577008829213602341521 7160682756621910201756141)
          ·
            refine ⟨2685256033733216325658553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7160682756621910201756141 2685256033733216325658553)
            ·
              refine ⟨2013942025299912244243915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2685256033733216325658553 2013942025299912244243915)
              ·
                refine ⟨3020913037949868366365873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2013942025299912244243915 3020913037949868366365873)
                ·
                  refine ⟨2265684778462401274774405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3020913037949868366365873 2265684778462401274774405)
                  ·
                    refine ⟨424815895961700239020201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2265684778462401274774405 424815895961700239020201)
                    ·
                      rfl

theorem cell22_1240989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_1240989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1240989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1240989 prefixEnd_1240989 := by exact prefixLift 1240989
  have htrace : WordTrace (prefixWord ++ tailWord_1240989) baseStart_1240989 baseEnd_1240989 := by
    simpa [prefixWord, tailWord_1240989, baseEnd_1240989] using wordTrace_append hprefix tailTrace_1240989
  have hstable : (prefixWord ++ tailWord_1240989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240989).length < 2 ^ (prefixWord ++ tailWord_1240989).sum := by decide
  have hdescent : baseEnd_1240989 < baseStart_1240989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241107 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 1, 6]
def baseStart_1241107 : Nat := 118140960795 + 1241107 * 2 ^ 59
def prefixEnd_1241107 : Nat := 4983230072969 + 3 ^ 40 * 1241107 * 2
def baseEnd_1241107 : Nat := 424856289773187264569839

theorem tailTrace_1241107 : CollatzResearch.WordTrace tailWord_1241107 prefixEnd_1241107 424856289773187264569839 := by
  unfold tailWord_1241107
  simp only [CollatzResearch.WordTrace]
  refine ⟨45266891114688778045377575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30177927409792518696918383 45266891114688778045377575)
  ·
    refine ⟨67900336672033167068066363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45266891114688778045377575 67900336672033167068066363)
    ·
      refine ⟨101850505008049750602099545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67900336672033167068066363 101850505008049750602099545)
      ·
        refine ⟨76387878756037312951574659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101850505008049750602099545 76387878756037312951574659)
        ·
          refine ⟨114581818134055969427361989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76387878756037312951574659 114581818134055969427361989)
          ·
            refine ⟨21484090900135494267630373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114581818134055969427361989 21484090900135494267630373)
            ·
              refine ⟨4028267043775405175180695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21484090900135494267630373 4028267043775405175180695)
              ·
                refine ⟨6042400565663107762771043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4028267043775405175180695 6042400565663107762771043)
                ·
                  refine ⟨9063600848494661644156565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6042400565663107762771043 9063600848494661644156565)
                  ·
                    refine ⟨424856289773187264569839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9063600848494661644156565 424856289773187264569839)
                    ·
                      rfl

theorem cell22_1241107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 6].length) (baseStart_1241107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241107 prefixEnd_1241107 := by exact prefixLift 1241107
  have htrace : WordTrace (prefixWord ++ tailWord_1241107) baseStart_1241107 baseEnd_1241107 := by
    simpa [prefixWord, tailWord_1241107, baseEnd_1241107] using wordTrace_append hprefix tailTrace_1241107
  have hstable : (prefixWord ++ tailWord_1241107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241107).length < 2 ^ (prefixWord ++ tailWord_1241107).sum := by decide
  have hdescent : baseEnd_1241107 < baseStart_1241107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241128 : List Nat := [2, 1, 5, 3, 1, 2, 1, 1, 6]
def baseStart_1241128 : Nat := 118140960795 + 1241128 * 2 ^ 59
def prefixEnd_1241128 : Nat := 4983230072969 + 3 ^ 40 * 1241128 * 2
def baseEnd_1241128 : Nat := 141621159500783403264925

theorem tailTrace_1241128 : CollatzResearch.WordTrace tailWord_1241128 prefixEnd_1241128 141621159500783403264925 := by
  unfold tailWord_1241128
  simp only [CollatzResearch.WordTrace]
  refine ⟨22633828523806349315946019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30178438031741799087928025 22633828523806349315946019)
  ·
    refine ⟨33950742785709523973919029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22633828523806349315946019 33950742785709523973919029)
    ·
      refine ⟨3182882136160267872554909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33950742785709523973919029 3182882136160267872554909)
      ·
        refine ⟨1193580801060100452208091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3182882136160267872554909 1193580801060100452208091)
        ·
          refine ⟨1790371201590150678312137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1193580801060100452208091 1790371201590150678312137)
          ·
            refine ⟨1342778401192613008734103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1790371201590150678312137 1342778401192613008734103)
            ·
              refine ⟨2014167601788919513101155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1342778401192613008734103 2014167601788919513101155)
              ·
                refine ⟨3021251402683379269651733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2014167601788919513101155 3021251402683379269651733)
                ·
                  refine ⟨141621159500783403264925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3021251402683379269651733 141621159500783403264925)
                  ·
                    rfl

theorem cell22_1241128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 6].length) (baseStart_1241128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241128 prefixEnd_1241128 := by exact prefixLift 1241128
  have htrace : WordTrace (prefixWord ++ tailWord_1241128) baseStart_1241128 baseEnd_1241128 := by
    simpa [prefixWord, tailWord_1241128, baseEnd_1241128] using wordTrace_append hprefix tailTrace_1241128
  have hstable : (prefixWord ++ tailWord_1241128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241128).length < 2 ^ (prefixWord ++ tailWord_1241128).sum := by decide
  have hdescent : baseEnd_1241128 < baseStart_1241128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241158 : List Nat := [6, 1, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_1241158 : Nat := 118140960795 + 1241158 * 2 ^ 59
def prefixEnd_1241158 : Nat := 4983230072969 + 3 ^ 40 * 1241158 * 2
def baseEnd_1241158 : Nat := 424873748115440131544683

theorem tailTrace_1241158 : CollatzResearch.WordTrace tailWord_1241158 prefixEnd_1241158 424873748115440131544683 := by
  unfold tailWord_1241158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1414648476172000429858879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30179167491669342503656085 1414648476172000429858879)
  ·
    refine ⟨2121972714258000644788319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1414648476172000429858879 2121972714258000644788319)
    ·
      refine ⟨3182959071387000967182479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2121972714258000644788319 3182959071387000967182479)
      ·
        refine ⟨4774438607080501450773719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3182959071387000967182479 4774438607080501450773719)
        ·
          refine ⟨7161657910620752176160579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4774438607080501450773719 7161657910620752176160579)
          ·
            refine ⟨10742486865931128264240869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7161657910620752176160579 10742486865931128264240869)
            ·
              refine ⟨2014216287362086549545163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10742486865931128264240869 2014216287362086549545163)
              ·
                refine ⟨3021324431043129824317745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2014216287362086549545163 3021324431043129824317745)
                ·
                  refine ⟨2265993323282347368238309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3021324431043129824317745 2265993323282347368238309)
                  ·
                    refine ⟨424873748115440131544683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2265993323282347368238309 424873748115440131544683)
                    ·
                      rfl

theorem cell22_1241158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_1241158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241158 prefixEnd_1241158 := by exact prefixLift 1241158
  have htrace : WordTrace (prefixWord ++ tailWord_1241158) baseStart_1241158 baseEnd_1241158 := by
    simpa [prefixWord, tailWord_1241158, baseEnd_1241158] using wordTrace_append hprefix tailTrace_1241158
  have hstable : (prefixWord ++ tailWord_1241158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241158).length < 2 ^ (prefixWord ++ tailWord_1241158).sum := by decide
  have hdescent : baseEnd_1241158 < baseStart_1241158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241184 : List Nat := [2, 1, 1, 3, 2, 3, 1, 4, 5]
def baseStart_1241184 : Nat := 118140960795 + 1241184 * 2 ^ 59
def prefixEnd_1241184 : Nat := 4983230072969 + 3 ^ 40 * 1241184 * 2
def baseEnd_1241184 : Nat := 141627549482261576798201

theorem tailTrace_1241184 : CollatzResearch.WordTrace tailWord_1241184 prefixEnd_1241184 141627549482261576798201 := by
  unfold tailWord_1241184
  simp only [CollatzResearch.WordTrace]
  refine ⟨22634849767704910097965303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30179799690273213463953737 22634849767704910097965303)
  ·
    refine ⟨33952274651557365146947955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22634849767704910097965303 33952274651557365146947955)
    ·
      refine ⟨50928411977336047720421933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33952274651557365146947955 50928411977336047720421933)
      ·
        refine ⟨19098154491501017895158225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50928411977336047720421933 19098154491501017895158225)
        ·
          refine ⟨14323615868625763421368669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19098154491501017895158225 14323615868625763421368669)
          ·
            refine ⟨5371355950734661283013251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14323615868625763421368669 5371355950734661283013251)
            ·
              refine ⟨8057033926101991924519877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5371355950734661283013251 8057033926101991924519877)
              ·
                refine ⟨1510693861144123485847477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8057033926101991924519877 1510693861144123485847477)
                ·
                  refine ⟨141627549482261576798201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1510693861144123485847477 141627549482261576798201)
                  ·
                    rfl

theorem cell22_1241184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 5].length) (baseStart_1241184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241184 prefixEnd_1241184 := by exact prefixLift 1241184
  have htrace : WordTrace (prefixWord ++ tailWord_1241184) baseStart_1241184 baseEnd_1241184 := by
    simpa [prefixWord, tailWord_1241184, baseEnd_1241184] using wordTrace_append hprefix tailTrace_1241184
  have hstable : (prefixWord ++ tailWord_1241184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241184).length < 2 ^ (prefixWord ++ tailWord_1241184).sum := by decide
  have hdescent : baseEnd_1241184 < baseStart_1241184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241199 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 2, 5]
def baseStart_1241199 : Nat := 118140960795 + 1241199 * 2 ^ 59
def prefixEnd_1241199 : Nat := 4983230072969 + 3 ^ 40 * 1241199 * 2
def baseEnd_1241199 : Nat := 424887783253329691269557

theorem tailTrace_1241199 : CollatzResearch.WordTrace tailWord_1241199 prefixEnd_1241199 424887783253329691269557 := by
  unfold tailWord_1241199
  simp only [CollatzResearch.WordTrace]
  refine ⟨45270246630355477757726651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30180164420236985171817767 45270246630355477757726651)
  ·
    refine ⟨67905369945533216636589977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45270246630355477757726651 67905369945533216636589977)
    ·
      refine ⟨50929027459149912477442483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67905369945533216636589977 50929027459149912477442483)
      ·
        refine ⟨76393541188724868716163725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50929027459149912477442483 76393541188724868716163725)
        ·
          refine ⟨28647577945771825768561397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76393541188724868716163725 28647577945771825768561397)
          ·
            refine ⟨2685710432416108665802631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28647577945771825768561397 2685710432416108665802631)
            ·
              refine ⟨4028565648624162998703947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2685710432416108665802631 4028565648624162998703947)
              ·
                refine ⟨6042848472936244498055921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4028565648624162998703947 6042848472936244498055921)
                ·
                  refine ⟨4532136354702183373541941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6042848472936244498055921 4532136354702183373541941)
                  ·
                    refine ⟨424887783253329691269557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4532136354702183373541941 424887783253329691269557)
                    ·
                      rfl

theorem cell22_1241199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 5].length) (baseStart_1241199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241199 prefixEnd_1241199 := by exact prefixLift 1241199
  have htrace : WordTrace (prefixWord ++ tailWord_1241199) baseStart_1241199 baseEnd_1241199 := by
    simpa [prefixWord, tailWord_1241199, baseEnd_1241199] using wordTrace_append hprefix tailTrace_1241199
  have hstable : (prefixWord ++ tailWord_1241199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241199).length < 2 ^ (prefixWord ++ tailWord_1241199).sum := by decide
  have hdescent : baseEnd_1241199 < baseStart_1241199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241411 : List Nat := [1, 1, 1, 3, 1, 3, 2, 4, 2, 4]
def baseStart_1241411 : Nat := 118140960795 + 1241411 * 2 ^ 59
def prefixEnd_1241411 : Nat := 4983230072969 + 3 ^ 40 * 1241411 * 2
def baseEnd_1241411 : Nat := 424960355185831804968907

theorem tailTrace_1241411 : CollatzResearch.WordTrace tailWord_1241411 prefixEnd_1241411 424960355185831804968907 := by
  unfold tailWord_1241411
  simp only [CollatzResearch.WordTrace]
  refine ⟨45277978905587437964444087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30185319270391625309629391 45277978905587437964444087)
  ·
    refine ⟨67916968358381156946666131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45277978905587437964444087 67916968358381156946666131)
    ·
      refine ⟨101875452537571735419999197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67916968358381156946666131 101875452537571735419999197)
      ·
        refine ⟨38203294701589400782499699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101875452537571735419999197 38203294701589400782499699)
        ·
          refine ⟨57304942052384101173749549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38203294701589400782499699 57304942052384101173749549)
          ·
            refine ⟨21489353269644037940156081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57304942052384101173749549 21489353269644037940156081)
            ·
              refine ⟨16117014952233028455117061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21489353269644037940156081 16117014952233028455117061)
              ·
                refine ⟨3021940303543692835334449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16117014952233028455117061 3021940303543692835334449)
                ·
                  refine ⟨2266455227657769626500837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3021940303543692835334449 2266455227657769626500837)
                  ·
                    refine ⟨424960355185831804968907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2266455227657769626500837 424960355185831804968907)
                    ·
                      rfl

theorem cell22_1241411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 4].length) (baseStart_1241411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241411 prefixEnd_1241411 := by exact prefixLift 1241411
  have htrace : WordTrace (prefixWord ++ tailWord_1241411) baseStart_1241411 baseEnd_1241411 := by
    simpa [prefixWord, tailWord_1241411, baseEnd_1241411] using wordTrace_append hprefix tailTrace_1241411
  have hstable : (prefixWord ++ tailWord_1241411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241411).length < 2 ^ (prefixWord ++ tailWord_1241411).sum := by decide
  have hdescent : baseEnd_1241411 < baseStart_1241411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241462 : List Nat := [5, 1, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_1241462 : Nat := 118140960795 + 1241462 * 2 ^ 59
def prefixEnd_1241462 : Nat := 4983230072969 + 3 ^ 40 * 1241462 * 2
def baseEnd_1241462 : Nat := 424977813528084671943751

theorem tailTrace_1241462 : CollatzResearch.WordTrace tailWord_1241462 prefixEnd_1241462 424977813528084671943751 := by
  unfold tailWord_1241462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2829989939275167104659415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30186559352268449116367093 2829989939275167104659415)
  ·
    refine ⟨4244984908912750656989123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2829989939275167104659415 4244984908912750656989123)
    ·
      refine ⟨6367477363369125985483685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4244984908912750656989123 6367477363369125985483685)
      ·
        refine ⟨1193902005631711122278191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6367477363369125985483685 1193902005631711122278191)
        ·
          refine ⟨1790853008447566683417287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1193902005631711122278191 1790853008447566683417287)
          ·
            refine ⟨2686279512671350025125931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1790853008447566683417287 2686279512671350025125931)
            ·
              refine ⟨4029419269007025037688897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2686279512671350025125931 4029419269007025037688897)
              ·
                refine ⟨3022064451755268778266673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4029419269007025037688897 3022064451755268778266673)
                ·
                  refine ⟨2266548338816451583700005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3022064451755268778266673 2266548338816451583700005)
                  ·
                    refine ⟨424977813528084671943751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2266548338816451583700005 424977813528084671943751)
                    ·
                      rfl

theorem cell22_1241462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_1241462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241462 prefixEnd_1241462 := by exact prefixLift 1241462
  have htrace : WordTrace (prefixWord ++ tailWord_1241462) baseStart_1241462 baseEnd_1241462 := by
    simpa [prefixWord, tailWord_1241462, baseEnd_1241462] using wordTrace_append hprefix tailTrace_1241462
  have hstable : (prefixWord ++ tailWord_1241462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241462).length < 2 ^ (prefixWord ++ tailWord_1241462).sum := by decide
  have hdescent : baseEnd_1241462 < baseStart_1241462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241565 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 4, 3]
def baseStart_1241565 : Nat := 118140960795 + 1241565 * 2 ^ 59
def prefixEnd_1241565 : Nat := 4983230072969 + 3 ^ 40 * 1241565 * 2
def baseEnd_1241565 : Nat := 425013072533026736618435

theorem tailTrace_1241565 : CollatzResearch.WordTrace tailWord_1241565 prefixEnd_1241565 425013072533026736618435 := by
  unfold tailWord_1241565
  simp only [CollatzResearch.WordTrace]
  refine ⟨45283595747029522265550149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30189063831353014843700099 45283595747029522265550149)
  ·
    refine ⟨8490674202568035424790653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45283595747029522265550149 8490674202568035424790653)
    ·
      refine ⟨3184002825963013284296495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8490674202568035424790653 3184002825963013284296495)
      ·
        refine ⟨4776004238944519926444743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3184002825963013284296495 4776004238944519926444743)
        ·
          refine ⟨7164006358416779889667115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4776004238944519926444743 7164006358416779889667115)
          ·
            refine ⟨10746009537625169834500673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7164006358416779889667115 10746009537625169834500673)
            ·
              refine ⟨8059507153218877375875505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10746009537625169834500673 8059507153218877375875505)
              ·
                refine ⟨6044630364914158031906629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8059507153218877375875505 6044630364914158031906629)
                ·
                  refine ⟨1133368193421404630982493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6044630364914158031906629 1133368193421404630982493)
                  ·
                    refine ⟨425013072533026736618435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1133368193421404630982493 425013072533026736618435)
                    ·
                      rfl

theorem cell22_1241565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_1241565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241565 prefixEnd_1241565 := by exact prefixLift 1241565
  have htrace : WordTrace (prefixWord ++ tailWord_1241565) baseStart_1241565 baseEnd_1241565 := by
    simpa [prefixWord, tailWord_1241565, baseEnd_1241565] using wordTrace_append hprefix tailTrace_1241565
  have hstable : (prefixWord ++ tailWord_1241565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241565).length < 2 ^ (prefixWord ++ tailWord_1241565).sum := by decide
  have hdescent : baseEnd_1241565 < baseStart_1241565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241578 : List Nat := [3, 1, 3, 1, 3, 2, 9]
def baseStart_1241578 : Nat := 118140960795 + 1241578 * 2 ^ 59
def prefixEnd_1241578 : Nat := 4983230072969 + 3 ^ 40 * 1241578 * 2
def baseEnd_1241578 : Nat := 15741389729581445779385

theorem tailTrace_1241578 : CollatzResearch.WordTrace tailWord_1241578 prefixEnd_1241578 15741389729581445779385 := by
  unfold tailWord_1241578
  simp only [CollatzResearch.WordTrace]
  refine ⟨11321017473995606371443347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30189379930654950323848925 11321017473995606371443347)
  ·
    refine ⟨16981526210993409557165021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11321017473995606371443347 16981526210993409557165021)
    ·
      refine ⟨6368072329122528583936883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16981526210993409557165021 6368072329122528583936883)
      ·
        refine ⟨9552108493683792875905325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6368072329122528583936883 9552108493683792875905325)
        ·
          refine ⟨3582040685131422328464497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9552108493683792875905325 3582040685131422328464497)
          ·
            refine ⟨2686530513848566746348373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3582040685131422328464497 2686530513848566746348373)
            ·
              refine ⟨15741389729581445779385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2686530513848566746348373 15741389729581445779385)
              ·
                rfl

theorem cell22_1241578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 9].length) (baseStart_1241578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241578 prefixEnd_1241578 := by exact prefixLift 1241578
  have htrace : WordTrace (prefixWord ++ tailWord_1241578) baseStart_1241578 baseEnd_1241578 := by
    simpa [prefixWord, tailWord_1241578, baseEnd_1241578] using wordTrace_append hprefix tailTrace_1241578
  have hstable : (prefixWord ++ tailWord_1241578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241578).length < 2 ^ (prefixWord ++ tailWord_1241578).sum := by decide
  have hdescent : baseEnd_1241578 < baseStart_1241578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241582 : List Nat := [4, 1, 2, 1, 2, 2, 3, 2, 2, 3]
def baseStart_1241582 : Nat := 118140960795 + 1241582 * 2 ^ 59
def prefixEnd_1241582 : Nat := 4983230072969 + 3 ^ 40 * 1241582 * 2
def baseEnd_1241582 : Nat := 425018891980444358943383

theorem tailTrace_1241582 : CollatzResearch.WordTrace tailWord_1241582 prefixEnd_1241582 425018891980444358943383 := by
  unfold tailWord_1241582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5660526973495991771114875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30189477191978622779279333 5660526973495991771114875)
  ·
    refine ⟨8490790460243987656672313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5660526973495991771114875 8490790460243987656672313)
    ·
      refine ⟨6368092845182990742504235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8490790460243987656672313 6368092845182990742504235)
      ·
        refine ⟨9552139267774486113756353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6368092845182990742504235 9552139267774486113756353)
        ·
          refine ⟨7164104450830864585317265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9552139267774486113756353 7164104450830864585317265)
          ·
            refine ⟨5373078338123148438987949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7164104450830864585317265 5373078338123148438987949)
            ·
              refine ⟨2014904376796180664620481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5373078338123148438987949 2014904376796180664620481)
              ·
                refine ⟨1511178282597135498465361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2014904376796180664620481 1511178282597135498465361)
                ·
                  refine ⟨1133383711947851623849021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1511178282597135498465361 1133383711947851623849021)
                  ·
                    refine ⟨425018891980444358943383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1133383711947851623849021 425018891980444358943383)
                    ·
                      rfl

theorem cell22_1241582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_1241582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241582 prefixEnd_1241582 := by exact prefixLift 1241582
  have htrace : WordTrace (prefixWord ++ tailWord_1241582) baseStart_1241582 baseEnd_1241582 := by
    simpa [prefixWord, tailWord_1241582, baseEnd_1241582] using wordTrace_append hprefix tailTrace_1241582
  have hstable : (prefixWord ++ tailWord_1241582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241582).length < 2 ^ (prefixWord ++ tailWord_1241582).sum := by decide
  have hdescent : baseEnd_1241582 < baseStart_1241582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241610 : List Nat := [3, 1, 2, 2, 2, 1, 1, 4, 3, 3]
def baseStart_1241610 : Nat := 118140960795 + 1241610 * 2 ^ 59
def prefixEnd_1241610 : Nat := 4983230072969 + 3 ^ 40 * 1241610 * 2
def baseEnd_1241610 : Nat := 425028476952661619243297

theorem tailTrace_1241610 : CollatzResearch.WordTrace tailWord_1241610 prefixEnd_1241610 425028476952661619243297 := by
  unfold tailWord_1241610
  simp only [CollatzResearch.WordTrace]
  refine ⟨11321309257966623737734571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30190158021244329967292189 11321309257966623737734571)
  ·
    refine ⟨16981963886949935606601857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11321309257966623737734571 16981963886949935606601857)
    ·
      refine ⟨12736472915212451704951393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16981963886949935606601857 12736472915212451704951393)
      ·
        refine ⟨9552354686409338778713545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12736472915212451704951393 9552354686409338778713545)
        ·
          refine ⟨7164266014807004084035159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9552354686409338778713545 7164266014807004084035159)
          ·
            refine ⟨10746399022210506126052739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7164266014807004084035159 10746399022210506126052739)
            ·
              refine ⟨16119598533315759189079109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10746399022210506126052739 16119598533315759189079109)
              ·
                refine ⟨3022424724996704847952333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16119598533315759189079109 3022424724996704847952333)
                ·
                  refine ⟨1133409271873764317982125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3022424724996704847952333 1133409271873764317982125)
                  ·
                    refine ⟨425028476952661619243297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1133409271873764317982125 425028476952661619243297)
                    ·
                      rfl

theorem cell22_1241610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_1241610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241610 prefixEnd_1241610 := by exact prefixLift 1241610
  have htrace : WordTrace (prefixWord ++ tailWord_1241610) baseStart_1241610 baseEnd_1241610 := by
    simpa [prefixWord, tailWord_1241610, baseEnd_1241610] using wordTrace_append hprefix tailTrace_1241610
  have hstable : (prefixWord ++ tailWord_1241610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241610).length < 2 ^ (prefixWord ++ tailWord_1241610).sum := by decide
  have hdescent : baseEnd_1241610 < baseStart_1241610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241640 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 7]
def baseStart_1241640 : Nat := 118140960795 + 1241640 * 2 ^ 59
def prefixEnd_1241640 : Nat := 4983230072969 + 3 ^ 40 * 1241640 * 2
def baseEnd_1241640 : Nat := 141679582188583846997735

theorem tailTrace_1241640 : CollatzResearch.WordTrace tailWord_1241640 prefixEnd_1241640 141679582188583846997735 := by
  unfold tailWord_1241640
  simp only [CollatzResearch.WordTrace]
  refine ⟨22643165610878905037265187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30190887481171873383020249 22643165610878905037265187)
  ·
    refine ⟨33964748416318357555897781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22643165610878905037265187 33964748416318357555897781)
    ·
      refine ⟨3184195164029846020865417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33964748416318357555897781 3184195164029846020865417)
      ·
        refine ⟨2388146373022384515649063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3184195164029846020865417 2388146373022384515649063)
        ·
          refine ⟨3582219559533576773473595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2388146373022384515649063 3582219559533576773473595)
          ·
            refine ⟨5373329339300365160210393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3582219559533576773473595 5373329339300365160210393)
            ·
              refine ⟨4029997004475273870157795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5373329339300365160210393 4029997004475273870157795)
              ·
                refine ⟨6044995506712910805236693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4029997004475273870157795 6044995506712910805236693)
                ·
                  refine ⟨141679582188583846997735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6044995506712910805236693 141679582188583846997735)
                  ·
                    rfl

theorem cell22_1241640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 7].length) (baseStart_1241640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241640 prefixEnd_1241640 := by exact prefixLift 1241640
  have htrace : WordTrace (prefixWord ++ tailWord_1241640) baseStart_1241640 baseEnd_1241640 := by
    simpa [prefixWord, tailWord_1241640, baseEnd_1241640] using wordTrace_append hprefix tailTrace_1241640
  have hstable : (prefixWord ++ tailWord_1241640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241640).length < 2 ^ (prefixWord ++ tailWord_1241640).sum := by decide
  have hdescent : baseEnd_1241640 < baseStart_1241640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241687 : List Nat := [1, 1, 3, 2, 2, 2, 5, 1, 1, 4]
def baseStart_1241687 : Nat := 118140960795 + 1241687 * 2 ^ 59
def prefixEnd_1241687 : Nat := 4983230072969 + 3 ^ 40 * 1241687 * 2
def baseEnd_1241687 : Nat := 425054835626259085068061

theorem tailTrace_1241687 : CollatzResearch.WordTrace tailWord_1241687 prefixEnd_1241687 425054835626259085068061 := by
  unfold tailWord_1241687
  simp only [CollatzResearch.WordTrace]
  refine ⟨45288045452587537101491315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30192030301725024734327543 45288045452587537101491315)
  ·
    refine ⟨67932068178881305652236973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45288045452587537101491315 67932068178881305652236973)
    ·
      refine ⟨25474525567080489619588865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67932068178881305652236973 25474525567080489619588865)
      ·
        refine ⟨19105894175310367214691649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25474525567080489619588865 19105894175310367214691649)
        ·
          refine ⟨14329420631482775411018737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19105894175310367214691649 14329420631482775411018737)
          ·
            refine ⟨10747065473612081558264053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14329420631482775411018737 10747065473612081558264053)
            ·
              refine ⟨1007537388151132646087255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10747065473612081558264053 1007537388151132646087255)
              ·
                refine ⟨1511306082226698969130883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007537388151132646087255 1511306082226698969130883)
                ·
                  refine ⟨2266959123340048453696325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511306082226698969130883 2266959123340048453696325)
                  ·
                    refine ⟨425054835626259085068061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2266959123340048453696325 425054835626259085068061)
                    ·
                      rfl

theorem cell22_1241687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 1, 4].length) (baseStart_1241687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241687 prefixEnd_1241687 := by exact prefixLift 1241687
  have htrace : WordTrace (prefixWord ++ tailWord_1241687) baseStart_1241687 baseEnd_1241687 := by
    simpa [prefixWord, tailWord_1241687, baseEnd_1241687] using wordTrace_append hprefix tailTrace_1241687
  have hstable : (prefixWord ++ tailWord_1241687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241687).length < 2 ^ (prefixWord ++ tailWord_1241687).sum := by decide
  have hdescent : baseEnd_1241687 < baseStart_1241687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241732 : List Nat := [2, 3, 2, 1, 3, 1, 3, 1, 2, 4]
def baseStart_1241732 : Nat := 118140960795 + 1241732 * 2 ^ 59
def prefixEnd_1241732 : Nat := 4983230072969 + 3 ^ 40 * 1241732 * 2
def baseEnd_1241732 : Nat := 425070240045893967692923

theorem tailTrace_1241732 : CollatzResearch.WordTrace tailWord_1241732 prefixEnd_1241732 425070240045893967692923 := by
  unfold tailWord_1241732
  simp only [CollatzResearch.WordTrace]
  refine ⟨22644843368712254893439725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30193124491616339857919633 22644843368712254893439725)
  ·
    refine ⟨8491816263267095585039897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22644843368712254893439725 8491816263267095585039897)
    ·
      refine ⟨6368862197450321688779923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8491816263267095585039897 6368862197450321688779923)
      ·
        refine ⟨9553293296175482533169885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6368862197450321688779923 9553293296175482533169885)
        ·
          refine ⟨3582484986065805949938707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9553293296175482533169885 3582484986065805949938707)
          ·
            refine ⟨5373727479098708924908061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3582484986065805949938707 5373727479098708924908061)
            ·
              refine ⟨2015147804662015846840523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5373727479098708924908061 2015147804662015846840523)
              ·
                refine ⟨3022721706993023770260785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2015147804662015846840523 3022721706993023770260785)
                ·
                  refine ⟨2267041280244767827695589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3022721706993023770260785 2267041280244767827695589)
                  ·
                    refine ⟨425070240045893967692923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2267041280244767827695589 425070240045893967692923)
                    ·
                      rfl

theorem cell22_1241732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_1241732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241732 prefixEnd_1241732 := by exact prefixLift 1241732
  have htrace : WordTrace (prefixWord ++ tailWord_1241732) baseStart_1241732 baseEnd_1241732 := by
    simpa [prefixWord, tailWord_1241732, baseEnd_1241732] using wordTrace_append hprefix tailTrace_1241732
  have hstable : (prefixWord ++ tailWord_1241732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241732).length < 2 ^ (prefixWord ++ tailWord_1241732).sum := by decide
  have hdescent : baseEnd_1241732 < baseStart_1241732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241743 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 4, 6]
def baseStart_1241743 : Nat := 118140960795 + 1241743 * 2 ^ 59
def prefixEnd_1241743 : Nat := 4983230072969 + 3 ^ 40 * 1241743 * 2
def baseEnd_1241743 : Nat := 425074005570693605667889

theorem tailTrace_1241743 : CollatzResearch.WordTrace tailWord_1241743 prefixEnd_1241743 425074005570693605667889 := by
  unfold tailWord_1241743
  simp only [CollatzResearch.WordTrace]
  refine ⟨45290087940384658665529883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30193391960256439110353255 45290087940384658665529883)
  ·
    refine ⟨67935131910576987998294825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45290087940384658665529883 67935131910576987998294825)
    ·
      refine ⟨50951348932932740998721119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67935131910576987998294825 50951348932932740998721119)
      ·
        refine ⟨76427023399399111498081679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50951348932932740998721119 76427023399399111498081679)
        ·
          refine ⟨114640535099098667247122519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76427023399399111498081679 114640535099098667247122519)
          ·
            refine ⟨171960802648648000870683779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114640535099098667247122519 171960802648648000870683779)
            ·
              refine ⟨257941203972972001306025669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171960802648648000870683779 257941203972972001306025669)
              ·
                refine ⟨48363975744932250244879813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 257941203972972001306025669 48363975744932250244879813)
                ·
                  refine ⟨9068245452174796920914965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48363975744932250244879813 9068245452174796920914965)
                  ·
                    refine ⟨425074005570693605667889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9068245452174796920914965 425074005570693605667889)
                    ·
                      rfl

theorem cell22_1241743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_1241743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241743 prefixEnd_1241743 := by exact prefixLift 1241743
  have htrace : WordTrace (prefixWord ++ tailWord_1241743) baseStart_1241743 baseEnd_1241743 := by
    simpa [prefixWord, tailWord_1241743, baseEnd_1241743] using wordTrace_append hprefix tailTrace_1241743
  have hstable : (prefixWord ++ tailWord_1241743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241743).length < 2 ^ (prefixWord ++ tailWord_1241743).sum := by decide
  have hdescent : baseEnd_1241743 < baseStart_1241743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241796 : List Nat := [2, 3, 3, 1, 1, 2, 3, 3, 1, 3]
def baseStart_1241796 : Nat := 118140960795 + 1241796 * 2 ^ 59
def prefixEnd_1241796 : Nat := 4983230072969 + 3 ^ 40 * 1241796 * 2
def baseEnd_1241796 : Nat := 425092148553819134092727

theorem tailTrace_1241796 : CollatzResearch.WordTrace tailWord_1241796 prefixEnd_1241796 425092148553819134092727 := by
  unfold tailWord_1241796
  simp only [CollatzResearch.WordTrace]
  refine ⟨22646010504596324358604621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30194680672795099144806161 22646010504596324358604621)
  ·
    refine ⟨8492253939223621634476733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22646010504596324358604621 8492253939223621634476733)
    ·
      refine ⟨3184595227208858112928775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8492253939223621634476733 3184595227208858112928775)
      ·
        refine ⟨4776892840813287169393163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3184595227208858112928775 4776892840813287169393163)
        ·
          refine ⟨7165339261219930754089745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4776892840813287169393163 7165339261219930754089745)
          ·
            refine ⟨5374004445914948065567309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7165339261219930754089745 5374004445914948065567309)
            ·
              refine ⟨2015251667218105524587741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5374004445914948065567309 2015251667218105524587741)
              ·
                refine ⟨755719375206789571720403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2015251667218105524587741 755719375206789571720403)
                ·
                  refine ⟨1133579062810184357580605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 755719375206789571720403 1133579062810184357580605)
                  ·
                    refine ⟨425092148553819134092727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1133579062810184357580605 425092148553819134092727)
                    ·
                      rfl

theorem cell22_1241796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_1241796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241796 prefixEnd_1241796 := by exact prefixLift 1241796
  have htrace : WordTrace (prefixWord ++ tailWord_1241796) baseStart_1241796 baseEnd_1241796 := by
    simpa [prefixWord, tailWord_1241796, baseEnd_1241796] using wordTrace_append hprefix tailTrace_1241796
  have hstable : (prefixWord ++ tailWord_1241796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241796).length < 2 ^ (prefixWord ++ tailWord_1241796).sum := by decide
  have hdescent : baseEnd_1241796 < baseStart_1241796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241813 : List Nat := [1, 3, 2, 5, 2, 1, 1, 1, 3, 3]
def baseStart_1241813 : Nat := 118140960795 + 1241813 * 2 ^ 59
def prefixEnd_1241813 : Nat := 4983230072969 + 3 ^ 40 * 1241813 * 2
def baseEnd_1241813 : Nat := 425097968001236756417675

theorem tailTrace_1241813 : CollatzResearch.WordTrace tailWord_1241813 prefixEnd_1241813 425097968001236756417675 := by
  unfold tailWord_1241813
  simp only [CollatzResearch.WordTrace]
  refine ⟨45292641050131060620578093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30195094033420707080385395 45292641050131060620578093)
  ·
    refine ⟨16984740393799147732716785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45292641050131060620578093 16984740393799147732716785)
    ·
      refine ⟨12738555295349360799537589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16984740393799147732716785 12738555295349360799537589)
      ·
        refine ⟨1194239558939002574956649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12738555295349360799537589 1194239558939002574956649)
        ·
          refine ⟨895679669204251931217487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1194239558939002574956649 895679669204251931217487)
          ·
            refine ⟨1343519503806377896826231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895679669204251931217487 1343519503806377896826231)
            ·
              refine ⟨2015279255709566845239347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1343519503806377896826231 2015279255709566845239347)
              ·
                refine ⟨3022918883564350267859021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2015279255709566845239347 3022918883564350267859021)
                ·
                  refine ⟨1133594581336631350447133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3022918883564350267859021 1133594581336631350447133)
                  ·
                    refine ⟨425097968001236756417675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1133594581336631350447133 425097968001236756417675)
                    ·
                      rfl

theorem cell22_1241813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_1241813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241813 prefixEnd_1241813 := by exact prefixLift 1241813
  have htrace : WordTrace (prefixWord ++ tailWord_1241813) baseStart_1241813 baseEnd_1241813 := by
    simpa [prefixWord, tailWord_1241813, baseEnd_1241813] using wordTrace_append hprefix tailTrace_1241813
  have hstable : (prefixWord ++ tailWord_1241813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241813).length < 2 ^ (prefixWord ++ tailWord_1241813).sum := by decide
  have hdescent : baseEnd_1241813 < baseStart_1241813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241835 : List Nat := [1, 1, 1, 1, 2, 4, 1, 5, 1, 5]
def baseStart_1241835 : Nat := 118140960795 + 1241835 * 2 ^ 59
def prefixEnd_1241835 : Nat := 4983230072969 + 3 ^ 40 * 1241835 * 2
def baseEnd_1241835 : Nat := 425105499050836032367607

theorem tailTrace_1241835 : CollatzResearch.WordTrace tailWord_1241835 prefixEnd_1241835 425105499050836032367607 := by
  unfold tailWord_1241835
  simp only [CollatzResearch.WordTrace]
  refine ⟨45293443456051358377878959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30195628970700905585252639 45293443456051358377878959)
  ·
    refine ⟨67940165184077037566818439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45293443456051358377878959 67940165184077037566818439)
    ·
      refine ⟨101910247776115556350227659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67940165184077037566818439 101910247776115556350227659)
      ·
        refine ⟨152865371664173334525341489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101910247776115556350227659 152865371664173334525341489)
        ·
          refine ⟨114649028748130000894006117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152865371664173334525341489 114649028748130000894006117)
          ·
            refine ⟨21496692890274375167626147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114649028748130000894006117 21496692890274375167626147)
            ·
              refine ⟨32245039335411562751439221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21496692890274375167626147 32245039335411562751439221)
              ·
                refine ⟨3022972437694834007947427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32245039335411562751439221 3022972437694834007947427)
                ·
                  refine ⟨4534458656542251011921141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3022972437694834007947427 4534458656542251011921141)
                  ·
                    refine ⟨425105499050836032367607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4534458656542251011921141 425105499050836032367607)
                    ·
                      rfl

theorem cell22_1241835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 5].length) (baseStart_1241835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241835 prefixEnd_1241835 := by exact prefixLift 1241835
  have htrace : WordTrace (prefixWord ++ tailWord_1241835) baseStart_1241835 baseEnd_1241835 := by
    simpa [prefixWord, tailWord_1241835, baseEnd_1241835] using wordTrace_append hprefix tailTrace_1241835
  have hstable : (prefixWord ++ tailWord_1241835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241835).length < 2 ^ (prefixWord ++ tailWord_1241835).sum := by decide
  have hdescent : baseEnd_1241835 < baseStart_1241835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241839 : List Nat := [1, 1, 2, 1, 5, 4, 1, 2, 1, 4]
def baseStart_1241839 : Nat := 118140960795 + 1241839 * 2 ^ 59
def prefixEnd_1241839 : Nat := 4983230072969 + 3 ^ 40 * 1241839 * 2
def baseEnd_1241839 : Nat := 425106868332581355267595

theorem tailTrace_1241839 : CollatzResearch.WordTrace tailWord_1241839 prefixEnd_1241839 425106868332581355267595 := by
  unfold tailWord_1241839
  simp only [CollatzResearch.WordTrace]
  refine ⟨45293589348036867061024571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30195726232024578040683047 45293589348036867061024571)
  ·
    refine ⟨67940384022055300591536857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45293589348036867061024571 67940384022055300591536857)
    ·
      refine ⟨50955288016541475443652643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67940384022055300591536857 50955288016541475443652643)
      ·
        refine ⟨76432932024812213165478965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50955288016541475443652643 76432932024812213165478965)
        ·
          refine ⟨7165587377326144984263653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76432932024812213165478965 7165587377326144984263653)
          ·
            refine ⟨1343547633248652184549435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7165587377326144984263653 1343547633248652184549435)
            ·
              refine ⟨2015321449872978276824153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1343547633248652184549435 2015321449872978276824153)
              ·
                refine ⟨1511491087404733707618115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2015321449872978276824153 1511491087404733707618115)
                ·
                  refine ⟨2267236631107100561427173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511491087404733707618115 2267236631107100561427173)
                  ·
                    refine ⟨425106868332581355267595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2267236631107100561427173 425106868332581355267595)
                    ·
                      rfl

theorem cell22_1241839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 4].length) (baseStart_1241839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241839 prefixEnd_1241839 := by exact prefixLift 1241839
  have htrace : WordTrace (prefixWord ++ tailWord_1241839) baseStart_1241839 baseEnd_1241839 := by
    simpa [prefixWord, tailWord_1241839, baseEnd_1241839] using wordTrace_append hprefix tailTrace_1241839
  have hstable : (prefixWord ++ tailWord_1241839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241839).length < 2 ^ (prefixWord ++ tailWord_1241839).sum := by decide
  have hdescent : baseEnd_1241839 < baseStart_1241839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241850 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 1, 6]
def baseStart_1241850 : Nat := 118140960795 + 1241850 * 2 ^ 59
def prefixEnd_1241850 : Nat := 4983230072969 + 3 ^ 40 * 1241850 * 2
def baseEnd_1241850 : Nat := 425110633857380993242561

theorem tailTrace_1241850 : CollatzResearch.WordTrace tailWord_1241850 prefixEnd_1241850 425110633857380993242561 := by
  unfold tailWord_1241850
  simp only [CollatzResearch.WordTrace]
  refine ⟨11323497637749253984918751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30195993700664677293116669 11323497637749253984918751)
  ·
    refine ⟨16985246456623880977378127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11323497637749253984918751 16985246456623880977378127)
    ·
      refine ⟨25477869684935821466067191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16985246456623880977378127 25477869684935821466067191)
      ·
        refine ⟨38216804527403732199100787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25477869684935821466067191 38216804527403732199100787)
        ·
          refine ⟨57325206791105598298651181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38216804527403732199100787 57325206791105598298651181)
          ·
            refine ⟨21496952546664599361994193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57325206791105598298651181 21496952546664599361994193)
            ·
              refine ⟨16122714409998449521495645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21496952546664599361994193 16122714409998449521495645)
              ·
                refine ⟨6046017903749418570560867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16122714409998449521495645 6046017903749418570560867)
                ·
                  refine ⟨9069026855624127855841301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6046017903749418570560867 9069026855624127855841301)
                  ·
                    refine ⟨425110633857380993242561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9069026855624127855841301 425110633857380993242561)
                    ·
                      rfl

theorem cell22_1241850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_1241850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241850 prefixEnd_1241850 := by exact prefixLift 1241850
  have htrace : WordTrace (prefixWord ++ tailWord_1241850) baseStart_1241850 baseEnd_1241850 := by
    simpa [prefixWord, tailWord_1241850, baseEnd_1241850] using wordTrace_append hprefix tailTrace_1241850
  have hstable : (prefixWord ++ tailWord_1241850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241850).length < 2 ^ (prefixWord ++ tailWord_1241850).sum := by decide
  have hdescent : baseEnd_1241850 < baseStart_1241850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241852 : List Nat := [2, 2, 2, 1, 3, 3, 1, 2, 1, 5]
def baseStart_1241852 : Nat := 118140960795 + 1241852 * 2 ^ 59
def prefixEnd_1241852 : Nat := 4983230072969 + 3 ^ 40 * 1241852 * 2
def baseEnd_1241852 : Nat := 425111318498253654692555

theorem tailTrace_1241852 : CollatzResearch.WordTrace tailWord_1241852 prefixEnd_1241852 425111318498253654692555 := by
  unfold tailWord_1241852
  simp only [CollatzResearch.WordTrace]
  refine ⟨22647031748494885140623905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30196042331326513520831873 22647031748494885140623905)
  ·
    refine ⟨16985273811371163855467929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22647031748494885140623905 16985273811371163855467929)
    ·
      refine ⟨12738955358528372891600947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16985273811371163855467929 12738955358528372891600947)
      ·
        refine ⟨19108433037792559337401421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12738955358528372891600947 19108433037792559337401421)
        ·
          refine ⟨7165662389172209751525533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19108433037792559337401421 7165662389172209751525533)
          ·
            refine ⟨2687123395939578656822075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7165662389172209751525533 2687123395939578656822075)
            ·
              refine ⟨4030685093909367985233113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2687123395939578656822075 4030685093909367985233113)
              ·
                refine ⟨3023013820432025988924835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4030685093909367985233113 3023013820432025988924835)
                ·
                  refine ⟨4534520730648038983387253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3023013820432025988924835 4534520730648038983387253)
                  ·
                    refine ⟨425111318498253654692555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4534520730648038983387253 425111318498253654692555)
                    ·
                      rfl

theorem cell22_1241852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_1241852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241852 prefixEnd_1241852 := by exact prefixLift 1241852
  have htrace : WordTrace (prefixWord ++ tailWord_1241852) baseStart_1241852 baseEnd_1241852 := by
    simpa [prefixWord, tailWord_1241852, baseEnd_1241852] using wordTrace_append hprefix tailTrace_1241852
  have hstable : (prefixWord ++ tailWord_1241852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241852).length < 2 ^ (prefixWord ++ tailWord_1241852).sum := by decide
  have hdescent : baseEnd_1241852 < baseStart_1241852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241880 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 2, 7]
def baseStart_1241880 : Nat := 118140960795 + 1241880 * 2 ^ 59
def prefixEnd_1241880 : Nat := 4983230072969 + 3 ^ 40 * 1241880 * 2
def baseEnd_1241880 : Nat := 425120903470470914992469

theorem tailTrace_1241880 : CollatzResearch.WordTrace tailWord_1241880 prefixEnd_1241880 425120903470470914992469 := by
  unfold tailWord_1241880
  simp only [CollatzResearch.WordTrace]
  refine ⟨22647542370444165531633547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30196723160592220708844729 22647542370444165531633547)
  ·
    refine ⟨33971313555666248297450321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22647542370444165531633547 33971313555666248297450321)
    ·
      refine ⟨25478485166749686223087741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33971313555666248297450321 25478485166749686223087741)
      ·
        refine ⟨9554431937531132333657903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25478485166749686223087741 9554431937531132333657903)
        ·
          refine ⟨14331647906296698500486855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9554431937531132333657903 14331647906296698500486855)
          ·
            refine ⟨21497471859445047750730283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14331647906296698500486855 21497471859445047750730283)
            ·
              refine ⟨32246207789167571626095425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21497471859445047750730283 32246207789167571626095425)
              ·
                refine ⟨24184655841875678719571569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32246207789167571626095425 24184655841875678719571569)
                ·
                  refine ⟨18138491881406759039678677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24184655841875678719571569 18138491881406759039678677)
                  ·
                    refine ⟨425120903470470914992469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18138491881406759039678677 425120903470470914992469)
                    ·
                      rfl

theorem cell22_1241880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_1241880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241880 prefixEnd_1241880 := by exact prefixLift 1241880
  have htrace : WordTrace (prefixWord ++ tailWord_1241880) baseStart_1241880 baseEnd_1241880 := by
    simpa [prefixWord, tailWord_1241880, baseEnd_1241880] using wordTrace_append hprefix tailTrace_1241880
  have hstable : (prefixWord ++ tailWord_1241880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241880).length < 2 ^ (prefixWord ++ tailWord_1241880).sum := by decide
  have hdescent : baseEnd_1241880 < baseStart_1241880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241897 : List Nat := [1, 2, 1, 1, 1, 1, 1, 8, 3, 3]
def baseStart_1241897 : Nat := 118140960795 + 1241897 * 2 ^ 59
def prefixEnd_1241897 : Nat := 4983230072969 + 3 ^ 40 * 1241897 * 2
def baseEnd_1241897 : Nat := 425126722917888537317417

theorem tailTrace_1241897 : CollatzResearch.WordTrace tailWord_1241897 prefixEnd_1241897 425126722917888537317417 := by
  unfold tailWord_1241897
  simp only [CollatzResearch.WordTrace]
  refine ⟨45295704781826742966635945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30197136521217828644423963 45295704781826742966635945)
  ·
    refine ⟨33971778586370057224976959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45295704781826742966635945 33971778586370057224976959)
    ·
      refine ⟨50957667879555085837465439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33971778586370057224976959 50957667879555085837465439)
      ·
        refine ⟨76436501819332628756198159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50957667879555085837465439 76436501819332628756198159)
        ·
          refine ⟨114654752728998943134297239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76436501819332628756198159 114654752728998943134297239)
          ·
            refine ⟨171982129093498414701445859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114654752728998943134297239 171982129093498414701445859)
            ·
              refine ⟨257973193640247622052168789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171982129093498414701445859 257973193640247622052168789)
              ·
                refine ⟨3023123362971651820923853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 257973193640247622052168789 3023123362971651820923853)
                ·
                  refine ⟨1133671261114369432846445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3023123362971651820923853 1133671261114369432846445)
                  ·
                    refine ⟨425126722917888537317417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1133671261114369432846445 425126722917888537317417)
                    ·
                      rfl

theorem cell22_1241897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 3].length) (baseStart_1241897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241897 prefixEnd_1241897 := by exact prefixLift 1241897
  have htrace : WordTrace (prefixWord ++ tailWord_1241897) baseStart_1241897 baseEnd_1241897 := by
    simpa [prefixWord, tailWord_1241897, baseEnd_1241897] using wordTrace_append hprefix tailTrace_1241897
  have hstable : (prefixWord ++ tailWord_1241897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241897).length < 2 ^ (prefixWord ++ tailWord_1241897).sum := by decide
  have hdescent : baseEnd_1241897 < baseStart_1241897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241901 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_1241901 : Nat := 118140960795 + 1241901 * 2 ^ 59
def prefixEnd_1241901 : Nat := 4983230072969 + 3 ^ 40 * 1241901 * 2
def baseEnd_1241901 : Nat := 425128092199633860217405

theorem tailTrace_1241901 : CollatzResearch.WordTrace tailWord_1241901 prefixEnd_1241901 425128092199633860217405 := by
  unfold tailWord_1241901
  simp only [CollatzResearch.WordTrace]
  refine ⟨45295850673812251649781557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30197233782541501099854371 45295850673812251649781557)
  ·
    refine ⟨4246486000669898592167021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45295850673812251649781557 4246486000669898592167021)
    ·
      refine ⟨1592432250251211972062633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4246486000669898592167021 1592432250251211972062633)
      ·
        refine ⟨1194324187688408979046975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1592432250251211972062633 1194324187688408979046975)
        ·
          refine ⟨1791486281532613468570463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1194324187688408979046975 1791486281532613468570463)
          ·
            refine ⟨2687229422298920202855695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1791486281532613468570463 2687229422298920202855695)
            ·
              refine ⟨4030844133448380304283543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2687229422298920202855695 4030844133448380304283543)
              ·
                refine ⟨6046266200172570456425315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4030844133448380304283543 6046266200172570456425315)
                ·
                  refine ⟨9069399300258855684637973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6046266200172570456425315 9069399300258855684637973)
                  ·
                    refine ⟨425128092199633860217405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9069399300258855684637973 425128092199633860217405)
                    ·
                      rfl

theorem cell22_1241901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_1241901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241901 prefixEnd_1241901 := by exact prefixLift 1241901
  have htrace : WordTrace (prefixWord ++ tailWord_1241901) baseStart_1241901 baseEnd_1241901 := by
    simpa [prefixWord, tailWord_1241901, baseEnd_1241901] using wordTrace_append hprefix tailTrace_1241901
  have hstable : (prefixWord ++ tailWord_1241901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241901).length < 2 ^ (prefixWord ++ tailWord_1241901).sum := by decide
  have hdescent : baseEnd_1241901 < baseStart_1241901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241957 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 3, 4]
def baseStart_1241957 : Nat := 118140960795 + 1241957 * 2 ^ 59
def prefixEnd_1241957 : Nat := 4983230072969 + 3 ^ 40 * 1241957 * 2
def baseEnd_1241957 : Nat := 425147262144068380817233

theorem tailTrace_1241957 : CollatzResearch.WordTrace tailWord_1241957 prefixEnd_1241957 425147262144068380817233 := by
  unfold tailWord_1241957
  simp only [CollatzResearch.WordTrace]
  refine ⟨45297893161609373213820125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30198595441072915475880083 45297893161609373213820125)
  ·
    refine ⟨16986709935603514955182547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45297893161609373213820125 16986709935603514955182547)
    ·
      refine ⟨25480064903405272432773821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16986709935603514955182547 25480064903405272432773821)
      ·
        refine ⟨9555024338776977162290183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25480064903405272432773821 9555024338776977162290183)
        ·
          refine ⟨14332536508165465743435275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9555024338776977162290183 14332536508165465743435275)
          ·
            refine ⟨21498804762248198615152913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14332536508165465743435275 21498804762248198615152913)
            ·
              refine ⟨16124103571686148961364685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21498804762248198615152913 16124103571686148961364685)
              ·
                refine ⟨6046538839382305860511757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16124103571686148961364685 6046538839382305860511757)
                ·
                  refine ⟨2267452064768364697691909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6046538839382305860511757 2267452064768364697691909)
                  ·
                    refine ⟨425147262144068380817233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2267452064768364697691909 425147262144068380817233)
                    ·
                      rfl

theorem cell22_1241957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_1241957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241957 prefixEnd_1241957 := by exact prefixLift 1241957
  have htrace : WordTrace (prefixWord ++ tailWord_1241957) baseStart_1241957 baseEnd_1241957 := by
    simpa [prefixWord, tailWord_1241957, baseEnd_1241957] using wordTrace_append hprefix tailTrace_1241957
  have hstable : (prefixWord ++ tailWord_1241957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241957).length < 2 ^ (prefixWord ++ tailWord_1241957).sum := by decide
  have hdescent : baseEnd_1241957 < baseStart_1241957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241982 : List Nat := [4, 2, 3, 1, 2, 1, 3, 2, 1, 3]
def baseStart_1241982 : Nat := 118140960795 + 1241982 * 2 ^ 59
def prefixEnd_1241982 : Nat := 4983230072969 + 3 ^ 40 * 1241982 * 2
def baseEnd_1241982 : Nat := 425155820154976648942157

theorem tailTrace_1241982 : CollatzResearch.WordTrace tailWord_1241982 prefixEnd_1241982 425155820154976648942157 := by
  unfold tailWord_1241982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5662350623314850310435025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30199203324345868322320133 5662350623314850310435025)
  ·
    refine ⟨4246762967486137732826269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5662350623314850310435025 4246762967486137732826269)
    ·
      refine ⟨1592536112807301649809851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4246762967486137732826269 1592536112807301649809851)
      ·
        refine ⟨2388804169210952474714777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1592536112807301649809851 2388804169210952474714777)
        ·
          refine ⟨1791603126908214356036083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2388804169210952474714777 1791603126908214356036083)
          ·
            refine ⟨2687404690362321534054125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1791603126908214356036083 2687404690362321534054125)
            ·
              refine ⟨1007776758885870575270297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2687404690362321534054125 1007776758885870575270297)
              ·
                refine ⟨755832569164402931452723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1007776758885870575270297 755832569164402931452723)
                ·
                  refine ⟨1133748853746604397179085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 755832569164402931452723 1133748853746604397179085)
                  ·
                    refine ⟨425155820154976648942157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1133748853746604397179085 425155820154976648942157)
                    ·
                      rfl

theorem cell22_1241982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_1241982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241982 prefixEnd_1241982 := by exact prefixLift 1241982
  have htrace : WordTrace (prefixWord ++ tailWord_1241982) baseStart_1241982 baseEnd_1241982 := by
    simpa [prefixWord, tailWord_1241982, baseEnd_1241982] using wordTrace_append hprefix tailTrace_1241982
  have hstable : (prefixWord ++ tailWord_1241982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241982).length < 2 ^ (prefixWord ++ tailWord_1241982).sum := by decide
  have hdescent : baseEnd_1241982 < baseStart_1241982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241989 : List Nat := [1, 3, 1, 1, 3, 5, 1, 1, 6]
def baseStart_1241989 : Nat := 118140960795 + 1241989 * 2 ^ 59
def prefixEnd_1241989 : Nat := 4983230072969 + 3 ^ 40 * 1241989 * 2
def baseEnd_1241989 : Nat := 141719405466010321339045

theorem tailTrace_1241989 : CollatzResearch.WordTrace tailWord_1241989 prefixEnd_1241989 141719405466010321339045 := by
  unfold tailWord_1241989
  simp only [CollatzResearch.WordTrace]
  refine ⟨45299060297493442678985021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30199373531662295119323347 45299060297493442678985021)
  ·
    refine ⟨16987147611560041004619383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45299060297493442678985021 16987147611560041004619383)
    ·
      refine ⟨25480721417340061506929075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16987147611560041004619383 25480721417340061506929075)
      ·
        refine ⟨38221082126010092260393613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25480721417340061506929075 38221082126010092260393613)
        ·
          refine ⟨14332905797253784597647605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38221082126010092260393613 14332905797253784597647605)
          ·
            refine ⟨1343709918492542306029463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14332905797253784597647605 1343709918492542306029463)
            ·
              refine ⟨2015564877738813459044195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1343709918492542306029463 2015564877738813459044195)
              ·
                refine ⟨3023347316608220188566293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2015564877738813459044195 3023347316608220188566293)
                ·
                  refine ⟨141719405466010321339045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3023347316608220188566293 141719405466010321339045)
                  ·
                    rfl

theorem cell22_1241989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_1241989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1241989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1241989 prefixEnd_1241989 := by exact prefixLift 1241989
  have htrace : WordTrace (prefixWord ++ tailWord_1241989) baseStart_1241989 baseEnd_1241989 := by
    simpa [prefixWord, tailWord_1241989, baseEnd_1241989] using wordTrace_append hprefix tailTrace_1241989
  have hstable : (prefixWord ++ tailWord_1241989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241989).length < 2 ^ (prefixWord ++ tailWord_1241989).sum := by decide
  have hdescent : baseEnd_1241989 < baseStart_1241989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242004 : List Nat := [2, 4, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1242004 : Nat := 118140960795 + 1242004 * 2 ^ 59
def prefixEnd_1242004 : Nat := 4983230072969 + 3 ^ 40 * 1242004 * 2
def baseEnd_1242004 : Nat := 425163351204575924892089

theorem tailTrace_1242004 : CollatzResearch.WordTrace tailWord_1242004 prefixEnd_1242004 425163351204575924892089 := by
  unfold tailWord_1242004
  simp only [CollatzResearch.WordTrace]
  refine ⟨22649803696219550120390533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30199738261626066827187377 22649803696219550120390533)
  ·
    refine ⟨4246838193041165647573225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22649803696219550120390533 4246838193041165647573225)
    ·
      refine ⟨3185128644780874235679919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4246838193041165647573225 3185128644780874235679919)
      ·
        refine ⟨4777692967171311353519879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3185128644780874235679919 4777692967171311353519879)
        ·
          refine ⟨7166539450756967030279819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4777692967171311353519879 7166539450756967030279819)
          ·
            refine ⟨10749809176135450545419729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7166539450756967030279819 10749809176135450545419729)
            ·
              refine ⟨8062356882101587909064797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10749809176135450545419729 8062356882101587909064797)
              ·
                refine ⟨3023383830788095465899299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8062356882101587909064797 3023383830788095465899299)
                ·
                  refine ⟨4535075746182143198848949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3023383830788095465899299 4535075746182143198848949)
                  ·
                    refine ⟨425163351204575924892089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4535075746182143198848949 425163351204575924892089)
                    ·
                      rfl

theorem cell22_1242004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1242004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242004 prefixEnd_1242004 := by exact prefixLift 1242004
  have htrace : WordTrace (prefixWord ++ tailWord_1242004) baseStart_1242004 baseEnd_1242004 := by
    simpa [prefixWord, tailWord_1242004, baseEnd_1242004] using wordTrace_append hprefix tailTrace_1242004
  have hstable : (prefixWord ++ tailWord_1242004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242004).length < 2 ^ (prefixWord ++ tailWord_1242004).sum := by decide
  have hdescent : baseEnd_1242004 < baseStart_1242004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242066 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 5, 3]
def baseStart_1242066 : Nat := 118140960795 + 1242066 * 2 ^ 59
def prefixEnd_1242066 : Nat := 4983230072969 + 3 ^ 40 * 1242066 * 2
def baseEnd_1242066 : Nat := 425184575071628429841899

theorem tailTrace_1242066 : CollatzResearch.WordTrace tailWord_1242066 prefixEnd_1242066 425184575071628429841899 := by
  unfold tailWord_1242066
  simp only [CollatzResearch.WordTrace]
  refine ⟨11325467179553621207384513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30201245812142989886358701 11325467179553621207384513)
  ·
    refine ⟨8494100384665215905538385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11325467179553621207384513 8494100384665215905538385)
    ·
      refine ⟨6370575288498911929153789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8494100384665215905538385 6370575288498911929153789)
      ·
        refine ⟨2388965733187091973432671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6370575288498911929153789 2388965733187091973432671)
        ·
          refine ⟨3583448599780637960149007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2388965733187091973432671 3583448599780637960149007)
          ·
            refine ⟨5375172899670956940223511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3583448599780637960149007 5375172899670956940223511)
            ·
              refine ⟨8062759349506435410335267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5375172899670956940223511 8062759349506435410335267)
              ·
                refine ⟨12094139024259653115502901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8062759349506435410335267 12094139024259653115502901)
                ·
                  refine ⟨1133825533524342479578397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12094139024259653115502901 1133825533524342479578397)
                  ·
                    refine ⟨425184575071628429841899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1133825533524342479578397 425184575071628429841899)
                    ·
                      rfl

theorem cell22_1242066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_1242066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242066 prefixEnd_1242066 := by exact prefixLift 1242066
  have htrace : WordTrace (prefixWord ++ tailWord_1242066) baseStart_1242066 baseEnd_1242066 := by
    simpa [prefixWord, tailWord_1242066, baseEnd_1242066] using wordTrace_append hprefix tailTrace_1242066
  have hstable : (prefixWord ++ tailWord_1242066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242066).length < 2 ^ (prefixWord ++ tailWord_1242066).sum := by decide
  have hdescent : baseEnd_1242066 < baseStart_1242066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242083 : List Nat := [1, 1, 1, 6, 1, 1, 4, 3, 1, 3]
def baseStart_1242083 : Nat := 118140960795 + 1242083 * 2 ^ 59
def prefixEnd_1242083 : Nat := 4983230072969 + 3 ^ 40 * 1242083 * 2
def baseEnd_1242083 : Nat := 425190394519046052166847

theorem tailTrace_1242083 : CollatzResearch.WordTrace tailWord_1242083 prefixEnd_1242083 425190394519046052166847 := by
  unfold tailWord_1242083
  simp only [CollatzResearch.WordTrace]
  refine ⟨45302488759152896732906903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30201659172768597821937935 45302488759152896732906903)
  ·
    refine ⟨67953733138729345099360355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45302488759152896732906903 67953733138729345099360355)
    ·
      refine ⟨101930599708094017649040533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67953733138729345099360355 101930599708094017649040533)
      ·
        refine ⟨4777996861316907077298775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 101930599708094017649040533 4777996861316907077298775)
        ·
          refine ⟨7166995291975360615948163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4777996861316907077298775 7166995291975360615948163)
          ·
            refine ⟨10750492937963040923922245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7166995291975360615948163 10750492937963040923922245)
            ·
              refine ⟨2015717425868070173235421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10750492937963040923922245 2015717425868070173235421)
              ·
                refine ⟨755894034700526314963283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2015717425868070173235421 755894034700526314963283)
                ·
                  refine ⟨1133841052050789472444925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 755894034700526314963283 1133841052050789472444925)
                  ·
                    refine ⟨425190394519046052166847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1133841052050789472444925 425190394519046052166847)
                    ·
                      rfl

theorem cell22_1242083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 1, 3].length) (baseStart_1242083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242083 prefixEnd_1242083 := by exact prefixLift 1242083
  have htrace : WordTrace (prefixWord ++ tailWord_1242083) baseStart_1242083 baseEnd_1242083 := by
    simpa [prefixWord, tailWord_1242083, baseEnd_1242083] using wordTrace_append hprefix tailTrace_1242083
  have hstable : (prefixWord ++ tailWord_1242083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242083).length < 2 ^ (prefixWord ++ tailWord_1242083).sum := by decide
  have hdescent : baseEnd_1242083 < baseStart_1242083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242124 : List Nat := [2, 2, 1, 2, 3, 2, 2, 2, 6]
def baseStart_1242124 : Nat := 118140960795 + 1242124 * 2 ^ 59
def prefixEnd_1242124 : Nat := 4983230072969 + 3 ^ 40 * 1242124 * 2
def baseEnd_1242124 : Nat := 141734809885645203963907

theorem tailTrace_1242124 : CollatzResearch.WordTrace tailWord_1242124 prefixEnd_1242124 141734809885645203963907 := by
  unfold tailWord_1242124
  simp only [CollatzResearch.WordTrace]
  refine ⟨22651992076002180367574713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30202656101336240490099617 22651992076002180367574713)
  ·
    refine ⟨16988994057001635275681035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22651992076002180367574713 16988994057001635275681035)
    ·
      refine ⟨25483491085502452913521553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16988994057001635275681035 25483491085502452913521553)
      ·
        refine ⟨19112618314126839685141165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25483491085502452913521553 19112618314126839685141165)
        ·
          refine ⟨7167231867797564881927937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19112618314126839685141165 7167231867797564881927937)
          ·
            refine ⟨5375423900848173661445953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7167231867797564881927937 5375423900848173661445953)
            ·
              refine ⟨4031567925636130246084465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5375423900848173661445953 4031567925636130246084465)
              ·
                refine ⟨3023675944227097684563349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4031567925636130246084465 3023675944227097684563349)
                ·
                  refine ⟨141734809885645203963907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3023675944227097684563349 141734809885645203963907)
                  ·
                    rfl

theorem cell22_1242124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_1242124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242124 prefixEnd_1242124 := by exact prefixLift 1242124
  have htrace : WordTrace (prefixWord ++ tailWord_1242124) baseStart_1242124 baseEnd_1242124 := by
    simpa [prefixWord, tailWord_1242124, baseEnd_1242124] using wordTrace_append hprefix tailTrace_1242124
  have hstable : (prefixWord ++ tailWord_1242124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242124).length < 2 ^ (prefixWord ++ tailWord_1242124).sum := by decide
  have hdescent : baseEnd_1242124 < baseStart_1242124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242126 : List Nat := [4, 1, 1, 2, 2, 2, 1, 4, 1, 4]
def baseStart_1242126 : Nat := 118140960795 + 1242126 * 2 ^ 59
def prefixEnd_1242126 : Nat := 4983230072969 + 3 ^ 40 * 1242126 * 2
def baseEnd_1242126 : Nat := 425205114297808273341715

theorem tailTrace_1242126 : CollatzResearch.WordTrace tailWord_1242126 prefixEnd_1242126 425205114297808273341715 := by
  unfold tailWord_1242126
  simp only [CollatzResearch.WordTrace]
  refine ⟨5663007137249639384590279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30202704731998076717814821 5663007137249639384590279)
  ·
    refine ⟨8494510705874459076885419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5663007137249639384590279 8494510705874459076885419)
    ·
      refine ⟨12741766058811688615328129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8494510705874459076885419 12741766058811688615328129)
      ·
        refine ⟨9556324544108766461496097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12741766058811688615328129 9556324544108766461496097)
        ·
          refine ⟨7167243408081574846122073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9556324544108766461496097 7167243408081574846122073)
          ·
            refine ⟨5375432556061181134591555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7167243408081574846122073 5375432556061181134591555)
            ·
              refine ⟨8063148834091771701887333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5375432556061181134591555 8063148834091771701887333)
              ·
                refine ⟨1511840406392207194103875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8063148834091771701887333 1511840406392207194103875)
                ·
                  refine ⟨2267760609588310791155813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511840406392207194103875 2267760609588310791155813)
                  ·
                    refine ⟨425205114297808273341715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2267760609588310791155813 425205114297808273341715)
                    ·
                      rfl

theorem cell22_1242126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_1242126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242126 prefixEnd_1242126 := by exact prefixLift 1242126
  have htrace : WordTrace (prefixWord ++ tailWord_1242126) baseStart_1242126 baseEnd_1242126 := by
    simpa [prefixWord, tailWord_1242126, baseEnd_1242126] using wordTrace_append hprefix tailTrace_1242126
  have hstable : (prefixWord ++ tailWord_1242126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242126).length < 2 ^ (prefixWord ++ tailWord_1242126).sum := by decide
  have hdescent : baseEnd_1242126 < baseStart_1242126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242156 : List Nat := [2, 2, 1, 1, 1, 2, 4, 4, 2, 3]
def baseStart_1242156 : Nat := 118140960795 + 1242156 * 2 ^ 59
def prefixEnd_1242156 : Nat := 4983230072969 + 3 ^ 40 * 1242156 * 2
def baseEnd_1242156 : Nat := 425215383910898195091623

theorem tailTrace_1242156 : CollatzResearch.WordTrace tailWord_1242156 prefixEnd_1242156 425215383910898195091623 := by
  unfold tailWord_1242156
  simp only [CollatzResearch.WordTrace]
  refine ⟨22652575643944215100157161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30203434191925620133542881 22652575643944215100157161)
  ·
    refine ⟨16989431732958161325117871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22652575643944215100157161 16989431732958161325117871)
    ·
      refine ⟨25484147599437241987676807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16989431732958161325117871 25484147599437241987676807)
      ·
        refine ⟨38226221399155862981515211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25484147599437241987676807 38226221399155862981515211)
        ·
          refine ⟨57339332098733794472272817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38226221399155862981515211 57339332098733794472272817)
          ·
            refine ⟨43004499074050345854204613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57339332098733794472272817 43004499074050345854204613)
            ·
              refine ⟨8063343576384439847663365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43004499074050345854204613 8063343576384439847663365)
              ·
                refine ⟨1511876920572082471436881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8063343576384439847663365 1511876920572082471436881)
                ·
                  refine ⟨1133907690429061853577661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1511876920572082471436881 1133907690429061853577661)
                  ·
                    refine ⟨425215383910898195091623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1133907690429061853577661 425215383910898195091623)
                    ·
                      rfl

theorem cell22_1242156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_1242156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242156 prefixEnd_1242156 := by exact prefixLift 1242156
  have htrace : WordTrace (prefixWord ++ tailWord_1242156) baseStart_1242156 baseEnd_1242156 := by
    simpa [prefixWord, tailWord_1242156, baseEnd_1242156] using wordTrace_append hprefix tailTrace_1242156
  have hstable : (prefixWord ++ tailWord_1242156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242156).length < 2 ^ (prefixWord ++ tailWord_1242156).sum := by decide
  have hdescent : baseEnd_1242156 < baseStart_1242156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242169 : List Nat := [1, 2, 1, 5, 2, 1, 1, 9]
def baseStart_1242169 : Nat := 118140960795 + 1242169 * 2 ^ 59
def prefixEnd_1242169 : Nat := 4983230072969 + 3 ^ 40 * 1242169 * 2
def baseEnd_1242169 : Nat := 47246648230730054946287

theorem tailTrace_1242169 : CollatzResearch.WordTrace tailWord_1242169 prefixEnd_1242169 47246648230730054946287 := by
  unfold tailWord_1242169
  simp only [CollatzResearch.WordTrace]
  refine ⟨45305625436841333420537561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30203750291227555613691707 45305625436841333420537561)
  ·
    refine ⟨33979219077631000065403171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45305625436841333420537561 33979219077631000065403171)
    ·
      refine ⟨50968828616446500098104757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33979219077631000065403171 50968828616446500098104757)
      ·
        refine ⟨4778327682791859384197321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50968828616446500098104757 4778327682791859384197321)
        ·
          refine ⟨3583745762093894538147991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4778327682791859384197321 3583745762093894538147991)
          ·
            refine ⟨5375618643140841807221987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3583745762093894538147991 5375618643140841807221987)
            ·
              refine ⟨8063427964711262710832981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5375618643140841807221987 8063427964711262710832981)
              ·
                refine ⟨47246648230730054946287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8063427964711262710832981 47246648230730054946287)
                ·
                  rfl

theorem cell22_1242169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 9].length) (baseStart_1242169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242169 prefixEnd_1242169 := by exact prefixLift 1242169
  have htrace : WordTrace (prefixWord ++ tailWord_1242169) baseStart_1242169 baseEnd_1242169 := by
    simpa [prefixWord, tailWord_1242169, baseEnd_1242169] using wordTrace_append hprefix tailTrace_1242169
  have hstable : (prefixWord ++ tailWord_1242169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242169).length < 2 ^ (prefixWord ++ tailWord_1242169).sum := by decide
  have hdescent : baseEnd_1242169 < baseStart_1242169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242173 : List Nat := [1, 4, 1, 3, 1, 3, 1, 3, 2, 3]
def baseStart_1242173 : Nat := 118140960795 + 1242173 * 2 ^ 59
def prefixEnd_1242173 : Nat := 4983230072969 + 3 ^ 40 * 1242173 * 2
def baseEnd_1242173 : Nat := 425221203358315817416571

theorem tailTrace_1242173 : CollatzResearch.WordTrace tailWord_1242173 prefixEnd_1242173 425221203358315817416571 := by
  unfold tailWord_1242173
  simp only [CollatzResearch.WordTrace]
  refine ⟨45305771328826842103683173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30203847552551228069122115 45305771328826842103683173)
  ·
    refine ⟨8494832124155032894440595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45305771328826842103683173 8494832124155032894440595)
    ·
      refine ⟨12742248186232549341660893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8494832124155032894440595 12742248186232549341660893)
      ·
        refine ⟨4778343069837206003122835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12742248186232549341660893 4778343069837206003122835)
        ·
          refine ⟨7167514604755809004684253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4778343069837206003122835 7167514604755809004684253)
          ·
            refine ⟨2687817976783428376756595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7167514604755809004684253 2687817976783428376756595)
            ·
              refine ⟨4031726965175142565134893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2687817976783428376756595 4031726965175142565134893)
              ·
                refine ⟨1511897611940678461925585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4031726965175142565134893 1511897611940678461925585)
                ·
                  refine ⟨1133923208955508846444189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1511897611940678461925585 1133923208955508846444189)
                  ·
                    refine ⟨425221203358315817416571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1133923208955508846444189 425221203358315817416571)
                    ·
                      rfl

theorem cell22_1242173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_1242173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242173 prefixEnd_1242173 := by exact prefixLift 1242173
  have htrace : WordTrace (prefixWord ++ tailWord_1242173) baseStart_1242173 baseEnd_1242173 := by
    simpa [prefixWord, tailWord_1242173, baseEnd_1242173] using wordTrace_append hprefix tailTrace_1242173
  have hstable : (prefixWord ++ tailWord_1242173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242173).length < 2 ^ (prefixWord ++ tailWord_1242173).sum := by decide
  have hdescent : baseEnd_1242173 < baseStart_1242173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242276 : List Nat := [2, 3, 1, 2, 3, 1, 1, 3, 6]
def baseStart_1242276 : Nat := 118140960795 + 1242276 * 2 ^ 59
def prefixEnd_1242276 : Nat := 4983230072969 + 3 ^ 40 * 1242276 * 2
def baseEnd_1242276 : Nat := 141752154121085960697085

theorem tailTrace_1242276 : CollatzResearch.WordTrace tailWord_1242276 prefixEnd_1242276 141752154121085960697085 := by
  unfold tailWord_1242276
  simp only [CollatzResearch.WordTrace]
  refine ⟨22654764023726845347341341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30206352031635793796455121 22654764023726845347341341)
  ·
    refine ⟨8495536508897567005253003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22654764023726845347341341 8495536508897567005253003)
    ·
      refine ⟨12743304763346350507879505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8495536508897567005253003 12743304763346350507879505)
      ·
        refine ⟨9557478572509762880909629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12743304763346350507879505 9557478572509762880909629)
        ·
          refine ⟨3584054464691161080341111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9557478572509762880909629 3584054464691161080341111)
          ·
            refine ⟨5376081697036741620511667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3584054464691161080341111 5376081697036741620511667)
            ·
              refine ⟨8064122545555112430767501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5376081697036741620511667 8064122545555112430767501)
              ·
                refine ⟨3024045954583167161537813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8064122545555112430767501 3024045954583167161537813)
                ·
                  refine ⟨141752154121085960697085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3024045954583167161537813 141752154121085960697085)
                  ·
                    rfl

theorem cell22_1242276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_1242276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242276 prefixEnd_1242276 := by exact prefixLift 1242276
  have htrace : WordTrace (prefixWord ++ tailWord_1242276) baseStart_1242276 baseEnd_1242276 := by
    simpa [prefixWord, tailWord_1242276, baseEnd_1242276] using wordTrace_append hprefix tailTrace_1242276
  have hstable : (prefixWord ++ tailWord_1242276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242276).length < 2 ^ (prefixWord ++ tailWord_1242276).sum := by decide
  have hdescent : baseEnd_1242276 < baseStart_1242276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242291 : List Nat := [1, 1, 1, 2, 3, 2, 5, 1, 1, 5]
def baseStart_1242291 : Nat := 118140960795 + 1242291 * 2 ^ 59
def prefixEnd_1242291 : Nat := 4983230072969 + 3 ^ 40 * 1242291 * 2
def baseEnd_1242291 : Nat := 425261597169802842966209

theorem tailTrace_1242291 : CollatzResearch.WordTrace tailWord_1242291 prefixEnd_1242291 425261597169802842966209 := by
  unfold tailWord_1242291
  simp only [CollatzResearch.WordTrace]
  refine ⟨45310075142399348256478727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30206716761599565504319151 45310075142399348256478727)
  ·
    refine ⟨67965112713599022384718091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45310075142399348256478727 67965112713599022384718091)
    ·
      refine ⟨101947669070398533577077137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67965112713599022384718091 101947669070398533577077137)
      ·
        refine ⟨76460751802798900182807853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101947669070398533577077137 76460751802798900182807853)
        ·
          refine ⟨28672781926049587568552945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76460751802798900182807853 28672781926049587568552945)
          ·
            refine ⟨21504586444537190676414709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28672781926049587568552945 21504586444537190676414709)
            ·
              refine ⟨2016054979175361625913879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21504586444537190676414709 2016054979175361625913879)
              ·
                refine ⟨3024082468763042438870819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2016054979175361625913879 3024082468763042438870819)
                ·
                  refine ⟨4536123703144563658306229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3024082468763042438870819 4536123703144563658306229)
                  ·
                    refine ⟨425261597169802842966209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4536123703144563658306229 425261597169802842966209)
                    ·
                      rfl

theorem cell22_1242291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 5].length) (baseStart_1242291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242291 prefixEnd_1242291 := by exact prefixLift 1242291
  have htrace : WordTrace (prefixWord ++ tailWord_1242291) baseStart_1242291 baseEnd_1242291 := by
    simpa [prefixWord, tailWord_1242291, baseEnd_1242291] using wordTrace_append hprefix tailTrace_1242291
  have hstable : (prefixWord ++ tailWord_1242291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242291).length < 2 ^ (prefixWord ++ tailWord_1242291).sum := by decide
  have hdescent : baseEnd_1242291 < baseStart_1242291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242430 : List Nat := [4, 2, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_1242430 : Nat := 118140960795 + 1242430 * 2 ^ 59
def prefixEnd_1242430 : Nat := 4983230072969 + 3 ^ 40 * 1242430 * 2
def baseEnd_1242430 : Nat := 425309179710452813740783

theorem tailTrace_1242430 : CollatzResearch.WordTrace tailWord_1242430 prefixEnd_1242430 425309179710452813740783 := by
  unfold tailWord_1242430
  simp only [CollatzResearch.WordTrace]
  refine ⟨5664393111111971874473593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30210096592597183330525829 5664393111111971874473593)
  ·
    refine ⟨4248294833333978905855195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5664393111111971874473593 4248294833333978905855195)
    ·
      refine ⟨6372442250000968358782793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4248294833333978905855195 6372442250000968358782793)
      ·
        refine ⟨4779331687500726269087095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6372442250000968358782793 4779331687500726269087095)
        ·
          refine ⟨7168997531251089403630643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4779331687500726269087095 7168997531251089403630643)
          ·
            refine ⟨10753496296876634105445965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7168997531251089403630643 10753496296876634105445965)
            ·
              refine ⟨4032561111328737789542237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10753496296876634105445965 4032561111328737789542237)
              ·
                refine ⟨1512210416748276671078339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4032561111328737789542237 1512210416748276671078339)
                ·
                  refine ⟨2268315625122415006617509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1512210416748276671078339 2268315625122415006617509)
                  ·
                    refine ⟨425309179710452813740783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2268315625122415006617509 425309179710452813740783)
                    ·
                      rfl

theorem cell22_1242430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_1242430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242430 prefixEnd_1242430 := by exact prefixLift 1242430
  have htrace : WordTrace (prefixWord ++ tailWord_1242430) baseStart_1242430 baseEnd_1242430 := by
    simpa [prefixWord, tailWord_1242430, baseEnd_1242430] using wordTrace_append hprefix tailTrace_1242430
  have hstable : (prefixWord ++ tailWord_1242430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242430).length < 2 ^ (prefixWord ++ tailWord_1242430).sum := by decide
  have hdescent : baseEnd_1242430 < baseStart_1242430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242456 : List Nat := [2, 1, 2, 2, 1, 1, 4, 9]
def baseStart_1242456 : Nat := 118140960795 + 1242456 * 2 ^ 59
def prefixEnd_1242456 : Nat := 4983230072969 + 3 ^ 40 * 1242456 * 2
def baseEnd_1242456 : Nat := 47257564449088601398967

theorem tailTrace_1242456 : CollatzResearch.WordTrace tailWord_1242456 prefixEnd_1242456 47257564449088601398967 := by
  unfold tailWord_1242456
  simp only [CollatzResearch.WordTrace]
  refine ⟨22658046593400790718117611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30210728791201054290823481 22658046593400790718117611)
  ·
    refine ⟨33987069890101186077176417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22658046593400790718117611 33987069890101186077176417)
    ·
      refine ⟨25490302417575889557882313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33987069890101186077176417 25490302417575889557882313)
      ·
        refine ⟨19117726813181917168411735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25490302417575889557882313 19117726813181917168411735)
        ·
          refine ⟨28676590219772875752617603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19117726813181917168411735 28676590219772875752617603)
          ·
            refine ⟨43014885329659313628926405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28676590219772875752617603 43014885329659313628926405)
            ·
              refine ⟨8065290999311121305423701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43014885329659313628926405 8065290999311121305423701)
              ·
                refine ⟨47257564449088601398967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8065290999311121305423701 47257564449088601398967)
                ·
                  rfl

theorem cell22_1242456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 9].length) (baseStart_1242456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242456 prefixEnd_1242456 := by exact prefixLift 1242456
  have htrace : WordTrace (prefixWord ++ tailWord_1242456) baseStart_1242456 baseEnd_1242456 := by
    simpa [prefixWord, tailWord_1242456, baseEnd_1242456] using wordTrace_append hprefix tailTrace_1242456
  have hstable : (prefixWord ++ tailWord_1242456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242456).length < 2 ^ (prefixWord ++ tailWord_1242456).sum := by decide
  have hdescent : baseEnd_1242456 < baseStart_1242456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242582 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1242582 : Nat := 118140960795 + 1242582 * 2 ^ 59
def prefixEnd_1242582 : Nat := 4983230072969 + 3 ^ 40 * 1242582 * 2
def baseEnd_1242582 : Nat := 425361212416775083940317

theorem tailTrace_1242582 : CollatzResearch.WordTrace tailWord_1242582 prefixEnd_1242582 425361212416775083940317 := by
  unfold tailWord_1242582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2832543049021569059707625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30213792522896736636881333 2832543049021569059707625)
  ·
    refine ⟨2124407286766176794780719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2832543049021569059707625 2124407286766176794780719)
    ·
      refine ⟨3186610930149265192171079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2124407286766176794780719 3186610930149265192171079)
      ·
        refine ⟨4779916395223897788256619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3186610930149265192171079 4779916395223897788256619)
        ·
          refine ⟨7169874592835846682384929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4779916395223897788256619 7169874592835846682384929)
          ·
            refine ⟨5377405944626885011788697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7169874592835846682384929 5377405944626885011788697)
            ·
              refine ⟨4033054458470163758841523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5377405944626885011788697 4033054458470163758841523)
              ·
                refine ⟨6049581687705245638262285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4033054458470163758841523 6049581687705245638262285)
                ·
                  refine ⟨2268593132889467114348357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6049581687705245638262285 2268593132889467114348357)
                  ·
                    refine ⟨425361212416775083940317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2268593132889467114348357 425361212416775083940317)
                    ·
                      rfl

theorem cell22_1242582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1242582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242582 prefixEnd_1242582 := by exact prefixLift 1242582
  have htrace : WordTrace (prefixWord ++ tailWord_1242582) baseStart_1242582 baseEnd_1242582 := by
    simpa [prefixWord, tailWord_1242582, baseEnd_1242582] using wordTrace_append hprefix tailTrace_1242582
  have hstable : (prefixWord ++ tailWord_1242582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242582).length < 2 ^ (prefixWord ++ tailWord_1242582).sum := by decide
  have hdescent : baseEnd_1242582 < baseStart_1242582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242595 : List Nat := [1, 1, 1, 6, 2, 1, 2, 2, 1, 5]
def baseStart_1242595 : Nat := 118140960795 + 1242595 * 2 ^ 59
def prefixEnd_1242595 : Nat := 4983230072969 + 3 ^ 40 * 1242595 * 2
def baseEnd_1242595 : Nat := 425365662582447383365277

theorem tailTrace_1242595 : CollatzResearch.WordTrace tailWord_1242595 prefixEnd_1242595 425365662582447383365277 := by
  unfold tailWord_1242595
  simp only [CollatzResearch.WordTrace]
  refine ⟨45321162933298008175545239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30214108622198672117030159 45321162933298008175545239)
  ·
    refine ⟨67981744399947012263317859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45321162933298008175545239 67981744399947012263317859)
    ·
      refine ⟨101972616599920518394976789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67981744399947012263317859 101972616599920518394976789)
      ·
        refine ⟨4779966403121274299764537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 101972616599920518394976789 4779966403121274299764537)
        ·
          refine ⟨3584974802340955724823403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4779966403121274299764537 3584974802340955724823403)
          ·
            refine ⟨5377462203511433587235105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3584974802340955724823403 5377462203511433587235105)
            ·
              refine ⟨4033096652633575190426329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5377462203511433587235105 4033096652633575190426329)
              ·
                refine ⟨3024822489475181392819747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4033096652633575190426329 3024822489475181392819747)
                ·
                  refine ⟨4537233734212772089229621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3024822489475181392819747 4537233734212772089229621)
                  ·
                    refine ⟨425365662582447383365277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4537233734212772089229621 425365662582447383365277)
                    ·
                      rfl

theorem cell22_1242595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 5].length) (baseStart_1242595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242595 prefixEnd_1242595 := by exact prefixLift 1242595
  have htrace : WordTrace (prefixWord ++ tailWord_1242595) baseStart_1242595 baseEnd_1242595 := by
    simpa [prefixWord, tailWord_1242595, baseEnd_1242595] using wordTrace_append hprefix tailTrace_1242595
  have hstable : (prefixWord ++ tailWord_1242595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242595).length < 2 ^ (prefixWord ++ tailWord_1242595).sum := by decide
  have hdescent : baseEnd_1242595 < baseStart_1242595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242597 : List Nat := [1, 3, 1, 5, 1, 1, 1, 5, 4]
def baseStart_1242597 : Nat := 118140960795 + 1242597 * 2 ^ 59
def prefixEnd_1242597 : Nat := 4983230072969 + 3 ^ 40 * 1242597 * 2
def baseEnd_1242597 : Nat := 141788782407773348271757

theorem tailTrace_1242597 : CollatzResearch.WordTrace tailWord_1242597 prefixEnd_1242597 141788782407773348271757 := by
  unfold tailWord_1242597
  simp only [CollatzResearch.WordTrace]
  refine ⟨45321235879290762517118045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30214157252860508344745363 45321235879290762517118045)
  ·
    refine ⟨16995463454734035943919267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45321235879290762517118045 16995463454734035943919267)
    ·
      refine ⟨25493195182101053915878901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16995463454734035943919267 25493195182101053915878901)
      ·
        refine ⟨2389987048321973804613647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25493195182101053915878901 2389987048321973804613647)
        ·
          refine ⟨3584980572482960706920471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2389987048321973804613647 3584980572482960706920471)
          ·
            refine ⟨5377470858724441060380707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3584980572482960706920471 5377470858724441060380707)
            ·
              refine ⟨8066206288086661590571061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5377470858724441060380707 8066206288086661590571061)
              ·
                refine ⟨756206839508124524116037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8066206288086661590571061 756206839508124524116037)
                ·
                  refine ⟨141788782407773348271757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 756206839508124524116037 141788782407773348271757)
                  ·
                    rfl

theorem cell22_1242597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 4].length) (baseStart_1242597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242597 prefixEnd_1242597 := by exact prefixLift 1242597
  have htrace : WordTrace (prefixWord ++ tailWord_1242597) baseStart_1242597 baseEnd_1242597 := by
    simpa [prefixWord, tailWord_1242597, baseEnd_1242597] using wordTrace_append hprefix tailTrace_1242597
  have hstable : (prefixWord ++ tailWord_1242597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242597).length < 2 ^ (prefixWord ++ tailWord_1242597).sum := by decide
  have hdescent : baseEnd_1242597 < baseStart_1242597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242599 : List Nat := [1, 1, 5, 2, 1, 4, 2, 1, 1, 4]
def baseStart_1242599 : Nat := 118140960795 + 1242599 * 2 ^ 59
def prefixEnd_1242599 : Nat := 4983230072969 + 3 ^ 40 * 1242599 * 2
def baseEnd_1242599 : Nat := 425367031864192706265265

theorem tailTrace_1242599 : CollatzResearch.WordTrace tailWord_1242599 prefixEnd_1242599 425367031864192706265265 := by
  unfold tailWord_1242599
  simp only [CollatzResearch.WordTrace]
  refine ⟨45321308825283516858690851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30214205883522344572460567 45321308825283516858690851)
  ·
    refine ⟨67981963237925275288036277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45321308825283516858690851 67981963237925275288036277)
    ·
      refine ⟨6373309053555494558253401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67981963237925275288036277 6373309053555494558253401)
      ·
        refine ⟨4779981790166620918690051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6373309053555494558253401 4779981790166620918690051)
        ·
          refine ⟨7169972685249931378035077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4779981790166620918690051 7169972685249931378035077)
          ·
            refine ⟨1344369878484362133381577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7169972685249931378035077 1344369878484362133381577)
            ·
              refine ⟨1008277408863271600036183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1344369878484362133381577 1008277408863271600036183)
              ·
                refine ⟨1512416113294907400054275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008277408863271600036183 1512416113294907400054275)
                ·
                  refine ⟨2268624169942361100081413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1512416113294907400054275 2268624169942361100081413)
                  ·
                    refine ⟨425367031864192706265265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2268624169942361100081413 425367031864192706265265)
                    ·
                      rfl

theorem cell22_1242599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_1242599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242599 prefixEnd_1242599 := by exact prefixLift 1242599
  have htrace : WordTrace (prefixWord ++ tailWord_1242599) baseStart_1242599 baseEnd_1242599 := by
    simpa [prefixWord, tailWord_1242599, baseEnd_1242599] using wordTrace_append hprefix tailTrace_1242599
  have hstable : (prefixWord ++ tailWord_1242599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242599).length < 2 ^ (prefixWord ++ tailWord_1242599).sum := by decide
  have hdescent : baseEnd_1242599 < baseStart_1242599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242608 : List Nat := [2, 1, 1, 1, 3, 5, 9]
def baseStart_1242608 : Nat := 118140960795 + 1242608 * 2 ^ 59
def prefixEnd_1242608 : Nat := 4983230072969 + 3 ^ 40 * 1242608 * 2
def baseEnd_1242608 : Nat := 15754448620300728992231

theorem tailTrace_1242608 : CollatzResearch.WordTrace tailWord_1242608 prefixEnd_1242608 15754448620300728992231 := by
  unfold tailWord_1242608
  simp only [CollatzResearch.WordTrace]
  refine ⟨22660818541125455697884239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30214424721500607597178985 22660818541125455697884239)
  ·
    refine ⟨33991227811688183546826359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22660818541125455697884239 33991227811688183546826359)
    ·
      refine ⟨50986841717532275320239539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33991227811688183546826359 50986841717532275320239539)
      ·
        refine ⟨76480262576298412980359309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50986841717532275320239539 76480262576298412980359309)
        ·
          refine ⟨28680098466111904867634741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76480262576298412980359309 28680098466111904867634741)
          ·
            refine ⟨2688759231197991081340757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28680098466111904867634741 2688759231197991081340757)
            ·
              refine ⟨15754448620300728992231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2688759231197991081340757 15754448620300728992231)
              ·
                rfl

theorem cell22_1242608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 9].length) (baseStart_1242608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242608 prefixEnd_1242608 := by exact prefixLift 1242608
  have htrace : WordTrace (prefixWord ++ tailWord_1242608) baseStart_1242608 baseEnd_1242608 := by
    simpa [prefixWord, tailWord_1242608, baseEnd_1242608] using wordTrace_append hprefix tailTrace_1242608
  have hstable : (prefixWord ++ tailWord_1242608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242608).length < 2 ^ (prefixWord ++ tailWord_1242608).sum := by decide
  have hdescent : baseEnd_1242608 < baseStart_1242608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242687 : List Nat := [1, 1, 2, 2, 3, 3, 4, 1, 5]
def baseStart_1242687 : Nat := 118140960795 + 1242687 * 2 ^ 59
def prefixEnd_1242687 : Nat := 4983230072969 + 3 ^ 40 * 1242687 * 2
def baseEnd_1242687 : Nat := 141799052020863270021665

theorem tailTrace_1242687 : CollatzResearch.WordTrace tailWord_1242687 prefixEnd_1242687 141799052020863270021665 := by
  unfold tailWord_1242687
  simp only [CollatzResearch.WordTrace]
  refine ⟨45324518448964707887894315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30216345632643138591929543 45324518448964707887894315)
  ·
    refine ⟨67986777673447061831841473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45324518448964707887894315 67986777673447061831841473)
    ·
      refine ⟨50990083255085296373881105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67986777673447061831841473 50990083255085296373881105)
      ·
        refine ⟨38242562441313972280410829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50990083255085296373881105 38242562441313972280410829)
        ·
          refine ⟨14340960915492739605154061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38242562441313972280410829 14340960915492739605154061)
          ·
            refine ⟨5377860343309777351932773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14340960915492739605154061 5377860343309777351932773)
            ·
              refine ⟨1008348814370583253487395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5377860343309777351932773 1008348814370583253487395)
              ·
                refine ⟨1512523221555874880231093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008348814370583253487395 1512523221555874880231093)
                ·
                  refine ⟨141799052020863270021665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1512523221555874880231093 141799052020863270021665)
                  ·
                    rfl

theorem cell22_1242687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 5].length) (baseStart_1242687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242687 prefixEnd_1242687 := by exact prefixLift 1242687
  have htrace : WordTrace (prefixWord ++ tailWord_1242687) baseStart_1242687 baseEnd_1242687 := by
    simpa [prefixWord, tailWord_1242687, baseEnd_1242687] using wordTrace_append hprefix tailTrace_1242687
  have hstable : (prefixWord ++ tailWord_1242687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242687).length < 2 ^ (prefixWord ++ tailWord_1242687).sum := by decide
  have hdescent : baseEnd_1242687 < baseStart_1242687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242745 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 1, 6]
def baseStart_1242745 : Nat := 118140960795 + 1242745 * 2 ^ 59
def prefixEnd_1242745 : Nat := 4983230072969 + 3 ^ 40 * 1242745 * 2
def baseEnd_1242745 : Nat := 425417010647896992114817

theorem tailTrace_1242745 : CollatzResearch.WordTrace tailWord_1242745 prefixEnd_1242745 425417010647896992114817 := by
  unfold tailWord_1242745
  simp only [CollatzResearch.WordTrace]
  refine ⟨45326633882754583793505689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30217755921836389195670459 45326633882754583793505689)
  ·
    refine ⟨33994975412065937845129267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45326633882754583793505689 33994975412065937845129267)
    ·
      refine ⟨50992463118098906767693901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33994975412065937845129267 50992463118098906767693901)
      ·
        refine ⟨19122173669287090037885213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50992463118098906767693901 19122173669287090037885213)
        ·
          refine ⟨7170815125982658764206955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19122173669287090037885213 7170815125982658764206955)
          ·
            refine ⟨10756222688973988146310433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7170815125982658764206955 10756222688973988146310433)
            ·
              refine ⟨8067167016730491109732825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10756222688973988146310433 8067167016730491109732825)
              ·
                refine ⟨6050375262547868332299619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8067167016730491109732825 6050375262547868332299619)
                ·
                  refine ⟨9075562893821802498449429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6050375262547868332299619 9075562893821802498449429)
                  ·
                    refine ⟨425417010647896992114817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9075562893821802498449429 425417010647896992114817)
                    ·
                      rfl

theorem cell22_1242745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_1242745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242745 prefixEnd_1242745 := by exact prefixLift 1242745
  have htrace : WordTrace (prefixWord ++ tailWord_1242745) baseStart_1242745 baseEnd_1242745 := by
    simpa [prefixWord, tailWord_1242745, baseEnd_1242745] using wordTrace_append hprefix tailTrace_1242745
  have hstable : (prefixWord ++ tailWord_1242745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242745).length < 2 ^ (prefixWord ++ tailWord_1242745).sum := by decide
  have hdescent : baseEnd_1242745 < baseStart_1242745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242747 : List Nat := [1, 1, 1, 1, 1, 4, 3, 5, 2, 3]
def baseStart_1242747 : Nat := 118140960795 + 1242747 * 2 ^ 59
def prefixEnd_1242747 : Nat := 4983230072969 + 3 ^ 40 * 1242747 * 2
def baseEnd_1242747 : Nat := 425417695288769653564811

theorem tailTrace_1242747 : CollatzResearch.WordTrace tailWord_1242747 prefixEnd_1242747 425417695288769653564811 := by
  unfold tailWord_1242747
  simp only [CollatzResearch.WordTrace]
  refine ⟨45326706828747338135078495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30217804552498225423385663 45326706828747338135078495)
  ·
    refine ⟨67990060243121007202617743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45326706828747338135078495 67990060243121007202617743)
    ·
      refine ⟨101985090364681510803926615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67990060243121007202617743 101985090364681510803926615)
      ·
        refine ⟨152977635547022266205889923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101985090364681510803926615 152977635547022266205889923)
        ·
          refine ⟨229466453320533399308834885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152977635547022266205889923 229466453320533399308834885)
          ·
            refine ⟨43024959997600012370406541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 229466453320533399308834885 43024959997600012370406541)
            ·
              refine ⟨16134359999100004638902453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43024959997600012370406541 16134359999100004638902453)
              ·
                refine ⟨1512596249915625434897105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16134359999100004638902453 1512596249915625434897105)
                ·
                  refine ⟨1134447187436719076172829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1512596249915625434897105 1134447187436719076172829)
                  ·
                    refine ⟨425417695288769653564811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1134447187436719076172829 425417695288769653564811)
                    ·
                      rfl

theorem cell22_1242747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 3].length) (baseStart_1242747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242747 prefixEnd_1242747 := by exact prefixLift 1242747
  have htrace : WordTrace (prefixWord ++ tailWord_1242747) baseStart_1242747 baseEnd_1242747 := by
    simpa [prefixWord, tailWord_1242747, baseEnd_1242747] using wordTrace_append hprefix tailTrace_1242747
  have hstable : (prefixWord ++ tailWord_1242747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242747).length < 2 ^ (prefixWord ++ tailWord_1242747).sum := by decide
  have hdescent : baseEnd_1242747 < baseStart_1242747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242762 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 1, 6]
def baseStart_1242762 : Nat := 118140960795 + 1242762 * 2 ^ 59
def prefixEnd_1242762 : Nat := 4983230072969 + 3 ^ 40 * 1242762 * 2
def baseEnd_1242762 : Nat := 425422830095314614439765

theorem tailTrace_1242762 : CollatzResearch.WordTrace tailWord_1242762 prefixEnd_1242762 425422830095314614439765 := by
  unfold tailWord_1242762
  simp only [CollatzResearch.WordTrace]
  refine ⟨11331813480923248924218635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30218169282461997131249693 11331813480923248924218635)
  ·
    refine ⟨16997720221384873386327953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11331813480923248924218635 16997720221384873386327953)
    ·
      refine ⟨12748290166038655039745965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16997720221384873386327953 12748290166038655039745965)
      ·
        refine ⟨4780608812264495639904737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12748290166038655039745965 4780608812264495639904737)
        ·
          refine ⟨3585456609198371729928553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4780608812264495639904737 3585456609198371729928553)
          ·
            refine ⟨2689092456898778797446415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3585456609198371729928553 2689092456898778797446415)
            ·
              refine ⟨4033638685348168196169623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2689092456898778797446415 4033638685348168196169623)
              ·
                refine ⟨6050458028022252294254435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4033638685348168196169623 6050458028022252294254435)
                ·
                  refine ⟨9075687042033378441381653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6050458028022252294254435 9075687042033378441381653)
                  ·
                    refine ⟨425422830095314614439765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9075687042033378441381653 425422830095314614439765)
                    ·
                      rfl

theorem cell22_1242762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_1242762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242762 prefixEnd_1242762 := by exact prefixLift 1242762
  have htrace : WordTrace (prefixWord ++ tailWord_1242762) baseStart_1242762 baseEnd_1242762 := by
    simpa [prefixWord, tailWord_1242762, baseEnd_1242762] using wordTrace_append hprefix tailTrace_1242762
  have hstable : (prefixWord ++ tailWord_1242762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242762).length < 2 ^ (prefixWord ++ tailWord_1242762).sum := by decide
  have hdescent : baseEnd_1242762 < baseStart_1242762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242798 : List Nat := [4, 1, 4, 1, 3, 1, 1, 1, 1, 5]
def baseStart_1242798 : Nat := 118140960795 + 1242798 * 2 ^ 59
def prefixEnd_1242798 : Nat := 4983230072969 + 3 ^ 40 * 1242798 * 2
def baseEnd_1242798 : Nat := 425435153631022520539655

theorem tailTrace_1242798 : CollatzResearch.WordTrace tailWord_1242798 prefixEnd_1242798 425435153631022520539655 := by
  unfold tailWord_1242798
  simp only [CollatzResearch.WordTrace]
  refine ⟨5666070868945321730648131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30219044634375049230123365 5666070868945321730648131)
  ·
    refine ⟨8499106303417982595972197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5666070868945321730648131 8499106303417982595972197)
    ·
      refine ⟨1593582431890871736744787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8499106303417982595972197 1593582431890871736744787)
      ·
        refine ⟨2390373647836307605117181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1593582431890871736744787 2390373647836307605117181)
        ·
          refine ⟨896390117938615351918943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2390373647836307605117181 896390117938615351918943)
          ·
            refine ⟨1344585176907923027878415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 896390117938615351918943 1344585176907923027878415)
            ·
              refine ⟨2016877765361884541817623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1344585176907923027878415 2016877765361884541817623)
              ·
                refine ⟨3025316648042826812726435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2016877765361884541817623 3025316648042826812726435)
                ·
                  refine ⟨4537974972064240219089653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3025316648042826812726435 4537974972064240219089653)
                  ·
                    refine ⟨425435153631022520539655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4537974972064240219089653 425435153631022520539655)
                    ·
                      rfl

theorem cell22_1242798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_1242798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242798 prefixEnd_1242798 := by exact prefixLift 1242798
  have htrace : WordTrace (prefixWord ++ tailWord_1242798) baseStart_1242798 baseEnd_1242798 := by
    simpa [prefixWord, tailWord_1242798, baseEnd_1242798] using wordTrace_append hprefix tailTrace_1242798
  have hstable : (prefixWord ++ tailWord_1242798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242798).length < 2 ^ (prefixWord ++ tailWord_1242798).sum := by decide
  have hdescent : baseEnd_1242798 < baseStart_1242798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242852 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_1242852 : Nat := 118140960795 + 1242852 * 2 ^ 59
def prefixEnd_1242852 : Nat := 4983230072969 + 3 ^ 40 * 1242852 * 2
def baseEnd_1242852 : Nat := 425453638934584379689489

theorem tailTrace_1242852 : CollatzResearch.WordTrace tailWord_1242852 prefixEnd_1242852 425453638934584379689489 := by
  unfold tailWord_1242852
  simp only [CollatzResearch.WordTrace]
  refine ⟨22665268246683470533825405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30220357662244627378433873 22665268246683470533825405)
  ·
    refine ⟨8499475592506301450184527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22665268246683470533825405 8499475592506301450184527)
    ·
      refine ⟨12749213388759452175276791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8499475592506301450184527 12749213388759452175276791)
      ·
        refine ⟨19123820083139178262915187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12749213388759452175276791 19123820083139178262915187)
        ·
          refine ⟨28685730124708767394372781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19123820083139178262915187 28685730124708767394372781)
          ·
            refine ⟨10757148796765787772889793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28685730124708767394372781 10757148796765787772889793)
            ·
              refine ⟨8067861597574340829667345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10757148796765787772889793 8067861597574340829667345)
              ·
                refine ⟨6050896198180755622250509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8067861597574340829667345 6050896198180755622250509)
                ·
                  refine ⟨2269086074317783358343941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6050896198180755622250509 2269086074317783358343941)
                  ·
                    refine ⟨425453638934584379689489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2269086074317783358343941 425453638934584379689489)
                    ·
                      rfl

theorem cell22_1242852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_1242852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242852 prefixEnd_1242852 := by exact prefixLift 1242852
  have htrace : WordTrace (prefixWord ++ tailWord_1242852) baseStart_1242852 baseEnd_1242852 := by
    simpa [prefixWord, tailWord_1242852, baseEnd_1242852] using wordTrace_append hprefix tailTrace_1242852
  have hstable : (prefixWord ++ tailWord_1242852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242852).length < 2 ^ (prefixWord ++ tailWord_1242852).sum := by decide
  have hdescent : baseEnd_1242852 < baseStart_1242852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242856 : List Nat := [2, 1, 4, 1, 3, 3, 2, 1, 5]
def baseStart_1242856 : Nat := 118140960795 + 1242856 * 2 ^ 59
def prefixEnd_1242856 : Nat := 4983230072969 + 3 ^ 40 * 1242856 * 2
def baseEnd_1242856 : Nat := 141818336072109900863159

theorem tailTrace_1242856 : CollatzResearch.WordTrace tailWord_1242856 prefixEnd_1242856 141818336072109900863159 := by
  unfold tailWord_1242856
  simp only [CollatzResearch.WordTrace]
  refine ⟨22665341192676224875398211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30220454923568299833864281 22665341192676224875398211)
  ·
    refine ⟨33998011789014337313097317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22665341192676224875398211 33998011789014337313097317)
    ·
      refine ⟨6374627210440188246205747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33998011789014337313097317 6374627210440188246205747)
      ·
        refine ⟨9561940815660282369308621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6374627210440188246205747 9561940815660282369308621)
        ·
          refine ⟨3585727805872605888490733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9561940815660282369308621 3585727805872605888490733)
          ·
            refine ⟨1344647927202227208184025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3585727805872605888490733 1344647927202227208184025)
            ·
              refine ⟨1008485945401670406138019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1344647927202227208184025 1008485945401670406138019)
              ·
                refine ⟨1512728918102505609207029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008485945401670406138019 1512728918102505609207029)
                ·
                  refine ⟨141818336072109900863159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1512728918102505609207029 141818336072109900863159)
                  ·
                    rfl

theorem cell22_1242856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 5].length) (baseStart_1242856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242856 prefixEnd_1242856 := by exact prefixLift 1242856
  have htrace : WordTrace (prefixWord ++ tailWord_1242856) baseStart_1242856 baseEnd_1242856 := by
    simpa [prefixWord, tailWord_1242856, baseEnd_1242856] using wordTrace_append hprefix tailTrace_1242856
  have hstable : (prefixWord ++ tailWord_1242856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242856).length < 2 ^ (prefixWord ++ tailWord_1242856).sum := by decide
  have hdescent : baseEnd_1242856 < baseStart_1242856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242901 : List Nat := [1, 3, 2, 1, 2, 3, 4, 2, 4]
def baseStart_1242901 : Nat := 118140960795 + 1242901 * 2 ^ 59
def prefixEnd_1242901 : Nat := 4983230072969 + 3 ^ 40 * 1242901 * 2
def baseEnd_1242901 : Nat := 141823470878654861738113

theorem tailTrace_1242901 : CollatzResearch.WordTrace tailWord_1242901 prefixEnd_1242901 141823470878654861738113 := by
  unfold tailWord_1242901
  simp only [CollatzResearch.WordTrace]
  refine ⟨45332323670189422436184557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30221549113459614957456371 45332323670189422436184557)
  ·
    refine ⟨16999621376321033413569209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45332323670189422436184557 16999621376321033413569209)
    ·
      refine ⟨12749716032240775060176907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16999621376321033413569209 12749716032240775060176907)
      ·
        refine ⟨19124574048361162590265361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12749716032240775060176907 19124574048361162590265361)
        ·
          refine ⟨14343430536270871942699021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19124574048361162590265361 14343430536270871942699021)
          ·
            refine ⟨5378786451101576978512133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14343430536270871942699021 5378786451101576978512133)
            ·
              refine ⟨1008522459581545683471025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5378786451101576978512133 1008522459581545683471025)
              ·
                refine ⟨756391844686159262603269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1008522459581545683471025 756391844686159262603269)
                ·
                  refine ⟨141823470878654861738113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 756391844686159262603269 141823470878654861738113)
                  ·
                    rfl

theorem cell22_1242901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 4].length) (baseStart_1242901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242901 prefixEnd_1242901 := by exact prefixLift 1242901
  have htrace : WordTrace (prefixWord ++ tailWord_1242901) baseStart_1242901 baseEnd_1242901 := by
    simpa [prefixWord, tailWord_1242901, baseEnd_1242901] using wordTrace_append hprefix tailTrace_1242901
  have hstable : (prefixWord ++ tailWord_1242901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242901).length < 2 ^ (prefixWord ++ tailWord_1242901).sum := by decide
  have hdescent : baseEnd_1242901 < baseStart_1242901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242916 : List Nat := [2, 3, 1, 3, 2, 1, 2, 3, 2, 3]
def baseStart_1242916 : Nat := 118140960795 + 1242916 * 2 ^ 59
def prefixEnd_1242916 : Nat := 4983230072969 + 3 ^ 40 * 1242916 * 2
def baseEnd_1242916 : Nat := 425475547442509546089293

theorem tailTrace_1242916 : CollatzResearch.WordTrace tailWord_1242916 prefixEnd_1242916 425475547442509546089293 := by
  unfold tailWord_1242916
  simp only [CollatzResearch.WordTrace]
  refine ⟨22666435382567539998990301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30221913843423386665320401 22666435382567539998990301)
  ·
    refine ⟨8499913268462827499621363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22666435382567539998990301 8499913268462827499621363)
    ·
      refine ⟨12749869902694241249432045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8499913268462827499621363 12749869902694241249432045)
      ·
        refine ⟨4781201213510340468537017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12749869902694241249432045 4781201213510340468537017)
        ·
          refine ⟨3585900910132755351402763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4781201213510340468537017 3585900910132755351402763)
          ·
            refine ⟨5378851365199133027104145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3585900910132755351402763 5378851365199133027104145)
            ·
              refine ⟨4034138523899349770328109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5378851365199133027104145 4034138523899349770328109)
              ·
                refine ⟨1512801946462256163873041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4034138523899349770328109 1512801946462256163873041)
                ·
                  refine ⟨1134601459846692122904781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1512801946462256163873041 1134601459846692122904781)
                  ·
                    refine ⟨425475547442509546089293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1134601459846692122904781 425475547442509546089293)
                    ·
                      rfl

theorem cell22_1242916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_1242916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242916 prefixEnd_1242916 := by exact prefixLift 1242916
  have htrace : WordTrace (prefixWord ++ tailWord_1242916) baseStart_1242916 baseEnd_1242916 := by
    simpa [prefixWord, tailWord_1242916, baseEnd_1242916] using wordTrace_append hprefix tailTrace_1242916
  have hstable : (prefixWord ++ tailWord_1242916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242916).length < 2 ^ (prefixWord ++ tailWord_1242916).sum := by decide
  have hdescent : baseEnd_1242916 < baseStart_1242916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242929 : List Nat := [1, 2, 2, 3, 2, 3, 3, 6]
def baseStart_1242929 : Nat := 118140960795 + 1242929 * 2 ^ 59
def prefixEnd_1242929 : Nat := 4983230072969 + 3 ^ 40 * 1242929 * 2
def baseEnd_1242929 : Nat := 47275555289797982834917

theorem tailTrace_1242929 : CollatzResearch.WordTrace tailWord_1242929 prefixEnd_1242929 47275555289797982834917 := by
  unfold tailWord_1242929
  simp only [CollatzResearch.WordTrace]
  refine ⟨45333344914087983218203841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30222229942725322145469227 45333344914087983218203841)
  ·
    refine ⟨34000008685565987413652881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45333344914087983218203841 34000008685565987413652881)
    ·
      refine ⟨25500006514174490560239661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34000008685565987413652881 25500006514174490560239661)
      ·
        refine ⟨9562502442815433960089873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25500006514174490560239661 9562502442815433960089873)
        ·
          refine ⟨7171876832111575470067405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9562502442815433960089873 7171876832111575470067405)
          ·
            refine ⟨2689453812041840801275277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7171876832111575470067405 2689453812041840801275277)
            ·
              refine ⟨1008545179515690300478229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2689453812041840801275277 1008545179515690300478229)
              ·
                refine ⟨47275555289797982834917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1008545179515690300478229 47275555289797982834917)
                ·
                  rfl

theorem cell22_1242929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 6].length) (baseStart_1242929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242929 prefixEnd_1242929 := by exact prefixLift 1242929
  have htrace : WordTrace (prefixWord ++ tailWord_1242929) baseStart_1242929 baseEnd_1242929 := by
    simpa [prefixWord, tailWord_1242929, baseEnd_1242929] using wordTrace_append hprefix tailTrace_1242929
  have hstable : (prefixWord ++ tailWord_1242929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242929).length < 2 ^ (prefixWord ++ tailWord_1242929).sum := by decide
  have hdescent : baseEnd_1242929 < baseStart_1242929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242931 : List Nat := [1, 1, 1, 2, 7, 2, 1, 1, 2, 4]
def baseStart_1242931 : Nat := 118140960795 + 1242931 * 2 ^ 59
def prefixEnd_1242931 : Nat := 4983230072969 + 3 ^ 40 * 1242931 * 2
def baseEnd_1242931 : Nat := 425480682249054506964247

theorem tailTrace_1242931 : CollatzResearch.WordTrace tailWord_1242931 prefixEnd_1242931 425480682249054506964247 := by
  unfold tailWord_1242931
  simp only [CollatzResearch.WordTrace]
  refine ⟨45333417860080737559776647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30222278573387158373184431 45333417860080737559776647)
  ·
    refine ⟨68000126790121106339664971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45333417860080737559776647 68000126790121106339664971)
    ·
      refine ⟨102000190185181659509497457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68000126790121106339664971 102000190185181659509497457)
      ·
        refine ⟨76500142638886244632123093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102000190185181659509497457 76500142638886244632123093)
        ·
          refine ⟨1792972093098896358565385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 76500142638886244632123093 1792972093098896358565385)
          ·
            refine ⟨1344729069824172268924039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1792972093098896358565385 1344729069824172268924039)
            ·
              refine ⟨2017093604736258403386059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1344729069824172268924039 2017093604736258403386059)
              ·
                refine ⟨3025640407104387605079089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2017093604736258403386059 3025640407104387605079089)
                ·
                  refine ⟨2269230305328290703809317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3025640407104387605079089 2269230305328290703809317)
                  ·
                    refine ⟨425480682249054506964247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2269230305328290703809317 425480682249054506964247)
                    ·
                      rfl

theorem cell22_1242931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 4].length) (baseStart_1242931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242931 prefixEnd_1242931 := by exact prefixLift 1242931
  have htrace : WordTrace (prefixWord ++ tailWord_1242931) baseStart_1242931 baseEnd_1242931 := by
    simpa [prefixWord, tailWord_1242931, baseEnd_1242931] using wordTrace_append hprefix tailTrace_1242931
  have hstable : (prefixWord ++ tailWord_1242931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242931).length < 2 ^ (prefixWord ++ tailWord_1242931).sum := by decide
  have hdescent : baseEnd_1242931 < baseStart_1242931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242950 : List Nat := [6, 1, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_1242950 : Nat := 118140960795 + 1242950 * 2 ^ 59
def prefixEnd_1242950 : Nat := 4983230072969 + 3 ^ 40 * 1242950 * 2
def baseEnd_1242950 : Nat := 425487186337344790739189

theorem tailTrace_1242950 : CollatzResearch.WordTrace tailWord_1242950 prefixEnd_1242950 425487186337344790739189 := by
  unfold tailWord_1242950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1416690963969121993897447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30222740564674602536478869 1416690963969121993897447)
  ·
    refine ⟨2125036445953682990846171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1416690963969121993897447 2125036445953682990846171)
    ·
      refine ⟨3187554668930524486269257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2125036445953682990846171 3187554668930524486269257)
      ·
        refine ⟨2390666001697893364701943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3187554668930524486269257 2390666001697893364701943)
        ·
          refine ⟨3585999002546840047052915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2390666001697893364701943 3585999002546840047052915)
          ·
            refine ⟨5378998503820260070579373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3585999002546840047052915 5378998503820260070579373)
            ·
              refine ⟨2017124438932597526467265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5378998503820260070579373 2017124438932597526467265)
              ·
                refine ⟨1512843329199448144850449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2017124438932597526467265 1512843329199448144850449)
                ·
                  refine ⟨1134632496899586108637837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1512843329199448144850449 1134632496899586108637837)
                  ·
                    refine ⟨425487186337344790739189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1134632496899586108637837 425487186337344790739189)
                    ·
                      rfl

theorem cell22_1242950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_1242950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242950 prefixEnd_1242950 := by exact prefixLift 1242950
  have htrace : WordTrace (prefixWord ++ tailWord_1242950) baseStart_1242950 baseEnd_1242950 := by
    simpa [prefixWord, tailWord_1242950, baseEnd_1242950] using wordTrace_append hprefix tailTrace_1242950
  have hstable : (prefixWord ++ tailWord_1242950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242950).length < 2 ^ (prefixWord ++ tailWord_1242950).sum := by decide
  have hdescent : baseEnd_1242950 < baseStart_1242950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242961 : List Nat := [1, 2, 2, 1, 5, 2, 2, 1, 3, 3]
def baseStart_1242961 : Nat := 118140960795 + 1242961 * 2 ^ 59
def prefixEnd_1242961 : Nat := 4983230072969 + 3 ^ 40 * 1242961 * 2
def baseEnd_1242961 : Nat := 425490951862144428714155

theorem tailTrace_1242961 : CollatzResearch.WordTrace tailWord_1242961 prefixEnd_1242961 425490951862144428714155 := by
  unfold tailWord_1242961
  simp only [CollatzResearch.WordTrace]
  refine ⟨45334512049972052683368737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30223008033314701788912491 45334512049972052683368737)
  ·
    refine ⟨34000884037479039512526553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45334512049972052683368737 34000884037479039512526553)
    ·
      refine ⟨25500663028109279634394915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34000884037479039512526553 25500663028109279634394915)
      ·
        refine ⟨38250994542163919451592373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25500663028109279634394915 38250994542163919451592373)
        ·
          refine ⟨3586030738327867448586785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38250994542163919451592373 3586030738327867448586785)
          ·
            refine ⟨2689523053745900586440089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3586030738327867448586785 2689523053745900586440089)
            ·
              refine ⟨2017142290309425439830067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2689523053745900586440089 2017142290309425439830067)
              ·
                refine ⟨3025713435464138159745101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2017142290309425439830067 3025713435464138159745101)
                ·
                  refine ⟨1134642538299051809904413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3025713435464138159745101 1134642538299051809904413)
                  ·
                    refine ⟨425490951862144428714155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1134642538299051809904413 425490951862144428714155)
                    ·
                      rfl

theorem cell22_1242961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_1242961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1242961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1242961 prefixEnd_1242961 := by exact prefixLift 1242961
  have htrace : WordTrace (prefixWord ++ tailWord_1242961) baseStart_1242961 baseEnd_1242961 := by
    simpa [prefixWord, tailWord_1242961, baseEnd_1242961] using wordTrace_append hprefix tailTrace_1242961
  have hstable : (prefixWord ++ tailWord_1242961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242961).length < 2 ^ (prefixWord ++ tailWord_1242961).sum := by decide
  have hdescent : baseEnd_1242961 < baseStart_1242961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243002 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 8]
def baseStart_1243002 : Nat := 118140960795 + 1243002 * 2 ^ 59
def prefixEnd_1243002 : Nat := 4983230072969 + 3 ^ 40 * 1243002 * 2
def baseEnd_1243002 : Nat := 141834995666677996146343

theorem tailTrace_1243002 : CollatzResearch.WordTrace tailWord_1243002 prefixEnd_1243002 141834995666677996146343 := by
  unfold tailWord_1243002
  simp only [CollatzResearch.WordTrace]
  refine ⟨11334001860705879171402815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30224004961882344457074173 11334001860705879171402815)
  ·
    refine ⟨17001002791058818757104223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11334001860705879171402815 17001002791058818757104223)
    ·
      refine ⟨25501504186588228135656335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17001002791058818757104223 25501504186588228135656335)
      ·
        refine ⟨38252256279882342203484503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25501504186588228135656335 38252256279882342203484503)
        ·
          refine ⟨57378384419823513305226755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38252256279882342203484503 57378384419823513305226755)
          ·
            refine ⟨86067576629735269957840133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57378384419823513305226755 86067576629735269957840133)
            ·
              refine ⟨16137670618075363117095025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86067576629735269957840133 16137670618075363117095025)
              ·
                refine ⟨12103252963556522337821269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16137670618075363117095025 12103252963556522337821269)
                ·
                  refine ⟨141834995666677996146343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12103252963556522337821269 141834995666677996146343)
                  ·
                    rfl

theorem cell22_1243002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_1243002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243002 prefixEnd_1243002 := by exact prefixLift 1243002
  have htrace : WordTrace (prefixWord ++ tailWord_1243002) baseStart_1243002 baseEnd_1243002 := by
    simpa [prefixWord, tailWord_1243002, baseEnd_1243002] using wordTrace_append hprefix tailTrace_1243002
  have hstable : (prefixWord ++ tailWord_1243002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243002).length < 2 ^ (prefixWord ++ tailWord_1243002).sum := by decide
  have hdescent : baseEnd_1243002 < baseStart_1243002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243070 : List Nat := [4, 2, 1, 1, 1, 5, 2, 2, 4]
def baseStart_1243070 : Nat := 118140960795 + 1243070 * 2 ^ 59
def prefixEnd_1243070 : Nat := 4983230072969 + 3 ^ 40 * 1243070 * 2
def baseEnd_1243070 : Nat := 141842754929901492579607

theorem tailTrace_1243070 : CollatzResearch.WordTrace tailWord_1243070 prefixEnd_1243070 141842754929901492579607 := by
  unfold tailWord_1243070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5667310950822145537385833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30225658404384776199391109 5667310950822145537385833)
  ·
    refine ⟨4250483213116609153039375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5667310950822145537385833 4250483213116609153039375)
    ·
      refine ⟨6375724819674913729559063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4250483213116609153039375 6375724819674913729559063)
      ·
        refine ⟨9563587229512370594338595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6375724819674913729559063 9563587229512370594338595)
        ·
          refine ⟨14345380844268555891507893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9563587229512370594338595 14345380844268555891507893)
          ·
            refine ⟨1344879454150177114828865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14345380844268555891507893 1344879454150177114828865)
            ·
              refine ⟨1008659590612632836121649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1344879454150177114828865 1008659590612632836121649)
              ·
                refine ⟨756494692959474627091237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1008659590612632836121649 756494692959474627091237)
                ·
                  refine ⟨141842754929901492579607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 756494692959474627091237 141842754929901492579607)
                  ·
                    rfl

theorem cell22_1243070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_1243070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243070 prefixEnd_1243070 := by exact prefixLift 1243070
  have htrace : WordTrace (prefixWord ++ tailWord_1243070) baseStart_1243070 baseEnd_1243070 := by
    simpa [prefixWord, tailWord_1243070, baseEnd_1243070] using wordTrace_append hprefix tailTrace_1243070
  have hstable : (prefixWord ++ tailWord_1243070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243070).length < 2 ^ (prefixWord ++ tailWord_1243070).sum := by decide
  have hdescent : baseEnd_1243070 < baseStart_1243070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243096 : List Nat := [2, 1, 2, 2, 2, 2, 3, 2, 3, 3]
def baseStart_1243096 : Nat := 118140960795 + 1243096 * 2 ^ 59
def prefixEnd_1243096 : Nat := 4983230072969 + 3 ^ 40 * 1243096 * 2
def baseEnd_1243096 : Nat := 425537165121049076588741

theorem tailTrace_1243096 : CollatzResearch.WordTrace tailWord_1243096 prefixEnd_1243096 425537165121049076588741 := by
  unfold tailWord_1243096
  simp only [CollatzResearch.WordTrace]
  refine ⟨22669717952241485369766571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30226290602988647159688761 22669717952241485369766571)
  ·
    refine ⟨34004576928362228054649857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22669717952241485369766571 34004576928362228054649857)
    ·
      refine ⟨25503432696271671040987393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34004576928362228054649857 25503432696271671040987393)
      ·
        refine ⟨19127574522203753280740545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25503432696271671040987393 19127574522203753280740545)
        ·
          refine ⟨14345680891652814960555409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19127574522203753280740545 14345680891652814960555409)
          ·
            refine ⟨10759260668739611220416557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14345680891652814960555409 10759260668739611220416557)
            ·
              refine ⟨4034722750777354207656209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10759260668739611220416557 4034722750777354207656209)
              ·
                refine ⟨3026042063083015655742157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4034722750777354207656209 3026042063083015655742157)
                ·
                  refine ⟨1134765773656130870903309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3026042063083015655742157 1134765773656130870903309)
                  ·
                    refine ⟨425537165121049076588741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1134765773656130870903309 425537165121049076588741)
                    ·
                      rfl

theorem cell22_1243096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_1243096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243096 prefixEnd_1243096 := by exact prefixLift 1243096
  have htrace : WordTrace (prefixWord ++ tailWord_1243096) baseStart_1243096 baseEnd_1243096 := by
    simpa [prefixWord, tailWord_1243096, baseEnd_1243096] using wordTrace_append hprefix tailTrace_1243096
  have hstable : (prefixWord ++ tailWord_1243096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243096).length < 2 ^ (prefixWord ++ tailWord_1243096).sum := by decide
  have hdescent : baseEnd_1243096 < baseStart_1243096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243100 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 1, 6]
def baseStart_1243100 : Nat := 118140960795 + 1243100 * 2 ^ 59
def prefixEnd_1243100 : Nat := 4983230072969 + 3 ^ 40 * 1243100 * 2
def baseEnd_1243100 : Nat := 425538534402794399488729

theorem tailTrace_1243100 : CollatzResearch.WordTrace tailWord_1243100 prefixEnd_1243100 425538534402794399488729 := by
  unfold tailWord_1243100
  simp only [CollatzResearch.WordTrace]
  refine ⟨22669790898234239711339377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30226387864312319615119169 22669790898234239711339377)
  ·
    refine ⟨17002343173675679783504533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22669790898234239711339377 17002343173675679783504533)
    ·
      refine ⟨796984836266047489851775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17002343173675679783504533 796984836266047489851775)
      ·
        refine ⟨1195477254399071234777663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 796984836266047489851775 1195477254399071234777663)
        ·
          refine ⟨1793215881598606852166495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1195477254399071234777663 1793215881598606852166495)
          ·
            refine ⟨2689823822397910278249743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1793215881598606852166495 2689823822397910278249743)
            ·
              refine ⟨4034735733596865417374615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2689823822397910278249743 4034735733596865417374615)
              ·
                refine ⟨6052103600395298126061923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4034735733596865417374615 6052103600395298126061923)
                ·
                  refine ⟨9078155400592947189092885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6052103600395298126061923 9078155400592947189092885)
                  ·
                    refine ⟨425538534402794399488729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9078155400592947189092885 425538534402794399488729)
                    ·
                      rfl

theorem cell22_1243100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_1243100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243100 prefixEnd_1243100 := by exact prefixLift 1243100
  have htrace : WordTrace (prefixWord ++ tailWord_1243100) baseStart_1243100 baseEnd_1243100 := by
    simpa [prefixWord, tailWord_1243100, baseEnd_1243100] using wordTrace_append hprefix tailTrace_1243100
  have hstable : (prefixWord ++ tailWord_1243100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243100).length < 2 ^ (prefixWord ++ tailWord_1243100).sum := by decide
  have hdescent : baseEnd_1243100 < baseStart_1243100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243139 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 5, 4]
def baseStart_1243139 : Nat := 118140960795 + 1243139 * 2 ^ 59
def prefixEnd_1243139 : Nat := 4983230072969 + 3 ^ 40 * 1243139 * 2
def baseEnd_1243139 : Nat := 425551884899811297763609

theorem tailTrace_1243139 : CollatzResearch.WordTrace tailWord_1243139 prefixEnd_1243139 425551884899811297763609 := by
  unfold tailWord_1243139
  simp only [CollatzResearch.WordTrace]
  refine ⟨45341004243327189083348471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30227336162218126055565647 45341004243327189083348471)
  ·
    refine ⟨68011506364990783625022707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45341004243327189083348471 68011506364990783625022707)
    ·
      refine ⟨102017259547486175437534061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68011506364990783625022707 102017259547486175437534061)
      ·
        refine ⟨38256472330307315789075273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102017259547486175437534061 38256472330307315789075273)
        ·
          refine ⟨28692354247730486841806455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38256472330307315789075273 28692354247730486841806455)
          ·
            refine ⟨43038531371595730262709683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28692354247730486841806455 43038531371595730262709683)
            ·
              refine ⟨64557797057393595394064525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43038531371595730262709683 64557797057393595394064525)
              ·
                refine ⟨24209173896522598272774197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64557797057393595394064525 24209173896522598272774197)
                ·
                  refine ⟨2269610052798993588072581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24209173896522598272774197 2269610052798993588072581)
                  ·
                    refine ⟨425551884899811297763609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2269610052798993588072581 425551884899811297763609)
                    ·
                      rfl

theorem cell22_1243139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 4].length) (baseStart_1243139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243139 prefixEnd_1243139 := by exact prefixLift 1243139
  have htrace : WordTrace (prefixWord ++ tailWord_1243139) baseStart_1243139 baseEnd_1243139 := by
    simpa [prefixWord, tailWord_1243139, baseEnd_1243139] using wordTrace_append hprefix tailTrace_1243139
  have hstable : (prefixWord ++ tailWord_1243139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243139).length < 2 ^ (prefixWord ++ tailWord_1243139).sum := by decide
  have hdescent : baseEnd_1243139 < baseStart_1243139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243143 : List Nat := [1, 1, 4, 3, 1, 3, 3, 1, 5]
def baseStart_1243143 : Nat := 118140960795 + 1243143 * 2 ^ 59
def prefixEnd_1243143 : Nat := 4983230072969 + 3 ^ 40 * 1243143 * 2
def baseEnd_1243143 : Nat := 141851084727185540221199

theorem tailTrace_1243143 : CollatzResearch.WordTrace tailWord_1243143 prefixEnd_1243143 141851084727185540221199 := by
  unfold tailWord_1243143
  simp only [CollatzResearch.WordTrace]
  refine ⟨45341150135312697766494083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30227433423541798510996055 45341150135312697766494083)
  ·
    refine ⟨68011725202969046649741125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45341150135312697766494083 68011725202969046649741125)
    ·
      refine ⟨12752198475556696246826461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68011725202969046649741125 12752198475556696246826461)
      ·
        refine ⟨4782074428333761092559923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12752198475556696246826461 4782074428333761092559923)
        ·
          refine ⟨7173111642500641638839885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4782074428333761092559923 7173111642500641638839885)
          ·
            refine ⟨2689916865937740614564957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7173111642500641638839885 2689916865937740614564957)
            ·
              refine ⟨1008718824726652730461859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2689916865937740614564957 1008718824726652730461859)
              ·
                refine ⟨1513078237089979095692789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008718824726652730461859 1513078237089979095692789)
                ·
                  refine ⟨141851084727185540221199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1513078237089979095692789 141851084727185540221199)
                  ·
                    rfl

theorem cell22_1243143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 5].length) (baseStart_1243143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243143 prefixEnd_1243143 := by exact prefixLift 1243143
  have htrace : WordTrace (prefixWord ++ tailWord_1243143) baseStart_1243143 baseEnd_1243143 := by
    simpa [prefixWord, tailWord_1243143, baseEnd_1243143] using wordTrace_append hprefix tailTrace_1243143
  have hstable : (prefixWord ++ tailWord_1243143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243143).length < 2 ^ (prefixWord ++ tailWord_1243143).sum := by decide
  have hdescent : baseEnd_1243143 < baseStart_1243143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243149 : List Nat := [1, 7, 1, 2, 2, 1, 2, 6]
def baseStart_1243149 : Nat := 118140960795 + 1243149 * 2 ^ 59
def prefixEnd_1243149 : Nat := 4983230072969 + 3 ^ 40 * 1243149 * 2
def baseEnd_1243149 : Nat := 47283923122686067223731

theorem tailTrace_1243149 : CollatzResearch.WordTrace tailWord_1243149 prefixEnd_1243149 47283923122686067223731 := by
  unfold tailWord_1243149
  simp only [CollatzResearch.WordTrace]
  refine ⟨45341368973290960791212501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30227579315527307194141667 45341368973290960791212501)
  ·
    refine ⟨1062688335311506893544043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 45341368973290960791212501 1062688335311506893544043)
    ·
      refine ⟨1594032502967260340316065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1062688335311506893544043 1594032502967260340316065)
      ·
        refine ⟨1195524377225445255237049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1594032502967260340316065 1195524377225445255237049)
        ·
          refine ⟨896643282919083941427787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1195524377225445255237049 896643282919083941427787)
          ·
            refine ⟨1344964924378625912141681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 896643282919083941427787 1344964924378625912141681)
            ·
              refine ⟨1008723693283969434106261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1344964924378625912141681 1008723693283969434106261)
              ·
                refine ⟨47283923122686067223731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1008723693283969434106261 47283923122686067223731)
                ·
                  rfl

theorem cell22_1243149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 6].length) (baseStart_1243149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243149 prefixEnd_1243149 := by exact prefixLift 1243149
  have htrace : WordTrace (prefixWord ++ tailWord_1243149) baseStart_1243149 baseEnd_1243149 := by
    simpa [prefixWord, tailWord_1243149, baseEnd_1243149] using wordTrace_append hprefix tailTrace_1243149
  have hstable : (prefixWord ++ tailWord_1243149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243149).length < 2 ^ (prefixWord ++ tailWord_1243149).sum := by decide
  have hdescent : baseEnd_1243149 < baseStart_1243149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243199 : List Nat := [1, 1, 2, 2, 3, 1, 3, 9]
def baseStart_1243199 : Nat := 118140960795 + 1243199 * 2 ^ 59
def prefixEnd_1243199 : Nat := 4983230072969 + 3 ^ 40 * 1243199 * 2
def baseEnd_1243199 : Nat := 47285824902887904584825

theorem tailTrace_1243199 : CollatzResearch.WordTrace tailWord_1243199 prefixEnd_1243199 47285824902887904584825 := by
  unfold tailWord_1243199
  simp only [CollatzResearch.WordTrace]
  refine ⟨45343192623109819330532651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30228795082073212887021767 45343192623109819330532651)
  ·
    refine ⟨68014788934664728995798977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45343192623109819330532651 68014788934664728995798977)
    ·
      refine ⟨51011091700998546746849233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68014788934664728995798977 51011091700998546746849233)
      ·
        refine ⟨38258318775748910060136925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51011091700998546746849233 38258318775748910060136925)
        ·
          refine ⟨14346869540905841272551347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38258318775748910060136925 14346869540905841272551347)
          ·
            refine ⟨21520304311358761908827021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14346869540905841272551347 21520304311358761908827021)
            ·
              refine ⟨8070114116759535715810133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21520304311358761908827021 8070114116759535715810133)
              ·
                refine ⟨47285824902887904584825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8070114116759535715810133 47285824902887904584825)
                ·
                  rfl

theorem cell22_1243199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 9].length) (baseStart_1243199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243199 prefixEnd_1243199 := by exact prefixLift 1243199
  have htrace : WordTrace (prefixWord ++ tailWord_1243199) baseStart_1243199 baseEnd_1243199 := by
    simpa [prefixWord, tailWord_1243199, baseEnd_1243199] using wordTrace_append hprefix tailTrace_1243199
  have hstable : (prefixWord ++ tailWord_1243199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243199).length < 2 ^ (prefixWord ++ tailWord_1243199).sum := by decide
  have hdescent : baseEnd_1243199 < baseStart_1243199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243231 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 7, 3]
def baseStart_1243231 : Nat := 118140960795 + 1243231 * 2 ^ 59
def prefixEnd_1243231 : Nat := 4983230072969 + 3 ^ 40 * 1243231 * 2
def baseEnd_1243231 : Nat := 425583378379953724463327

theorem tailTrace_1243231 : CollatzResearch.WordTrace tailWord_1243231 prefixEnd_1243231 425583378379953724463327 := by
  unfold tailWord_1243231
  simp only [CollatzResearch.WordTrace]
  refine ⟨45344359758993888795697547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30229573172662592530465031 45344359758993888795697547)
  ·
    refine ⟨68016539638490833193546321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45344359758993888795697547 68016539638490833193546321)
    ·
      refine ⟨51012404728868124895159741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68016539638490833193546321 51012404728868124895159741)
      ·
        refine ⟨19129651773325546835684903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51012404728868124895159741 19129651773325546835684903)
        ·
          refine ⟨28694477659988320253527355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19129651773325546835684903 28694477659988320253527355)
          ·
            refine ⟨43041716489982480380291033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28694477659988320253527355 43041716489982480380291033)
            ·
              refine ⟨32281287367486860285218275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43041716489982480380291033 32281287367486860285218275)
              ·
                refine ⟨48421931051230290427827413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32281287367486860285218275 48421931051230290427827413)
                ·
                  refine ⟨1134889009013209931902205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 48421931051230290427827413 1134889009013209931902205)
                  ·
                    refine ⟨425583378379953724463327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1134889009013209931902205 425583378379953724463327)
                    ·
                      rfl

theorem cell22_1243231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 3].length) (baseStart_1243231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243231 prefixEnd_1243231 := by exact prefixLift 1243231
  have htrace : WordTrace (prefixWord ++ tailWord_1243231) baseStart_1243231 baseEnd_1243231 := by
    simpa [prefixWord, tailWord_1243231, baseEnd_1243231] using wordTrace_append hprefix tailTrace_1243231
  have hstable : (prefixWord ++ tailWord_1243231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243231).length < 2 ^ (prefixWord ++ tailWord_1243231).sum := by decide
  have hdescent : baseEnd_1243231 < baseStart_1243231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243246 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_1243246 : Nat := 118140960795 + 1243246 * 2 ^ 59
def prefixEnd_1243246 : Nat := 4983230072969 + 3 ^ 40 * 1243246 * 2
def baseEnd_1243246 : Nat := 425588513186498685338281

theorem tailTrace_1243246 : CollatzResearch.WordTrace tailWord_1243246 prefixEnd_1243246 425588513186498685338281 := by
  unfold tailWord_1243246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5668113356742443294686699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30229937902626364238329061 5668113356742443294686699)
  ·
    refine ⟨8502170035113664942030049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5668113356742443294686699 8502170035113664942030049)
    ·
      refine ⟨6376627526335248706522537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8502170035113664942030049 6376627526335248706522537)
      ·
        refine ⟨4782470644751436529891903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6376627526335248706522537 4782470644751436529891903)
        ·
          refine ⟨7173705967127154794837855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4782470644751436529891903 7173705967127154794837855)
          ·
            refine ⟨10760558950690732192256783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7173705967127154794837855 10760558950690732192256783)
            ·
              refine ⟨16140838426036098288385175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10760558950690732192256783 16140838426036098288385175)
              ·
                refine ⟨24211257639054147432577763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16140838426036098288385175 24211257639054147432577763)
                ·
                  refine ⟨36316886458581221148866645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24211257639054147432577763 36316886458581221148866645)
                  ·
                    refine ⟨425588513186498685338281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36316886458581221148866645 425588513186498685338281)
                    ·
                      rfl

theorem cell22_1243246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_1243246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243246 prefixEnd_1243246 := by exact prefixLift 1243246
  have htrace : WordTrace (prefixWord ++ tailWord_1243246) baseStart_1243246 baseEnd_1243246 := by
    simpa [prefixWord, tailWord_1243246, baseEnd_1243246] using wordTrace_append hprefix tailTrace_1243246
  have hstable : (prefixWord ++ tailWord_1243246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243246).length < 2 ^ (prefixWord ++ tailWord_1243246).sum := by decide
  have hdescent : baseEnd_1243246 < baseStart_1243246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243265 : List Nat := [1, 2, 4, 2, 3, 1, 1, 2, 3, 3]
def baseStart_1243265 : Nat := 118140960795 + 1243265 * 2 ^ 59
def prefixEnd_1243265 : Nat := 4983230072969 + 3 ^ 40 * 1243265 * 2
def baseEnd_1243265 : Nat := 425595017274788969113223

theorem tailTrace_1243265 : CollatzResearch.WordTrace tailWord_1243265 prefixEnd_1243265 425595017274788969113223 := by
  unfold tailWord_1243265
  simp only [CollatzResearch.WordTrace]
  refine ⟨45345599840870712602435249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30230399893913808401623499 45345599840870712602435249)
  ·
    refine ⟨34009199880653034451826437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45345599840870712602435249 34009199880653034451826437)
    ·
      refine ⟨6376724977622443959717457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34009199880653034451826437 6376724977622443959717457)
      ·
        refine ⟨4782543733216832969788093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6376724977622443959717457 4782543733216832969788093)
        ·
          refine ⟨1793453899956312363670535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4782543733216832969788093 1793453899956312363670535)
          ·
            refine ⟨2690180849934468545505803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1793453899956312363670535 2690180849934468545505803)
            ·
              refine ⟨4035271274901702818258705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2690180849934468545505803 4035271274901702818258705)
              ·
                refine ⟨3026453456176277113694029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4035271274901702818258705 3026453456176277113694029)
                ·
                  refine ⟨1134920046066103917635261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3026453456176277113694029 1134920046066103917635261)
                  ·
                    refine ⟨425595017274788969113223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1134920046066103917635261 425595017274788969113223)
                    ·
                      rfl

theorem cell22_1243265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_1243265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243265 prefixEnd_1243265 := by exact prefixLift 1243265
  have htrace : WordTrace (prefixWord ++ tailWord_1243265) baseStart_1243265 baseEnd_1243265 := by
    simpa [prefixWord, tailWord_1243265, baseEnd_1243265] using wordTrace_append hprefix tailTrace_1243265
  have hstable : (prefixWord ++ tailWord_1243265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243265).length < 2 ^ (prefixWord ++ tailWord_1243265).sum := by decide
  have hdescent : baseEnd_1243265 < baseStart_1243265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243282 : List Nat := [3, 2, 3, 1, 1, 1, 4, 3, 1, 3]
def baseStart_1243282 : Nat := 118140960795 + 1243282 * 2 ^ 59
def prefixEnd_1243282 : Nat := 4983230072969 + 3 ^ 40 * 1243282 * 2
def baseEnd_1243282 : Nat := 425600836722206591438171

theorem tailTrace_1243282 : CollatzResearch.WordTrace tailWord_1243282 prefixEnd_1243282 425600836722206591438171 := by
  unfold tailWord_1243282
  simp only [CollatzResearch.WordTrace]
  refine ⟨11336554970452281126451025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30230813254539416337202733 11336554970452281126451025)
  ·
    refine ⟨8502416227839210844838269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11336554970452281126451025 8502416227839210844838269)
    ·
      refine ⟨3188406085439704066814351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8502416227839210844838269 3188406085439704066814351)
      ·
        refine ⟨4782609128159556100221527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3188406085439704066814351 4782609128159556100221527)
        ·
          refine ⟨7173913692239334150332291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4782609128159556100221527 7173913692239334150332291)
          ·
            refine ⟨10760870538359001225498437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7173913692239334150332291 10760870538359001225498437)
            ·
              refine ⟨2017663225942312729780957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10760870538359001225498437 2017663225942312729780957)
              ·
                refine ⟨756623709728367273667859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2017663225942312729780957 756623709728367273667859)
                ·
                  refine ⟨1134935564592550910501789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 756623709728367273667859 1134935564592550910501789)
                  ·
                    refine ⟨425600836722206591438171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1134935564592550910501789 425600836722206591438171)
                    ·
                      rfl

theorem cell22_1243282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_1243282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243282 prefixEnd_1243282 := by exact prefixLift 1243282
  have htrace : WordTrace (prefixWord ++ tailWord_1243282) baseStart_1243282 baseEnd_1243282 := by
    simpa [prefixWord, tailWord_1243282, baseEnd_1243282] using wordTrace_append hprefix tailTrace_1243282
  have hstable : (prefixWord ++ tailWord_1243282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243282).length < 2 ^ (prefixWord ++ tailWord_1243282).sum := by decide
  have hdescent : baseEnd_1243282 < baseStart_1243282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243295 : List Nat := [1, 1, 2, 6, 1, 3, 1, 2, 5]
def baseStart_1243295 : Nat := 118140960795 + 1243295 * 2 ^ 59
def prefixEnd_1243295 : Nat := 4983230072969 + 3 ^ 40 * 1243295 * 2
def baseEnd_1243295 : Nat := 141868428962626296954377

theorem tailTrace_1243295 : CollatzResearch.WordTrace tailWord_1243295 prefixEnd_1243295 141868428962626296954377 := by
  unfold tailWord_1243295
  simp only [CollatzResearch.WordTrace]
  refine ⟨45346694030762027726027339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30231129353841351817351559 45346694030762027726027339)
  ·
    refine ⟨68020041046143041589041009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45346694030762027726027339 68020041046143041589041009)
    ·
      refine ⟨51015030784607281191780757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68020041046143041589041009 51015030784607281191780757)
      ·
        refine ⟨2391329568028466305864723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51015030784607281191780757 2391329568028466305864723)
        ·
          refine ⟨3586994352042699458797085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2391329568028466305864723 3586994352042699458797085)
          ·
            refine ⟨1345122882016012297048907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3586994352042699458797085 1345122882016012297048907)
            ·
              refine ⟨2017684323024018445573361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1345122882016012297048907 2017684323024018445573361)
              ·
                refine ⟨1513263242268013834180021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2017684323024018445573361 1513263242268013834180021)
                ·
                  refine ⟨141868428962626296954377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1513263242268013834180021 141868428962626296954377)
                  ·
                    rfl

theorem cell22_1243295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 5].length) (baseStart_1243295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243295 prefixEnd_1243295 := by exact prefixLift 1243295
  have htrace : WordTrace (prefixWord ++ tailWord_1243295) baseStart_1243295 baseEnd_1243295 := by
    simpa [prefixWord, tailWord_1243295, baseEnd_1243295] using wordTrace_append hprefix tailTrace_1243295
  have hstable : (prefixWord ++ tailWord_1243295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243295).length < 2 ^ (prefixWord ++ tailWord_1243295).sum := by decide
  have hdescent : baseEnd_1243295 < baseStart_1243295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243338 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 6, 3]
def baseStart_1243338 : Nat := 118140960795 + 1243338 * 2 ^ 59
def prefixEnd_1243338 : Nat := 4983230072969 + 3 ^ 40 * 1243338 * 2
def baseEnd_1243338 : Nat := 425620006666641112037999

theorem tailTrace_1243338 : CollatzResearch.WordTrace tailWord_1243338 prefixEnd_1243338 425620006666641112037999 := by
  unfold tailWord_1243338
  simp only [CollatzResearch.WordTrace]
  refine ⟨11337065592401561517460667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30232174913070830713228445 11337065592401561517460667)
  ·
    refine ⟨17005598388602342276191001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11337065592401561517460667 17005598388602342276191001)
    ·
      refine ⟨12754198791451756707143251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17005598388602342276191001 12754198791451756707143251)
      ·
        refine ⟨19131298187177635060714877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12754198791451756707143251 19131298187177635060714877)
        ·
          refine ⟨7174236820191613147768079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19131298187177635060714877 7174236820191613147768079)
          ·
            refine ⟨10761355230287419721652119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7174236820191613147768079 10761355230287419721652119)
            ·
              refine ⟨16142032845431129582478179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10761355230287419721652119 16142032845431129582478179)
              ·
                refine ⟨24213049268146694373717269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16142032845431129582478179 24213049268146694373717269)
                ·
                  refine ⟨1134986684444376298767997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24213049268146694373717269 1134986684444376298767997)
                  ·
                    refine ⟨425620006666641112037999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1134986684444376298767997 425620006666641112037999)
                    ·
                      rfl

theorem cell22_1243338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_1243338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243338 prefixEnd_1243338 := by exact prefixLift 1243338
  have htrace : WordTrace (prefixWord ++ tailWord_1243338) baseStart_1243338 baseEnd_1243338 := by
    simpa [prefixWord, tailWord_1243338, baseEnd_1243338] using wordTrace_append hprefix tailTrace_1243338
  have hstable : (prefixWord ++ tailWord_1243338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243338).length < 2 ^ (prefixWord ++ tailWord_1243338).sum := by decide
  have hdescent : baseEnd_1243338 < baseStart_1243338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243368 : List Nat := [2, 1, 4, 1, 2, 3, 2, 7]
def baseStart_1243368 : Nat := 118140960795 + 1243368 * 2 ^ 59
def prefixEnd_1243368 : Nat := 4983230072969 + 3 ^ 40 * 1243368 * 2
def baseEnd_1243368 : Nat := 47292252919970114865323

theorem tailTrace_1243368 : CollatzResearch.WordTrace tailWord_1243368 prefixEnd_1243368 47292252919970114865323 := by
  unfold tailWord_1243368
  simp only [CollatzResearch.WordTrace]
  refine ⟨22674678279748780596717379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30232904372998374128956505 22674678279748780596717379)
  ·
    refine ⟨34012017419623170895076069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22674678279748780596717379 34012017419623170895076069)
    ·
      refine ⟨6377253266179344542826763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34012017419623170895076069 6377253266179344542826763)
      ·
        refine ⟨9565879899269016814240145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6377253266179344542826763 9565879899269016814240145)
        ·
          refine ⟨7174409924451762610680109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9565879899269016814240145 7174409924451762610680109)
          ·
            refine ⟨2690403721669410979005041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7174409924451762610680109 2690403721669410979005041)
            ·
              refine ⟨2017802791252058234253781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2690403721669410979005041 2017802791252058234253781)
              ·
                refine ⟨47292252919970114865323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2017802791252058234253781 47292252919970114865323)
                ·
                  rfl

theorem cell22_1243368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 7].length) (baseStart_1243368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243368 prefixEnd_1243368 := by exact prefixLift 1243368
  have htrace : WordTrace (prefixWord ++ tailWord_1243368) baseStart_1243368 baseEnd_1243368 := by
    simpa [prefixWord, tailWord_1243368, baseEnd_1243368] using wordTrace_append hprefix tailTrace_1243368
  have hstable : (prefixWord ++ tailWord_1243368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243368).length < 2 ^ (prefixWord ++ tailWord_1243368).sum := by decide
  have hdescent : baseEnd_1243368 < baseStart_1243368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243411 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 3, 7]
def baseStart_1243411 : Nat := 118140960795 + 1243411 * 2 ^ 59
def prefixEnd_1243411 : Nat := 4983230072969 + 3 ^ 40 * 1243411 * 2
def baseEnd_1243411 : Nat := 425644996058493254962775

theorem tailTrace_1243411 : CollatzResearch.WordTrace tailWord_1243411 prefixEnd_1243411 425644996058493254962775 := by
  unfold tailWord_1243411
  simp only [CollatzResearch.WordTrace]
  refine ⟨45350924898341779537250087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30233949932227853024833391 45350924898341779537250087)
  ·
    refine ⟨68026387347512669305875131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45350924898341779537250087 68026387347512669305875131)
    ·
      refine ⟨102039581021269003958812697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68026387347512669305875131 102039581021269003958812697)
      ·
        refine ⟨76529685765951752969109523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102039581021269003958812697 76529685765951752969109523)
        ·
          refine ⟨114794528648927629453664285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76529685765951752969109523 114794528648927629453664285)
          ·
            refine ⟨43047948243347861045124107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114794528648927629453664285 43047948243347861045124107)
            ·
              refine ⟨64571922365021791567686161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43047948243347861045124107 64571922365021791567686161)
              ·
                refine ⟨48428941773766343675764621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64571922365021791567686161 48428941773766343675764621)
                ·
                  refine ⟨18160853165162378878411733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48428941773766343675764621 18160853165162378878411733)
                  ·
                    refine ⟨425644996058493254962775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18160853165162378878411733 425644996058493254962775)
                    ·
                      rfl

theorem cell22_1243411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 7].length) (baseStart_1243411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243411 prefixEnd_1243411 := by exact prefixLift 1243411
  have htrace : WordTrace (prefixWord ++ tailWord_1243411) baseStart_1243411 baseEnd_1243411 := by
    simpa [prefixWord, tailWord_1243411, baseEnd_1243411] using wordTrace_append hprefix tailTrace_1243411
  have hstable : (prefixWord ++ tailWord_1243411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243411).length < 2 ^ (prefixWord ++ tailWord_1243411).sum := by decide
  have hdescent : baseEnd_1243411 < baseStart_1243411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243413 : List Nat := [1, 3, 2, 1, 2, 1, 3, 4, 5]
def baseStart_1243413 : Nat := 118140960795 + 1243413 * 2 ^ 59
def prefixEnd_1243413 : Nat := 4983230072969 + 3 ^ 40 * 1243413 * 2
def baseEnd_1243413 : Nat := 141881893566455305470923

theorem tailTrace_1243413 : CollatzResearch.WordTrace tailWord_1243413 prefixEnd_1243413 141881893566455305470923 := by
  unfold tailWord_1243413
  simp only [CollatzResearch.WordTrace]
  refine ⟨45350997844334533878822893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30233998562889689252548595 45350997844334533878822893)
  ·
    refine ⟨17006624191625450204558585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45350997844334533878822893 17006624191625450204558585)
    ·
      refine ⟨12754968143719087653418939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17006624191625450204558585 12754968143719087653418939)
      ·
        refine ⟨19132452215578631480128409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12754968143719087653418939 19132452215578631480128409)
        ·
          refine ⟨14349339161683973610096307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19132452215578631480128409 14349339161683973610096307)
          ·
            refine ⟨21524008742525960415144461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14349339161683973610096307 21524008742525960415144461)
            ·
              refine ⟨8071503278447235155679173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21524008742525960415144461 8071503278447235155679173)
              ·
                refine ⟨1513406864708856591689845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8071503278447235155679173 1513406864708856591689845)
                ·
                  refine ⟨141881893566455305470923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1513406864708856591689845 141881893566455305470923)
                  ·
                    rfl

theorem cell22_1243413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_1243413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243413 prefixEnd_1243413 := by exact prefixLift 1243413
  have htrace : WordTrace (prefixWord ++ tailWord_1243413) baseStart_1243413 baseEnd_1243413 := by
    simpa [prefixWord, tailWord_1243413, baseEnd_1243413] using wordTrace_append hprefix tailTrace_1243413
  have hstable : (prefixWord ++ tailWord_1243413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243413).length < 2 ^ (prefixWord ++ tailWord_1243413).sum := by decide
  have hdescent : baseEnd_1243413 < baseStart_1243413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243428 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_1243428 : Nat := 118140960795 + 1243428 * 2 ^ 59
def prefixEnd_1243428 : Nat := 4983230072969 + 3 ^ 40 * 1243428 * 2
def baseEnd_1243428 : Nat := 425650815505910877287723

theorem tailTrace_1243428 : CollatzResearch.WordTrace tailWord_1243428 prefixEnd_1243428 425650815505910877287723 := by
  unfold tailWord_1243428
  simp only [CollatzResearch.WordTrace]
  refine ⟨22675772469640095720309469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30234363292853460960412625 22675772469640095720309469)
  ·
    refine ⟨8503414676115035895116051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22675772469640095720309469 8503414676115035895116051)
    ·
      refine ⟨12755122014172553842674077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8503414676115035895116051 12755122014172553842674077)
      ·
        refine ⟨4783170755314707691002779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12755122014172553842674077 4783170755314707691002779)
        ·
          refine ⟨7174756132972061536504169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4783170755314707691002779 7174756132972061536504169)
          ·
            refine ⟨5381067099729046152378127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7174756132972061536504169 5381067099729046152378127)
            ·
              refine ⟨8071600649593569228567191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5381067099729046152378127 8071600649593569228567191)
              ·
                refine ⟨12107400974390353842850787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8071600649593569228567191 12107400974390353842850787)
                ·
                  refine ⟨18161101461585530764276181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12107400974390353842850787 18161101461585530764276181)
                  ·
                    refine ⟨425650815505910877287723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18161101461585530764276181 425650815505910877287723)
                    ·
                      rfl

theorem cell22_1243428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_1243428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243428 prefixEnd_1243428 := by exact prefixLift 1243428
  have htrace : WordTrace (prefixWord ++ tailWord_1243428) baseStart_1243428 baseEnd_1243428 := by
    simpa [prefixWord, tailWord_1243428, baseEnd_1243428] using wordTrace_append hprefix tailTrace_1243428
  have hstable : (prefixWord ++ tailWord_1243428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243428).length < 2 ^ (prefixWord ++ tailWord_1243428).sum := by decide
  have hdescent : baseEnd_1243428 < baseStart_1243428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243443 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 3, 4]
def baseStart_1243443 : Nat := 118140960795 + 1243443 * 2 ^ 59
def prefixEnd_1243443 : Nat := 4983230072969 + 3 ^ 40 * 1243443 * 2
def baseEnd_1243443 : Nat := 425655950312455838162677

theorem tailTrace_1243443 : CollatzResearch.WordTrace tailWord_1243443 prefixEnd_1243443 425655950312455838162677 := by
  unfold tailWord_1243443
  simp only [CollatzResearch.WordTrace]
  refine ⟨45352092034225849002414983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30234728022817232668276655 45352092034225849002414983)
  ·
    refine ⟨68028138051338773503622475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45352092034225849002414983 68028138051338773503622475)
    ·
      refine ⟨102042207077008160255433713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68028138051338773503622475 102042207077008160255433713)
      ·
        refine ⟨76531655307756120191575285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102042207077008160255433713 76531655307756120191575285)
        ·
          refine ⟨7174842685102136267960183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76531655307756120191575285 7174842685102136267960183)
          ·
            refine ⟨10762264027653204401940275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7174842685102136267960183 10762264027653204401940275)
            ·
              refine ⟨16143396041479806602910413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10762264027653204401940275 16143396041479806602910413)
              ·
                refine ⟨6053773515554927476091405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16143396041479806602910413 6053773515554927476091405)
                ·
                  refine ⟨2270165068333097803534277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6053773515554927476091405 2270165068333097803534277)
                  ·
                    refine ⟨425655950312455838162677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2270165068333097803534277 425655950312455838162677)
                    ·
                      rfl

theorem cell22_1243443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 4].length) (baseStart_1243443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243443 prefixEnd_1243443 := by exact prefixLift 1243443
  have htrace : WordTrace (prefixWord ++ tailWord_1243443) baseStart_1243443 baseEnd_1243443 := by
    simpa [prefixWord, tailWord_1243443, baseEnd_1243443] using wordTrace_append hprefix tailTrace_1243443
  have hstable : (prefixWord ++ tailWord_1243443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243443).length < 2 ^ (prefixWord ++ tailWord_1243443).sum := by decide
  have hdescent : baseEnd_1243443 < baseStart_1243443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243509 : List Nat := [1, 3, 4, 1, 2, 3, 1, 3, 4]
def baseStart_1243509 : Nat := 118140960795 + 1243509 * 2 ^ 59
def prefixEnd_1243509 : Nat := 4983230072969 + 3 ^ 40 * 1243509 * 2
def baseEnd_1243509 : Nat := 141892847820417888670825

theorem tailTrace_1243509 : CollatzResearch.WordTrace tailWord_1243509 prefixEnd_1243509 141892847820417888670825 := by
  unfold tailWord_1243509
  simp only [CollatzResearch.WordTrace]
  refine ⟨45354499251986742274317581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30236332834657828182878387 45354499251986742274317581)
  ·
    refine ⟨17007937219495028352869093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45354499251986742274317581 17007937219495028352869093)
    ·
      refine ⟨3188988228655317816162955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17007937219495028352869093 3188988228655317816162955)
      ·
        refine ⟨4783482342982976724244433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3188988228655317816162955 4783482342982976724244433)
        ·
          refine ⟨3587611757237232543183325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4783482342982976724244433 3587611757237232543183325)
          ·
            refine ⟨1345354408963962203693747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3587611757237232543183325 1345354408963962203693747)
            ·
              refine ⟨2018031613445943305540621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1345354408963962203693747 2018031613445943305540621)
              ·
                refine ⟨756761855042228739577733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2018031613445943305540621 756761855042228739577733)
                ·
                  refine ⟨141892847820417888670825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 756761855042228739577733 141892847820417888670825)
                  ·
                    rfl

theorem cell22_1243509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 4].length) (baseStart_1243509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243509 prefixEnd_1243509 := by exact prefixLift 1243509
  have htrace : WordTrace (prefixWord ++ tailWord_1243509) baseStart_1243509 baseEnd_1243509 := by
    simpa [prefixWord, tailWord_1243509, baseEnd_1243509] using wordTrace_append hprefix tailTrace_1243509
  have hstable : (prefixWord ++ tailWord_1243509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243509).length < 2 ^ (prefixWord ++ tailWord_1243509).sum := by decide
  have hdescent : baseEnd_1243509 < baseStart_1243509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243610 : List Nat := [3, 1, 1, 2, 3, 1, 3, 2, 6]
def baseStart_1243610 : Nat := 118140960795 + 1243610 * 2 ^ 59
def prefixEnd_1243610 : Nat := 4983230072969 + 3 ^ 40 * 1243610 * 2
def baseEnd_1243610 : Nat := 141904372608441023079055

theorem tailTrace_1243610 : CollatzResearch.WordTrace tailWord_1243610 prefixEnd_1243610 141904372608441023079055 := by
  unfold tailWord_1243610
  simp only [CollatzResearch.WordTrace]
  refine ⟨11339545756155209130936071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30238788683080557682496189 11339545756155209130936071)
  ·
    refine ⟨17009318634232813696404107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11339545756155209130936071 17009318634232813696404107)
    ·
      refine ⟨25513977951349220544606161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17009318634232813696404107 25513977951349220544606161)
      ·
        refine ⟨19135483463511915408454621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25513977951349220544606161 19135483463511915408454621)
        ·
          refine ⟨7175806298816968278170483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19135483463511915408454621 7175806298816968278170483)
          ·
            refine ⟨10763709448225452417255725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7175806298816968278170483 10763709448225452417255725)
            ·
              refine ⟨4036391043084544656470897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10763709448225452417255725 4036391043084544656470897)
              ·
                refine ⟨3027293282313408492353173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4036391043084544656470897 3027293282313408492353173)
                ·
                  refine ⟨141904372608441023079055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3027293282313408492353173 141904372608441023079055)
                  ·
                    rfl

theorem cell22_1243610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_1243610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243610 prefixEnd_1243610 := by exact prefixLift 1243610
  have htrace : WordTrace (prefixWord ++ tailWord_1243610) baseStart_1243610 baseEnd_1243610 := by
    simpa [prefixWord, tailWord_1243610, baseEnd_1243610] using wordTrace_append hprefix tailTrace_1243610
  have hstable : (prefixWord ++ tailWord_1243610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243610).length < 2 ^ (prefixWord ++ tailWord_1243610).sum := by decide
  have hdescent : baseEnd_1243610 < baseStart_1243610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243627 : List Nat := [1, 1, 1, 1, 2, 3, 6, 3, 4]
def baseStart_1243627 : Nat := 118140960795 + 1243627 * 2 ^ 59
def prefixEnd_1243627 : Nat := 4983230072969 + 3 ^ 40 * 1243627 * 2
def baseEnd_1243627 : Nat := 141906312424246897187371

theorem tailTrace_1243627 : CollatzResearch.WordTrace tailWord_1243627 prefixEnd_1243627 141906312424246897187371 := by
  unfold tailWord_1243627
  simp only [CollatzResearch.WordTrace]
  refine ⟨45358803065559248427113135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30239202043706165618075423 45358803065559248427113135)
  ·
    refine ⟨68038204598338872640669703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45358803065559248427113135 68038204598338872640669703)
    ·
      refine ⟨102057306897508308961004555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68038204598338872640669703 102057306897508308961004555)
      ·
        refine ⟨153085960346262463441506833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102057306897508308961004555 153085960346262463441506833)
        ·
          refine ⟨114814470259696847581130125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153085960346262463441506833 114814470259696847581130125)
          ·
            refine ⟨43055426347386317842923797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114814470259696847581130125 43055426347386317842923797)
            ·
              refine ⟨2018223110033733648887053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43055426347386317842923797 2018223110033733648887053)
              ·
                refine ⟨756833666262650118332645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2018223110033733648887053 756833666262650118332645)
                ·
                  refine ⟨141906312424246897187371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 756833666262650118332645 141906312424246897187371)
                  ·
                    rfl

theorem cell22_1243627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 4].length) (baseStart_1243627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243627 prefixEnd_1243627 := by exact prefixLift 1243627
  have htrace : WordTrace (prefixWord ++ tailWord_1243627) baseStart_1243627 baseEnd_1243627 := by
    simpa [prefixWord, tailWord_1243627, baseEnd_1243627] using wordTrace_append hprefix tailTrace_1243627
  have hstable : (prefixWord ++ tailWord_1243627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243627).length < 2 ^ (prefixWord ++ tailWord_1243627).sum := by decide
  have hdescent : baseEnd_1243627 < baseStart_1243627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243629 : List Nat := [1, 5, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_1243629 : Nat := 118140960795 + 1243629 * 2 ^ 59
def prefixEnd_1243629 : Nat := 4983230072969 + 3 ^ 40 * 1243629 * 2
def baseEnd_1243629 : Nat := 425719621913613353012107

theorem tailTrace_1243629 : CollatzResearch.WordTrace tailWord_1243629 prefixEnd_1243629 425719621913613353012107 := by
  unfold tailWord_1243629
  simp only [CollatzResearch.WordTrace]
  refine ⟨45358876011552002768685941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30239250674368001845790627 45358876011552002768685941)
  ·
    refine ⟨4252394626083000259564307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45358876011552002768685941 4252394626083000259564307)
    ·
      refine ⟨6378591939124500389346461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4252394626083000259564307 6378591939124500389346461)
      ·
        refine ⟨2391971977171687646004923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6378591939124500389346461 2391971977171687646004923)
        ·
          refine ⟨3587957965757531469007385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2391971977171687646004923 3587957965757531469007385)
          ·
            refine ⟨2690968474318148601755539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3587957965757531469007385 2690968474318148601755539)
            ·
              refine ⟨4036452711477222902633309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2690968474318148601755539 4036452711477222902633309)
              ·
                refine ⟨1513669766803958588487491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4036452711477222902633309 1513669766803958588487491)
                ·
                  refine ⟨2270504650205937882731237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1513669766803958588487491 2270504650205937882731237)
                  ·
                    refine ⟨425719621913613353012107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2270504650205937882731237 425719621913613353012107)
                    ·
                      rfl

theorem cell22_1243629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_1243629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243629 prefixEnd_1243629 := by exact prefixLift 1243629
  have htrace : WordTrace (prefixWord ++ tailWord_1243629) baseStart_1243629 baseEnd_1243629 := by
    simpa [prefixWord, tailWord_1243629, baseEnd_1243629] using wordTrace_append hprefix tailTrace_1243629
  have hstable : (prefixWord ++ tailWord_1243629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243629).length < 2 ^ (prefixWord ++ tailWord_1243629).sum := by decide
  have hdescent : baseEnd_1243629 < baseStart_1243629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243640 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 4, 4]
def baseStart_1243640 : Nat := 118140960795 + 1243640 * 2 ^ 59
def prefixEnd_1243640 : Nat := 4983230072969 + 3 ^ 40 * 1243640 * 2
def baseEnd_1243640 : Nat := 425723387438412990987073

theorem tailTrace_1243640 : CollatzResearch.WordTrace tailWord_1243640 prefixEnd_1243640 425723387438412990987073 := by
  unfold tailWord_1243640
  simp only [CollatzResearch.WordTrace]
  refine ⟨22679638607256075823668187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30239518143008101098224249 22679638607256075823668187)
  ·
    refine ⟨34019457910884113735502281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22679638607256075823668187 34019457910884113735502281)
    ·
      refine ⟨25514593433163085301626711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34019457910884113735502281 25514593433163085301626711)
      ·
        refine ⟨38271890149744627952440067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25514593433163085301626711 38271890149744627952440067)
        ·
          refine ⟨57407835224616941928660101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38271890149744627952440067 57407835224616941928660101)
          ·
            refine ⟨10763969104615676611623769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57407835224616941928660101 10763969104615676611623769)
            ·
              refine ⟨8072976828461757458717827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10763969104615676611623769 8072976828461757458717827)
              ·
                refine ⟨12109465242692636188076741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8072976828461757458717827 12109465242692636188076741)
                ·
                  refine ⟨2270524733004869285264389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12109465242692636188076741 2270524733004869285264389)
                  ·
                    refine ⟨425723387438412990987073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2270524733004869285264389 425723387438412990987073)
                    ·
                      rfl

theorem cell22_1243640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_1243640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243640 prefixEnd_1243640 := by exact prefixLift 1243640
  have htrace : WordTrace (prefixWord ++ tailWord_1243640) baseStart_1243640 baseEnd_1243640 := by
    simpa [prefixWord, tailWord_1243640, baseEnd_1243640] using wordTrace_append hprefix tailTrace_1243640
  have hstable : (prefixWord ++ tailWord_1243640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243640).length < 2 ^ (prefixWord ++ tailWord_1243640).sum := by decide
  have hdescent : baseEnd_1243640 < baseStart_1243640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243642 : List Nat := [3, 1, 1, 1, 1, 2, 2, 6, 2, 3]
def baseStart_1243642 : Nat := 118140960795 + 1243642 * 2 ^ 59
def prefixEnd_1243642 : Nat := 4983230072969 + 3 ^ 40 * 1243642 * 2
def baseEnd_1243642 : Nat := 425724072079285652437067

theorem tailTrace_1243642 : CollatzResearch.WordTrace tailWord_1243642 prefixEnd_1243642 425724072079285652437067 := by
  unfold tailWord_1243642
  simp only [CollatzResearch.WordTrace]
  refine ⟨11339837540126226497227295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30239566773669937325939453 11339837540126226497227295)
  ·
    refine ⟨17009756310189339745840943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11339837540126226497227295 17009756310189339745840943)
    ·
      refine ⟨25514634465284009618761415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17009756310189339745840943 25514634465284009618761415)
      ·
        refine ⟨38271951697926014428142123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25514634465284009618761415 38271951697926014428142123)
        ·
          refine ⟨57407927546889021642213185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38271951697926014428142123 57407927546889021642213185)
          ·
            refine ⟨43055945660166766231659889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57407927546889021642213185 43055945660166766231659889)
            ·
              refine ⟨32291959245125074673744917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43055945660166766231659889 32291959245125074673744917)
              ·
                refine ⟨1513685589615237875331793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32291959245125074673744917 1513685589615237875331793)
                ·
                  refine ⟨1135264192211428406498845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1513685589615237875331793 1135264192211428406498845)
                  ·
                    refine ⟨425724072079285652437067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1135264192211428406498845 425724072079285652437067)
                    ·
                      rfl

theorem cell22_1243642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_1243642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243642 prefixEnd_1243642 := by exact prefixLift 1243642
  have htrace : WordTrace (prefixWord ++ tailWord_1243642) baseStart_1243642 baseEnd_1243642 := by
    simpa [prefixWord, tailWord_1243642, baseEnd_1243642] using wordTrace_append hprefix tailTrace_1243642
  have hstable : (prefixWord ++ tailWord_1243642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243642).length < 2 ^ (prefixWord ++ tailWord_1243642).sum := by decide
  have hdescent : baseEnd_1243642 < baseStart_1243642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243672 : List Nat := [2, 1, 2, 3, 3, 1, 4, 6]
def baseStart_1243672 : Nat := 118140960795 + 1243672 * 2 ^ 59
def prefixEnd_1243672 : Nat := 4983230072969 + 3 ^ 40 * 1243672 * 2
def baseEnd_1243672 : Nat := 47303815743597286020775

theorem tailTrace_1243672 : CollatzResearch.WordTrace tailWord_1243672 prefixEnd_1243672 47303815743597286020775 := by
  unfold tailWord_1243672
  simp only [CollatzResearch.WordTrace]
  refine ⟨22680222175198110556250635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30240296233597480741667513 22680222175198110556250635)
  ·
    refine ⟨34020333262797165834375953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22680222175198110556250635 34020333262797165834375953)
    ·
      refine ⟨25515249947097874375781965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34020333262797165834375953 25515249947097874375781965)
      ·
        refine ⟨9568218730161702890918237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25515249947097874375781965 9568218730161702890918237)
        ·
          refine ⟨3588082023810638584094339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9568218730161702890918237 3588082023810638584094339)
          ·
            refine ⟨5382123035715957876141509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3588082023810638584094339 5382123035715957876141509)
            ·
              refine ⟨1009148069196742101776533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5382123035715957876141509 1009148069196742101776533)
              ·
                refine ⟨47303815743597286020775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1009148069196742101776533 47303815743597286020775)
                ·
                  rfl

theorem cell22_1243672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 6].length) (baseStart_1243672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243672 prefixEnd_1243672 := by exact prefixLift 1243672
  have htrace : WordTrace (prefixWord ++ tailWord_1243672) baseStart_1243672 baseEnd_1243672 := by
    simpa [prefixWord, tailWord_1243672, baseEnd_1243672] using wordTrace_append hprefix tailTrace_1243672
  have hstable : (prefixWord ++ tailWord_1243672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243672).length < 2 ^ (prefixWord ++ tailWord_1243672).sum := by decide
  have hdescent : baseEnd_1243672 < baseStart_1243672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243710 : List Nat := [4, 2, 1, 4, 1, 2, 2, 1, 2, 3]
def baseStart_1243710 : Nat := 118140960795 + 1243710 * 2 ^ 59
def prefixEnd_1243710 : Nat := 4983230072969 + 3 ^ 40 * 1243710 * 2
def baseEnd_1243710 : Nat := 425747349868956141736859

theorem tailTrace_1243710 : CollatzResearch.WordTrace tailWord_1243710 prefixEnd_1243710 425747349868956141736859 := by
  unfold tailWord_1243710
  simp only [CollatzResearch.WordTrace]
  refine ⟨5670228790532319200298073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30241220216172369068256389 5670228790532319200298073)
  ·
    refine ⟨4252671592899239400223555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5670228790532319200298073 4252671592899239400223555)
    ·
      refine ⟨6379007389348859100335333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4252671592899239400223555 6379007389348859100335333)
      ·
        refine ⟨1196063885502911081312875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6379007389348859100335333 1196063885502911081312875)
        ·
          refine ⟨1794095828254366621969313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1196063885502911081312875 1794095828254366621969313)
          ·
            refine ⟨1345571871190774966476985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1794095828254366621969313 1345571871190774966476985)
            ·
              refine ⟨1009178903393081224857739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1345571871190774966476985 1009178903393081224857739)
              ·
                refine ⟨1513768355089621837286609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1009178903393081224857739 1513768355089621837286609)
                ·
                  refine ⟨1135326266317216377964957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1513768355089621837286609 1135326266317216377964957)
                  ·
                    refine ⟨425747349868956141736859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1135326266317216377964957 425747349868956141736859)
                    ·
                      rfl

theorem cell22_1243710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_1243710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243710 prefixEnd_1243710 := by exact prefixLift 1243710
  have htrace : WordTrace (prefixWord ++ tailWord_1243710) baseStart_1243710 baseEnd_1243710 := by
    simpa [prefixWord, tailWord_1243710, baseEnd_1243710] using wordTrace_append hprefix tailTrace_1243710
  have hstable : (prefixWord ++ tailWord_1243710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243710).length < 2 ^ (prefixWord ++ tailWord_1243710).sum := by decide
  have hdescent : baseEnd_1243710 < baseStart_1243710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243715 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 2, 5]
def baseStart_1243715 : Nat := 118140960795 + 1243715 * 2 ^ 59
def prefixEnd_1243715 : Nat := 4983230072969 + 3 ^ 40 * 1243715 * 2
def baseEnd_1243715 : Nat := 425749061471137795361843

theorem tailTrace_1243715 : CollatzResearch.WordTrace tailWord_1243715 prefixEnd_1243715 425749061471137795361843 := by
  unfold tailWord_1243715
  simp only [CollatzResearch.WordTrace]
  refine ⟨45362012689240439456316599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30241341792826959637544399 45362012689240439456316599)
  ·
    refine ⟨68043019033860659184474899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45362012689240439456316599 68043019033860659184474899)
    ·
      refine ⟨102064528550790988776712349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68043019033860659184474899 102064528550790988776712349)
      ·
        refine ⟨38274198206546620791267131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102064528550790988776712349 38274198206546620791267131)
        ·
          refine ⟨57411297309819931186900697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38274198206546620791267131 57411297309819931186900697)
          ·
            refine ⟨43058472982364948390175523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57411297309819931186900697 43058472982364948390175523)
            ·
              refine ⟨64587709473547422585263285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43058472982364948390175523 64587709473547422585263285)
              ·
                refine ⟨6055097763145070867368433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64587709473547422585263285 6055097763145070867368433)
                ·
                  refine ⟨4541323322358803150526325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6055097763145070867368433 4541323322358803150526325)
                  ·
                    refine ⟨425749061471137795361843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4541323322358803150526325 425749061471137795361843)
                    ·
                      rfl

theorem cell22_1243715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 5].length) (baseStart_1243715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243715 prefixEnd_1243715 := by exact prefixLift 1243715
  have htrace : WordTrace (prefixWord ++ tailWord_1243715) baseStart_1243715 baseEnd_1243715 := by
    simpa [prefixWord, tailWord_1243715, baseEnd_1243715] using wordTrace_append hprefix tailTrace_1243715
  have hstable : (prefixWord ++ tailWord_1243715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243715).length < 2 ^ (prefixWord ++ tailWord_1243715).sum := by decide
  have hdescent : baseEnd_1243715 < baseStart_1243715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243717 : List Nat := [1, 3, 1, 1, 1, 6, 1, 3, 5]
def baseStart_1243717 : Nat := 118140960795 + 1243717 * 2 ^ 59
def prefixEnd_1243717 : Nat := 4983230072969 + 3 ^ 40 * 1243717 * 2
def baseEnd_1243717 : Nat := 141916582037336818937279

theorem tailTrace_1243717 : CollatzResearch.WordTrace tailWord_1243717 prefixEnd_1243717 141916582037336818937279 := by
  unfold tailWord_1243717
  simp only [CollatzResearch.WordTrace]
  refine ⟨45362085635233193797889405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30241390423488795865259603 45362085635233193797889405)
  ·
    refine ⟨17010782113212447674208527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45362085635233193797889405 17010782113212447674208527)
    ·
      refine ⟨25516173169818671511312791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17010782113212447674208527 25516173169818671511312791)
      ·
        refine ⟨38274259754728007266969187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25516173169818671511312791 38274259754728007266969187)
        ·
          refine ⟨57411389632092010900453781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38274259754728007266969187 57411389632092010900453781)
          ·
            refine ⟨2691158889004313010958771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57411389632092010900453781 2691158889004313010958771)
            ·
              refine ⟨4036738333506469516438157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2691158889004313010958771 4036738333506469516438157)
              ·
                refine ⟨1513776875064926068664309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4036738333506469516438157 1513776875064926068664309)
                ·
                  refine ⟨141916582037336818937279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1513776875064926068664309 141916582037336818937279)
                  ·
                    rfl

theorem cell22_1243717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_1243717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243717 prefixEnd_1243717 := by exact prefixLift 1243717
  have htrace : WordTrace (prefixWord ++ tailWord_1243717) baseStart_1243717 baseEnd_1243717 := by
    simpa [prefixWord, tailWord_1243717, baseEnd_1243717] using wordTrace_append hprefix tailTrace_1243717
  have hstable : (prefixWord ++ tailWord_1243717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243717).length < 2 ^ (prefixWord ++ tailWord_1243717).sum := by decide
  have hdescent : baseEnd_1243717 < baseStart_1243717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243794 : List Nat := [3, 2, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_1243794 : Nat := 118140960795 + 1243794 * 2 ^ 59
def prefixEnd_1243794 : Nat := 4983230072969 + 3 ^ 40 * 1243794 * 2
def baseEnd_1243794 : Nat := 425776104785607922636601

theorem tailTrace_1243794 : CollatzResearch.WordTrace tailWord_1243794 prefixEnd_1243794 425776104785607922636601 := by
  unfold tailWord_1243794
  simp only [CollatzResearch.WordTrace]
  refine ⟨11341223513988558987110609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30243262703969490632294957 11341223513988558987110609)
  ·
    refine ⟨8505917635491419240332957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11341223513988558987110609 8505917635491419240332957)
    ·
      refine ⟨3189719113309282215124859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8505917635491419240332957 3189719113309282215124859)
      ·
        refine ⟨4784578669963923322687289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3189719113309282215124859 4784578669963923322687289)
        ·
          refine ⟨3588434002472942492015467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4784578669963923322687289 3588434002472942492015467)
          ·
            refine ⟨5382651003709413738023201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3588434002472942492015467 5382651003709413738023201)
            ·
              refine ⟨4036988252782060303517401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5382651003709413738023201 4036988252782060303517401)
              ·
                refine ⟨3027741189586545227638051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4036988252782060303517401 3027741189586545227638051)
                ·
                  refine ⟨4541611784379817841457077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3027741189586545227638051 4541611784379817841457077)
                  ·
                    refine ⟨425776104785607922636601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4541611784379817841457077 425776104785607922636601)
                    ·
                      rfl

theorem cell22_1243794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_1243794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243794 prefixEnd_1243794 := by exact prefixLift 1243794
  have htrace : WordTrace (prefixWord ++ tailWord_1243794) baseStart_1243794 baseEnd_1243794 := by
    simpa [prefixWord, tailWord_1243794, baseEnd_1243794] using wordTrace_append hprefix tailTrace_1243794
  have hstable : (prefixWord ++ tailWord_1243794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243794).length < 2 ^ (prefixWord ++ tailWord_1243794).sum := by decide
  have hdescent : baseEnd_1243794 < baseStart_1243794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243796 : List Nat := [2, 4, 2, 2, 1, 1, 1, 5, 4]
def baseStart_1243796 : Nat := 118140960795 + 1243796 * 2 ^ 59
def prefixEnd_1243796 : Nat := 4983230072969 + 3 ^ 40 * 1243796 * 2
def baseEnd_1243796 : Nat := 141925596475493528028865

theorem tailTrace_1243796 : CollatzResearch.WordTrace tailWord_1243796 prefixEnd_1243796 141925596475493528028865 := by
  unfold tailWord_1243796
  simp only [CollatzResearch.WordTrace]
  refine ⟨22682483500973495145007621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30243311334631326860010161 22682483500973495145007621)
  ·
    refine ⟨4252965656432530339688929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22682483500973495145007621 4252965656432530339688929)
    ·
      refine ⟨3189724242324397754766697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4252965656432530339688929 3189724242324397754766697)
      ·
        refine ⟨2392293181743298316075023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3189724242324397754766697 2392293181743298316075023)
        ·
          refine ⟨3588439772614947474112535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2392293181743298316075023 3588439772614947474112535)
          ·
            refine ⟨5382659658922421211168803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3588439772614947474112535 5382659658922421211168803)
            ·
              refine ⟨8073989488383631816753205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5382659658922421211168803 8073989488383631816753205)
              ·
                refine ⟨756936514535965482820613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8073989488383631816753205 756936514535965482820613)
                ·
                  refine ⟨141925596475493528028865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 756936514535965482820613 141925596475493528028865)
                  ·
                    rfl

theorem cell22_1243796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_1243796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243796 prefixEnd_1243796 := by exact prefixLift 1243796
  have htrace : WordTrace (prefixWord ++ tailWord_1243796) baseStart_1243796 baseEnd_1243796 := by
    simpa [prefixWord, tailWord_1243796, baseEnd_1243796] using wordTrace_append hprefix tailTrace_1243796
  have hstable : (prefixWord ++ tailWord_1243796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243796).length < 2 ^ (prefixWord ++ tailWord_1243796).sum := by decide
  have hdescent : baseEnd_1243796 < baseStart_1243796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243839 : List Nat := [1, 1, 2, 2, 2, 4, 2, 2, 3, 3]
def baseStart_1243839 : Nat := 118140960795 + 1243839 * 2 ^ 59
def prefixEnd_1243839 : Nat := 4983230072969 + 3 ^ 40 * 1243839 * 2
def baseEnd_1243839 : Nat := 425791509205242805261463

theorem tailTrace_1243839 : CollatzResearch.WordTrace tailWord_1243839 prefixEnd_1243839 425791509205242805261463 := by
  unfold tailWord_1243839
  simp only [CollatzResearch.WordTrace]
  refine ⟨45366535340791208633830571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30244356893860805755887047 45366535340791208633830571)
  ·
    refine ⟨68049803011186812950745857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45366535340791208633830571 68049803011186812950745857)
    ·
      refine ⟨51037352258390109713059393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68049803011186812950745857 51037352258390109713059393)
      ·
        refine ⟨38278014193792582284794545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51037352258390109713059393 38278014193792582284794545)
        ·
          refine ⟨28708510645344436713595909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38278014193792582284794545 28708510645344436713595909)
          ·
            refine ⟨5382845746002081883799233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28708510645344436713595909 5382845746002081883799233)
            ·
              refine ⟨4037134309501561412849425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5382845746002081883799233 4037134309501561412849425)
              ·
                refine ⟨3027850732126171059637069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4037134309501561412849425 3027850732126171059637069)
                ·
                  refine ⟨1135444024547314147363901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3027850732126171059637069 1135444024547314147363901)
                  ·
                    refine ⟨425791509205242805261463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1135444024547314147363901 425791509205242805261463)
                    ·
                      rfl

theorem cell22_1243839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 3].length) (baseStart_1243839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243839 prefixEnd_1243839 := by exact prefixLift 1243839
  have htrace : WordTrace (prefixWord ++ tailWord_1243839) baseStart_1243839 baseEnd_1243839 := by
    simpa [prefixWord, tailWord_1243839, baseEnd_1243839] using wordTrace_append hprefix tailTrace_1243839
  have hstable : (prefixWord ++ tailWord_1243839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243839).length < 2 ^ (prefixWord ++ tailWord_1243839).sum := by decide
  have hdescent : baseEnd_1243839 < baseStart_1243839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243841 : List Nat := [1, 2, 6, 2, 1, 1, 1, 8]
def baseStart_1243841 : Nat := 118140960795 + 1243841 * 2 ^ 59
def prefixEnd_1243841 : Nat := 4983230072969 + 3 ^ 40 * 1243841 * 2
def baseEnd_1243841 : Nat := 47310243760679496301273

theorem tailTrace_1243841 : CollatzResearch.WordTrace tailWord_1243841 prefixEnd_1243841 47310243760679496301273 := by
  unfold tailWord_1243841
  simp only [CollatzResearch.WordTrace]
  refine ⟨45366608286783962975403377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30244405524522641983602251 45366608286783962975403377)
  ·
    refine ⟨34024956215087972231552533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45366608286783962975403377 34024956215087972231552533)
    ·
      refine ⟨1594919822582248698354025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34024956215087972231552533 1594919822582248698354025)
      ·
        refine ⟨1196189866936686523765519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1594919822582248698354025 1196189866936686523765519)
        ·
          refine ⟨1794284800405029785648279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1196189866936686523765519 1794284800405029785648279)
          ·
            refine ⟨2691427200607544678472419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1794284800405029785648279 2691427200607544678472419)
            ·
              refine ⟨4037140800911317017708629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2691427200607544678472419 4037140800911317017708629)
              ·
                refine ⟨47310243760679496301273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4037140800911317017708629 47310243760679496301273)
                ·
                  rfl

theorem cell22_1243841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 8].length) (baseStart_1243841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243841 prefixEnd_1243841 := by exact prefixLift 1243841
  have htrace : WordTrace (prefixWord ++ tailWord_1243841) baseStart_1243841 baseEnd_1243841 := by
    simpa [prefixWord, tailWord_1243841, baseEnd_1243841] using wordTrace_append hprefix tailTrace_1243841
  have hstable : (prefixWord ++ tailWord_1243841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243841).length < 2 ^ (prefixWord ++ tailWord_1243841).sum := by decide
  have hdescent : baseEnd_1243841 < baseStart_1243841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243882 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 2, 8]
def baseStart_1243882 : Nat := 118140960795 + 1243882 * 2 ^ 59
def prefixEnd_1243882 : Nat := 4983230072969 + 3 ^ 40 * 1243882 * 2
def baseEnd_1243882 : Nat := 425806228984005026436331

theorem tailTrace_1243882 : CollatzResearch.WordTrace tailWord_1243882 prefixEnd_1243882 425806228984005026436331 := by
  unfold tailWord_1243882
  simp only [CollatzResearch.WordTrace]
  refine ⟨11342025919908856744411475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30245402453090284651763933 11342025919908856744411475)
  ·
    refine ⟨17013038879863285116617213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11342025919908856744411475 17013038879863285116617213)
    ·
      refine ⟨6379889579948731918731455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17013038879863285116617213 6379889579948731918731455)
      ·
        refine ⟨9569834369923097878097183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6379889579948731918731455 9569834369923097878097183)
        ·
          refine ⟨14354751554884646817145775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9569834369923097878097183 14354751554884646817145775)
          ·
            refine ⟨21532127332326970225718663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14354751554884646817145775 21532127332326970225718663)
            ·
              refine ⟨32298190998490455338577995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21532127332326970225718663 32298190998490455338577995)
              ·
                refine ⟨48447286497735683007866993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32298190998490455338577995 48447286497735683007866993)
                ·
                  refine ⟨36335464873301762255900245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48447286497735683007866993 36335464873301762255900245)
                  ·
                    refine ⟨425806228984005026436331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36335464873301762255900245 425806228984005026436331)
                    ·
                      rfl

theorem cell22_1243882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_1243882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243882 prefixEnd_1243882 := by exact prefixLift 1243882
  have htrace : WordTrace (prefixWord ++ tailWord_1243882) baseStart_1243882 baseEnd_1243882 := by
    simpa [prefixWord, tailWord_1243882, baseEnd_1243882] using wordTrace_append hprefix tailTrace_1243882
  have hstable : (prefixWord ++ tailWord_1243882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243882).length < 2 ^ (prefixWord ++ tailWord_1243882).sum := by decide
  have hdescent : baseEnd_1243882 < baseStart_1243882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243886 : List Nat := [4, 1, 2, 1, 1, 3, 4, 1, 5]
def baseStart_1243886 : Nat := 118140960795 + 1243886 * 2 ^ 59
def prefixEnd_1243886 : Nat := 4983230072969 + 3 ^ 40 * 1243886 * 2
def baseEnd_1243886 : Nat := 141935866088583449778773

theorem tailTrace_1243886 : CollatzResearch.WordTrace tailWord_1243886 prefixEnd_1243886 141935866088583449778773 := by
  unfold tailWord_1243886
  simp only [CollatzResearch.WordTrace]
  refine ⟨5671031196452616957598939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30245499714413957107194341 5671031196452616957598939)
  ·
    refine ⟨8506546794678925436398409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5671031196452616957598939 8506546794678925436398409)
    ·
      refine ⟨6379910096009194077298807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8506546794678925436398409 6379910096009194077298807)
      ·
        refine ⟨9569865144013791115948211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6379910096009194077298807 9569865144013791115948211)
        ·
          refine ⟨14354797716020686673922317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9569865144013791115948211 14354797716020686673922317)
          ·
            refine ⟨5383049143507757502720869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14354797716020686673922317 5383049143507757502720869)
            ·
              refine ⟨1009321714407704531760163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5383049143507757502720869 1009321714407704531760163)
              ·
                refine ⟨1513982571611556797640245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1009321714407704531760163 1513982571611556797640245)
                ·
                  refine ⟨141935866088583449778773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1513982571611556797640245 141935866088583449778773)
                  ·
                    rfl

theorem cell22_1243886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_1243886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243886 prefixEnd_1243886 := by exact prefixLift 1243886
  have htrace : WordTrace (prefixWord ++ tailWord_1243886) baseStart_1243886 baseEnd_1243886 := by
    simpa [prefixWord, tailWord_1243886, baseEnd_1243886] using wordTrace_append hprefix tailTrace_1243886
  have hstable : (prefixWord ++ tailWord_1243886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243886).length < 2 ^ (prefixWord ++ tailWord_1243886).sum := by decide
  have hdescent : baseEnd_1243886 < baseStart_1243886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243897 : List Nat := [1, 2, 1, 3, 1, 1, 1, 6, 6]
def baseStart_1243897 : Nat := 118140960795 + 1243897 * 2 ^ 59
def prefixEnd_1243897 : Nat := 4983230072969 + 3 ^ 40 * 1243897 * 2
def baseEnd_1243897 : Nat := 141937121263516662437095

theorem tailTrace_1243897 : CollatzResearch.WordTrace tailWord_1243897 prefixEnd_1243897 141937121263516662437095 := by
  unfold tailWord_1243897
  simp only [CollatzResearch.WordTrace]
  refine ⟨45368650774581084539441945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30245767183054056359627963 45368650774581084539441945)
  ·
    refine ⟨34026488080935813404581459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45368650774581084539441945 34026488080935813404581459)
    ·
      refine ⟨51039732121403720106872189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34026488080935813404581459 51039732121403720106872189)
      ·
        refine ⟨19139899545526395040077071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51039732121403720106872189 19139899545526395040077071)
        ·
          refine ⟨28709849318289592560115607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19139899545526395040077071 28709849318289592560115607)
          ·
            refine ⟨43064773977434388840173411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28709849318289592560115607 43064773977434388840173411)
            ·
              refine ⟨64597160966151583260260117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43064773977434388840173411 64597160966151583260260117)
              ·
                refine ⟨3027991920288355465324693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64597160966151583260260117 3027991920288355465324693)
                ·
                  refine ⟨141937121263516662437095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3027991920288355465324693 141937121263516662437095)
                  ·
                    rfl

theorem cell22_1243897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 6].length) (baseStart_1243897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243897 prefixEnd_1243897 := by exact prefixLift 1243897
  have htrace : WordTrace (prefixWord ++ tailWord_1243897) baseStart_1243897 baseEnd_1243897 := by
    simpa [prefixWord, tailWord_1243897, baseEnd_1243897] using wordTrace_append hprefix tailTrace_1243897
  have hstable : (prefixWord ++ tailWord_1243897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243897).length < 2 ^ (prefixWord ++ tailWord_1243897).sum := by decide
  have hdescent : baseEnd_1243897 < baseStart_1243897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243944 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 1, 6]
def baseStart_1243944 : Nat := 118140960795 + 1243944 * 2 ^ 59
def prefixEnd_1243944 : Nat := 4983230072969 + 3 ^ 40 * 1243944 * 2
def baseEnd_1243944 : Nat := 425827452851057531386141

theorem tailTrace_1243944 : CollatzResearch.WordTrace tailWord_1243944 prefixEnd_1243944 425827452851057531386141 := by
  unfold tailWord_1243944
  simp only [CollatzResearch.WordTrace]
  refine ⟨22685182502705405783201443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30246910003607207710935257 22685182502705405783201443)
  ·
    refine ⟨34027773754058108674802165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22685182502705405783201443 34027773754058108674802165)
    ·
      refine ⟨3190103789442947688262703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34027773754058108674802165 3190103789442947688262703)
      ·
        refine ⟨4785155684164421532394055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3190103789442947688262703 4785155684164421532394055)
        ·
          refine ⟨7177733526246632298591083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4785155684164421532394055 7177733526246632298591083)
          ·
            refine ⟨10766600289369948447886625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7177733526246632298591083 10766600289369948447886625)
            ·
              refine ⟨8074950217027461335914969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10766600289369948447886625 8074950217027461335914969)
              ·
                refine ⟨6056212662770596001936227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8074950217027461335914969 6056212662770596001936227)
                ·
                  refine ⟨9084318994155894002904341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6056212662770596001936227 9084318994155894002904341)
                  ·
                    refine ⟨425827452851057531386141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9084318994155894002904341 425827452851057531386141)
                    ·
                      rfl

theorem cell22_1243944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_1243944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243944 prefixEnd_1243944 := by exact prefixLift 1243944
  have htrace : WordTrace (prefixWord ++ tailWord_1243944) baseStart_1243944 baseEnd_1243944 := by
    simpa [prefixWord, tailWord_1243944, baseEnd_1243944] using wordTrace_append hprefix tailTrace_1243944
  have hstable : (prefixWord ++ tailWord_1243944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243944).length < 2 ^ (prefixWord ++ tailWord_1243944).sum := by decide
  have hdescent : baseEnd_1243944 < baseStart_1243944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243959 : List Nat := [1, 1, 3, 1, 2, 1, 7, 6]
def baseStart_1243959 : Nat := 118140960795 + 1243959 * 2 ^ 59
def prefixEnd_1243959 : Nat := 4983230072969 + 3 ^ 40 * 1243959 * 2
def baseEnd_1243959 : Nat := 47314731961955832473455

theorem tailTrace_1243959 : CollatzResearch.WordTrace tailWord_1243959 prefixEnd_1243959 47314731961955832473455 := by
  unfold tailWord_1243959
  simp only [CollatzResearch.WordTrace]
  refine ⟨45370912100356469128198931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30247274733570979418799287 45370912100356469128198931)
  ·
    refine ⟨68056368150534703692298397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45370912100356469128198931 68056368150534703692298397)
    ·
      refine ⟨25521138056450513884611899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68056368150534703692298397 25521138056450513884611899)
      ·
        refine ⟨38281707084675770826917849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25521138056450513884611899 38281707084675770826917849)
        ·
          refine ⟨28711280313506828120188387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38281707084675770826917849 28711280313506828120188387)
          ·
            refine ⟨43066920470260242180282581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28711280313506828120188387 43066920470260242180282581)
            ·
              refine ⟨1009380948521724426100373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 43066920470260242180282581 1009380948521724426100373)
              ·
                refine ⟨47314731961955832473455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1009380948521724426100373 47314731961955832473455)
                ·
                  rfl

theorem cell22_1243959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 6].length) (baseStart_1243959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243959 prefixEnd_1243959 := by exact prefixLift 1243959
  have htrace : WordTrace (prefixWord ++ tailWord_1243959) baseStart_1243959 baseEnd_1243959 := by
    simpa [prefixWord, tailWord_1243959, baseEnd_1243959] using wordTrace_append hprefix tailTrace_1243959
  have hstable : (prefixWord ++ tailWord_1243959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243959).length < 2 ^ (prefixWord ++ tailWord_1243959).sum := by decide
  have hdescent : baseEnd_1243959 < baseStart_1243959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243991 : List Nat := [1, 1, 3, 2, 4, 1, 1, 3, 3, 3]
def baseStart_1243991 : Nat := 118140960795 + 1243991 * 2 ^ 59
def prefixEnd_1243991 : Nat := 4983230072969 + 3 ^ 40 * 1243991 * 2
def baseEnd_1243991 : Nat := 425843541911565075460997

theorem tailTrace_1243991 : CollatzResearch.WordTrace tailWord_1243991 prefixEnd_1243991 425843541911565075460997 := by
  unfold tailWord_1243991
  simp only [CollatzResearch.WordTrace]
  refine ⟨45372079236240538593363827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30248052824160359062242551 45372079236240538593363827)
  ·
    refine ⟨68058118854360807890045741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45372079236240538593363827 68058118854360807890045741)
    ·
      refine ⟨25521794570385302958767153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68058118854360807890045741 25521794570385302958767153)
      ·
        refine ⟨19141345927788977219075365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25521794570385302958767153 19141345927788977219075365)
        ·
          refine ⟨3589002361460433228576631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19141345927788977219075365 3589002361460433228576631)
          ·
            refine ⟨5383503542190649842864947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3589002361460433228576631 5383503542190649842864947)
            ·
              refine ⟨8075255313285974764297421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5383503542190649842864947 8075255313285974764297421)
              ·
                refine ⟨3028220742482240536611533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8075255313285974764297421 3028220742482240536611533)
                ·
                  refine ⟨1135582778430840201229325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3028220742482240536611533 1135582778430840201229325)
                  ·
                    refine ⟨425843541911565075460997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1135582778430840201229325 425843541911565075460997)
                    ·
                      rfl

theorem cell22_1243991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_1243991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1243991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1243991 prefixEnd_1243991 := by exact prefixLift 1243991
  have htrace : WordTrace (prefixWord ++ tailWord_1243991) baseStart_1243991 baseEnd_1243991 := by
    simpa [prefixWord, tailWord_1243991, baseEnd_1243991] using wordTrace_append hprefix tailTrace_1243991
  have hstable : (prefixWord ++ tailWord_1243991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243991).length < 2 ^ (prefixWord ++ tailWord_1243991).sum := by decide
  have hdescent : baseEnd_1243991 < baseStart_1243991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244025 : List Nat := [1, 2, 1, 3, 2, 5, 1, 3, 1, 3]
def baseStart_1244025 : Nat := 118140960795 + 1244025 * 2 ^ 59
def prefixEnd_1244025 : Nat := 4983230072969 + 3 ^ 40 * 1244025 * 2
def baseEnd_1244025 : Nat := 425855180806400320110893

theorem tailTrace_1244025 : CollatzResearch.WordTrace tailWord_1244025 prefixEnd_1244025 425855180806400320110893 := by
  unfold tailWord_1244025
  simp only [CollatzResearch.WordTrace]
  refine ⟨45373319318117362400101529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30248879545411574933401019 45373319318117362400101529)
  ·
    refine ⟨34029989488588021800076147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45373319318117362400101529 34029989488588021800076147)
    ·
      refine ⟨51044984232882032700114221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34029989488588021800076147 51044984232882032700114221)
      ·
        refine ⟨19141869087330762262542833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51044984232882032700114221 19141869087330762262542833)
        ·
          refine ⟨14356401815498071696907125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19141869087330762262542833 14356401815498071696907125)
          ·
            refine ⟨1345912670202944221585043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14356401815498071696907125 1345912670202944221585043)
            ·
              refine ⟨2018869005304416332377565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1345912670202944221585043 2018869005304416332377565)
              ·
                refine ⟨757075876989156124641587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2018869005304416332377565 757075876989156124641587)
                ·
                  refine ⟨1135613815483734186962381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 757075876989156124641587 1135613815483734186962381)
                  ·
                    refine ⟨425855180806400320110893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1135613815483734186962381 425855180806400320110893)
                    ·
                      rfl

theorem cell22_1244025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 1, 3].length) (baseStart_1244025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244025 prefixEnd_1244025 := by exact prefixLift 1244025
  have htrace : WordTrace (prefixWord ++ tailWord_1244025) baseStart_1244025 baseEnd_1244025 := by
    simpa [prefixWord, tailWord_1244025, baseEnd_1244025] using wordTrace_append hprefix tailTrace_1244025
  have hstable : (prefixWord ++ tailWord_1244025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244025).length < 2 ^ (prefixWord ++ tailWord_1244025).sum := by decide
  have hdescent : baseEnd_1244025 < baseStart_1244025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244042 : List Nat := [3, 1, 2, 4, 1, 2, 3, 2, 1, 3]
def baseStart_1244042 : Nat := 118140960795 + 1244042 * 2 ^ 59
def prefixEnd_1244042 : Nat := 4983230072969 + 3 ^ 40 * 1244042 * 2
def baseEnd_1244042 : Nat := 425861000253817942435841

theorem tailTrace_1244042 : CollatzResearch.WordTrace tailWord_1244042 prefixEnd_1244042 425861000253817942435841 := by
  unfold tailWord_1244042
  simp only [CollatzResearch.WordTrace]
  refine ⟨11343484839763943575867595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30249292906037182868980253 11343484839763943575867595)
  ·
    refine ⟨17015227259645915363801393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11343484839763943575867595 17015227259645915363801393)
    ·
      refine ⟨12761420444734436522851045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17015227259645915363801393 12761420444734436522851045)
      ·
        refine ⟨2392766333387706848034571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12761420444734436522851045 2392766333387706848034571)
        ·
          refine ⟨3589149500081560272051857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2392766333387706848034571 3589149500081560272051857)
          ·
            refine ⟨2691862125061170204038893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3589149500081560272051857 2691862125061170204038893)
            ·
              refine ⟨1009448296897938826514585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2691862125061170204038893 1009448296897938826514585)
              ·
                refine ⟨757086222673454119885939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1009448296897938826514585 757086222673454119885939)
                ·
                  refine ⟨1135629334010181179828909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 757086222673454119885939 1135629334010181179828909)
                  ·
                    refine ⟨425861000253817942435841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1135629334010181179828909 425861000253817942435841)
                    ·
                      rfl

theorem cell22_1244042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_1244042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244042 prefixEnd_1244042 := by exact prefixLift 1244042
  have htrace : WordTrace (prefixWord ++ tailWord_1244042) baseStart_1244042 baseEnd_1244042 := by
    simpa [prefixWord, tailWord_1244042, baseEnd_1244042] using wordTrace_append hprefix tailTrace_1244042
  have hstable : (prefixWord ++ tailWord_1244042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244042).length < 2 ^ (prefixWord ++ tailWord_1244042).sum := by decide
  have hdescent : baseEnd_1244042 < baseStart_1244042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244096 : List Nat := [2, 1, 1, 2, 3, 3, 2, 2, 2, 4]
def baseStart_1244096 : Nat := 118140960795 + 1244096 * 2 ^ 59
def prefixEnd_1244096 : Nat := 4983230072969 + 3 ^ 40 * 1244096 * 2
def baseEnd_1244096 : Nat := 425879485557379801585675

theorem tailTrace_1244096 : CollatzResearch.WordTrace tailWord_1244096 prefixEnd_1244096 425879485557379801585675 := by
  unfold tailWord_1244096
  simp only [CollatzResearch.WordTrace]
  refine ⟨22687954450430070762968071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30250605933906761017290761 22687954450430070762968071)
  ·
    refine ⟨34031931675645106144452107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22687954450430070762968071 34031931675645106144452107)
    ·
      refine ⟨51047897513467659216678161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34031931675645106144452107 51047897513467659216678161)
      ·
        refine ⟨38285923135100744412508621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51047897513467659216678161 38285923135100744412508621)
        ·
          refine ⟨14357221175662779154690733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38285923135100744412508621 14357221175662779154690733)
          ·
            refine ⟨5383957940873542183009025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14357221175662779154690733 5383957940873542183009025)
            ·
              refine ⟨4037968455655156637256769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5383957940873542183009025 4037968455655156637256769)
              ·
                refine ⟨3028476341741367477942577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4037968455655156637256769 3028476341741367477942577)
                ·
                  refine ⟨2271357256306025608456933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3028476341741367477942577 2271357256306025608456933)
                  ·
                    refine ⟨425879485557379801585675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2271357256306025608456933 425879485557379801585675)
                    ·
                      rfl

theorem cell22_1244096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 2, 4].length) (baseStart_1244096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244096 prefixEnd_1244096 := by exact prefixLift 1244096
  have htrace : WordTrace (prefixWord ++ tailWord_1244096) baseStart_1244096 baseEnd_1244096 := by
    simpa [prefixWord, tailWord_1244096, baseEnd_1244096] using wordTrace_append hprefix tailTrace_1244096
  have hstable : (prefixWord ++ tailWord_1244096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244096).length < 2 ^ (prefixWord ++ tailWord_1244096).sum := by decide
  have hdescent : baseEnd_1244096 < baseStart_1244096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244111 : List Nat := [1, 1, 2, 1, 1, 8, 1, 7]
def baseStart_1244111 : Nat := 118140960795 + 1244111 * 2 ^ 59
def prefixEnd_1244111 : Nat := 4983230072969 + 3 ^ 40 * 1244111 * 2
def baseEnd_1244111 : Nat := 47320513373769418051181

theorem tailTrace_1244111 : CollatzResearch.WordTrace tailWord_1244111 prefixEnd_1244111 47320513373769418051181 := by
  unfold tailWord_1244111
  simp only [CollatzResearch.WordTrace]
  refine ⟨45376455995805799087732187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30250970663870532725154791 45376455995805799087732187)
  ·
    refine ⟨68064683993708698631598281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45376455995805799087732187 68064683993708698631598281)
    ·
      refine ⟨51048512995281523973698711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68064683993708698631598281 51048512995281523973698711)
      ·
        refine ⟨76572769492922285960548067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51048512995281523973698711 76572769492922285960548067)
        ·
          refine ⟨114859154239383428940822101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76572769492922285960548067 114859154239383428940822101)
          ·
            refine ⟨1346005713742774557900259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 114859154239383428940822101 1346005713742774557900259)
            ·
              refine ⟨2019008570614161836850389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1346005713742774557900259 2019008570614161836850389)
              ·
                refine ⟨47320513373769418051181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2019008570614161836850389 47320513373769418051181)
                ·
                  rfl

theorem cell22_1244111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 7].length) (baseStart_1244111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244111 prefixEnd_1244111 := by exact prefixLift 1244111
  have htrace : WordTrace (prefixWord ++ tailWord_1244111) baseStart_1244111 baseEnd_1244111 := by
    simpa [prefixWord, tailWord_1244111, baseEnd_1244111] using wordTrace_append hprefix tailTrace_1244111
  have hstable : (prefixWord ++ tailWord_1244111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244111).length < 2 ^ (prefixWord ++ tailWord_1244111).sum := by decide
  have hdescent : baseEnd_1244111 < baseStart_1244111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244130 : List Nat := [3, 3, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1244130 : Nat := 118140960795 + 1244130 * 2 ^ 59
def prefixEnd_1244130 : Nat := 4983230072969 + 3 ^ 40 * 1244130 * 2
def baseEnd_1244130 : Nat := 425891124452215046235571

theorem tailTrace_1244130 : CollatzResearch.WordTrace tailWord_1244130 prefixEnd_1244130 425891124452215046235571 := by
  unfold tailWord_1244130
  simp only [CollatzResearch.WordTrace]
  refine ⟨11344287245684241333168461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30251432655157976888449229 11344287245684241333168461)
  ·
    refine ⟨4254107717131590499938173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11344287245684241333168461 4254107717131590499938173)
    ·
      refine ⟨1595290393924346437476815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4254107717131590499938173 1595290393924346437476815)
      ·
        refine ⟨2392935590886519656215223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1595290393924346437476815 2392935590886519656215223)
        ·
          refine ⟨3589403386329779484322835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2392935590886519656215223 3589403386329779484322835)
          ·
            refine ⟨5384105079494669226484253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3589403386329779484322835 5384105079494669226484253)
            ·
              refine ⟨2019039404810500959931595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5384105079494669226484253 2019039404810500959931595)
              ·
                refine ⟨3028559107215751439897393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2019039404810500959931595 3028559107215751439897393)
                ·
                  refine ⟨2271419330411813579923045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3028559107215751439897393 2271419330411813579923045)
                  ·
                    refine ⟨425891124452215046235571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2271419330411813579923045 425891124452215046235571)
                    ·
                      rfl

theorem cell22_1244130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1244130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244130 prefixEnd_1244130 := by exact prefixLift 1244130
  have htrace : WordTrace (prefixWord ++ tailWord_1244130) baseStart_1244130 baseEnd_1244130 := by
    simpa [prefixWord, tailWord_1244130, baseEnd_1244130] using wordTrace_append hprefix tailTrace_1244130
  have hstable : (prefixWord ++ tailWord_1244130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244130).length < 2 ^ (prefixWord ++ tailWord_1244130).sum := by decide
  have hdescent : baseEnd_1244130 < baseStart_1244130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244149 : List Nat := [1, 3, 5, 2, 1, 2, 1, 2, 2, 3]
def baseStart_1244149 : Nat := 118140960795 + 1244149 * 2 ^ 59
def prefixEnd_1244149 : Nat := 4983230072969 + 3 ^ 40 * 1244149 * 2
def baseEnd_1244149 : Nat := 425897628540505330010513

theorem tailTrace_1244149 : CollatzResearch.WordTrace tailWord_1244149 prefixEnd_1244149 425897628540505330010513 := by
  unfold tailWord_1244149
  simp only [CollatzResearch.WordTrace]
  refine ⟨45377841969668131577615501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30251894646445421051743667 45377841969668131577615501)
  ·
    refine ⟨17016690738625549341605813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45377841969668131577615501 17016690738625549341605813)
    ·
      refine ⟨1595314756746145250775545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17016690738625549341605813 1595314756746145250775545)
      ·
        refine ⟨1196486067559608938081659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1595314756746145250775545 1196486067559608938081659)
        ·
          refine ⟨1794729101339413407122489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1196486067559608938081659 1794729101339413407122489)
          ·
            refine ⟨1346046826004560055341867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1794729101339413407122489 1346046826004560055341867)
            ·
              refine ⟨2019070239006840083012801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1346046826004560055341867 2019070239006840083012801)
              ·
                refine ⟨1514302679255130062259601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2019070239006840083012801 1514302679255130062259601)
                ·
                  refine ⟨1135727009441347546694701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1514302679255130062259601 1135727009441347546694701)
                  ·
                    refine ⟨425897628540505330010513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1135727009441347546694701 425897628540505330010513)
                    ·
                      rfl

theorem cell22_1244149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_1244149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244149 prefixEnd_1244149 := by exact prefixLift 1244149
  have htrace : WordTrace (prefixWord ++ tailWord_1244149) baseStart_1244149 baseEnd_1244149 := by
    simpa [prefixWord, tailWord_1244149, baseEnd_1244149] using wordTrace_append hprefix tailTrace_1244149
  have hstable : (prefixWord ++ tailWord_1244149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244149).length < 2 ^ (prefixWord ++ tailWord_1244149).sum := by decide
  have hdescent : baseEnd_1244149 < baseStart_1244149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244156 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 7]
def baseStart_1244156 : Nat := 118140960795 + 1244156 * 2 ^ 59
def prefixEnd_1244156 : Nat := 4983230072969 + 3 ^ 40 * 1244156 * 2
def baseEnd_1244156 : Nat := 141966674927853215028497

theorem tailTrace_1244156 : CollatzResearch.WordTrace tailWord_1244156 prefixEnd_1244156 141966674927853215028497 := by
  unfold tailWord_1244156
  simp only [CollatzResearch.WordTrace]
  refine ⟨22689048640321385886560161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30252064853761847848746881 22689048640321385886560161)
  ·
    refine ⟨17016786480241039414920121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22689048640321385886560161 17016786480241039414920121)
    ·
      refine ⟨12762589860180779561190091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17016786480241039414920121 12762589860180779561190091)
      ·
        refine ⟨19143884790271169341785137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12762589860180779561190091 19143884790271169341785137)
        ·
          refine ⟨14357913592703377006338853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19143884790271169341785137 14357913592703377006338853)
          ·
            refine ⟨2692108798631883188688535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14357913592703377006338853 2692108798631883188688535)
            ·
              refine ⟨4038163197947824783032803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2692108798631883188688535 4038163197947824783032803)
              ·
                refine ⟨6057244796921737174549205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4038163197947824783032803 6057244796921737174549205)
                ·
                  refine ⟨141966674927853215028497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6057244796921737174549205 141966674927853215028497)
                  ·
                    rfl

theorem cell22_1244156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_1244156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244156 prefixEnd_1244156 := by exact prefixLift 1244156
  have htrace : WordTrace (prefixWord ++ tailWord_1244156) baseStart_1244156 baseEnd_1244156 := by
    simpa [prefixWord, tailWord_1244156, baseEnd_1244156] using wordTrace_append hprefix tailTrace_1244156
  have hstable : (prefixWord ++ tailWord_1244156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244156).length < 2 ^ (prefixWord ++ tailWord_1244156).sum := by decide
  have hdescent : baseEnd_1244156 < baseStart_1244156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244171 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 2, 5]
def baseStart_1244171 : Nat := 118140960795 + 1244171 * 2 ^ 59
def prefixEnd_1244171 : Nat := 4983230072969 + 3 ^ 40 * 1244171 * 2
def baseEnd_1244171 : Nat := 425905159590104605960445

theorem tailTrace_1244171 : CollatzResearch.WordTrace tailWord_1244171 prefixEnd_1244171 425905159590104605960445 := by
  unfold tailWord_1244171
  simp only [CollatzResearch.WordTrace]
  refine ⟨45378644375588429334916367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30252429583725619556610911 45378644375588429334916367)
  ·
    refine ⟨68067966563382644002374551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45378644375588429334916367 68067966563382644002374551)
    ·
      refine ⟨102101949845073966003561827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68067966563382644002374551 102101949845073966003561827)
      ·
        refine ⟨153152924767610949005342741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102101949845073966003561827 153152924767610949005342741)
        ·
          refine ⟨7179043348481763234625441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 153152924767610949005342741 7179043348481763234625441)
          ·
            refine ⟨5384282511361322425969081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7179043348481763234625441 5384282511361322425969081)
            ·
              refine ⟨4038211883520991819476811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5384282511361322425969081 4038211883520991819476811)
              ·
                refine ⟨6057317825281487729215217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4038211883520991819476811 6057317825281487729215217)
                ·
                  refine ⟨4542988368961115796911413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6057317825281487729215217 4542988368961115796911413)
                  ·
                    refine ⟨425905159590104605960445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4542988368961115796911413 425905159590104605960445)
                    ·
                      rfl

theorem cell22_1244171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 5].length) (baseStart_1244171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244171 prefixEnd_1244171 := by exact prefixLift 1244171
  have htrace : WordTrace (prefixWord ++ tailWord_1244171) baseStart_1244171 baseEnd_1244171 := by
    simpa [prefixWord, tailWord_1244171, baseEnd_1244171] using wordTrace_append hprefix tailTrace_1244171
  have hstable : (prefixWord ++ tailWord_1244171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244171).length < 2 ^ (prefixWord ++ tailWord_1244171).sum := by decide
  have hdescent : baseEnd_1244171 < baseStart_1244171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244218 : List Nat := [3, 1, 1, 1, 3, 1, 2, 6, 4]
def baseStart_1244218 : Nat := 118140960795 + 1244218 * 2 ^ 59
def prefixEnd_1244218 : Nat := 4983230072969 + 3 ^ 40 * 1244218 * 2
def baseEnd_1244218 : Nat := 141973749550204050011767

theorem tailTrace_1244218 : CollatzResearch.WordTrace tailWord_1244218 prefixEnd_1244218 141973749550204050011767 := by
  unfold tailWord_1244218
  simp only [CollatzResearch.WordTrace]
  refine ⟨11345089651604539090469327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30253572404278770907918205 11345089651604539090469327)
  ·
    refine ⟨17017634477406808635703991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11345089651604539090469327 17017634477406808635703991)
    ·
      refine ⟨25526451716110212953555987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17017634477406808635703991 25526451716110212953555987)
      ·
        refine ⟨38289677574165319430333981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25526451716110212953555987 38289677574165319430333981)
        ·
          refine ⟨14358629090311994786375243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38289677574165319430333981 14358629090311994786375243)
          ·
            refine ⟨21537943635467992179562865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14358629090311994786375243 21537943635467992179562865)
            ·
              refine ⟨16153457726600994134672149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21537943635467992179562865 16153457726600994134672149)
              ·
                refine ⟨757193330934421600062757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16153457726600994134672149 757193330934421600062757)
                ·
                  refine ⟨141973749550204050011767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 757193330934421600062757 141973749550204050011767)
                  ·
                    rfl

theorem cell22_1244218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 4].length) (baseStart_1244218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244218 prefixEnd_1244218 := by exact prefixLift 1244218
  have htrace : WordTrace (prefixWord ++ tailWord_1244218) baseStart_1244218 baseEnd_1244218 := by
    simpa [prefixWord, tailWord_1244218, baseEnd_1244218] using wordTrace_append hprefix tailTrace_1244218
  have hstable : (prefixWord ++ tailWord_1244218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244218).length < 2 ^ (prefixWord ++ tailWord_1244218).sum := by decide
  have hdescent : baseEnd_1244218 < baseStart_1244218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244237 : List Nat := [1, 6, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_1244237 : Nat := 118140960795 + 1244237 * 2 ^ 59
def prefixEnd_1244237 : Nat := 4983230072969 + 3 ^ 40 * 1244237 * 2
def baseEnd_1244237 : Nat := 425927752738902433810243

theorem tailTrace_1244237 : CollatzResearch.WordTrace tailWord_1244237 prefixEnd_1244237 425927752738902433810243 := by
  unfold tailWord_1244237
  simp only [CollatzResearch.WordTrace]
  refine ⟨45381051593349322606818965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30254034395566215071212643 45381051593349322606818965)
  ·
    refine ⟨2127236793438249497194639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45381051593349322606818965 2127236793438249497194639)
    ·
      refine ⟨3190855190157374245791959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2127236793438249497194639 3190855190157374245791959)
      ·
        refine ⟨4786282785236061368687939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3190855190157374245791959 4786282785236061368687939)
        ·
          refine ⟨7179424177854092053031909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4786282785236061368687939 7179424177854092053031909)
          ·
            refine ⟨1346142033347642259943483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7179424177854092053031909 1346142033347642259943483)
            ·
              refine ⟨2019213050021463389915225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1346142033347642259943483 2019213050021463389915225)
              ·
                refine ⟨1514409787516097542436419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2019213050021463389915225 1514409787516097542436419)
                ·
                  refine ⟨2271614681274146313654629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1514409787516097542436419 2271614681274146313654629)
                  ·
                    refine ⟨425927752738902433810243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2271614681274146313654629 425927752738902433810243)
                    ·
                      rfl

theorem cell22_1244237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_1244237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244237 prefixEnd_1244237 := by exact prefixLift 1244237
  have htrace : WordTrace (prefixWord ++ tailWord_1244237) baseStart_1244237 baseEnd_1244237 := by
    simpa [prefixWord, tailWord_1244237, baseEnd_1244237] using wordTrace_append hprefix tailTrace_1244237
  have hstable : (prefixWord ++ tailWord_1244237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244237).length < 2 ^ (prefixWord ++ tailWord_1244237).sum := by decide
  have hdescent : baseEnd_1244237 < baseStart_1244237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244248 : List Nat := [2, 1, 2, 2, 1, 3, 4, 1, 2, 4]
def baseStart_1244248 : Nat := 118140960795 + 1244248 * 2 ^ 59
def prefixEnd_1244248 : Nat := 4983230072969 + 3 ^ 40 * 1244248 * 2
def baseEnd_1244248 : Nat := 425931518263702071785209

theorem tailTrace_1244248 : CollatzResearch.WordTrace tailWord_1244248 prefixEnd_1244248 425931518263702071785209 := by
  unfold tailWord_1244248
  simp only [CollatzResearch.WordTrace]
  refine ⟨22690726398154735742734699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30254301864206314323646265 22690726398154735742734699)
  ·
    refine ⟨34036089597232103614102049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22690726398154735742734699 34036089597232103614102049)
    ·
      refine ⟨25527067197924077710576537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34036089597232103614102049 25527067197924077710576537)
      ·
        refine ⟨19145300398443058282932403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25527067197924077710576537 19145300398443058282932403)
        ·
          refine ⟨28717950597664587424398605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19145300398443058282932403 28717950597664587424398605)
          ·
            refine ⟨10769231474124220284149477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28717950597664587424398605 10769231474124220284149477)
            ·
              refine ⟨2019230901398291303278027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10769231474124220284149477 2019230901398291303278027)
              ·
                refine ⟨3028846352097436954917041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2019230901398291303278027 3028846352097436954917041)
                ·
                  refine ⟨2271634764073077716187781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3028846352097436954917041 2271634764073077716187781)
                  ·
                    refine ⟨425931518263702071785209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2271634764073077716187781 425931518263702071785209)
                    ·
                      rfl

theorem cell22_1244248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_1244248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244248 prefixEnd_1244248 := by exact prefixLift 1244248
  have htrace : WordTrace (prefixWord ++ tailWord_1244248) baseStart_1244248 baseEnd_1244248 := by
    simpa [prefixWord, tailWord_1244248, baseEnd_1244248] using wordTrace_append hprefix tailTrace_1244248
  have hstable : (prefixWord ++ tailWord_1244248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244248).length < 2 ^ (prefixWord ++ tailWord_1244248).sum := by decide
  have hdescent : baseEnd_1244248 < baseStart_1244248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244312 : List Nat := [2, 1, 2, 4, 2, 1, 1, 5, 1, 3]
def baseStart_1244312 : Nat := 118140960795 + 1244312 * 2 ^ 59
def prefixEnd_1244312 : Nat := 4983230072969 + 3 ^ 40 * 1244312 * 2
def baseEnd_1244312 : Nat := 425953426771627238185013

theorem tailTrace_1244312 : CollatzResearch.WordTrace tailWord_1244312 prefixEnd_1244312 425953426771627238185013 := by
  unfold tailWord_1244312
  simp only [CollatzResearch.WordTrace]
  refine ⟨22691893534038805207899595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30255858045385073610532793 22691893534038805207899595)
  ·
    refine ⟨34037840301058207811849393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22691893534038805207899595 34037840301058207811849393)
    ·
      refine ⟨25528380225793655858887045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34037840301058207811849393 25528380225793655858887045)
      ·
        refine ⟨4786571292336310473541321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25528380225793655858887045 4786571292336310473541321)
        ·
          refine ⟨3589928469252232855155991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4786571292336310473541321 3589928469252232855155991)
          ·
            refine ⟨5384892703878349282733987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3589928469252232855155991 5384892703878349282733987)
            ·
              refine ⟨8077339055817523924100981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5384892703878349282733987 8077339055817523924100981)
              ·
                refine ⟨757250536482892867884467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8077339055817523924100981 757250536482892867884467)
                ·
                  refine ⟨1135875804724339301826701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 757250536482892867884467 1135875804724339301826701)
                  ·
                    refine ⟨425953426771627238185013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1135875804724339301826701 425953426771627238185013)
                    ·
                      rfl

theorem cell22_1244312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 1, 3].length) (baseStart_1244312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244312 prefixEnd_1244312 := by exact prefixLift 1244312
  have htrace : WordTrace (prefixWord ++ tailWord_1244312) baseStart_1244312 baseEnd_1244312 := by
    simpa [prefixWord, tailWord_1244312, baseEnd_1244312] using wordTrace_append hprefix tailTrace_1244312
  have hstable : (prefixWord ++ tailWord_1244312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244312).length < 2 ^ (prefixWord ++ tailWord_1244312).sum := by decide
  have hdescent : baseEnd_1244312 < baseStart_1244312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244325 : List Nat := [1, 3, 1, 2, 1, 6, 1, 2, 5]
def baseStart_1244325 : Nat := 118140960795 + 1244325 * 2 ^ 59
def prefixEnd_1244325 : Nat := 4983230072969 + 3 ^ 40 * 1244325 * 2
def baseEnd_1244325 : Nat := 141985958979099845869991

theorem tailTrace_1244325 : CollatzResearch.WordTrace tailWord_1244325 prefixEnd_1244325 141985958979099845869991 := by
  unfold tailWord_1244325
  simp only [CollatzResearch.WordTrace]
  refine ⟨45384261217030513636022429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30256174144687009090681619 45384261217030513636022429)
  ·
    refine ⟨17019097956386442613508411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45384261217030513636022429 17019097956386442613508411)
    ·
      refine ⟨25528646934579663920262617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17019097956386442613508411 25528646934579663920262617)
      ·
        refine ⟨19146485200934747940196963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25528646934579663920262617 19146485200934747940196963)
        ·
          refine ⟨28719727801402121910295445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19146485200934747940196963 28719727801402121910295445)
          ·
            refine ⟨1346237240690724464545099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28719727801402121910295445 1346237240690724464545099)
            ·
              refine ⟨2019355861036086696817649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1346237240690724464545099 2019355861036086696817649)
              ·
                refine ⟨1514516895777065022613237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2019355861036086696817649 1514516895777065022613237)
                ·
                  refine ⟨141985958979099845869991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1514516895777065022613237 141985958979099845869991)
                  ·
                    rfl

theorem cell22_1244325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_1244325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244325 prefixEnd_1244325 := by exact prefixLift 1244325
  have htrace : WordTrace (prefixWord ++ tailWord_1244325) baseStart_1244325 baseEnd_1244325 := by
    simpa [prefixWord, tailWord_1244325, baseEnd_1244325] using wordTrace_append hprefix tailTrace_1244325
  have hstable : (prefixWord ++ tailWord_1244325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244325).length < 2 ^ (prefixWord ++ tailWord_1244325).sum := by decide
  have hdescent : baseEnd_1244325 < baseStart_1244325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244336 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 10]
def baseStart_1244336 : Nat := 118140960795 + 1244336 * 2 ^ 59
def prefixEnd_1244336 : Nat := 4983230072969 + 3 ^ 40 * 1244336 * 2
def baseEnd_1244336 : Nat := 141987214154033058528313

theorem tailTrace_1244336 : CollatzResearch.WordTrace tailWord_1244336 prefixEnd_1244336 141987214154033058528313 := by
  unfold tailWord_1244336
  simp only [CollatzResearch.WordTrace]
  refine ⟨22692331209995331257336431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30256441613327108343115241 22692331209995331257336431)
  ·
    refine ⟨34038496814992996886004647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22692331209995331257336431 34038496814992996886004647)
    ·
      refine ⟨51057745222489495329006971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34038496814992996886004647 51057745222489495329006971)
      ·
        refine ⟨76586617833734242993510457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51057745222489495329006971 76586617833734242993510457)
        ·
          refine ⟨57439963375300682245132843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76586617833734242993510457 57439963375300682245132843)
          ·
            refine ⟨86159945062951023367699265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57439963375300682245132843 86159945062951023367699265)
            ·
              refine ⟨64619958797213267525774449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86159945062951023367699265 64619958797213267525774449)
              ·
                refine ⟨48464969097909950644330837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64619958797213267525774449 48464969097909950644330837)
                ·
                  refine ⟨141987214154033058528313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 48464969097909950644330837 141987214154033058528313)
                  ·
                    rfl

theorem cell22_1244336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 10].length) (baseStart_1244336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244336 prefixEnd_1244336 := by exact prefixLift 1244336
  have htrace : WordTrace (prefixWord ++ tailWord_1244336) baseStart_1244336 baseEnd_1244336 := by
    simpa [prefixWord, tailWord_1244336, baseEnd_1244336] using wordTrace_append hprefix tailTrace_1244336
  have hstable : (prefixWord ++ tailWord_1244336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244336).length < 2 ^ (prefixWord ++ tailWord_1244336).sum := by decide
  have hdescent : baseEnd_1244336 < baseStart_1244336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244383 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 4, 4]
def baseStart_1244383 : Nat := 118140960795 + 1244383 * 2 ^ 59
def prefixEnd_1244383 : Nat := 4983230072969 + 3 ^ 40 * 1244383 * 2
def baseEnd_1244383 : Nat := 425977731522606719659795

theorem tailTrace_1244383 : CollatzResearch.WordTrace tailWord_1244383 prefixEnd_1244383 425977731522606719659795 := by
  unfold tailWord_1244383
  simp only [CollatzResearch.WordTrace]
  refine ⟨45386376650820389541633803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30257584433880259694422535 45386376650820389541633803)
  ·
    refine ⟨68079564976230584312450705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45386376650820389541633803 68079564976230584312450705)
    ·
      refine ⟨51059673732172938234338029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68079564976230584312450705 51059673732172938234338029)
      ·
        refine ⟨19147377649564851837876761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51059673732172938234338029 19147377649564851837876761)
        ·
          refine ⟨14360533237173638878407571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19147377649564851837876761 14360533237173638878407571)
          ·
            refine ⟨21540799855760458317611357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14360533237173638878407571 21540799855760458317611357)
            ·
              refine ⟨8077799945910171869104259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21540799855760458317611357 8077799945910171869104259)
              ·
                refine ⟨12116699918865257803656389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8077799945910171869104259 12116699918865257803656389)
                ·
                  refine ⟨2271881234787235838185573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12116699918865257803656389 2271881234787235838185573)
                  ·
                    refine ⟨425977731522606719659795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2271881234787235838185573 425977731522606719659795)
                    ·
                      rfl

theorem cell22_1244383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 4].length) (baseStart_1244383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244383 prefixEnd_1244383 := by exact prefixLift 1244383
  have htrace : WordTrace (prefixWord ++ tailWord_1244383) baseStart_1244383 baseEnd_1244383 := by
    simpa [prefixWord, tailWord_1244383, baseEnd_1244383] using wordTrace_append hprefix tailTrace_1244383
  have hstable : (prefixWord ++ tailWord_1244383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244383).length < 2 ^ (prefixWord ++ tailWord_1244383).sum := by decide
  have hdescent : baseEnd_1244383 < baseStart_1244383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244385 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 4, 3]
def baseStart_1244385 : Nat := 118140960795 + 1244385 * 2 ^ 59
def prefixEnd_1244385 : Nat := 4983230072969 + 3 ^ 40 * 1244385 * 2
def baseEnd_1244385 : Nat := 425978416163479381109789

theorem tailTrace_1244385 : CollatzResearch.WordTrace tailWord_1244385 prefixEnd_1244385 425978416163479381109789 := by
  unfold tailWord_1244385
  simp only [CollatzResearch.WordTrace]
  refine ⟨45386449596813143883206609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30257633064542095922137739 45386449596813143883206609)
  ·
    refine ⟨34039837197609857912404957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45386449596813143883206609 34039837197609857912404957)
    ·
      refine ⟨12764938949103696717151859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34039837197609857912404957 12764938949103696717151859)
      ·
        refine ⟨19147408423655545075727789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12764938949103696717151859 19147408423655545075727789)
        ·
          refine ⟨7180278158870829403397921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19147408423655545075727789 7180278158870829403397921)
          ·
            refine ⟨5385208619153122052548441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7180278158870829403397921 5385208619153122052548441)
            ·
              refine ⟨4038906464364841539411331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5385208619153122052548441 4038906464364841539411331)
              ·
                refine ⟨6058359696547262309116997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4038906464364841539411331 6058359696547262309116997)
                ·
                  refine ⟨1135942443102611682959437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6058359696547262309116997 1135942443102611682959437)
                  ·
                    refine ⟨425978416163479381109789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1135942443102611682959437 425978416163479381109789)
                    ·
                      rfl

theorem cell22_1244385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_1244385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244385 prefixEnd_1244385 := by exact prefixLift 1244385
  have htrace : WordTrace (prefixWord ++ tailWord_1244385) baseStart_1244385 baseEnd_1244385 := by
    simpa [prefixWord, tailWord_1244385, baseEnd_1244385] using wordTrace_append hprefix tailTrace_1244385
  have hstable : (prefixWord ++ tailWord_1244385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244385).length < 2 ^ (prefixWord ++ tailWord_1244385).sum := by decide
  have hdescent : baseEnd_1244385 < baseStart_1244385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244398 : List Nat := [4, 1, 2, 1, 1, 1, 3, 9]
def baseStart_1244398 : Nat := 118140960795 + 1244398 * 2 ^ 59
def prefixEnd_1244398 : Nat := 4983230072969 + 3 ^ 40 * 1244398 * 2
def baseEnd_1244398 : Nat := 47331429592127964503861

theorem tailTrace_1244398 : CollatzResearch.WordTrace tailWord_1244398 prefixEnd_1244398 47331429592127964503861 := by
  unfold tailWord_1244398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5673365468220755887928731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30257949163844031402286565 5673365468220755887928731)
  ·
    refine ⟨8510048202331133831893097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5673365468220755887928731 8510048202331133831893097)
    ·
      refine ⟨6382536151748350373919823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8510048202331133831893097 6382536151748350373919823)
      ·
        refine ⟨9573804227622525560879735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6382536151748350373919823 9573804227622525560879735)
        ·
          refine ⟨14360706341433788341319603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9573804227622525560879735 14360706341433788341319603)
          ·
            refine ⟨21541059512150682511979405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14360706341433788341319603 21541059512150682511979405)
            ·
              refine ⟨8077897317056505941992277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21541059512150682511979405 8077897317056505941992277)
              ·
                refine ⟨47331429592127964503861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8077897317056505941992277 47331429592127964503861)
                ·
                  rfl

theorem cell22_1244398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_1244398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244398 prefixEnd_1244398 := by exact prefixLift 1244398
  have htrace : WordTrace (prefixWord ++ tailWord_1244398) baseStart_1244398 baseEnd_1244398 := by
    simpa [prefixWord, tailWord_1244398, baseEnd_1244398] using wordTrace_append hprefix tailTrace_1244398
  have hstable : (prefixWord ++ tailWord_1244398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244398).length < 2 ^ (prefixWord ++ tailWord_1244398).sum := by decide
  have hdescent : baseEnd_1244398 < baseStart_1244398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244445 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_1244445 : Nat := 118140960795 + 1244445 * 2 ^ 59
def prefixEnd_1244445 : Nat := 4983230072969 + 3 ^ 40 * 1244445 * 2
def baseEnd_1244445 : Nat := 425998955389659224609605

theorem tailTrace_1244445 : CollatzResearch.WordTrace tailWord_1244445 prefixEnd_1244445 425998955389659224609605 := by
  unfold tailWord_1244445
  simp only [CollatzResearch.WordTrace]
  refine ⟨45388637976595774130390789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30259091984397182753593859 45388637976595774130390789)
  ·
    refine ⟨8510369620611707649448273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45388637976595774130390789 8510369620611707649448273)
    ·
      refine ⟨6382777215458780737086205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8510369620611707649448273 6382777215458780737086205)
      ·
        refine ⟨2393541455797042776407327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6382777215458780737086205 2393541455797042776407327)
        ·
          refine ⟨3590312183695564164610991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2393541455797042776407327 3590312183695564164610991)
          ·
            refine ⟨5385468275543346246916487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3590312183695564164610991 5385468275543346246916487)
            ·
              refine ⟨8078202413315019370374731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5385468275543346246916487 8078202413315019370374731)
              ·
                refine ⟨12117303619972529055562097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8078202413315019370374731 12117303619972529055562097)
                ·
                  refine ⟨9087977714979396791671573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12117303619972529055562097 9087977714979396791671573)
                  ·
                    refine ⟨425998955389659224609605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9087977714979396791671573 425998955389659224609605)
                    ·
                      rfl

theorem cell22_1244445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_1244445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244445 prefixEnd_1244445 := by exact prefixLift 1244445
  have htrace : WordTrace (prefixWord ++ tailWord_1244445) baseStart_1244445 baseEnd_1244445 := by
    simpa [prefixWord, tailWord_1244445, baseEnd_1244445] using wordTrace_append hprefix tailTrace_1244445
  have hstable : (prefixWord ++ tailWord_1244445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244445).length < 2 ^ (prefixWord ++ tailWord_1244445).sum := by decide
  have hdescent : baseEnd_1244445 < baseStart_1244445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244481 : List Nat := [1, 2, 5, 2, 1, 2, 2, 3, 1, 3]
def baseStart_1244481 : Nat := 118140960795 + 1244481 * 2 ^ 59
def prefixEnd_1244481 : Nat := 4983230072969 + 3 ^ 40 * 1244481 * 2
def baseEnd_1244481 : Nat := 426011278925367130709495

theorem tailTrace_1244481 : CollatzResearch.WordTrace tailWord_1244481 prefixEnd_1244481 426011278925367130709495 := by
  unfold tailWord_1244481
  simp only [CollatzResearch.WordTrace]
  refine ⟨45389951004465352278701297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30259967336310234852467531 45389951004465352278701297)
  ·
    refine ⟨34042463253349014209025973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45389951004465352278701297 34042463253349014209025973)
    ·
      refine ⟨3191480930001470082096185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34042463253349014209025973 3191480930001470082096185)
      ·
        refine ⟨2393610697501102561572139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3191480930001470082096185 2393610697501102561572139)
        ·
          refine ⟨3590416046251653842358209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2393610697501102561572139 3590416046251653842358209)
          ·
            refine ⟨2692812034688740381768657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3590416046251653842358209 2692812034688740381768657)
            ·
              refine ⟨2019609026016555286326493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2692812034688740381768657 2019609026016555286326493)
              ·
                refine ⟨757353384756208232372435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2019609026016555286326493 757353384756208232372435)
                ·
                  refine ⟨1136030077134312348558653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 757353384756208232372435 1136030077134312348558653)
                  ·
                    refine ⟨426011278925367130709495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1136030077134312348558653 426011278925367130709495)
                    ·
                      rfl

theorem cell22_1244481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_1244481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244481 prefixEnd_1244481 := by exact prefixLift 1244481
  have htrace : WordTrace (prefixWord ++ tailWord_1244481) baseStart_1244481 baseEnd_1244481 := by
    simpa [prefixWord, tailWord_1244481, baseEnd_1244481] using wordTrace_append hprefix tailTrace_1244481
  have hstable : (prefixWord ++ tailWord_1244481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244481).length < 2 ^ (prefixWord ++ tailWord_1244481).sum := by decide
  have hdescent : baseEnd_1244481 < baseStart_1244481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244488 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 10]
def baseStart_1244488 : Nat := 118140960795 + 1244488 * 2 ^ 59
def prefixEnd_1244488 : Nat := 4983230072969 + 3 ^ 40 * 1244488 * 2
def baseEnd_1244488 : Nat := 142004558389473815261491

theorem tailTrace_1244488 : CollatzResearch.WordTrace tailWord_1244488 prefixEnd_1244488 142004558389473815261491 := by
  unfold tailWord_1244488
  simp only [CollatzResearch.WordTrace]
  refine ⟨22695103157719996237103059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30260137543626661649470745 22695103157719996237103059)
  ·
    refine ⟨34042654736579994355654589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22695103157719996237103059 34042654736579994355654589)
    ·
      refine ⟨12765995526217497883370471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34042654736579994355654589 12765995526217497883370471)
      ·
        refine ⟨19148993289326246825055707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12765995526217497883370471 19148993289326246825055707)
        ·
          refine ⟨28723489933989370237583561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19148993289326246825055707 28723489933989370237583561)
          ·
            refine ⟨21542617450492027678187671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28723489933989370237583561 21542617450492027678187671)
            ·
              refine ⟨32313926175738041517281507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21542617450492027678187671 32313926175738041517281507)
              ·
                refine ⟨48470889263607062275922261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32313926175738041517281507 48470889263607062275922261)
                ·
                  refine ⟨142004558389473815261491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 48470889263607062275922261 142004558389473815261491)
                  ·
                    rfl

theorem cell22_1244488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 10].length) (baseStart_1244488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244488 prefixEnd_1244488 := by exact prefixLift 1244488
  have htrace : WordTrace (prefixWord ++ tailWord_1244488) baseStart_1244488 baseEnd_1244488 := by
    simpa [prefixWord, tailWord_1244488, baseEnd_1244488] using wordTrace_append hprefix tailTrace_1244488
  have hstable : (prefixWord ++ tailWord_1244488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244488).length < 2 ^ (prefixWord ++ tailWord_1244488).sum := by decide
  have hdescent : baseEnd_1244488 < baseStart_1244488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244535 : List Nat := [1, 1, 3, 1, 1, 2, 4, 3, 2, 4]
def baseStart_1244535 : Nat := 118140960795 + 1244535 * 2 ^ 59
def prefixEnd_1244535 : Nat := 4983230072969 + 3 ^ 40 * 1244535 * 2
def baseEnd_1244535 : Nat := 426029764228928989859329

theorem tailTrace_1244535 : CollatzResearch.WordTrace tailWord_1244535 prefixEnd_1244535 426029764228928989859329 := by
  unfold tailWord_1244535
  simp only [CollatzResearch.WordTrace]
  refine ⟨45391920546269719501167059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30261280364179813000778039 45391920546269719501167059)
  ·
    refine ⟨68087880819404579251750589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45391920546269719501167059 68087880819404579251750589)
    ·
      refine ⟨25532955307276717219406471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68087880819404579251750589 25532955307276717219406471)
      ·
        refine ⟨38299432960915075829109707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25532955307276717219406471 38299432960915075829109707)
        ·
          refine ⟨57449149441372613743664561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38299432960915075829109707 57449149441372613743664561)
          ·
            refine ⟨43086862081029460307748421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57449149441372613743664561 43086862081029460307748421)
            ·
              refine ⟨8078786640193023807702829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43086862081029460307748421 8078786640193023807702829)
              ·
                refine ⟨3029544990072383927888561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8078786640193023807702829 3029544990072383927888561)
                ·
                  refine ⟨2272158742554287945916421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3029544990072383927888561 2272158742554287945916421)
                  ·
                    refine ⟨426029764228928989859329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2272158742554287945916421 426029764228928989859329)
                    ·
                      rfl

theorem cell22_1244535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_1244535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244535 prefixEnd_1244535 := by exact prefixLift 1244535
  have htrace : WordTrace (prefixWord ++ tailWord_1244535) baseStart_1244535 baseEnd_1244535 := by
    simpa [prefixWord, tailWord_1244535, baseEnd_1244535] using wordTrace_append hprefix tailTrace_1244535
  have hstable : (prefixWord ++ tailWord_1244535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244535).length < 2 ^ (prefixWord ++ tailWord_1244535).sum := by decide
  have hdescent : baseEnd_1244535 < baseStart_1244535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244552 : List Nat := [2, 1, 3, 3, 1, 3, 1, 2, 2, 4]
def baseStart_1244552 : Nat := 118140960795 + 1244552 * 2 ^ 59
def prefixEnd_1244552 : Nat := 4983230072969 + 3 ^ 40 * 1244552 * 2
def baseEnd_1244552 : Nat := 426035583676346612184277

theorem tailTrace_1244552 : CollatzResearch.WordTrace tailWord_1244552 prefixEnd_1244552 426035583676346612184277 := by
  unfold tailWord_1244552
  simp only [CollatzResearch.WordTrace]
  refine ⟨22696270293604065702267955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30261693724805420936357273 22696270293604065702267955)
  ·
    refine ⟨34044405440406098553401933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22696270293604065702267955 34044405440406098553401933)
    ·
      refine ⟨12766652040152286957525725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34044405440406098553401933 12766652040152286957525725)
      ·
        refine ⟨4787494515057107609072147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12766652040152286957525725 4787494515057107609072147)
        ·
          refine ⟨7181241772585661413608221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4787494515057107609072147 7181241772585661413608221)
          ·
            refine ⟨2692965664719623030103083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7181241772585661413608221 2692965664719623030103083)
            ·
              refine ⟨4039448497079434545154625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2692965664719623030103083 4039448497079434545154625)
              ·
                refine ⟨3029586372809575908865969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4039448497079434545154625 3029586372809575908865969)
                ·
                  refine ⟨2272189779607181931649477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3029586372809575908865969 2272189779607181931649477)
                  ·
                    refine ⟨426035583676346612184277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2272189779607181931649477 426035583676346612184277)
                    ·
                      rfl

theorem cell22_1244552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_1244552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244552 prefixEnd_1244552 := by exact prefixLift 1244552
  have htrace : WordTrace (prefixWord ++ tailWord_1244552) baseStart_1244552 baseEnd_1244552 := by
    simpa [prefixWord, tailWord_1244552, baseEnd_1244552] using wordTrace_append hprefix tailTrace_1244552
  have hstable : (prefixWord ++ tailWord_1244552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244552).length < 2 ^ (prefixWord ++ tailWord_1244552).sum := by decide
  have hdescent : baseEnd_1244552 < baseStart_1244552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244599 : List Nat := [1, 1, 3, 1, 3, 2, 2, 5, 1, 3]
def baseStart_1244599 : Nat := 118140960795 + 1244599 * 2 ^ 59
def prefixEnd_1244599 : Nat := 4983230072969 + 3 ^ 40 * 1244599 * 2
def baseEnd_1244599 : Nat := 426051672736854156259133

theorem tailTrace_1244599 : CollatzResearch.WordTrace tailWord_1244599 prefixEnd_1244599 426051672736854156259133 := by
  unfold tailWord_1244599
  simp only [CollatzResearch.WordTrace]
  refine ⟨45394254818037858431496851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30262836545358572287664567 45394254818037858431496851)
  ·
    refine ⟨68091382227056787647245277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45394254818037858431496851 68091382227056787647245277)
    ·
      refine ⟨25534268335146295367716979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68091382227056787647245277 25534268335146295367716979)
      ·
        refine ⟨38301402502719443051575469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25534268335146295367716979 38301402502719443051575469)
        ·
          refine ⟨14363025938519791144340801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38301402502719443051575469 14363025938519791144340801)
          ·
            refine ⟨10772269453889843358255601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14363025938519791144340801 10772269453889843358255601)
            ·
              refine ⟨8079202090417382518691701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10772269453889843358255601 8079202090417382518691701)
              ·
                refine ⟨757425195976629611127347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8079202090417382518691701 757425195976629611127347)
                ·
                  refine ⟨1136137793964944416691021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 757425195976629611127347 1136137793964944416691021)
                  ·
                    refine ⟨426051672736854156259133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1136137793964944416691021 426051672736854156259133)
                    ·
                      rfl

theorem cell22_1244599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 1, 3].length) (baseStart_1244599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244599 prefixEnd_1244599 := by exact prefixLift 1244599
  have htrace : WordTrace (prefixWord ++ tailWord_1244599) baseStart_1244599 baseEnd_1244599 := by
    simpa [prefixWord, tailWord_1244599, baseEnd_1244599] using wordTrace_append hprefix tailTrace_1244599
  have hstable : (prefixWord ++ tailWord_1244599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244599).length < 2 ^ (prefixWord ++ tailWord_1244599).sum := by decide
  have hdescent : baseEnd_1244599 < baseStart_1244599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244674 : List Nat := [3, 4, 1, 2, 1, 1, 1, 3, 6]
def baseStart_1244674 : Nat := 118140960795 + 1244674 * 2 ^ 59
def prefixEnd_1244674 : Nat := 4983230072969 + 3 ^ 40 * 1244674 * 2
def baseEnd_1244674 : Nat := 142025782256526320211301

theorem tailTrace_1244674 : CollatzResearch.WordTrace tailWord_1244674 prefixEnd_1244674 142025782256526320211301 := by
  unfold tailWord_1244674
  simp only [CollatzResearch.WordTrace]
  refine ⟨11349247573191536560119269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30264660195177430826984717 11349247573191536560119269)
  ·
    refine ⟨2127983919973413105022363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11349247573191536560119269 2127983919973413105022363)
    ·
      refine ⟨3191975879960119657533545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2127983919973413105022363 3191975879960119657533545)
      ·
        refine ⟨2393981909970089743150159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3191975879960119657533545 2393981909970089743150159)
        ·
          refine ⟨3590972864955134614725239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2393981909970089743150159 3590972864955134614725239)
          ·
            refine ⟨5386459297432701922087859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3590972864955134614725239 5386459297432701922087859)
            ·
              refine ⟨8079688946149052883131789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5386459297432701922087859 8079688946149052883131789)
              ·
                refine ⟨3029883354805894831174421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8079688946149052883131789 3029883354805894831174421)
                ·
                  refine ⟨142025782256526320211301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3029883354805894831174421 142025782256526320211301)
                  ·
                    rfl

theorem cell22_1244674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_1244674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244674 prefixEnd_1244674 := by exact prefixLift 1244674
  have htrace : WordTrace (prefixWord ++ tailWord_1244674) baseStart_1244674 baseEnd_1244674 := by
    simpa [prefixWord, tailWord_1244674, baseEnd_1244674] using wordTrace_append hprefix tailTrace_1244674
  have hstable : (prefixWord ++ tailWord_1244674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244674).length < 2 ^ (prefixWord ++ tailWord_1244674).sum := by decide
  have hdescent : baseEnd_1244674 < baseStart_1244674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244715 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 3, 8]
def baseStart_1244715 : Nat := 118140960795 + 1244715 * 2 ^ 59
def prefixEnd_1244715 : Nat := 4983230072969 + 3 ^ 40 * 1244715 * 2
def baseEnd_1244715 : Nat := 426091381907468520358777

theorem tailTrace_1244715 : CollatzResearch.WordTrace tailWord_1244715 prefixEnd_1244715 426091381907468520358777 := by
  unfold tailWord_1244715
  simp only [CollatzResearch.WordTrace]
  refine ⟨45398485685617610242719599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30265657123745073495146399 45398485685617610242719599)
  ·
    refine ⟨68097728528426415364079399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45398485685617610242719599 68097728528426415364079399)
    ·
      refine ⟨102146592792639623046119099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68097728528426415364079399 102146592792639623046119099)
      ·
        refine ⟨153219889188959434569178649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102146592792639623046119099 153219889188959434569178649)
        ·
          refine ⟨114914916891719575926883987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153219889188959434569178649 114914916891719575926883987)
          ·
            refine ⟨172372375337579363890325981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114914916891719575926883987 172372375337579363890325981)
            ·
              refine ⟨64639640751592261458872243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172372375337579363890325981 64639640751592261458872243)
              ·
                refine ⟨96959461127388392188308365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64639640751592261458872243 96959461127388392188308365)
                ·
                  refine ⟨36359797922770647070615637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96959461127388392188308365 36359797922770647070615637)
                  ·
                    refine ⟨426091381907468520358777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36359797922770647070615637 426091381907468520358777)
                    ·
                      rfl

theorem cell22_1244715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 8].length) (baseStart_1244715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244715 prefixEnd_1244715 := by exact prefixLift 1244715
  have htrace : WordTrace (prefixWord ++ tailWord_1244715) baseStart_1244715 baseEnd_1244715 := by
    simpa [prefixWord, tailWord_1244715, baseEnd_1244715] using wordTrace_append hprefix tailTrace_1244715
  have hstable : (prefixWord ++ tailWord_1244715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244715).length < 2 ^ (prefixWord ++ tailWord_1244715).sum := by decide
  have hdescent : baseEnd_1244715 < baseStart_1244715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244781 : List Nat := [1, 5, 1, 1, 4, 1, 2, 2, 5]
def baseStart_1244781 : Nat := 118140960795 + 1244781 * 2 ^ 59
def prefixEnd_1244781 : Nat := 4983230072969 + 3 ^ 40 * 1244781 * 2
def baseEnd_1244781 : Nat := 142037991685422116069525

theorem tailTrace_1244781 : CollatzResearch.WordTrace tailWord_1244781 prefixEnd_1244781 142037991685422116069525 := by
  unfold tailWord_1244781
  simp only [CollatzResearch.WordTrace]
  refine ⟨45400892903378503514622197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30267261935585669009748131 45400892903378503514622197)
  ·
    refine ⟨4256333709691734704495831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45400892903378503514622197 4256333709691734704495831)
    ·
      refine ⟨6384500564537602056743747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4256333709691734704495831 6384500564537602056743747)
      ·
        refine ⟨9576750846806403085115621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6384500564537602056743747 9576750846806403085115621)
        ·
          refine ⟨1795640783776200578459179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9576750846806403085115621 1795640783776200578459179)
          ·
            refine ⟨2693461175664300867688769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1795640783776200578459179 2693461175664300867688769)
            ·
              refine ⟨2020095881748225650766577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2693461175664300867688769 2020095881748225650766577)
              ·
                refine ⟨1515071911311169238074933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2020095881748225650766577 1515071911311169238074933)
                ·
                  refine ⟨142037991685422116069525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1515071911311169238074933 142037991685422116069525)
                  ·
                    rfl

theorem cell22_1244781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_1244781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244781 prefixEnd_1244781 := by exact prefixLift 1244781
  have htrace : WordTrace (prefixWord ++ tailWord_1244781) baseStart_1244781 baseEnd_1244781 := by
    simpa [prefixWord, tailWord_1244781, baseEnd_1244781] using wordTrace_append hprefix tailTrace_1244781
  have hstable : (prefixWord ++ tailWord_1244781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244781).length < 2 ^ (prefixWord ++ tailWord_1244781).sum := by decide
  have hdescent : baseEnd_1244781 < baseStart_1244781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244824 : List Nat := [2, 1, 2, 4, 1, 2, 2, 2, 1, 5]
def baseStart_1244824 : Nat := 118140960795 + 1244824 * 2 ^ 59
def prefixEnd_1244824 : Nat := 4983230072969 + 3 ^ 40 * 1244824 * 2
def baseEnd_1244824 : Nat := 426128694835028569383443

theorem tailTrace_1244824 : CollatzResearch.WordTrace tailWord_1244824 prefixEnd_1244824 426128694835028569383443 := by
  unfold tailWord_1244824
  simp only [CollatzResearch.WordTrace]
  refine ⟨22701230621111360929218763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30268307494815147905625017 22701230621111360929218763)
  ·
    refine ⟨34051845931667041393828145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22701230621111360929218763 34051845931667041393828145)
    ·
      refine ⟨25538884448750281045371109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34051845931667041393828145 25538884448750281045371109)
      ·
        refine ⟨4788540834140677696007083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25538884448750281045371109 4788540834140677696007083)
        ·
          refine ⟨7182811251211016544010625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4788540834140677696007083 7182811251211016544010625)
          ·
            refine ⟨5387108438408262408007969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7182811251211016544010625 5387108438408262408007969)
            ·
              refine ⟨4040331328806196806005977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5387108438408262408007969 4040331328806196806005977)
              ·
                refine ⟨3030248496604647604504483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4040331328806196806005977 3030248496604647604504483)
                ·
                  refine ⟨4545372744906971406756725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3030248496604647604504483 4545372744906971406756725)
                  ·
                    refine ⟨426128694835028569383443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4545372744906971406756725 426128694835028569383443)
                    ·
                      rfl

theorem cell22_1244824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_1244824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244824 prefixEnd_1244824 := by exact prefixLift 1244824
  have htrace : WordTrace (prefixWord ++ tailWord_1244824) baseStart_1244824 baseEnd_1244824 := by
    simpa [prefixWord, tailWord_1244824, baseEnd_1244824] using wordTrace_append hprefix tailTrace_1244824
  have hstable : (prefixWord ++ tailWord_1244824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244824).length < 2 ^ (prefixWord ++ tailWord_1244824).sum := by decide
  have hdescent : baseEnd_1244824 < baseStart_1244824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244858 : List Nat := [3, 1, 1, 1, 2, 5, 3, 1, 2, 3]
def baseStart_1244858 : Nat := 118140960795 + 1244858 * 2 ^ 59
def prefixEnd_1244858 : Nat := 4983230072969 + 3 ^ 40 * 1244858 * 2
def baseEnd_1244858 : Nat := 426140333729863814033339

theorem tailTrace_1244858 : CollatzResearch.WordTrace tailWord_1244858 prefixEnd_1244858 426140333729863814033339 := by
  unfold tailWord_1244858
  simp only [CollatzResearch.WordTrace]
  refine ⟨11350925331024886416293807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30269134216066363776783485 11350925331024886416293807)
  ·
    refine ⟨17026387996537329624440711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11350925331024886416293807 17026387996537329624440711)
    ·
      refine ⟨25539581994805994436661067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17026387996537329624440711 25539581994805994436661067)
      ·
        refine ⟨38309372992208991654991601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25539581994805994436661067 38309372992208991654991601)
        ·
          refine ⟨28732029744156743741243701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38309372992208991654991601 28732029744156743741243701)
          ·
            refine ⟨2693627788514694725741597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28732029744156743741243701 2693627788514694725741597)
            ·
              refine ⟨1010110420693010522153099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2693627788514694725741597 1010110420693010522153099)
              ·
                refine ⟨1515165631039515783229649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1010110420693010522153099 1515165631039515783229649)
                ·
                  refine ⟨1136374223279636837422237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1515165631039515783229649 1136374223279636837422237)
                  ·
                    refine ⟨426140333729863814033339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1136374223279636837422237 426140333729863814033339)
                    ·
                      rfl

theorem cell22_1244858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 2, 3].length) (baseStart_1244858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244858 prefixEnd_1244858 := by exact prefixLift 1244858
  have htrace : WordTrace (prefixWord ++ tailWord_1244858) baseStart_1244858 baseEnd_1244858 := by
    simpa [prefixWord, tailWord_1244858, baseEnd_1244858] using wordTrace_append hprefix tailTrace_1244858
  have hstable : (prefixWord ++ tailWord_1244858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244858).length < 2 ^ (prefixWord ++ tailWord_1244858).sum := by decide
  have hdescent : baseEnd_1244858 < baseStart_1244858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244914 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_1244914 : Nat := 118140960795 + 1244914 * 2 ^ 59
def prefixEnd_1244914 : Nat := 4983230072969 + 3 ^ 40 * 1244914 * 2
def baseEnd_1244914 : Nat := 426159503674298334633167

theorem tailTrace_1244914 : CollatzResearch.WordTrace tailWord_1244914 prefixEnd_1244914 426159503674298334633167 := by
  unfold tailWord_1244914
  simp only [CollatzResearch.WordTrace]
  refine ⟨11351435952974166807303449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30270495874597778152809197 11351435952974166807303449)
  ·
    refine ⟨8513576964730625105477587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11351435952974166807303449 8513576964730625105477587)
    ·
      refine ⟨12770365447095937658216381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8513576964730625105477587 12770365447095937658216381)
      ·
        refine ⟨4788887042660976621831143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12770365447095937658216381 4788887042660976621831143)
        ·
          refine ⟨7183330563991464932746715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4788887042660976621831143 7183330563991464932746715)
          ·
            refine ⟨10774995845987197399120073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7183330563991464932746715 10774995845987197399120073)
            ·
              refine ⟨8081246884490398049340055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10774995845987197399120073 8081246884490398049340055)
              ·
                refine ⟨12121870326735597074010083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8081246884490398049340055 12121870326735597074010083)
                ·
                  refine ⟨18182805490103395611015125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12121870326735597074010083 18182805490103395611015125)
                  ·
                    refine ⟨426159503674298334633167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18182805490103395611015125 426159503674298334633167)
                    ·
                      rfl

theorem cell22_1244914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_1244914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244914 prefixEnd_1244914 := by exact prefixLift 1244914
  have htrace : WordTrace (prefixWord ++ tailWord_1244914) baseStart_1244914 baseEnd_1244914 := by
    simpa [prefixWord, tailWord_1244914, baseEnd_1244914] using wordTrace_append hprefix tailTrace_1244914
  have hstable : (prefixWord ++ tailWord_1244914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244914).length < 2 ^ (prefixWord ++ tailWord_1244914).sum := by decide
  have hdescent : baseEnd_1244914 < baseStart_1244914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244959 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 3, 5]
def baseStart_1244959 : Nat := 118140960795 + 1244959 * 2 ^ 59
def prefixEnd_1244959 : Nat := 4983230072969 + 3 ^ 40 * 1244959 * 2
def baseEnd_1244959 : Nat := 426174908093933217258029

theorem tailTrace_1244959 : CollatzResearch.WordTrace tailWord_1244959 prefixEnd_1244959 426174908093933217258029 := by
  unfold tailWord_1244959
  simp only [CollatzResearch.WordTrace]
  refine ⟨45407385096733639914601931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30271590064489093276401287 45407385096733639914601931)
  ·
    refine ⟨68111077645100459871902897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45407385096733639914601931 68111077645100459871902897)
    ·
      refine ⟨51083308233825344903927173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68111077645100459871902897 51083308233825344903927173)
      ·
        refine ⟨9578120293842252169486345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51083308233825344903927173 9578120293842252169486345)
        ·
          refine ⟨7183590220381689127114759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9578120293842252169486345 7183590220381689127114759)
          ·
            refine ⟨10775385330572533690672139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7183590220381689127114759 10775385330572533690672139)
            ·
              refine ⟨16163077995858800536008209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10775385330572533690672139 16163077995858800536008209)
              ·
                refine ⟨12122308496894100402006157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16163077995858800536008209 12122308496894100402006157)
                ·
                  refine ⟨4545865686335287650752309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12122308496894100402006157 4545865686335287650752309)
                  ·
                    refine ⟨426174908093933217258029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4545865686335287650752309 426174908093933217258029)
                    ·
                      rfl

theorem cell22_1244959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_1244959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244959 prefixEnd_1244959 := by exact prefixLift 1244959
  have htrace : WordTrace (prefixWord ++ tailWord_1244959) baseStart_1244959 baseEnd_1244959 := by
    simpa [prefixWord, tailWord_1244959, baseEnd_1244959] using wordTrace_append hprefix tailTrace_1244959
  have hstable : (prefixWord ++ tailWord_1244959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244959).length < 2 ^ (prefixWord ++ tailWord_1244959).sum := by decide
  have hdescent : baseEnd_1244959 < baseStart_1244959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244991 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 1, 6]
def baseStart_1244991 : Nat := 118140960795 + 1244991 * 2 ^ 59
def prefixEnd_1244991 : Nat := 4983230072969 + 3 ^ 40 * 1244991 * 2
def baseEnd_1244991 : Nat := 426185862347895800457931

theorem tailTrace_1244991 : CollatzResearch.WordTrace tailWord_1244991 prefixEnd_1244991 426185862347895800457931 := by
  unfold tailWord_1244991
  simp only [CollatzResearch.WordTrace]
  refine ⟨45408552232617709379766827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30272368155078472919844551 45408552232617709379766827)
  ·
    refine ⟨68112828348926564069650241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45408552232617709379766827 68112828348926564069650241)
    ·
      refine ⟨51084621261694923052237681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68112828348926564069650241 51084621261694923052237681)
      ·
        refine ⟨38313465946271192289178261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51084621261694923052237681 38313465946271192289178261)
        ·
          refine ⟨1795943716231462138555231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38313465946271192289178261 1795943716231462138555231)
          ·
            refine ⟨2693915574347193207832847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1795943716231462138555231 2693915574347193207832847)
            ·
              refine ⟨4040873361520789811749271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2693915574347193207832847 4040873361520789811749271)
              ·
                refine ⟨6061310042281184717623907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4040873361520789811749271 6061310042281184717623907)
                ·
                  refine ⟨9091965063421777076435861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6061310042281184717623907 9091965063421777076435861)
                  ·
                    refine ⟨426185862347895800457931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9091965063421777076435861 426185862347895800457931)
                    ·
                      rfl

theorem cell22_1244991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 6].length) (baseStart_1244991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1244991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1244991 prefixEnd_1244991 := by exact prefixLift 1244991
  have htrace : WordTrace (prefixWord ++ tailWord_1244991) baseStart_1244991 baseEnd_1244991 := by
    simpa [prefixWord, tailWord_1244991, baseEnd_1244991] using wordTrace_append hprefix tailTrace_1244991
  have hstable : (prefixWord ++ tailWord_1244991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244991).length < 2 ^ (prefixWord ++ tailWord_1244991).sum := by decide
  have hdescent : baseEnd_1244991 < baseStart_1244991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245010 : List Nat := [3, 2, 2, 1, 1, 5, 1, 2, 2, 3]
def baseStart_1245010 : Nat := 118140960795 + 1245010 * 2 ^ 59
def prefixEnd_1245010 : Nat := 4983230072969 + 3 ^ 40 * 1245010 * 2
def baseEnd_1245010 : Nat := 426192366436186084232873

theorem tailTrace_1245010 : CollatzResearch.WordTrace tailWord_1245010 prefixEnd_1245010 426192366436186084232873 := by
  unfold tailWord_1245010
  simp only [CollatzResearch.WordTrace]
  refine ⟨11352311304887218906177121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30272830146365917083138989 11352311304887218906177121)
  ·
    refine ⟨8514233478665414179632841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11352311304887218906177121 8514233478665414179632841)
    ·
      refine ⟨6385675108999060634724631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8514233478665414179632841 6385675108999060634724631)
      ·
        refine ⟨9578512663498590952086947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6385675108999060634724631 9578512663498590952086947)
        ·
          refine ⟨14367768995247886428130421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9578512663498590952086947 14367768995247886428130421)
          ·
            refine ⟨1346978343304489352637227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14367768995247886428130421 1346978343304489352637227)
            ·
              refine ⟨2020467514956734028955841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1346978343304489352637227 2020467514956734028955841)
              ·
                refine ⟨1515350636217550521716881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2020467514956734028955841 1515350636217550521716881)
                ·
                  refine ⟨1136512977163162891287661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1515350636217550521716881 1136512977163162891287661)
                  ·
                    refine ⟨426192366436186084232873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1136512977163162891287661 426192366436186084232873)
                    ·
                      rfl

theorem cell22_1245010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_1245010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245010 prefixEnd_1245010 := by exact prefixLift 1245010
  have htrace : WordTrace (prefixWord ++ tailWord_1245010) baseStart_1245010 baseEnd_1245010 := by
    simpa [prefixWord, tailWord_1245010, baseEnd_1245010] using wordTrace_append hprefix tailTrace_1245010
  have hstable : (prefixWord ++ tailWord_1245010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245010).length < 2 ^ (prefixWord ++ tailWord_1245010).sum := by decide
  have hdescent : baseEnd_1245010 < baseStart_1245010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245078 : List Nat := [5, 3, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_1245078 : Nat := 118140960795 + 1245078 * 2 ^ 59
def prefixEnd_1245078 : Nat := 4983230072969 + 3 ^ 40 * 1245078 * 2
def baseEnd_1245078 : Nat := 426215644225856573532665

theorem tailTrace_1245078 : CollatzResearch.WordTrace tailWord_1245078 prefixEnd_1245078 426215644225856573532665 := by
  unfold tailWord_1245078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2838232836456407702386493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30274483588868348825455925 2838232836456407702386493)
  ·
    refine ⟨1064337313671152888394935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2838232836456407702386493 1064337313671152888394935)
    ·
      refine ⟨1596505970506729332592403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1064337313671152888394935 1596505970506729332592403)
      ·
        refine ⟨2394758955760093998888605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1596505970506729332592403 2394758955760093998888605)
        ·
          refine ⟨898034608410035249583227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2394758955760093998888605 898034608410035249583227)
          ·
            refine ⟨1347051912615052874374841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 898034608410035249583227 1347051912615052874374841)
            ·
              refine ⟨1010288934461289655781131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1347051912615052874374841 1010288934461289655781131)
              ·
                refine ⟨1515433401691934483671697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1010288934461289655781131 1515433401691934483671697)
                ·
                  refine ⟨1136575051268950862753773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1515433401691934483671697 1136575051268950862753773)
                  ·
                    refine ⟨426215644225856573532665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1136575051268950862753773 426215644225856573532665)
                    ·
                      rfl

theorem cell22_1245078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_1245078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245078 prefixEnd_1245078 := by exact prefixLift 1245078
  have htrace : WordTrace (prefixWord ++ tailWord_1245078) baseStart_1245078 baseEnd_1245078 := by
    simpa [prefixWord, tailWord_1245078, baseEnd_1245078] using wordTrace_append hprefix tailTrace_1245078
  have hstable : (prefixWord ++ tailWord_1245078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245078).length < 2 ^ (prefixWord ++ tailWord_1245078).sum := by decide
  have hdescent : baseEnd_1245078 < baseStart_1245078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245085 : List Nat := [1, 4, 2, 1, 2, 4, 2, 1, 5]
def baseStart_1245085 : Nat := 118140960795 + 1245085 * 2 ^ 59
def prefixEnd_1245085 : Nat := 4983230072969 + 3 ^ 40 * 1245085 * 2
def baseEnd_1245085 : Nat := 142072680156303629535881

theorem tailTrace_1245085 : CollatzResearch.WordTrace tailWord_1245085 prefixEnd_1245085 142072680156303629535881 := by
  unfold tailWord_1245085
  simp only [CollatzResearch.WordTrace]
  refine ⟨45411980694277163433688709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30274653796184775622459139 45411980694277163433688709)
  ·
    refine ⟨8514746380176968143816633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45411980694277163433688709 8514746380176968143816633)
    ·
      refine ⟨6386059785132726107862475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8514746380176968143816633 6386059785132726107862475)
      ·
        refine ⟨9579089677699089161793713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6386059785132726107862475 9579089677699089161793713)
        ·
          refine ⟨7184317258274316871345285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9579089677699089161793713 7184317258274316871345285)
          ·
            refine ⟨1347059485926434413377241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7184317258274316871345285 1347059485926434413377241)
            ·
              refine ⟨1010294614444825810032931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1347059485926434413377241 1010294614444825810032931)
              ·
                refine ⟨1515441921667238715049397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1010294614444825810032931 1515441921667238715049397)
                ·
                  refine ⟨142072680156303629535881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1515441921667238715049397 142072680156303629535881)
                  ·
                    rfl

theorem cell22_1245085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_1245085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245085 prefixEnd_1245085 := by exact prefixLift 1245085
  have htrace : WordTrace (prefixWord ++ tailWord_1245085) baseStart_1245085 baseEnd_1245085 := by
    simpa [prefixWord, tailWord_1245085, baseEnd_1245085] using wordTrace_append hprefix tailTrace_1245085
  have hstable : (prefixWord ++ tailWord_1245085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245085).length < 2 ^ (prefixWord ++ tailWord_1245085).sum := by decide
  have hdescent : baseEnd_1245085 < baseStart_1245085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245113 : List Nat := [1, 2, 1, 4, 2, 1, 2, 5, 4]
def baseStart_1245113 : Nat := 118140960795 + 1245113 * 2 ^ 59
def prefixEnd_1245113 : Nat := 4983230072969 + 3 ^ 40 * 1245113 * 2
def baseEnd_1245113 : Nat := 142075875147042716302519

theorem tailTrace_1245113 : CollatzResearch.WordTrace tailWord_1245113 prefixEnd_1245113 142075875147042716302519 := by
  unfold tailWord_1245113
  simp only [CollatzResearch.WordTrace]
  refine ⟨45413001938175724215707993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30275334625450482810471995 45413001938175724215707993)
  ·
    refine ⟨34059751453631793161780995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45413001938175724215707993 34059751453631793161780995)
    ·
      refine ⟨51089627180447689742671493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34059751453631793161780995 51089627180447689742671493)
      ·
        refine ⟨9579305096333941826750905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51089627180447689742671493 9579305096333941826750905)
        ·
          refine ⟨7184478822250456370063179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9579305096333941826750905 7184478822250456370063179)
          ·
            refine ⟨10776718233375684555094769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7184478822250456370063179 10776718233375684555094769)
            ·
              refine ⟨8082538675031763416321077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10776718233375684555094769 8082538675031763416321077)
              ·
                refine ⟨757738000784227820280101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8082538675031763416321077 757738000784227820280101)
                ·
                  refine ⟨142075875147042716302519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 757738000784227820280101 142075875147042716302519)
                  ·
                    rfl

theorem cell22_1245113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 4].length) (baseStart_1245113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245113 prefixEnd_1245113 := by exact prefixLift 1245113
  have htrace : WordTrace (prefixWord ++ tailWord_1245113) baseStart_1245113 baseEnd_1245113 := by
    simpa [prefixWord, tailWord_1245113, baseEnd_1245113] using wordTrace_append hprefix tailTrace_1245113
  have hstable : (prefixWord ++ tailWord_1245113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245113).length < 2 ^ (prefixWord ++ tailWord_1245113).sum := by decide
  have hdescent : baseEnd_1245113 < baseStart_1245113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245130 : List Nat := [3, 1, 2, 1, 2, 1, 6, 2, 4]
def baseStart_1245130 : Nat := 118140960795 + 1245130 * 2 ^ 59
def prefixEnd_1245130 : Nat := 4983230072969 + 3 ^ 40 * 1245130 * 2
def baseEnd_1245130 : Nat := 142077814962848590410835

theorem tailTrace_1245130 : CollatzResearch.WordTrace tailWord_1245130 prefixEnd_1245130 142077814962848590410835 := by
  unfold tailWord_1245130
  simp only [CollatzResearch.WordTrace]
  refine ⟨11353405494778534029769211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30275747986076090746051229 11353405494778534029769211)
  ·
    refine ⟨17030108242167801044653817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11353405494778534029769211 17030108242167801044653817)
    ·
      refine ⟨12772581181625850783490363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17030108242167801044653817 12772581181625850783490363)
      ·
        refine ⟨19158871772438776175235545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12772581181625850783490363 19158871772438776175235545)
        ·
          refine ⟨14369153829329082131426659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19158871772438776175235545 14369153829329082131426659)
          ·
            refine ⟨21553730743993623197139989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14369153829329082131426659 21553730743993623197139989)
            ·
              refine ⟨1010331128624701087365937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21553730743993623197139989 1010331128624701087365937)
              ·
                refine ⟨757748346468525815524453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1010331128624701087365937 757748346468525815524453)
                ·
                  refine ⟨142077814962848590410835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 757748346468525815524453 142077814962848590410835)
                  ·
                    rfl

theorem cell22_1245130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 4].length) (baseStart_1245130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245130 prefixEnd_1245130 := by exact prefixLift 1245130
  have htrace : WordTrace (prefixWord ++ tailWord_1245130) baseStart_1245130 baseEnd_1245130 := by
    simpa [prefixWord, tailWord_1245130, baseEnd_1245130] using wordTrace_append hprefix tailTrace_1245130
  have hstable : (prefixWord ++ tailWord_1245130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245130).length < 2 ^ (prefixWord ++ tailWord_1245130).sum := by decide
  have hdescent : baseEnd_1245130 < baseStart_1245130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
