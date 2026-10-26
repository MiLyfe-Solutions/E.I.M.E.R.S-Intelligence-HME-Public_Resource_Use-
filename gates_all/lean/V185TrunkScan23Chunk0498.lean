import V185TrunkScan23Chunk0497

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2945439 : List Nat := [1, 1, 2, 5, 1, 1, 1, 6, 1, 2, 2]
def baseStart_2945439 : Nat := 118140960795 + 2945439 * 2 ^ 59
def prefixEnd_2945439 : Nat := 4983230072969 + 3 ^ 40 * 2945439 * 2
def baseEnd_2945439 : Nat := 1512425945498406690066679

theorem tailTrace_2945439 : CollatzResearch.WordTrace tailWord_2945439 prefixEnd_2945439 1512425945498406690066679 := by
  unfold tailWord_2945439
  simp only [CollatzResearch.WordTrace]
  refine ⟨107428985976185018777175371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71619323984123345851450247 107428985976185018777175371)
  ·
    refine ⟨161143478964277528165763057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107428985976185018777175371 161143478964277528165763057)
    ·
      refine ⟨120857609223208146124322293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161143478964277528165763057 120857609223208146124322293)
      ·
        refine ⟨11330400864675763699155215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120857609223208146124322293 11330400864675763699155215)
        ·
          refine ⟨16995601297013645548732823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11330400864675763699155215 16995601297013645548732823)
          ·
            refine ⟨25493401945520468323099235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16995601297013645548732823 25493401945520468323099235)
            ·
              refine ⟨38240102918280702484648853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25493401945520468323099235 38240102918280702484648853)
              ·
                refine ⟨1792504824294407928967915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38240102918280702484648853 1792504824294407928967915)
                ·
                  refine ⟨2688757236441611893451873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1792504824294407928967915 2688757236441611893451873)
                  ·
                    refine ⟨2016567927331208920088905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2688757236441611893451873 2016567927331208920088905)
                    ·
                      refine ⟨1512425945498406690066679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2016567927331208920088905 1512425945498406690066679)
                      ·
                        rfl

theorem cell23_2945439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_2945439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945439 prefixEnd_2945439 := by exact prefixLift 2945439
  have htrace : WordTrace (prefixWord ++ tailWord_2945439) baseStart_2945439 baseEnd_2945439 := by
    simpa [prefixWord, tailWord_2945439, baseEnd_2945439] using wordTrace_append hprefix tailTrace_2945439
  have hstable : (prefixWord ++ tailWord_2945439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945439).length < 2 ^ (prefixWord ++ tailWord_2945439).sum := by decide
  have hdescent : baseEnd_2945439 < baseStart_2945439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945451 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 7]
def baseStart_2945451 : Nat := 118140960795 + 2945451 * 2 ^ 59
def prefixEnd_2945451 : Nat := 4983230072969 + 3 ^ 40 * 2945451 * 2
def baseEnd_2945451 : Nat := 1512432107266260643116623

theorem tailTrace_2945451 : CollatzResearch.WordTrace tailWord_2945451 prefixEnd_2945451 1512432107266260643116623 := by
  unfold tailWord_2945451
  simp only [CollatzResearch.WordTrace]
  refine ⟨107429423652141544826612207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71619615768094363217741471 107429423652141544826612207)
  ·
    refine ⟨161144135478212317239918311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107429423652141544826612207 161144135478212317239918311)
    ·
      refine ⟨241716203217318475859877467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161144135478212317239918311 241716203217318475859877467)
      ·
        refine ⟨362574304825977713789816201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241716203217318475859877467 362574304825977713789816201)
        ·
          refine ⟨271930728619483285342362151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362574304825977713789816201 271930728619483285342362151)
          ·
            refine ⟨407896092929224928013543227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271930728619483285342362151 407896092929224928013543227)
            ·
              refine ⟨611844139393837392020314841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407896092929224928013543227 611844139393837392020314841)
              ·
                refine ⟨458883104545378044015236131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 611844139393837392020314841 458883104545378044015236131)
                ·
                  refine ⟨688324656818067066022854197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458883104545378044015236131 688324656818067066022854197)
                  ·
                    refine ⟨64530436576693787439642581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 688324656818067066022854197 64530436576693787439642581)
                    ·
                      refine ⟨1512432107266260643116623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64530436576693787439642581 1512432107266260643116623)
                      ·
                        rfl

theorem cell23_2945451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 7].length) (baseStart_2945451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945451 prefixEnd_2945451 := by exact prefixLift 2945451
  have htrace : WordTrace (prefixWord ++ tailWord_2945451) baseStart_2945451 baseEnd_2945451 := by
    simpa [prefixWord, tailWord_2945451, baseEnd_2945451] using wordTrace_append hprefix tailTrace_2945451
  have hstable : (prefixWord ++ tailWord_2945451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945451).length < 2 ^ (prefixWord ++ tailWord_2945451).sum := by decide
  have hdescent : baseEnd_2945451 < baseStart_2945451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945482 : List Nat := [3, 1, 2, 1, 2, 2, 1, 5, 1, 3, 2]
def baseStart_2945482 : Nat := 118140960795 + 2945482 * 2 ^ 59
def prefixEnd_2945482 : Nat := 4983230072969 + 3 ^ 40 * 2945482 * 2
def baseEnd_2945482 : Nat := 1512448025166550021828981

theorem tailTrace_2945482 : CollatzResearch.WordTrace tailWord_2945482 prefixEnd_2945482 1512448025166550021828981 := by
  unfold tailWord_2945482
  simp only [CollatzResearch.WordTrace]
  refine ⟨26857638578757309280247675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71620369543352824747327133 26857638578757309280247675)
  ·
    refine ⟨40286457868135963920371513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26857638578757309280247675 40286457868135963920371513)
    ·
      refine ⟨30214843401101972940278635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40286457868135963920371513 30214843401101972940278635)
      ·
        refine ⟨45322265101652959410417953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30214843401101972940278635 45322265101652959410417953)
        ·
          refine ⟨33991698826239719557813465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45322265101652959410417953 33991698826239719557813465)
          ·
            refine ⟨25493774119679789668360099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33991698826239719557813465 25493774119679789668360099)
            ·
              refine ⟨38240661179519684502540149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25493774119679789668360099 38240661179519684502540149)
              ·
                refine ⟨3585061985579970422113139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38240661179519684502540149 3585061985579970422113139)
                ·
                  refine ⟨5377592978369955633169709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3585061985579970422113139 5377592978369955633169709)
                  ·
                    refine ⟨2016597366888733362438641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5377592978369955633169709 2016597366888733362438641)
                    ·
                      refine ⟨1512448025166550021828981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2016597366888733362438641 1512448025166550021828981)
                      ·
                        rfl

theorem cell23_2945482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_2945482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945482 prefixEnd_2945482 := by exact prefixLift 2945482
  have htrace : WordTrace (prefixWord ++ tailWord_2945482) baseStart_2945482 baseEnd_2945482 := by
    simpa [prefixWord, tailWord_2945482, baseEnd_2945482] using wordTrace_append hprefix tailTrace_2945482
  have hstable : (prefixWord ++ tailWord_2945482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945482).length < 2 ^ (prefixWord ++ tailWord_2945482).sum := by decide
  have hdescent : baseEnd_2945482 < baseStart_2945482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945490 : List Nat := [3, 2, 2, 4, 1, 1, 3, 2, 1, 2, 2]
def baseStart_2945490 : Nat := 118140960795 + 2945490 * 2 ^ 59
def prefixEnd_2945490 : Nat := 4983230072969 + 3 ^ 40 * 2945490 * 2
def baseEnd_2945490 : Nat := 1512452133011785990528945

theorem tailTrace_2945490 : CollatzResearch.WordTrace tailWord_2945490 prefixEnd_2945490 1512452133011785990528945 := by
  unfold tailWord_2945490
  simp only [CollatzResearch.WordTrace]
  refine ⟨26857711524750063621820481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71620564066000169658187949 26857711524750063621820481)
  ·
    refine ⟨20143283643562547716365361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26857711524750063621820481 20143283643562547716365361)
    ·
      refine ⟨15107462732671910787274021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20143283643562547716365361 15107462732671910787274021)
      ·
        refine ⟨2832649262375983272613879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15107462732671910787274021 2832649262375983272613879)
        ·
          refine ⟨4248973893563974908920819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2832649262375983272613879 4248973893563974908920819)
          ·
            refine ⟨6373460840345962363381229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4248973893563974908920819 6373460840345962363381229)
            ·
              refine ⟨2390047815129735886267961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6373460840345962363381229 2390047815129735886267961)
              ·
                refine ⟨1792535861347301914700971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2390047815129735886267961 1792535861347301914700971)
                ·
                  refine ⟨2688803792020952872051457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1792535861347301914700971 2688803792020952872051457)
                  ·
                    refine ⟨2016602844015714654038593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2688803792020952872051457 2016602844015714654038593)
                    ·
                      refine ⟨1512452133011785990528945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2016602844015714654038593 1512452133011785990528945)
                      ·
                        rfl

theorem cell23_2945490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_2945490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945490 prefixEnd_2945490 := by exact prefixLift 2945490
  have htrace : WordTrace (prefixWord ++ tailWord_2945490) baseStart_2945490 baseEnd_2945490 := by
    simpa [prefixWord, tailWord_2945490, baseEnd_2945490] using wordTrace_append hprefix tailTrace_2945490
  have hstable : (prefixWord ++ tailWord_2945490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945490).length < 2 ^ (prefixWord ++ tailWord_2945490).sum := by decide
  have hdescent : baseEnd_2945490 < baseStart_2945490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945498 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5]
def baseStart_2945498 : Nat := 118140960795 + 2945498 * 2 ^ 59
def prefixEnd_2945498 : Nat := 4983230072969 + 3 ^ 40 * 2945498 * 2
def baseEnd_2945498 : Nat := 1512456240857021959228907

theorem tailTrace_2945498 : CollatzResearch.WordTrace tailWord_2945498 prefixEnd_2945498 1512456240857021959228907 := by
  unfold tailWord_2945498
  simp only [CollatzResearch.WordTrace]
  refine ⟨26857784470742817963393287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71620758588647514569048765 26857784470742817963393287)
  ·
    refine ⟨40286676706114226945089931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26857784470742817963393287 40286676706114226945089931)
    ·
      refine ⟨60430015059171340417634897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40286676706114226945089931 60430015059171340417634897)
      ·
        refine ⟨45322511294378505313226173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60430015059171340417634897 45322511294378505313226173)
        ·
          refine ⟨16995941735391939492459815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45322511294378505313226173 16995941735391939492459815)
          ·
            refine ⟨25493912603087909238689723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16995941735391939492459815 25493912603087909238689723)
            ·
              refine ⟨38240868904631863858034585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25493912603087909238689723 38240868904631863858034585)
              ·
                refine ⟨28680651678473897893525939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38240868904631863858034585 28680651678473897893525939)
                ·
                  refine ⟨43020977517710846840288909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28680651678473897893525939 43020977517710846840288909)
                  ·
                    refine ⟨16132866569141567565108341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43020977517710846840288909 16132866569141567565108341)
                    ·
                      refine ⟨1512456240857021959228907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16132866569141567565108341 1512456240857021959228907)
                      ·
                        rfl

theorem cell23_2945498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_2945498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945498 prefixEnd_2945498 := by exact prefixLift 2945498
  have htrace : WordTrace (prefixWord ++ tailWord_2945498) baseStart_2945498 baseEnd_2945498 := by
    simpa [prefixWord, tailWord_2945498, baseEnd_2945498] using wordTrace_append hprefix tailTrace_2945498
  have hstable : (prefixWord ++ tailWord_2945498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945498).length < 2 ^ (prefixWord ++ tailWord_2945498).sum := by decide
  have hdescent : baseEnd_2945498 < baseStart_2945498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945535 : List Nat := [1, 1, 2, 2, 1, 2, 4, 5, 5]
def baseStart_2945535 : Nat := 118140960795 + 2945535 * 2 ^ 59
def prefixEnd_2945535 : Nat := 4983230072969 + 3 ^ 40 * 2945535 * 2
def baseEnd_2945535 : Nat := 168052804404582034940693

theorem tailTrace_2945535 : CollatzResearch.WordTrace tailWord_2945535 prefixEnd_2945535 168052804404582034940693 := by
  unfold tailWord_2945535
  simp only [CollatzResearch.WordTrace]
  refine ⟨107432487383837227172670059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71621658255891484781780039 107432487383837227172670059)
  ·
    refine ⟨161148731075755840759005089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107432487383837227172670059 161148731075755840759005089)
    ·
      refine ⟨120861548306816880569253817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161148731075755840759005089 120861548306816880569253817)
      ·
        refine ⟨90646161230112660426940363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120861548306816880569253817 90646161230112660426940363)
        ·
          refine ⟨135969241845168990640410545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90646161230112660426940363 135969241845168990640410545)
          ·
            refine ⟨101976931383876742980307909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135969241845168990640410545 101976931383876742980307909)
            ·
              refine ⟨19120674634476889308807733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101976931383876742980307909 19120674634476889308807733)
              ·
                refine ⟨1792563246982208372700725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19120674634476889308807733 1792563246982208372700725)
                ·
                  refine ⟨168052804404582034940693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1792563246982208372700725 168052804404582034940693)
                  ·
                    rfl

theorem cell23_2945535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 5].length) (baseStart_2945535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945535 prefixEnd_2945535 := by exact prefixLift 2945535
  have htrace : WordTrace (prefixWord ++ tailWord_2945535) baseStart_2945535 baseEnd_2945535 := by
    simpa [prefixWord, tailWord_2945535, baseEnd_2945535] using wordTrace_append hprefix tailTrace_2945535
  have hstable : (prefixWord ++ tailWord_2945535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945535).length < 2 ^ (prefixWord ++ tailWord_2945535).sum := by decide
  have hdescent : baseEnd_2945535 < baseStart_2945535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945549 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_2945549 : Nat := 118140960795 + 2945549 * 2 ^ 59
def prefixEnd_2945549 : Nat := 4983230072969 + 3 ^ 40 * 2945549 * 2
def baseEnd_2945549 : Nat := 1512482428370401259691173

theorem tailTrace_2945549 : CollatzResearch.WordTrace tailWord_2945549 prefixEnd_2945549 1512482428370401259691173 := by
  unfold tailWord_2945549
  simp only [CollatzResearch.WordTrace]
  refine ⟨107432998005786507563679701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71621998670524338375786467 107432998005786507563679701)
  ·
    refine ⟨2517960890760621271023743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 107432998005786507563679701 2517960890760621271023743)
    ·
      refine ⟨3776941336140931906535615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2517960890760621271023743 3776941336140931906535615)
      ·
        refine ⟨5665412004211397859803423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3776941336140931906535615 5665412004211397859803423)
        ·
          refine ⟨8498118006317096789705135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5665412004211397859803423 8498118006317096789705135)
          ·
            refine ⟨12747177009475645184557703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8498118006317096789705135 12747177009475645184557703)
            ·
              refine ⟨19120765514213467776836555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12747177009475645184557703 19120765514213467776836555)
              ·
                refine ⟨28681148271320201665254833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19120765514213467776836555 28681148271320201665254833)
                ·
                  refine ⟨21510861203490151248941125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28681148271320201665254833 21510861203490151248941125)
                  ·
                    refine ⟨4033286475654403359176461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21510861203490151248941125 4033286475654403359176461)
                    ·
                      refine ⟨1512482428370401259691173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4033286475654403359176461 1512482428370401259691173)
                      ·
                        rfl

theorem cell23_2945549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_2945549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945549 prefixEnd_2945549 := by exact prefixLift 2945549
  have htrace : WordTrace (prefixWord ++ tailWord_2945549) baseStart_2945549 baseEnd_2945549 := by
    simpa [prefixWord, tailWord_2945549, baseEnd_2945549] using wordTrace_append hprefix tailTrace_2945549
  have hstable : (prefixWord ++ tailWord_2945549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945549).length < 2 ^ (prefixWord ++ tailWord_2945549).sum := by decide
  have hdescent : baseEnd_2945549 < baseStart_2945549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945555 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 1, 7, 2]
def baseStart_2945555 : Nat := 118140960795 + 2945555 * 2 ^ 59
def prefixEnd_2945555 : Nat := 4983230072969 + 3 ^ 40 * 2945555 * 2
def baseEnd_2945555 : Nat := 1512485509254328236216145

theorem tailTrace_2945555 : CollatzResearch.WordTrace tailWord_2945555 prefixEnd_2945555 1512485509254328236216145 := by
  unfold tailWord_2945555
  simp only [CollatzResearch.WordTrace]
  refine ⟨107433216843764770588398119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71622144562509847058932079 107433216843764770588398119)
  ·
    refine ⟨161149825265647155882597179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107433216843764770588398119 161149825265647155882597179)
    ·
      refine ⟨241724737898470733823895769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161149825265647155882597179 241724737898470733823895769)
      ·
        refine ⟨181293553423853050367921827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241724737898470733823895769 181293553423853050367921827)
        ·
          refine ⟨271940330135779575551882741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181293553423853050367921827 271940330135779575551882741)
          ·
            refine ⟨25494405950229335207989007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 271940330135779575551882741 25494405950229335207989007)
            ·
              refine ⟨38241608925344002811983511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25494405950229335207989007 38241608925344002811983511)
              ·
                refine ⟨57362413388016004217975267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38241608925344002811983511 57362413388016004217975267)
                ·
                  refine ⟨86043620082024006326962901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57362413388016004217975267 86043620082024006326962901)
                  ·
                    refine ⟨2016647345672437648288193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 86043620082024006326962901 2016647345672437648288193)
                    ·
                      refine ⟨1512485509254328236216145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2016647345672437648288193 1512485509254328236216145)
                      ·
                        rfl

theorem cell23_2945555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 7, 2].length) (baseStart_2945555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945555 prefixEnd_2945555 := by exact prefixLift 2945555
  have htrace : WordTrace (prefixWord ++ tailWord_2945555) baseStart_2945555 baseEnd_2945555 := by
    simpa [prefixWord, tailWord_2945555, baseEnd_2945555] using wordTrace_append hprefix tailTrace_2945555
  have hstable : (prefixWord ++ tailWord_2945555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945555).length < 2 ^ (prefixWord ++ tailWord_2945555).sum := by decide
  have hdescent : baseEnd_2945555 < baseStart_2945555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945582 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 1, 7]
def baseStart_2945582 : Nat := 118140960795 + 2945582 * 2 ^ 59
def prefixEnd_2945582 : Nat := 4983230072969 + 3 ^ 40 * 2945582 * 2
def baseEnd_2945582 : Nat := 504166457743999876859507

theorem tailTrace_2945582 : CollatzResearch.WordTrace tailWord_2945582 prefixEnd_2945582 504166457743999876859507 := by
  unfold tailWord_2945582
  simp only [CollatzResearch.WordTrace]
  refine ⟨13429275201833369274953875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71622801076444636133087333 13429275201833369274953875)
  ·
    refine ⟨20143912802750053912430813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13429275201833369274953875 20143912802750053912430813)
    ·
      refine ⟨7553967301031270217161555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20143912802750053912430813 7553967301031270217161555)
      ·
        refine ⟨11330950951546905325742333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7553967301031270217161555 11330950951546905325742333)
        ·
          refine ⟨4249106606830089497153375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11330950951546905325742333 4249106606830089497153375)
          ·
            refine ⟨6373659910245134245730063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4249106606830089497153375 6373659910245134245730063)
            ·
              refine ⟨9560489865367701368595095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6373659910245134245730063 9560489865367701368595095)
              ·
                refine ⟨14340734798051552052892643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9560489865367701368595095 14340734798051552052892643)
                ·
                  refine ⟨21511102197077328079338965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14340734798051552052892643 21511102197077328079338965)
                  ·
                    refine ⟨504166457743999876859507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21511102197077328079338965 504166457743999876859507)
                    ·
                      rfl

theorem cell23_2945582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_2945582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945582 prefixEnd_2945582 := by exact prefixLift 2945582
  have htrace : WordTrace (prefixWord ++ tailWord_2945582) baseStart_2945582 baseEnd_2945582 := by
    simpa [prefixWord, tailWord_2945582, baseEnd_2945582] using wordTrace_append hprefix tailTrace_2945582
  have hstable : (prefixWord ++ tailWord_2945582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945582).length < 2 ^ (prefixWord ++ tailWord_2945582).sum := by decide
  have hdescent : baseEnd_2945582 < baseStart_2945582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945612 : List Nat := [2, 2, 1, 3, 1, 2, 4, 1, 3, 4]
def baseStart_2945612 : Nat := 118140960795 + 2945612 * 2 ^ 59
def prefixEnd_2945612 : Nat := 4983230072969 + 3 ^ 40 * 2945612 * 2
def baseEnd_2945612 : Nat := 504171592550544837734461

theorem tailTrace_2945612 : CollatzResearch.WordTrace tailWord_2945612 prefixEnd_2945612 504171592550544837734461 := by
  unfold tailWord_2945612
  simp only [CollatzResearch.WordTrace]
  refine ⟨53717647902279134661611545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71623530536372179548815393 53717647902279134661611545)
  ·
    refine ⟨40288235926709350996208659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53717647902279134661611545 40288235926709350996208659)
    ·
      refine ⟨60432353890064026494312989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40288235926709350996208659 60432353890064026494312989)
      ·
        refine ⟨22662132708774009935367371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60432353890064026494312989 22662132708774009935367371)
        ·
          refine ⟨33993199063161014903051057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22662132708774009935367371 33993199063161014903051057)
          ·
            refine ⟨25494899297370761177288293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33993199063161014903051057 25494899297370761177288293)
            ·
              refine ⟨4780293618257017720741555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25494899297370761177288293 4780293618257017720741555)
              ·
                refine ⟨7170440427385526581112333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4780293618257017720741555 7170440427385526581112333)
                ·
                  refine ⟨2688915160269572467917125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7170440427385526581112333 2688915160269572467917125)
                  ·
                    refine ⟨504171592550544837734461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2688915160269572467917125 504171592550544837734461)
                    ·
                      rfl

theorem cell23_2945612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 3, 4].length) (baseStart_2945612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945612 prefixEnd_2945612 := by exact prefixLift 2945612
  have htrace : WordTrace (prefixWord ++ tailWord_2945612) baseStart_2945612 baseEnd_2945612 := by
    simpa [prefixWord, tailWord_2945612, baseEnd_2945612] using wordTrace_append hprefix tailTrace_2945612
  have hstable : (prefixWord ++ tailWord_2945612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945612).length < 2 ^ (prefixWord ++ tailWord_2945612).sum := by decide
  have hdescent : baseEnd_2945612 < baseStart_2945612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945635 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 3]
def baseStart_2945635 : Nat := 118140960795 + 2945635 * 2 ^ 59
def prefixEnd_2945635 : Nat := 4983230072969 + 3 ^ 40 * 2945635 * 2
def baseEnd_2945635 : Nat := 1512526587706687923215777

theorem tailTrace_2945635 : CollatzResearch.WordTrace tailWord_2945635 prefixEnd_2945635 1512526587706687923215777 := by
  unfold tailWord_2945635
  simp only [CollatzResearch.WordTrace]
  refine ⟨107436134683474944251310359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71624089788983296167540239 107436134683474944251310359)
  ·
    refine ⟨161154202025212416376965539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107436134683474944251310359 161154202025212416376965539)
    ·
      refine ⟨241731303037818624565448309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161154202025212416376965539 241731303037818624565448309)
      ·
        refine ⟨22662309659795496053010779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 241731303037818624565448309 22662309659795496053010779)
        ·
          refine ⟨33993464489693244079516169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22662309659795496053010779 33993464489693244079516169)
          ·
            refine ⟨25495098367269933059637127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33993464489693244079516169 25495098367269933059637127)
            ·
              refine ⟨38242647550904899589455691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25495098367269933059637127 38242647550904899589455691)
              ·
                refine ⟨57363971326357349384183537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38242647550904899589455691 57363971326357349384183537)
                ·
                  refine ⟨43022978494768012038137653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57363971326357349384183537 43022978494768012038137653)
                  ·
                    refine ⟨4033404233884501128575405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43022978494768012038137653 4033404233884501128575405)
                    ·
                      refine ⟨1512526587706687923215777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4033404233884501128575405 1512526587706687923215777)
                      ·
                        rfl

theorem cell23_2945635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_2945635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945635 prefixEnd_2945635 := by exact prefixLift 2945635
  have htrace : WordTrace (prefixWord ++ tailWord_2945635) baseStart_2945635 baseEnd_2945635 := by
    simpa [prefixWord, tailWord_2945635, baseEnd_2945635] using wordTrace_append hprefix tailTrace_2945635
  have hstable : (prefixWord ++ tailWord_2945635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945635).length < 2 ^ (prefixWord ++ tailWord_2945635).sum := by decide
  have hdescent : baseEnd_2945635 < baseStart_2945635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945646 : List Nat := [4, 1, 2, 2, 2, 1, 3, 3, 1, 4]
def baseStart_2945646 : Nat := 118140960795 + 2945646 * 2 ^ 59
def prefixEnd_2945646 : Nat := 4983230072969 + 3 ^ 40 * 2945646 * 2
def baseEnd_2945646 : Nat := 504177411997962460059409

theorem tailTrace_2945646 : CollatzResearch.WordTrace tailWord_2945646 prefixEnd_2945646 504177411997962460059409 := by
  unfold tailWord_2945646
  simp only [CollatzResearch.WordTrace]
  refine ⟨13429566985804386641245099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71624357257623395419973861 13429566985804386641245099)
  ·
    refine ⟨20144350478706579961867649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13429566985804386641245099 20144350478706579961867649)
    ·
      refine ⟨15108262859029934971400737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20144350478706579961867649 15108262859029934971400737)
      ·
        refine ⟨11331197144272451228550553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15108262859029934971400737 11331197144272451228550553)
        ·
          refine ⟨8498397858204338421412915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11331197144272451228550553 8498397858204338421412915)
          ·
            refine ⟨12747596787306507632119373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8498397858204338421412915 12747596787306507632119373)
            ·
              refine ⟨4780348795239940362044765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12747596787306507632119373 4780348795239940362044765)
              ·
                refine ⟨1792630798214977635766787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4780348795239940362044765 1792630798214977635766787)
                ·
                  refine ⟨2688946197322466453650181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1792630798214977635766787 2688946197322466453650181)
                  ·
                    refine ⟨504177411997962460059409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2688946197322466453650181 504177411997962460059409)
                    ·
                      rfl

theorem cell23_2945646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_2945646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945646 prefixEnd_2945646 := by exact prefixLift 2945646
  have htrace : WordTrace (prefixWord ++ tailWord_2945646) baseStart_2945646 baseEnd_2945646 := by
    simpa [prefixWord, tailWord_2945646, baseEnd_2945646] using wordTrace_append hprefix tailTrace_2945646
  have hstable : (prefixWord ++ tailWord_2945646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945646).length < 2 ^ (prefixWord ++ tailWord_2945646).sum := by decide
  have hdescent : baseEnd_2945646 < baseStart_2945646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945669 : List Nat := [1, 3, 1, 1, 4, 2, 3, 1, 3, 1, 3]
def baseStart_2945669 : Nat := 118140960795 + 2945669 * 2 ^ 59
def prefixEnd_2945669 : Nat := 4983230072969 + 3 ^ 40 * 2945669 * 2
def baseEnd_2945669 : Nat := 1512544046048940790190621

theorem tailTrace_2945669 : CollatzResearch.WordTrace tailWord_2945669 prefixEnd_2945669 1512544046048940790190621 := by
  unfold tailWord_2945669
  simp only [CollatzResearch.WordTrace]
  refine ⟨107437374765351768058048061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71624916510234512038698707 107437374765351768058048061)
  ·
    refine ⟨40289015537006913021768023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107437374765351768058048061 40289015537006913021768023)
    ·
      refine ⟨60433523305510369532652035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40289015537006913021768023 60433523305510369532652035)
      ·
        refine ⟨90650284958265554298978053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60433523305510369532652035 90650284958265554298978053)
        ·
          refine ⟨16996928429674791431058385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90650284958265554298978053 16996928429674791431058385)
          ·
            refine ⟨12747696322256093573293789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16996928429674791431058385 12747696322256093573293789)
            ·
              refine ⟨4780386120846035089985171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12747696322256093573293789 4780386120846035089985171)
              ·
                refine ⟨7170579181269052634977757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4780386120846035089985171 7170579181269052634977757)
                ·
                  refine ⟨2688967192975894738116659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7170579181269052634977757 2688967192975894738116659)
                  ·
                    refine ⟨4033450789463842107174989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2688967192975894738116659 4033450789463842107174989)
                    ·
                      refine ⟨1512544046048940790190621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4033450789463842107174989 1512544046048940790190621)
                      ·
                        rfl

theorem cell23_2945669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 1, 3].length) (baseStart_2945669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945669 prefixEnd_2945669 := by exact prefixLift 2945669
  have htrace : WordTrace (prefixWord ++ tailWord_2945669) baseStart_2945669 baseEnd_2945669 := by
    simpa [prefixWord, tailWord_2945669, baseEnd_2945669] using wordTrace_append hprefix tailTrace_2945669
  have hstable : (prefixWord ++ tailWord_2945669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945669).length < 2 ^ (prefixWord ++ tailWord_2945669).sum := by decide
  have hdescent : baseEnd_2945669 < baseStart_2945669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945696 : List Nat := [2, 1, 1, 4, 4, 1, 2, 1, 2, 3, 2]
def baseStart_2945696 : Nat := 118140960795 + 2945696 * 2 ^ 59
def prefixEnd_2945696 : Nat := 4983230072969 + 3 ^ 40 * 2945696 * 2
def baseEnd_2945696 : Nat := 1512557910026612184552997

theorem tailTrace_2945696 : CollatzResearch.WordTrace tailWord_2945696 prefixEnd_2945696 1512557910026612184552997 := by
  unfold tailWord_2945696
  simp only [CollatzResearch.WordTrace]
  refine ⟨53719179768126975834640471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71625573024169301112853961 53719179768126975834640471)
  ·
    refine ⟨80578769652190463751960707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53719179768126975834640471 80578769652190463751960707)
    ·
      refine ⟨120868154478285695627941061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80578769652190463751960707 120868154478285695627941061)
      ·
        refine ⟨22662778964678567930238949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120868154478285695627941061 22662778964678567930238949)
        ·
          refine ⟨4249271055877231486919803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22662778964678567930238949 4249271055877231486919803)
          ·
            refine ⟨6373906583815847230379705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4249271055877231486919803 6373906583815847230379705)
            ·
              refine ⟨4780429937861885422784779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6373906583815847230379705 4780429937861885422784779)
              ·
                refine ⟨7170644906792828134177169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4780429937861885422784779 7170644906792828134177169)
                ·
                  refine ⟨5377983680094621100632877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7170644906792828134177169 5377983680094621100632877)
                  ·
                    refine ⟨2016743880035482912737329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5377983680094621100632877 2016743880035482912737329)
                    ·
                      refine ⟨1512557910026612184552997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2016743880035482912737329 1512557910026612184552997)
                      ·
                        rfl

theorem cell23_2945696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_2945696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945696 prefixEnd_2945696 := by exact prefixLift 2945696
  have htrace : WordTrace (prefixWord ++ tailWord_2945696) baseStart_2945696 baseEnd_2945696 := by
    simpa [prefixWord, tailWord_2945696, baseEnd_2945696] using wordTrace_append hprefix tailTrace_2945696
  have hstable : (prefixWord ++ tailWord_2945696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945696).length < 2 ^ (prefixWord ++ tailWord_2945696).sum := by decide
  have hdescent : baseEnd_2945696 < baseStart_2945696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945705 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 3, 2, 4]
def baseStart_2945705 : Nat := 118140960795 + 2945705 * 2 ^ 59
def prefixEnd_2945705 : Nat := 4983230072969 + 3 ^ 40 * 2945705 * 2
def baseEnd_2945705 : Nat := 1512562531352502649340455

theorem tailTrace_2945705 : CollatzResearch.WordTrace tailWord_2945705 prefixEnd_2945705 1512562531352502649340455 := by
  unfold tailWord_2945705
  simp only [CollatzResearch.WordTrace]
  refine ⟨107438687793221346206358569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71625791862147564137572379 107438687793221346206358569)
  ·
    refine ⟨80579015844916009654768927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107438687793221346206358569 80579015844916009654768927)
    ·
      refine ⟨120868523767374014482153391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80579015844916009654768927 120868523767374014482153391)
      ·
        refine ⟨181302785651061021723230087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120868523767374014482153391 181302785651061021723230087)
        ·
          refine ⟨271954178476591532584845131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181302785651061021723230087 271954178476591532584845131)
          ·
            refine ⟨407931267714887298877267697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271954178476591532584845131 407931267714887298877267697)
            ·
              refine ⟨305948450786165474157950773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 407931267714887298877267697 305948450786165474157950773)
              ·
                refine ⟨28682667261203013202307885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 305948450786165474157950773 28682667261203013202307885)
                ·
                  refine ⟨10756000222951129950865457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28682667261203013202307885 10756000222951129950865457)
                  ·
                    refine ⟨8067000167213347463149093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10756000222951129950865457 8067000167213347463149093)
                    ·
                      refine ⟨1512562531352502649340455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8067000167213347463149093 1512562531352502649340455)
                      ·
                        rfl

theorem cell23_2945705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 2, 4].length) (baseStart_2945705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945705 prefixEnd_2945705 := by exact prefixLift 2945705
  have htrace : WordTrace (prefixWord ++ tailWord_2945705) baseStart_2945705 baseEnd_2945705 := by
    simpa [prefixWord, tailWord_2945705, baseEnd_2945705] using wordTrace_append hprefix tailTrace_2945705
  have hstable : (prefixWord ++ tailWord_2945705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945705).length < 2 ^ (prefixWord ++ tailWord_2945705).sum := by decide
  have hdescent : baseEnd_2945705 < baseStart_2945705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945726 : List Nat := [4, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2]
def baseStart_2945726 : Nat := 118140960795 + 2945726 * 2 ^ 59
def prefixEnd_2945726 : Nat := 4983230072969 + 3 ^ 40 * 2945726 * 2
def baseEnd_2945726 : Nat := 1512573314446247067177859

theorem tailTrace_2945726 : CollatzResearch.WordTrace tailWord_2945726 prefixEnd_2945726 1512573314446247067177859 := by
  unfold tailWord_2945726
  simp only [CollatzResearch.WordTrace]
  refine ⟨13429931715768158349109129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71626302484096844528582021 13429931715768158349109129)
  ·
    refine ⟨10072448786826118761831847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13429931715768158349109129 10072448786826118761831847)
    ·
      refine ⟨15108673180239178142747771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10072448786826118761831847 15108673180239178142747771)
      ·
        refine ⟨22663009770358767214121657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15108673180239178142747771 22663009770358767214121657)
        ·
          refine ⟨16997257327769075410591243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22663009770358767214121657 16997257327769075410591243)
          ·
            refine ⟨25495885991653613115886865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16997257327769075410591243 25495885991653613115886865)
            ·
              refine ⟨19121914493740209836915149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25495885991653613115886865 19121914493740209836915149)
              ·
                refine ⟨7170717935152578688843181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19121914493740209836915149 7170717935152578688843181)
                ·
                  refine ⟨2689019225682217008316193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7170717935152578688843181 2689019225682217008316193)
                  ·
                    refine ⟨2016764419261662756237145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2689019225682217008316193 2016764419261662756237145)
                    ·
                      refine ⟨1512573314446247067177859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2016764419261662756237145 1512573314446247067177859)
                      ·
                        rfl

theorem cell23_2945726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_2945726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945726 prefixEnd_2945726 := by exact prefixLift 2945726
  have htrace : WordTrace (prefixWord ++ tailWord_2945726) baseStart_2945726 baseEnd_2945726 := by
    simpa [prefixWord, tailWord_2945726, baseEnd_2945726] using wordTrace_append hprefix tailTrace_2945726
  have hstable : (prefixWord ++ tailWord_2945726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945726).length < 2 ^ (prefixWord ++ tailWord_2945726).sum := by decide
  have hdescent : baseEnd_2945726 < baseStart_2945726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945732 : List Nat := [2, 3, 3, 1, 1, 2, 3, 8]
def baseStart_2945732 : Nat := 118140960795 + 2945732 * 2 ^ 59
def prefixEnd_2945732 : Nat := 4983230072969 + 3 ^ 40 * 2945732 * 2
def baseEnd_2945732 : Nat := 56021347975191631248253

theorem tailTrace_2945732 : CollatzResearch.WordTrace tailWord_2945732 prefixEnd_2945732 56021347975191631248253 := by
  unfold tailWord_2945732
  simp only [CollatzResearch.WordTrace]
  refine ⟨53719836282061764908795725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71626448376082353211727633 53719836282061764908795725)
  ·
    refine ⟨20144938605773161840798397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53719836282061764908795725 20144938605773161840798397)
    ·
      refine ⟨7554351977164935690299399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20144938605773161840798397 7554351977164935690299399)
      ·
        refine ⟨11331527965747403535449099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7554351977164935690299399 11331527965747403535449099)
        ·
          refine ⟨16997291948621105303173649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11331527965747403535449099 16997291948621105303173649)
          ·
            refine ⟨12747968961465828977380237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16997291948621105303173649 12747968961465828977380237)
            ·
              refine ⟨4780488360549685866517589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12747968961465828977380237 4780488360549685866517589)
              ·
                refine ⟨56021347975191631248253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4780488360549685866517589 56021347975191631248253)
                ·
                  rfl

theorem cell23_2945732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 8].length) (baseStart_2945732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945732 prefixEnd_2945732 := by exact prefixLift 2945732
  have htrace : WordTrace (prefixWord ++ tailWord_2945732) baseStart_2945732 baseEnd_2945732 := by
    simpa [prefixWord, tailWord_2945732, baseEnd_2945732] using wordTrace_append hprefix tailTrace_2945732
  have hstable : (prefixWord ++ tailWord_2945732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945732).length < 2 ^ (prefixWord ++ tailWord_2945732).sum := by decide
  have hdescent : baseEnd_2945732 < baseStart_2945732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945745 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 2, 7]
def baseStart_2945745 : Nat := 118140960795 + 2945745 * 2 ^ 59
def prefixEnd_2945745 : Nat := 4983230072969 + 3 ^ 40 * 2945745 * 2
def baseEnd_2945745 : Nat := 504194356859560830946757

theorem tailTrace_2945745 : CollatzResearch.WordTrace tailWord_2945745 prefixEnd_2945745 504194356859560830946757 := by
  unfold tailWord_2945745
  simp only [CollatzResearch.WordTrace]
  refine ⟨107440146713076433037814689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71626764475384288691876459 107440146713076433037814689)
  ·
    refine ⟨80580110034807324778361017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107440146713076433037814689 80580110034807324778361017)
    ·
      refine ⟨60435082526105493583770763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80580110034807324778361017 60435082526105493583770763)
      ·
        refine ⟨90652623789158240375656145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60435082526105493583770763 90652623789158240375656145)
        ·
          refine ⟨67989467841868680281742109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90652623789158240375656145 67989467841868680281742109)
          ·
            refine ⟨25496050440700755105653291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67989467841868680281742109 25496050440700755105653291)
            ·
              refine ⟨38244075661051132658479937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25496050440700755105653291 38244075661051132658479937)
              ·
                refine ⟨28683056745788349493859953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38244075661051132658479937 28683056745788349493859953)
                ·
                  refine ⟨21512292559341262120394965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28683056745788349493859953 21512292559341262120394965)
                  ·
                    refine ⟨504194356859560830946757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21512292559341262120394965 504194356859560830946757)
                    ·
                      rfl

theorem cell23_2945745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_2945745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945745 prefixEnd_2945745 := by exact prefixLift 2945745
  have htrace : WordTrace (prefixWord ++ tailWord_2945745) baseStart_2945745 baseEnd_2945745 := by
    simpa [prefixWord, tailWord_2945745, baseEnd_2945745] using wordTrace_append hprefix tailTrace_2945745
  have hstable : (prefixWord ++ tailWord_2945745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945745).length < 2 ^ (prefixWord ++ tailWord_2945745).sum := by decide
  have hdescent : baseEnd_2945745 < baseStart_2945745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945763 : List Nat := [1, 1, 1, 7, 1, 3, 2, 1, 1, 2, 3]
def baseStart_2945763 : Nat := 118140960795 + 2945763 * 2 ^ 59
def prefixEnd_2945763 : Nat := 4983230072969 + 3 ^ 40 * 2945763 * 2
def baseEnd_2945763 : Nat := 1512592313230463422415189

theorem tailTrace_2945763 : CollatzResearch.WordTrace tailWord_2945763 prefixEnd_2945763 1512592313230463422415189 := by
  unfold tailWord_2945763
  simp only [CollatzResearch.WordTrace]
  refine ⟨107440803227011222111969943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71627202151340814741313295 107440803227011222111969943)
  ·
    refine ⟨161161204840516833167954915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107440803227011222111969943 161161204840516833167954915)
    ·
      refine ⟨241741807260775249751932373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161161204840516833167954915 241741807260775249751932373)
      ·
        refine ⟨5665823607674419916060915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 241741807260775249751932373 5665823607674419916060915)
        ·
          refine ⟨8498735411511629874091373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5665823607674419916060915 8498735411511629874091373)
          ·
            refine ⟨3187025779316861202784265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8498735411511629874091373 3187025779316861202784265)
            ·
              refine ⟨2390269334487645902088199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3187025779316861202784265 2390269334487645902088199)
              ·
                refine ⟨3585404001731468853132299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2390269334487645902088199 3585404001731468853132299)
                ·
                  refine ⟨5378106002597203279698449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3585404001731468853132299 5378106002597203279698449)
                  ·
                    refine ⟨4033579501947902459773837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5378106002597203279698449 4033579501947902459773837)
                    ·
                      refine ⟨1512592313230463422415189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4033579501947902459773837 1512592313230463422415189)
                      ·
                        rfl

theorem cell23_2945763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_2945763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945763 prefixEnd_2945763 := by exact prefixLift 2945763
  have htrace : WordTrace (prefixWord ++ tailWord_2945763) baseStart_2945763 baseEnd_2945763 := by
    simpa [prefixWord, tailWord_2945763, baseEnd_2945763] using wordTrace_append hprefix tailTrace_2945763
  have hstable : (prefixWord ++ tailWord_2945763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945763).length < 2 ^ (prefixWord ++ tailWord_2945763).sum := by decide
  have hdescent : baseEnd_2945763 < baseStart_2945763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945802 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_2945802 : Nat := 118140960795 + 2945802 * 2 ^ 59
def prefixEnd_2945802 : Nat := 4983230072969 + 3 ^ 40 * 2945802 * 2
def baseEnd_2945802 : Nat := 1512612338975988769827509

theorem tailTrace_2945802 : CollatzResearch.WordTrace tailWord_2945802 prefixEnd_2945802 1512612338975988769827509 := by
  unfold tailWord_2945802
  simp only [CollatzResearch.WordTrace]
  refine ⟨26860556418467482943159915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71628150449246621181759773 26860556418467482943159915)
  ·
    refine ⟨40290834627701224414739873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26860556418467482943159915 40290834627701224414739873)
    ·
      refine ⟨30218125970775918311054905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40290834627701224414739873 30218125970775918311054905)
      ·
        refine ⟨22663594478081938733291179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30218125970775918311054905 22663594478081938733291179)
        ·
          refine ⟨33995391717122908099936769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22663594478081938733291179 33995391717122908099936769)
          ·
            refine ⟨25496543787842181074952577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33995391717122908099936769 25496543787842181074952577)
            ·
              refine ⟨19122407840881635806214433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25496543787842181074952577 19122407840881635806214433)
              ·
                refine ⟨14341805880661226854660825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19122407840881635806214433 14341805880661226854660825)
                ·
                  refine ⟨10756354410495920140995619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14341805880661226854660825 10756354410495920140995619)
                  ·
                    refine ⟨16134531615743880211493429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10756354410495920140995619 16134531615743880211493429)
                    ·
                      refine ⟨1512612338975988769827509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16134531615743880211493429 1512612338975988769827509)
                      ·
                        rfl

theorem cell23_2945802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_2945802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945802 prefixEnd_2945802 := by exact prefixLift 2945802
  have htrace : WordTrace (prefixWord ++ tailWord_2945802) baseStart_2945802 baseEnd_2945802 := by
    simpa [prefixWord, tailWord_2945802, baseEnd_2945802] using wordTrace_append hprefix tailTrace_2945802
  have hstable : (prefixWord ++ tailWord_2945802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945802).length < 2 ^ (prefixWord ++ tailWord_2945802).sum := by decide
  have hdescent : baseEnd_2945802 < baseStart_2945802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945832 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_2945832 : Nat := 118140960795 + 2945832 * 2 ^ 59
def prefixEnd_2945832 : Nat := 4983230072969 + 3 ^ 40 * 2945832 * 2
def baseEnd_2945832 : Nat := 1512627743395623652452371

theorem tailTrace_2945832 : CollatzResearch.WordTrace tailWord_2945832 prefixEnd_2945832 1512627743395623652452371 := by
  unfold tailWord_2945832
  simp only [CollatzResearch.WordTrace]
  refine ⟨53721659931880623448115875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71628879909174164597487833 53721659931880623448115875)
  ·
    refine ⟨80582489897820935172173813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53721659931880623448115875 80582489897820935172173813)
    ·
      refine ⟨7554608427920712672391295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80582489897820935172173813 7554608427920712672391295)
      ·
        refine ⟨11331912641881069008586943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7554608427920712672391295 11331912641881069008586943)
        ·
          refine ⟨16997868962821603512880415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11331912641881069008586943 16997868962821603512880415)
          ·
            refine ⟨25496803444232405269320623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16997868962821603512880415 25496803444232405269320623)
            ·
              refine ⟨38245205166348607903980935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25496803444232405269320623 38245205166348607903980935)
              ·
                refine ⟨57367807749522911855971403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38245205166348607903980935 57367807749522911855971403)
                ·
                  refine ⟨86051711624284367783957105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57367807749522911855971403 86051711624284367783957105)
                  ·
                    refine ⟨64538783718213275837967829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86051711624284367783957105 64538783718213275837967829)
                    ·
                      refine ⟨1512627743395623652452371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64538783718213275837967829 1512627743395623652452371)
                      ·
                        rfl

theorem cell23_2945832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_2945832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945832 prefixEnd_2945832 := by exact prefixLift 2945832
  have htrace : WordTrace (prefixWord ++ tailWord_2945832) baseStart_2945832 baseEnd_2945832 := by
    simpa [prefixWord, tailWord_2945832, baseEnd_2945832] using wordTrace_append hprefix tailTrace_2945832
  have hstable : (prefixWord ++ tailWord_2945832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945832).length < 2 ^ (prefixWord ++ tailWord_2945832).sum := by decide
  have hdescent : baseEnd_2945832 < baseStart_2945832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945852 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 6, 5]
def baseStart_2945852 : Nat := 118140960795 + 2945852 * 2 ^ 59
def prefixEnd_2945852 : Nat := 4983230072969 + 3 ^ 40 * 2945852 * 2
def baseEnd_2945852 : Nat := 504212671002904524734093

theorem tailTrace_2945852 : CollatzResearch.WordTrace tailWord_2945852 prefixEnd_2945852 504212671002904524734093 := by
  unfold tailWord_2945852
  simp only [CollatzResearch.WordTrace]
  refine ⟨53722024661844395155979905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71629366215792526874639873 53722024661844395155979905)
  ·
    refine ⟨40291518496383296366984929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53722024661844395155979905 40291518496383296366984929)
    ·
      refine ⟨30218638872287472275238697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40291518496383296366984929 30218638872287472275238697)
      ·
        refine ⟨22663979154215604206429023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30218638872287472275238697 22663979154215604206429023)
        ·
          refine ⟨33995968731323406309643535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22663979154215604206429023 33995968731323406309643535)
          ·
            refine ⟨50993953096985109464465303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33995968731323406309643535 50993953096985109464465303)
            ·
              refine ⟨76490929645477664196697955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50993953096985109464465303 76490929645477664196697955)
              ·
                refine ⟨114736394468216496295046933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76490929645477664196697955 114736394468216496295046933)
                ·
                  refine ⟨5378268490697648263830325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 114736394468216496295046933 5378268490697648263830325)
                  ·
                    refine ⟨504212671002904524734093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5378268490697648263830325 504212671002904524734093)
                    ·
                      rfl

theorem cell23_2945852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_2945852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945852 prefixEnd_2945852 := by exact prefixLift 2945852
  have htrace : WordTrace (prefixWord ++ tailWord_2945852) baseStart_2945852 baseEnd_2945852 := by
    simpa [prefixWord, tailWord_2945852, baseEnd_2945852] using wordTrace_append hprefix tailTrace_2945852
  have hstable : (prefixWord ++ tailWord_2945852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945852).length < 2 ^ (prefixWord ++ tailWord_2945852).sum := by decide
  have hdescent : baseEnd_2945852 < baseStart_2945852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945872 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 4]
def baseStart_2945872 : Nat := 118140960795 + 2945872 * 2 ^ 59
def prefixEnd_2945872 : Nat := 4983230072969 + 3 ^ 40 * 2945872 * 2
def baseEnd_2945872 : Nat := 1512648282621803495952187

theorem tailTrace_2945872 : CollatzResearch.WordTrace tailWord_2945872 prefixEnd_2945872 1512648282621803495952187 := by
  unfold tailWord_2945872
  simp only [CollatzResearch.WordTrace]
  refine ⟨53722389391808166863843935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71629852522410889151791913 53722389391808166863843935)
  ·
    refine ⟨80583584087712250295765903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53722389391808166863843935 80583584087712250295765903)
    ·
      refine ⟨120875376131568375443648855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80583584087712250295765903 120875376131568375443648855)
      ·
        refine ⟨181313064197352563165473283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120875376131568375443648855 181313064197352563165473283)
        ·
          refine ⟨271969596296028844748209925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181313064197352563165473283 271969596296028844748209925)
          ·
            refine ⟨50994299305505408390289361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 271969596296028844748209925 50994299305505408390289361)
            ·
              refine ⟨38245724479129056292717021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50994299305505408390289361 38245724479129056292717021)
              ·
                refine ⟨14342146679673396109768883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38245724479129056292717021 14342146679673396109768883)
                ·
                  refine ⟨21513220019510094164653325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14342146679673396109768883 21513220019510094164653325)
                  ·
                    refine ⟨8067457507316285311744997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21513220019510094164653325 8067457507316285311744997)
                    ·
                      refine ⟨1512648282621803495952187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8067457507316285311744997 1512648282621803495952187)
                      ·
                        rfl

theorem cell23_2945872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 4].length) (baseStart_2945872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945872 prefixEnd_2945872 := by exact prefixLift 2945872
  have htrace : WordTrace (prefixWord ++ tailWord_2945872) baseStart_2945872 baseEnd_2945872 := by
    simpa [prefixWord, tailWord_2945872, baseEnd_2945872] using wordTrace_append hprefix tailTrace_2945872
  have hstable : (prefixWord ++ tailWord_2945872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945872).length < 2 ^ (prefixWord ++ tailWord_2945872).sum := by decide
  have hdescent : baseEnd_2945872 < baseStart_2945872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945890 : List Nat := [3, 3, 2, 1, 3, 2, 2, 2, 5]
def baseStart_2945890 : Nat := 118140960795 + 2945890 * 2 ^ 59
def prefixEnd_2945890 : Nat := 4983230072969 + 3 ^ 40 * 2945890 * 2
def baseEnd_2945890 : Nat := 168073058363731602836345

theorem tailTrace_2945890 : CollatzResearch.WordTrace tailWord_2945890 prefixEnd_2945890 168073058363731602836345 := by
  unfold tailWord_2945890
  simp only [CollatzResearch.WordTrace]
  refine ⟨26861358824387780700460781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71630290198367415201228749 26861358824387780700460781)
  ·
    refine ⟨10073009559145417762672793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26861358824387780700460781 10073009559145417762672793)
    ·
      refine ⟨7554757169359063322004595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10073009559145417762672793 7554757169359063322004595)
      ·
        refine ⟨11332135754038594983006893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7554757169359063322004595 11332135754038594983006893)
        ·
          refine ⟨4249550907764473118627585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11332135754038594983006893 4249550907764473118627585)
          ·
            refine ⟨3187163180823354838970689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4249550907764473118627585 3187163180823354838970689)
            ·
              refine ⟨2390372385617516129228017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3187163180823354838970689 2390372385617516129228017)
              ·
                refine ⟨1792779289213137096921013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2390372385617516129228017 1792779289213137096921013)
                ·
                  refine ⟨168073058363731602836345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1792779289213137096921013 168073058363731602836345)
                  ·
                    rfl

theorem cell23_2945890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_2945890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945890 prefixEnd_2945890 := by exact prefixLift 2945890
  have htrace : WordTrace (prefixWord ++ tailWord_2945890) baseStart_2945890 baseEnd_2945890 := by
    simpa [prefixWord, tailWord_2945890, baseEnd_2945890] using wordTrace_append hprefix tailTrace_2945890
  have hstable : (prefixWord ++ tailWord_2945890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945890).length < 2 ^ (prefixWord ++ tailWord_2945890).sum := by decide
  have hdescent : baseEnd_2945890 < baseStart_2945890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945976 : List Nat := [2, 1, 2, 1, 2, 5, 2, 2, 1, 5]
def baseStart_2945976 : Nat := 118140960795 + 2945976 * 2 ^ 59
def prefixEnd_2945976 : Nat := 4983230072969 + 3 ^ 40 * 2945976 * 2
def baseEnd_2945976 : Nat := 504233894869957029683903

theorem tailTrace_2945976 : CollatzResearch.WordTrace tailWord_2945976 prefixEnd_2945976 504233894869957029683903 := by
  unfold tailWord_2945976
  simp only [CollatzResearch.WordTrace]
  refine ⟨53724285987619779744736891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71632381316826372992982521 53724285987619779744736891)
  ·
    refine ⟨80586428981429669617105337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53724285987619779744736891 80586428981429669617105337)
    ·
      refine ⟨60439821736072252212829003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80586428981429669617105337 60439821736072252212829003)
      ·
        refine ⟨90659732604108378319243505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60439821736072252212829003 90659732604108378319243505)
        ·
          refine ⟨67994799453081283739432629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90659732604108378319243505 67994799453081283739432629)
          ·
            refine ⟨6374512448726370350571809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67994799453081283739432629 6374512448726370350571809)
            ·
              refine ⟨4780884336544777762928857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6374512448726370350571809 4780884336544777762928857)
              ·
                refine ⟨3585663252408583322196643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4780884336544777762928857 3585663252408583322196643)
                ·
                  refine ⟨5378494878612874983294965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3585663252408583322196643 5378494878612874983294965)
                  ·
                    refine ⟨504233894869957029683903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5378494878612874983294965 504233894869957029683903)
                    ·
                      rfl

theorem cell23_2945976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 1, 5].length) (baseStart_2945976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945976 prefixEnd_2945976 := by exact prefixLift 2945976
  have htrace : WordTrace (prefixWord ++ tailWord_2945976) baseStart_2945976 baseEnd_2945976 := by
    simpa [prefixWord, tailWord_2945976, baseEnd_2945976] using wordTrace_append hprefix tailTrace_2945976
  have hstable : (prefixWord ++ tailWord_2945976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945976).length < 2 ^ (prefixWord ++ tailWord_2945976).sum := by decide
  have hdescent : baseEnd_2945976 < baseStart_2945976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945996 : List Nat := [2, 2, 1, 4, 1, 1, 1, 5, 1, 1, 4]
def baseStart_2945996 : Nat := 118140960795 + 2945996 * 2 ^ 59
def prefixEnd_2945996 : Nat := 4983230072969 + 3 ^ 40 * 2945996 * 2
def baseEnd_2945996 : Nat := 1512711954222961010801617

theorem tailTrace_2945996 : CollatzResearch.WordTrace tailWord_2945996 prefixEnd_2945996 1512711954222961010801617 := by
  unfold tailWord_2945996
  simp only [CollatzResearch.WordTrace]
  refine ⟨53724650717583551452600921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71632867623444735270134561 53724650717583551452600921)
  ·
    refine ⟨40293488038187663589450691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53724650717583551452600921 40293488038187663589450691)
    ·
      refine ⟨60440232057281495384176037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40293488038187663589450691 60440232057281495384176037)
      ·
        refine ⟨11332543510740280384533007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60440232057281495384176037 11332543510740280384533007)
        ·
          refine ⟨16998815266110420576799511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11332543510740280384533007 16998815266110420576799511)
          ·
            refine ⟨25498222899165630865199267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16998815266110420576799511 25498222899165630865199267)
            ·
              refine ⟨38247334348748446297798901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25498222899165630865199267 38247334348748446297798901)
              ·
                refine ⟨3585687595195166840418647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38247334348748446297798901 3585687595195166840418647)
                ·
                  refine ⟨5378531392792750260627971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3585687595195166840418647 5378531392792750260627971)
                  ·
                    refine ⟨8067797089189125390941957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5378531392792750260627971 8067797089189125390941957)
                    ·
                      refine ⟨1512711954222961010801617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8067797089189125390941957 1512711954222961010801617)
                      ·
                        rfl

theorem cell23_2945996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_2945996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945996 prefixEnd_2945996 := by exact prefixLift 2945996
  have htrace : WordTrace (prefixWord ++ tailWord_2945996) baseStart_2945996 baseEnd_2945996 := by
    simpa [prefixWord, tailWord_2945996, baseEnd_2945996] using wordTrace_append hprefix tailTrace_2945996
  have hstable : (prefixWord ++ tailWord_2945996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945996).length < 2 ^ (prefixWord ++ tailWord_2945996).sum := by decide
  have hdescent : baseEnd_2945996 < baseStart_2945996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2945999 : List Nat := [1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 5]
def baseStart_2945999 : Nat := 118140960795 + 2945999 * 2 ^ 59
def prefixEnd_2945999 : Nat := 4983230072969 + 3 ^ 40 * 2945999 * 2
def baseEnd_2945999 : Nat := 1512713494664924499064103

theorem tailTrace_2945999 : CollatzResearch.WordTrace tailWord_2945999 prefixEnd_2945999 1512713494664924499064103 := by
  unfold tailWord_2945999
  simp only [CollatzResearch.WordTrace]
  refine ⟨107449410854156234417561051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71632940569437489611707367 107449410854156234417561051)
  ·
    refine ⟨161174116281234351626341577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107449410854156234417561051 161174116281234351626341577)
    ·
      refine ⟨120880587210925763719756183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161174116281234351626341577 120880587210925763719756183)
      ·
        refine ⟨181320880816388645579634275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120880587210925763719756183 181320880816388645579634275)
        ·
          refine ⟨271981321224582968369451413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181320880816388645579634275 271981321224582968369451413)
          ·
            refine ⟨12749124432402326642318035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 271981321224582968369451413 12749124432402326642318035)
            ·
              refine ⟨19123686648603489963477053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12749124432402326642318035 19123686648603489963477053)
              ·
                refine ⟨7171382493226308736303895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19123686648603489963477053 7171382493226308736303895)
                ·
                  refine ⟨10757073739839463104455843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7171382493226308736303895 10757073739839463104455843)
                  ·
                    refine ⟨16135610609759194656683765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10757073739839463104455843 16135610609759194656683765)
                    ·
                      refine ⟨1512713494664924499064103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16135610609759194656683765 1512713494664924499064103)
                      ·
                        rfl

theorem cell23_2945999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 5].length) (baseStart_2945999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2945999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2945999 prefixEnd_2945999 := by exact prefixLift 2945999
  have htrace : WordTrace (prefixWord ++ tailWord_2945999) baseStart_2945999 baseEnd_2945999 := by
    simpa [prefixWord, tailWord_2945999, baseEnd_2945999] using wordTrace_append hprefix tailTrace_2945999
  have hstable : (prefixWord ++ tailWord_2945999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2945999).length < 2 ^ (prefixWord ++ tailWord_2945999).sum := by decide
  have hdescent : baseEnd_2945999 < baseStart_2945999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2945999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946009 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 1, 1, 6]
def baseStart_2946009 : Nat := 118140960795 + 2946009 * 2 ^ 59
def prefixEnd_2946009 : Nat := 4983230072969 + 3 ^ 40 * 2946009 * 2
def baseEnd_2946009 : Nat := 1512718629471469459939057

theorem tailTrace_2946009 : CollatzResearch.WordTrace tailWord_2946009 prefixEnd_2946009 1512718629471469459939057 := by
  unfold tailWord_2946009
  simp only [CollatzResearch.WordTrace]
  refine ⟨107449775584120006125425081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71633183722746670750283387 107449775584120006125425081)
  ·
    refine ⟨80587331688090004594068811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107449775584120006125425081 80587331688090004594068811)
    ·
      refine ⟨120880997532135006891103217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80587331688090004594068811 120880997532135006891103217)
      ·
        refine ⟨90660748149101255168327413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120880997532135006891103217 90660748149101255168327413)
        ·
          refine ⟨8499445138978242672030695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90660748149101255168327413 8499445138978242672030695)
          ·
            refine ⟨12749167708467364008046043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8499445138978242672030695 12749167708467364008046043)
            ·
              refine ⟨19123751562701046012069065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12749167708467364008046043 19123751562701046012069065)
              ·
                refine ⟨14342813672025784509051799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19123751562701046012069065 14342813672025784509051799)
                ·
                  refine ⟨21514220508038676763577699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14342813672025784509051799 21514220508038676763577699)
                  ·
                    refine ⟨32271330762058015145366549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21514220508038676763577699 32271330762058015145366549)
                    ·
                      refine ⟨1512718629471469459939057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32271330762058015145366549 1512718629471469459939057)
                      ·
                        rfl

theorem cell23_2946009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_2946009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946009 prefixEnd_2946009 := by exact prefixLift 2946009
  have htrace : WordTrace (prefixWord ++ tailWord_2946009) baseStart_2946009 baseEnd_2946009 := by
    simpa [prefixWord, tailWord_2946009, baseEnd_2946009] using wordTrace_append hprefix tailTrace_2946009
  have hstable : (prefixWord ++ tailWord_2946009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946009).length < 2 ^ (prefixWord ++ tailWord_2946009).sum := by decide
  have hdescent : baseEnd_2946009 < baseStart_2946009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946019 : List Nat := [1, 1, 1, 6, 1, 1, 4, 8]
def baseStart_2946019 : Nat := 118140960795 + 2946019 * 2 ^ 59
def prefixEnd_2946019 : Nat := 4983230072969 + 3 ^ 40 * 2946019 * 2
def baseEnd_2946019 : Nat := 56026806084370904474593

theorem tailTrace_2946019 : CollatzResearch.WordTrace tailWord_2946019 prefixEnd_2946019 56026806084370904474593 := by
  unfold tailWord_2946019
  simp only [CollatzResearch.WordTrace]
  refine ⟨107450140314083777833289111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71633426876055851888859407 107450140314083777833289111)
  ·
    refine ⟨161175210471125666749933667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107450140314083777833289111 161175210471125666749933667)
    ·
      refine ⟨241762815706688500124900501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161175210471125666749933667 241762815706688500124900501)
      ·
        refine ⟨11332631986251023443354711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 241762815706688500124900501 11332631986251023443354711)
        ·
          refine ⟨16998947979376535165032067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11332631986251023443354711 16998947979376535165032067)
          ·
            refine ⟨25498421969064802747548101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16998947979376535165032067 25498421969064802747548101)
            ·
              refine ⟨4780954119199650515165269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25498421969064802747548101 4780954119199650515165269)
              ·
                refine ⟨56026806084370904474593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4780954119199650515165269 56026806084370904474593)
                ·
                  rfl

theorem cell23_2946019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 8].length) (baseStart_2946019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946019 prefixEnd_2946019 := by exact prefixLift 2946019
  have htrace : WordTrace (prefixWord ++ tailWord_2946019) baseStart_2946019 baseEnd_2946019 := by
    simpa [prefixWord, tailWord_2946019, baseEnd_2946019] using wordTrace_append hprefix tailTrace_2946019
  have hstable : (prefixWord ++ tailWord_2946019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946019).length < 2 ^ (prefixWord ++ tailWord_2946019).sum := by decide
  have hdescent : baseEnd_2946019 < baseStart_2946019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946023 : List Nat := [1, 1, 5, 2, 2, 2, 1, 3, 2, 4]
def baseStart_2946023 : Nat := 118140960795 + 2946023 * 2 ^ 59
def prefixEnd_2946023 : Nat := 4983230072969 + 3 ^ 40 * 2946023 * 2
def baseEnd_2946023 : Nat := 504241939400210801721331

theorem tailTrace_2946023 : CollatzResearch.WordTrace tailWord_2946023 prefixEnd_2946023 504241939400210801721331 := by
  unfold tailWord_2946023
  simp only [CollatzResearch.WordTrace]
  refine ⟨107450286206069286516434723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71633524137379524344289815 107450286206069286516434723)
  ·
    refine ⟨161175429309103929774652085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107450286206069286516434723 161175429309103929774652085)
    ·
      refine ⟨15110196497728493416373633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161175429309103929774652085 15110196497728493416373633)
      ·
        refine ⟨11332647373296370062280225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15110196497728493416373633 11332647373296370062280225)
        ·
          refine ⟨8499485529972277546710169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11332647373296370062280225 8499485529972277546710169)
          ·
            refine ⟨6374614147479208160032627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8499485529972277546710169 6374614147479208160032627)
            ·
              refine ⟨9561921221218812240048941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6374614147479208160032627 9561921221218812240048941)
              ·
                refine ⟨3585720457957054590018353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9561921221218812240048941 3585720457957054590018353)
                ·
                  refine ⟨2689290343467790942513765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3585720457957054590018353 2689290343467790942513765)
                  ·
                    refine ⟨504241939400210801721331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2689290343467790942513765 504241939400210801721331)
                    ·
                      rfl

theorem cell23_2946023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_2946023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946023 prefixEnd_2946023 := by exact prefixLift 2946023
  have htrace : WordTrace (prefixWord ++ tailWord_2946023) baseStart_2946023 baseEnd_2946023 := by
    simpa [prefixWord, tailWord_2946023, baseEnd_2946023] using wordTrace_append hprefix tailTrace_2946023
  have hstable : (prefixWord ++ tailWord_2946023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946023).length < 2 ^ (prefixWord ++ tailWord_2946023).sum := by decide
  have hdescent : baseEnd_2946023 < baseStart_2946023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946030 : List Nat := [4, 1, 2, 1, 4, 2, 1, 2, 1, 1, 4]
def baseStart_2946030 : Nat := 118140960795 + 2946030 * 2 ^ 59
def prefixEnd_2946030 : Nat := 4983230072969 + 3 ^ 40 * 2946030 * 2
def baseEnd_2946030 : Nat := 1512729412565213877776461

theorem tailTrace_2946030 : CollatzResearch.WordTrace tailWord_2946030 prefixEnd_2946030 1512729412565213877776461 := by
  unfold tailWord_2946030
  simp only [CollatzResearch.WordTrace]
  refine ⟨13431317689630490838992443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71633694344695951141293029 13431317689630490838992443)
  ·
    refine ⟨20146976534445736258488665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13431317689630490838992443 20146976534445736258488665)
    ·
      refine ⟨15110232400834302193866499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20146976534445736258488665 15110232400834302193866499)
      ·
        refine ⟨22665348601251453290799749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15110232400834302193866499 22665348601251453290799749)
        ·
          refine ⟨4249752862734647492024953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22665348601251453290799749 4249752862734647492024953)
          ·
            refine ⟨3187314647050985619018715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4249752862734647492024953 3187314647050985619018715)
            ·
              refine ⟨4780971970576478428528073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3187314647050985619018715 4780971970576478428528073)
              ·
                refine ⟨3585728977932358821396055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4780971970576478428528073 3585728977932358821396055)
                ·
                  refine ⟨5378593466898538232094083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3585728977932358821396055 5378593466898538232094083)
                  ·
                    refine ⟨8067890200347807348141125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5378593466898538232094083 8067890200347807348141125)
                    ·
                      refine ⟨1512729412565213877776461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8067890200347807348141125 1512729412565213877776461)
                      ·
                        rfl

theorem cell23_2946030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_2946030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946030 prefixEnd_2946030 := by exact prefixLift 2946030
  have htrace : WordTrace (prefixWord ++ tailWord_2946030) baseStart_2946030 baseEnd_2946030 := by
    simpa [prefixWord, tailWord_2946030, baseEnd_2946030] using wordTrace_append hprefix tailTrace_2946030
  have hstable : (prefixWord ++ tailWord_2946030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946030).length < 2 ^ (prefixWord ++ tailWord_2946030).sum := by decide
  have hdescent : baseEnd_2946030 < baseStart_2946030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946033 : List Nat := [1, 2, 2, 2, 4, 1, 3, 2, 1, 2, 3]
def baseStart_2946033 : Nat := 118140960795 + 2946033 * 2 ^ 59
def prefixEnd_2946033 : Nat := 4983230072969 + 3 ^ 40 * 2946033 * 2
def baseEnd_2946033 : Nat := 1512730953007177366038947

theorem tailTrace_2946033 : CollatzResearch.WordTrace tailWord_2946033 prefixEnd_2946033 1512730953007177366038947 := by
  unfold tailWord_2946033
  simp only [CollatzResearch.WordTrace]
  refine ⟨107450650936033058224298753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71633767290688705482865835 107450650936033058224298753)
  ·
    refine ⟨80587988202024793668224065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107450650936033058224298753 80587988202024793668224065)
    ·
      refine ⟨60440991151518595251168049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80587988202024793668224065 60440991151518595251168049)
      ·
        refine ⟨45330743363638946438376037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60440991151518595251168049 45330743363638946438376037)
        ·
          refine ⟨8499514380682302457195507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45330743363638946438376037 8499514380682302457195507)
          ·
            refine ⟨12749271571023453685793261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8499514380682302457195507 12749271571023453685793261)
            ·
              refine ⟨4780976839133795132172473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12749271571023453685793261 4780976839133795132172473)
              ·
                refine ⟨3585732629350346349129355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4780976839133795132172473 3585732629350346349129355)
                ·
                  refine ⟨5378598944025519523694033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3585732629350346349129355 5378598944025519523694033)
                  ·
                    refine ⟨4033949208019139642770525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5378598944025519523694033 4033949208019139642770525)
                    ·
                      refine ⟨1512730953007177366038947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4033949208019139642770525 1512730953007177366038947)
                      ·
                        rfl

theorem cell23_2946033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_2946033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946033 prefixEnd_2946033 := by exact prefixLift 2946033
  have htrace : WordTrace (prefixWord ++ tailWord_2946033) baseStart_2946033 baseEnd_2946033 := by
    simpa [prefixWord, tailWord_2946033, baseEnd_2946033] using wordTrace_append hprefix tailTrace_2946033
  have hstable : (prefixWord ++ tailWord_2946033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946033).length < 2 ^ (prefixWord ++ tailWord_2946033).sum := by decide
  have hdescent : baseEnd_2946033 < baseStart_2946033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946079 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 1, 8]
def baseStart_2946079 : Nat := 118140960795 + 2946079 * 2 ^ 59
def prefixEnd_2946079 : Nat := 4983230072969 + 3 ^ 40 * 2946079 * 2
def baseEnd_2946079 : Nat := 504251524372428062021245

theorem tailTrace_2946079 : CollatzResearch.WordTrace tailWord_2946079 prefixEnd_2946079 504251524372428062021245 := by
  unfold tailWord_2946079
  simp only [CollatzResearch.WordTrace]
  refine ⟨107452328693866408080473291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71634885795910938720315527 107452328693866408080473291)
  ·
    refine ⟨161178493040799612120709937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107452328693866408080473291 161178493040799612120709937)
    ·
      refine ⟨120883869780599709090532453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161178493040799612120709937 120883869780599709090532453)
      ·
        refine ⟨22665725583862445454474835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120883869780599709090532453 22665725583862445454474835)
        ·
          refine ⟨33998588375793668181712253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22665725583862445454474835 33998588375793668181712253)
          ·
            refine ⟨12749470640922625568142095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33998588375793668181712253 12749470640922625568142095)
            ·
              refine ⟨19124205961383938352213143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12749470640922625568142095 19124205961383938352213143)
              ·
                refine ⟨28686308942075907528319715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19124205961383938352213143 28686308942075907528319715)
                ·
                  refine ⟨43029463413113861292479573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28686308942075907528319715 43029463413113861292479573)
                  ·
                    refine ⟨504251524372428062021245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43029463413113861292479573 504251524372428062021245)
                    ·
                      rfl

theorem cell23_2946079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 8].length) (baseStart_2946079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946079 prefixEnd_2946079 := by exact prefixLift 2946079
  have htrace : WordTrace (prefixWord ++ tailWord_2946079) baseStart_2946079 baseEnd_2946079 := by
    simpa [prefixWord, tailWord_2946079, baseEnd_2946079] using wordTrace_append hprefix tailTrace_2946079
  have hstable : (prefixWord ++ tailWord_2946079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946079).length < 2 ^ (prefixWord ++ tailWord_2946079).sum := by decide
  have hdescent : baseEnd_2946079 < baseStart_2946079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946080 : List Nat := [2, 1, 1, 7, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2946080 : Nat := 118140960795 + 2946080 * 2 ^ 59
def prefixEnd_2946080 : Nat := 4983230072969 + 3 ^ 40 * 2946080 * 2
def baseEnd_2946080 : Nat := 1512755086597938682151231

theorem tailTrace_2946080 : CollatzResearch.WordTrace tailWord_2946080 prefixEnd_2946080 1512755086597938682151231 := by
  unfold tailWord_2946080
  simp only [CollatzResearch.WordTrace]
  refine ⟨53726182583431392625629847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71634910111241856834173129 53726182583431392625629847)
  ·
    refine ⟨80589273875147088938444771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53726182583431392625629847 80589273875147088938444771)
    ·
      refine ⟨120883910812720633407667157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80589273875147088938444771 120883910812720633407667157)
      ·
        refine ⟨2833216659673139845492199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 120883910812720633407667157 2833216659673139845492199)
        ·
          refine ⟨4249824989509709768238299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2833216659673139845492199 4249824989509709768238299)
          ·
            refine ⟨6374737484264564652357449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4249824989509709768238299 6374737484264564652357449)
            ·
              refine ⟨4781053113198423489268087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6374737484264564652357449 4781053113198423489268087)
              ·
                refine ⟨7171579669797635233902131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4781053113198423489268087 7171579669797635233902131)
                ·
                  refine ⟨10757369504696452850853197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7171579669797635233902131 10757369504696452850853197)
                  ·
                    refine ⟨4034013564261169819069949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10757369504696452850853197 4034013564261169819069949)
                    ·
                      refine ⟨1512755086597938682151231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4034013564261169819069949 1512755086597938682151231)
                      ·
                        rfl

theorem cell23_2946080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2946080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946080 prefixEnd_2946080 := by exact prefixLift 2946080
  have htrace : WordTrace (prefixWord ++ tailWord_2946080) baseStart_2946080 baseEnd_2946080 := by
    simpa [prefixWord, tailWord_2946080, baseEnd_2946080] using wordTrace_append hprefix tailTrace_2946080
  have hstable : (prefixWord ++ tailWord_2946080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946080).length < 2 ^ (prefixWord ++ tailWord_2946080).sum := by decide
  have hdescent : baseEnd_2946080 < baseStart_2946080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946099 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 4]
def baseStart_2946099 : Nat := 118140960795 + 2946099 * 2 ^ 59
def prefixEnd_2946099 : Nat := 4983230072969 + 3 ^ 40 * 2946099 * 2
def baseEnd_2946099 : Nat := 1512764842730374107813643

theorem tailTrace_2946099 : CollatzResearch.WordTrace tailWord_2946099 prefixEnd_2946099 1512764842730374107813643 := by
  unfold tailWord_2946099
  simp only [CollatzResearch.WordTrace]
  refine ⟨107453058153793951496201351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71635372102529300997467567 107453058153793951496201351)
  ·
    refine ⟨161179587230690927244302027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107453058153793951496201351 161179587230690927244302027)
    ·
      refine ⟨241769380846036390866453041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161179587230690927244302027 241769380846036390866453041)
      ·
        refine ⟨181327035634527293149839781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241769380846036390866453041 181327035634527293149839781)
        ·
          refine ⟨33998819181473867465594959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181327035634527293149839781 33998819181473867465594959)
          ·
            refine ⟨50998228772210801198392439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33998819181473867465594959 50998228772210801198392439)
            ·
              refine ⟨76497343158316201797588659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50998228772210801198392439 76497343158316201797588659)
              ·
                refine ⟨114746014737474302696382989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76497343158316201797588659 114746014737474302696382989)
                ·
                  refine ⟨43029755526552863511143621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114746014737474302696382989 43029755526552863511143621)
                  ·
                    refine ⟨8068079161228661908339429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43029755526552863511143621 8068079161228661908339429)
                    ·
                      refine ⟨1512764842730374107813643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8068079161228661908339429 1512764842730374107813643)
                      ·
                        rfl

theorem cell23_2946099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 4].length) (baseStart_2946099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946099 prefixEnd_2946099 := by exact prefixLift 2946099
  have htrace : WordTrace (prefixWord ++ tailWord_2946099) baseStart_2946099 baseEnd_2946099 := by
    simpa [prefixWord, tailWord_2946099, baseEnd_2946099] using wordTrace_append hprefix tailTrace_2946099
  have hstable : (prefixWord ++ tailWord_2946099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946099).length < 2 ^ (prefixWord ++ tailWord_2946099).sum := by decide
  have hdescent : baseEnd_2946099 < baseStart_2946099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946103 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 4, 2, 2]
def baseStart_2946103 : Nat := 118140960795 + 2946103 * 2 ^ 59
def prefixEnd_2946103 : Nat := 4983230072969 + 3 ^ 40 * 2946103 * 2
def baseEnd_2946103 : Nat := 1512766896652992092163625

theorem tailTrace_2946103 : CollatzResearch.WordTrace tailWord_2946103 prefixEnd_2946103 1512766896652992092163625 := by
  unfold tailWord_2946103
  simp only [CollatzResearch.WordTrace]
  refine ⟨107453204045779460179346963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71635469363852973452897975 107453204045779460179346963)
  ·
    refine ⟨161179806068669190269020445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107453204045779460179346963 161179806068669190269020445)
    ·
      refine ⟨60442427275750946350882667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161179806068669190269020445 60442427275750946350882667)
      ·
        refine ⟨90663640913626419526324001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60442427275750946350882667 90663640913626419526324001)
        ·
          refine ⟨67997730685219814644743001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90663640913626419526324001 67997730685219814644743001)
          ·
            refine ⟨50998298013914860983557251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67997730685219814644743001 50998298013914860983557251)
            ·
              refine ⟨76497447020872291475335877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50998298013914860983557251 76497447020872291475335877)
              ·
                refine ⟨14343271316413554651625477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76497447020872291475335877 14343271316413554651625477)
                ·
                  refine ⟨2689363371827541497179777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14343271316413554651625477 2689363371827541497179777)
                  ·
                    refine ⟨2017022528870656122884833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2689363371827541497179777 2017022528870656122884833)
                    ·
                      refine ⟨1512766896652992092163625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2017022528870656122884833 1512766896652992092163625)
                      ·
                        rfl

theorem cell23_2946103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 2, 2].length) (baseStart_2946103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946103 prefixEnd_2946103 := by exact prefixLift 2946103
  have htrace : WordTrace (prefixWord ++ tailWord_2946103) baseStart_2946103 baseEnd_2946103 := by
    simpa [prefixWord, tailWord_2946103, baseEnd_2946103] using wordTrace_append hprefix tailTrace_2946103
  have hstable : (prefixWord ++ tailWord_2946103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946103).length < 2 ^ (prefixWord ++ tailWord_2946103).sum := by decide
  have hdescent : baseEnd_2946103 < baseStart_2946103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946126 : List Nat := [4, 1, 1, 1, 1, 3, 4, 1, 7]
def baseStart_2946126 : Nat := 118140960795 + 2946126 * 2 ^ 59
def prefixEnd_2946126 : Nat := 4983230072969 + 3 ^ 40 * 2946126 * 2
def baseEnd_2946126 : Nat := 168086522967560611352891

theorem tailTrace_2946126 : CollatzResearch.WordTrace tailWord_2946126 prefixEnd_2946126 168086522967560611352891 := by
  unfold tailWord_2946126
  simp only [CollatzResearch.WordTrace]
  refine ⟨13431755365587016888429279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71636028616464090071622821 13431755365587016888429279)
  ·
    refine ⟨20147633048380525332643919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13431755365587016888429279 20147633048380525332643919)
    ·
      refine ⟨30221449572570787998965879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20147633048380525332643919 30221449572570787998965879)
      ·
        refine ⟨45332174358856181998448819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30221449572570787998965879 45332174358856181998448819)
        ·
          refine ⟨67998261538284272997673229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45332174358856181998448819 67998261538284272997673229)
          ·
            refine ⟨25499348076856602374127461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67998261538284272997673229 25499348076856602374127461)
            ·
              refine ⟨4781127764410612945148899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25499348076856602374127461 4781127764410612945148899)
              ·
                refine ⟨7171691646615919417723349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4781127764410612945148899 7171691646615919417723349)
                ·
                  refine ⟨168086522967560611352891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7171691646615919417723349 168086522967560611352891)
                  ·
                    rfl

theorem cell23_2946126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_2946126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946126 prefixEnd_2946126 := by exact prefixLift 2946126
  have htrace : WordTrace (prefixWord ++ tailWord_2946126) baseStart_2946126 baseEnd_2946126 := by
    simpa [prefixWord, tailWord_2946126, baseEnd_2946126] using wordTrace_append hprefix tailTrace_2946126
  have hstable : (prefixWord ++ tailWord_2946126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946126).length < 2 ^ (prefixWord ++ tailWord_2946126).sum := by decide
  have hdescent : baseEnd_2946126 < baseStart_2946126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946136 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 2, 3, 3]
def baseStart_2946136 : Nat := 118140960795 + 2946136 * 2 ^ 59
def prefixEnd_2946136 : Nat := 4983230072969 + 3 ^ 40 * 2946136 * 2
def baseEnd_2946136 : Nat := 1512783841514590463050973

theorem tailTrace_2946136 : CollatzResearch.WordTrace tailWord_2946136 prefixEnd_2946136 1512783841514590463050973 := by
  unfold tailWord_2946136
  simp only [CollatzResearch.WordTrace]
  refine ⟨53727203827329953407649131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71636271769773271210198841 53727203827329953407649131)
  ·
    refine ⟨80590805740994930111473697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53727203827329953407649131 80590805740994930111473697)
    ·
      refine ⟨60443104305746197583605273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80590805740994930111473697 60443104305746197583605273)
      ·
        refine ⟨45332328229309648187703955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60443104305746197583605273 45332328229309648187703955)
        ·
          refine ⟨67998492343964472281555933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45332328229309648187703955 67998492343964472281555933)
          ·
            refine ⟨25499434628986677105583475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67998492343964472281555933 25499434628986677105583475)
            ·
              refine ⟨38249151943480015658375213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25499434628986677105583475 38249151943480015658375213)
              ·
                refine ⟨14343431978805005871890705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38249151943480015658375213 14343431978805005871890705)
                ·
                  refine ⟨10757573984103754403918029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14343431978805005871890705 10757573984103754403918029)
                  ·
                    refine ⟨4034090244038907901469261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10757573984103754403918029 4034090244038907901469261)
                    ·
                      refine ⟨1512783841514590463050973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4034090244038907901469261 1512783841514590463050973)
                      ·
                        rfl

theorem cell23_2946136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_2946136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946136 prefixEnd_2946136 := by exact prefixLift 2946136
  have htrace : WordTrace (prefixWord ++ tailWord_2946136) baseStart_2946136 baseEnd_2946136 := by
    simpa [prefixWord, tailWord_2946136, baseEnd_2946136] using wordTrace_append hprefix tailTrace_2946136
  have hstable : (prefixWord ++ tailWord_2946136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946136).length < 2 ^ (prefixWord ++ tailWord_2946136).sum := by decide
  have hdescent : baseEnd_2946136 < baseStart_2946136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946156 : List Nat := [2, 2, 1, 1, 3, 2, 2, 3, 2, 5]
def baseStart_2946156 : Nat := 118140960795 + 2946156 * 2 ^ 59
def prefixEnd_2946156 : Nat := 4983230072969 + 3 ^ 40 * 2946156 * 2
def baseEnd_2946156 : Nat := 504264703709226794933627

theorem tailTrace_2946156 : CollatzResearch.WordTrace tailWord_2946156 prefixEnd_2946156 504264703709226794933627 := by
  unfold tailWord_2946156
  simp only [CollatzResearch.WordTrace]
  refine ⟨53727568557293725115513161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71636758076391633487350881 53727568557293725115513161)
  ·
    refine ⟨40295676417970293836634871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53727568557293725115513161 40295676417970293836634871)
    ·
      refine ⟨60443514626955440754952307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40295676417970293836634871 60443514626955440754952307)
      ·
        refine ⟨90665271940433161132428461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60443514626955440754952307 90665271940433161132428461)
        ·
          refine ⟨33999476977662435424660673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90665271940433161132428461 33999476977662435424660673)
          ·
            refine ⟨25499607733246826568495505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33999476977662435424660673 25499607733246826568495505)
            ·
              refine ⟨19124705799935119926371629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25499607733246826568495505 19124705799935119926371629)
              ·
                refine ⟨7171764674975669972389361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19124705799935119926371629 7171764674975669972389361)
                ·
                  refine ⟨5378823506231752479292021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7171764674975669972389361 5378823506231752479292021)
                  ·
                    refine ⟨504264703709226794933627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5378823506231752479292021 504264703709226794933627)
                    ·
                      rfl

theorem cell23_2946156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_2946156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946156 prefixEnd_2946156 := by exact prefixLift 2946156
  have htrace : WordTrace (prefixWord ++ tailWord_2946156) baseStart_2946156 baseEnd_2946156 := by
    simpa [prefixWord, tailWord_2946156, baseEnd_2946156] using wordTrace_append hprefix tailTrace_2946156
  have hstable : (prefixWord ++ tailWord_2946156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946156).length < 2 ^ (prefixWord ++ tailWord_2946156).sum := by decide
  have hdescent : baseEnd_2946156 < baseStart_2946156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946176 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 4]
def baseStart_2946176 : Nat := 118140960795 + 2946176 * 2 ^ 59
def prefixEnd_2946176 : Nat := 4983230072969 + 3 ^ 40 * 2946176 * 2
def baseEnd_2946176 : Nat := 1512804380740770306550789

theorem tailTrace_2946176 : CollatzResearch.WordTrace tailWord_2946176 prefixEnd_2946176 1512804380740770306550789 := by
  unfold tailWord_2946176
  simp only [CollatzResearch.WordTrace]
  refine ⟨53727933287257496823377191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71637244383009995764502921 53727933287257496823377191)
  ·
    refine ⟨80591899930886245235065787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53727933287257496823377191 80591899930886245235065787)
    ·
      refine ⟨120887849896329367852598681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80591899930886245235065787 120887849896329367852598681)
      ·
        refine ⟨90665887422247025889449011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120887849896329367852598681 90665887422247025889449011)
        ·
          refine ⟨135998831133370538834173517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90665887422247025889449011 135998831133370538834173517)
          ·
            refine ⟨50999561675013952062815069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135998831133370538834173517 50999561675013952062815069)
            ·
              refine ⟨19124835628130232023555651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50999561675013952062815069 19124835628130232023555651)
              ·
                refine ⟨28687253442195348035333477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19124835628130232023555651 28687253442195348035333477)
                ·
                  refine ⟨5378860020411627756625027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28687253442195348035333477 5378860020411627756625027)
                  ·
                    refine ⟨8068290030617441634937541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5378860020411627756625027 8068290030617441634937541)
                    ·
                      refine ⟨1512804380740770306550789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8068290030617441634937541 1512804380740770306550789)
                      ·
                        rfl

theorem cell23_2946176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_2946176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946176 prefixEnd_2946176 := by exact prefixLift 2946176
  have htrace : WordTrace (prefixWord ++ tailWord_2946176) baseStart_2946176 baseEnd_2946176 := by
    simpa [prefixWord, tailWord_2946176, baseEnd_2946176] using wordTrace_append hprefix tailTrace_2946176
  have hstable : (prefixWord ++ tailWord_2946176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946176).length < 2 ^ (prefixWord ++ tailWord_2946176).sum := by decide
  have hdescent : baseEnd_2946176 < baseStart_2946176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946213 : List Nat := [1, 3, 1, 2, 1, 4, 1, 3, 2, 2, 3]
def baseStart_2946213 : Nat := 118140960795 + 2946213 * 2 ^ 59
def prefixEnd_2946213 : Nat := 4983230072969 + 3 ^ 40 * 2946213 * 2
def baseEnd_2946213 : Nat := 1512823379524986661788119

theorem tailTrace_2946213 : CollatzResearch.WordTrace tailWord_2946213 prefixEnd_2946213 1512823379524986661788119 := by
  unfold tailWord_2946213
  simp only [CollatzResearch.WordTrace]
  refine ⟨107457216075380948965851293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71638144050253965977234195 107457216075380948965851293)
  ·
    refine ⟨40296456028267855862194235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107457216075380948965851293 40296456028267855862194235)
    ·
      refine ⟨60444684042401783793291353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40296456028267855862194235 60444684042401783793291353)
      ·
        refine ⟨45333513031801337844968515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60444684042401783793291353 45333513031801337844968515)
        ·
          refine ⟨68000269547702006767452773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45333513031801337844968515 68000269547702006767452773)
          ·
            refine ⟨12750050540194126268897395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68000269547702006767452773 12750050540194126268897395)
            ·
              refine ⟨19125075810291189403346093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12750050540194126268897395 19125075810291189403346093)
              ·
                refine ⟨7171903428859196026254785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19125075810291189403346093 7171903428859196026254785)
                ·
                  refine ⟨5378927571644397019691089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7171903428859196026254785 5378927571644397019691089)
                  ·
                    refine ⟨4034195678733297764768317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5378927571644397019691089 4034195678733297764768317)
                    ·
                      refine ⟨1512823379524986661788119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4034195678733297764768317 1512823379524986661788119)
                      ·
                        rfl

theorem cell23_2946213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_2946213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946213 prefixEnd_2946213 := by exact prefixLift 2946213
  have htrace : WordTrace (prefixWord ++ tailWord_2946213) baseStart_2946213 baseEnd_2946213 := by
    simpa [prefixWord, tailWord_2946213, baseEnd_2946213] using wordTrace_append hprefix tailTrace_2946213
  have hstable : (prefixWord ++ tailWord_2946213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946213).length < 2 ^ (prefixWord ++ tailWord_2946213).sum := by decide
  have hdescent : baseEnd_2946213 < baseStart_2946213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946233 : List Nat := [1, 2, 1, 4, 1, 4, 2, 2, 6]
def baseStart_2946233 : Nat := 118140960795 + 2946233 * 2 ^ 59
def prefixEnd_2946233 : Nat := 4983230072969 + 3 ^ 40 * 2946233 * 2
def baseEnd_2946233 : Nat := 168092627682008509282003

theorem tailTrace_2946233 : CollatzResearch.WordTrace tailWord_2946233 prefixEnd_2946233 168092627682008509282003 := by
  unfold tailWord_2946233
  simp only [CollatzResearch.WordTrace]
  refine ⟨107457945535308492381579353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71638630356872328254386235 107457945535308492381579353)
  ·
    refine ⟨80593459151481369286184515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107457945535308492381579353 80593459151481369286184515)
    ·
      refine ⟨120890188727222053929276773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80593459151481369286184515 120890188727222053929276773)
      ·
        refine ⟨22666910386354135111739395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120890188727222053929276773 22666910386354135111739395)
        ·
          refine ⟨34000365579531202667609093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22666910386354135111739395 34000365579531202667609093)
          ·
            refine ⟨6375068546162100500176705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34000365579531202667609093 6375068546162100500176705)
            ·
              refine ⟨4781301409621575375132529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6375068546162100500176705 4781301409621575375132529)
              ·
                refine ⟨3585976057216181531349397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4781301409621575375132529 3585976057216181531349397)
                ·
                  refine ⟨168092627682008509282003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3585976057216181531349397 168092627682008509282003)
                  ·
                    rfl

theorem cell23_2946233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 6].length) (baseStart_2946233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946233 prefixEnd_2946233 := by exact prefixLift 2946233
  have htrace : WordTrace (prefixWord ++ tailWord_2946233) baseStart_2946233 baseEnd_2946233 := by
    simpa [prefixWord, tailWord_2946233, baseEnd_2946233] using wordTrace_append hprefix tailTrace_2946233
  have hstable : (prefixWord ++ tailWord_2946233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946233).length < 2 ^ (prefixWord ++ tailWord_2946233).sum := by decide
  have hdescent : baseEnd_2946233 < baseStart_2946233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946237 : List Nat := [1, 4, 1, 2, 1, 1, 6, 2, 1, 4]
def baseStart_2946237 : Nat := 118140960795 + 2946237 * 2 ^ 59
def prefixEnd_2946237 : Nat := 4983230072969 + 3 ^ 40 * 2946237 * 2
def baseEnd_2946237 : Nat := 504278567686898189296003

theorem tailTrace_2946237 : CollatzResearch.WordTrace tailWord_2946237 prefixEnd_2946237 504278567686898189296003 := by
  unfold tailWord_2946237
  simp only [CollatzResearch.WordTrace]
  refine ⟨107458091427294001064724965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71638727618196000709816643 107458091427294001064724965)
  ·
    refine ⟨20148392142617625199635931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107458091427294001064724965 20148392142617625199635931)
    ·
      refine ⟨30222588213926437799453897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20148392142617625199635931 30222588213926437799453897)
      ·
        refine ⟨22666941160444828349590423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30222588213926437799453897 22666941160444828349590423)
        ·
          refine ⟨34000411740667242524385635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22666941160444828349590423 34000411740667242524385635)
          ·
            refine ⟨51000617611000863786578453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34000411740667242524385635 51000617611000863786578453)
            ·
              refine ⟨2390653950515665489995865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51000617611000863786578453 2390653950515665489995865)
              ·
                refine ⟨1792990462886749117496899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2390653950515665489995865 1792990462886749117496899)
                ·
                  refine ⟨2689485694330123676245349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1792990462886749117496899 2689485694330123676245349)
                  ·
                    refine ⟨504278567686898189296003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2689485694330123676245349 504278567686898189296003)
                    ·
                      rfl

theorem cell23_2946237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_2946237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946237 prefixEnd_2946237 := by exact prefixLift 2946237
  have htrace : WordTrace (prefixWord ++ tailWord_2946237) baseStart_2946237 baseEnd_2946237 := by
    simpa [prefixWord, tailWord_2946237, baseEnd_2946237] using wordTrace_append hprefix tailTrace_2946237
  have hstable : (prefixWord ++ tailWord_2946237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946237).length < 2 ^ (prefixWord ++ tailWord_2946237).sum := by decide
  have hdescent : baseEnd_2946237 < baseStart_2946237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946296 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 2, 6, 4]
def baseStart_2946296 : Nat := 118140960795 + 2946296 * 2 ^ 59
def prefixEnd_2946296 : Nat := 4983230072969 + 3 ^ 40 * 2946296 * 2
def baseEnd_2946296 : Nat := 1512865998419309837050237

theorem tailTrace_2946296 : CollatzResearch.WordTrace tailWord_2946296 prefixEnd_2946296 1512865998419309837050237 := by
  unfold tailWord_2946296
  simp only [CollatzResearch.WordTrace]
  refine ⟨53730121667040127070561371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71640162222720169427415161 53730121667040127070561371)
  ·
    refine ⟨80595182500560190605842057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53730121667040127070561371 80595182500560190605842057)
    ·
      refine ⟨60446386875420142954381543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80595182500560190605842057 60446386875420142954381543)
      ·
        refine ⟨90669580313130214431572315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60446386875420142954381543 90669580313130214431572315)
        ·
          refine ⟨136004370469695321647358473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90669580313130214431572315 136004370469695321647358473)
          ·
            refine ⟨102003277852271491235518855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136004370469695321647358473 102003277852271491235518855)
            ·
              refine ⟨153004916778407236853278283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102003277852271491235518855 153004916778407236853278283)
              ·
                refine ⟨229507375167610855279917425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153004916778407236853278283 229507375167610855279917425)
                ·
                  refine ⟨172130531375708141459938069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229507375167610855279917425 172130531375708141459938069)
                  ·
                    refine ⟨8068618658236319130934597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 172130531375708141459938069 8068618658236319130934597)
                    ·
                      refine ⟨1512865998419309837050237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8068618658236319130934597 1512865998419309837050237)
                      ·
                        rfl

theorem cell23_2946296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_2946296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946296 prefixEnd_2946296 := by exact prefixLift 2946296
  have htrace : WordTrace (prefixWord ++ tailWord_2946296) baseStart_2946296 baseEnd_2946296 := by
    simpa [prefixWord, tailWord_2946296, baseEnd_2946296] using wordTrace_append hprefix tailTrace_2946296
  have hstable : (prefixWord ++ tailWord_2946296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946296).length < 2 ^ (prefixWord ++ tailWord_2946296).sum := by decide
  have hdescent : baseEnd_2946296 < baseStart_2946296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946303 : List Nat := [1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 5]
def baseStart_2946303 : Nat := 118140960795 + 2946303 * 2 ^ 59
def prefixEnd_2946303 : Nat := 4983230072969 + 3 ^ 40 * 2946303 * 2
def baseEnd_2946303 : Nat := 1512869592783891309662705

theorem tailTrace_2946303 : CollatzResearch.WordTrace tailWord_2946303 prefixEnd_2946303 1512869592783891309662705 := by
  unfold tailWord_2946303
  simp only [CollatzResearch.WordTrace]
  refine ⟨107460498645054894336627563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71640332430036596224418375 107460498645054894336627563)
  ·
    refine ⟨161190747967582341504941345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107460498645054894336627563 161190747967582341504941345)
    ·
      refine ⟨120893060975686756128706009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161190747967582341504941345 120893060975686756128706009)
      ·
        refine ⟨90669795731765067096529507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120893060975686756128706009 90669795731765067096529507)
        ·
          refine ⟨136004693597647600644794261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90669795731765067096529507 136004693597647600644794261)
          ·
            refine ⟨6375220012389731280224731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 136004693597647600644794261 6375220012389731280224731)
            ·
              refine ⟨9562830018584596920337097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6375220012389731280224731 9562830018584596920337097)
              ·
                refine ⟨7172122513938447690252823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9562830018584596920337097 7172122513938447690252823)
                ·
                  refine ⟨10758183770907671535379235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7172122513938447690252823 10758183770907671535379235)
                  ·
                    refine ⟨16137275656361507303068853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10758183770907671535379235 16137275656361507303068853)
                    ·
                      refine ⟨1512869592783891309662705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16137275656361507303068853 1512869592783891309662705)
                      ·
                        rfl

theorem cell23_2946303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_2946303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946303 prefixEnd_2946303 := by exact prefixLift 2946303
  have htrace : WordTrace (prefixWord ++ tailWord_2946303) baseStart_2946303 baseEnd_2946303 := by
    simpa [prefixWord, tailWord_2946303, baseEnd_2946303] using wordTrace_append hprefix tailTrace_2946303
  have hstable : (prefixWord ++ tailWord_2946303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946303).length < 2 ^ (prefixWord ++ tailWord_2946303).sum := by decide
  have hdescent : baseEnd_2946303 < baseStart_2946303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946360 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 3, 3, 2]
def baseStart_2946360 : Nat := 118140960795 + 2946360 * 2 ^ 59
def prefixEnd_2946360 : Nat := 4983230072969 + 3 ^ 40 * 2946360 * 2
def baseEnd_2946360 : Nat := 1512898861181197586649943

theorem tailTrace_2946360 : CollatzResearch.WordTrace tailWord_2946360 prefixEnd_2946360 1512898861181197586649943 := by
  unfold tailWord_2946360
  simp only [CollatzResearch.WordTrace]
  refine ⟨53731288802924196535726267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71641718403898928714301689 53731288802924196535726267)
  ·
    refine ⟨80596933204386294803589401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53731288802924196535726267 80596933204386294803589401)
    ·
      refine ⟨60447699903289721102692051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80596933204386294803589401 60447699903289721102692051)
      ·
        refine ⟨90671549854934581654038077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60447699903289721102692051 90671549854934581654038077)
        ·
          refine ⟨34001831195600468120264279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90671549854934581654038077 34001831195600468120264279)
          ·
            refine ⟨51002746793400702180396419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34001831195600468120264279 51002746793400702180396419)
            ·
              refine ⟨76504120190101053270594629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51002746793400702180396419 76504120190101053270594629)
              ·
                refine ⟨14344522535643947488236493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76504120190101053270594629 14344522535643947488236493)
                ·
                  refine ⟨5379195950866480308088685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14344522535643947488236493 5379195950866480308088685)
                  ·
                    refine ⟨2017198481574930115533257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5379195950866480308088685 2017198481574930115533257)
                    ·
                      refine ⟨1512898861181197586649943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2017198481574930115533257 1512898861181197586649943)
                      ·
                        rfl

theorem cell23_2946360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 3, 3, 2].length) (baseStart_2946360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946360 prefixEnd_2946360 := by exact prefixLift 2946360
  have htrace : WordTrace (prefixWord ++ tailWord_2946360) baseStart_2946360 baseEnd_2946360 := by
    simpa [prefixWord, tailWord_2946360, baseEnd_2946360] using wordTrace_append hprefix tailTrace_2946360
  have hstable : (prefixWord ++ tailWord_2946360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946360).length < 2 ^ (prefixWord ++ tailWord_2946360).sum := by decide
  have hdescent : baseEnd_2946360 < baseStart_2946360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946361 : List Nat := [1, 2, 1, 6, 3, 1, 2, 1, 2, 4]
def baseStart_2946361 : Nat := 118140960795 + 2946361 * 2 ^ 59
def prefixEnd_2946361 : Nat := 4983230072969 + 3 ^ 40 * 2946361 * 2
def baseEnd_2946361 : Nat := 504299791553950694245813

theorem tailTrace_2946361 : CollatzResearch.WordTrace tailWord_2946361 prefixEnd_2946361 504299791553950694245813 := by
  unfold tailWord_2946361
  simp only [CollatzResearch.WordTrace]
  refine ⟨107462614078844770242238937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71641742719229846828159291 107462614078844770242238937)
  ·
    refine ⟨80596960559133577681679203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107462614078844770242238937 80596960559133577681679203)
    ·
      refine ⟨120895440838700366522518805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80596960559133577681679203 120895440838700366522518805)
      ·
        refine ⟨5666973789314079680743069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 120895440838700366522518805 5666973789314079680743069)
        ·
          refine ⟨2125115170992779880278651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5666973789314079680743069 2125115170992779880278651)
          ·
            refine ⟨3187672756489169820417977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2125115170992779880278651 3187672756489169820417977)
            ·
              refine ⟨2390754567366877365313483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3187672756489169820417977 2390754567366877365313483)
              ·
                refine ⟨3586131851050316047970225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2390754567366877365313483 3586131851050316047970225)
                ·
                  refine ⟨2689598888287737035977669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3586131851050316047970225 2689598888287737035977669)
                  ·
                    refine ⟨504299791553950694245813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2689598888287737035977669 504299791553950694245813)
                    ·
                      rfl

theorem cell23_2946361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 2, 4].length) (baseStart_2946361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946361 prefixEnd_2946361 := by exact prefixLift 2946361
  have htrace : WordTrace (prefixWord ++ tailWord_2946361) baseStart_2946361 baseEnd_2946361 := by
    simpa [prefixWord, tailWord_2946361, baseEnd_2946361] using wordTrace_append hprefix tailTrace_2946361
  have hstable : (prefixWord ++ tailWord_2946361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946361).length < 2 ^ (prefixWord ++ tailWord_2946361).sum := by decide
  have hdescent : baseEnd_2946361 < baseStart_2946361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946367 : List Nat := [1, 1, 2, 2, 4, 3, 1, 3, 2, 1, 3]
def baseStart_2946367 : Nat := 118140960795 + 2946367 * 2 ^ 59
def prefixEnd_2946367 : Nat := 4983230072969 + 3 ^ 40 * 2946367 * 2
def baseEnd_2946367 : Nat := 1512902455545779059262411

theorem tailTrace_2946367 : CollatzResearch.WordTrace tailWord_2946367 prefixEnd_2946367 1512902455545779059262411 := by
  unfold tailWord_2946367
  simp only [CollatzResearch.WordTrace]
  refine ⟨107462832916823033266957355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71641888611215355511304903 107462832916823033266957355)
  ·
    refine ⟨161194249375234549900436033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107462832916823033266957355 161194249375234549900436033)
    ·
      refine ⟨120895687031425912425327025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161194249375234549900436033 120895687031425912425327025)
      ·
        refine ⟨90671765273569434318995269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120895687031425912425327025 90671765273569434318995269)
        ·
          refine ⟨17000955988794268934811613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90671765273569434318995269 17000955988794268934811613)
          ·
            refine ⟨6375358495797850850554355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17000955988794268934811613 6375358495797850850554355)
            ·
              refine ⟨9563037743696776275831533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6375358495797850850554355 9563037743696776275831533)
              ·
                refine ⟨3586139153886291103436825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9563037743696776275831533 3586139153886291103436825)
                ·
                  refine ⟨2689604365414718327577619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3586139153886291103436825 2689604365414718327577619)
                  ·
                    refine ⟨4034406548122077491366429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2689604365414718327577619 4034406548122077491366429)
                    ·
                      refine ⟨1512902455545779059262411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4034406548122077491366429 1512902455545779059262411)
                      ·
                        rfl

theorem cell23_2946367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 1, 3].length) (baseStart_2946367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946367 prefixEnd_2946367 := by exact prefixLift 2946367
  have htrace : WordTrace (prefixWord ++ tailWord_2946367) baseStart_2946367 baseEnd_2946367 := by
    simpa [prefixWord, tailWord_2946367, baseEnd_2946367] using wordTrace_append hprefix tailTrace_2946367
  have hstable : (prefixWord ++ tailWord_2946367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946367).length < 2 ^ (prefixWord ++ tailWord_2946367).sum := by decide
  have hdescent : baseEnd_2946367 < baseStart_2946367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946377 : List Nat := [1, 2, 1, 1, 2, 3, 5, 2, 1, 3, 2]
def baseStart_2946377 : Nat := 118140960795 + 2946377 * 2 ^ 59
def prefixEnd_2946377 : Nat := 4983230072969 + 3 ^ 40 * 2946377 * 2
def baseEnd_2946377 : Nat := 1512907590352324020137365

theorem tailTrace_2946377 : CollatzResearch.WordTrace tailWord_2946377 prefixEnd_2946377 1512907590352324020137365 := by
  unfold tailWord_2946377
  simp only [CollatzResearch.WordTrace]
  refine ⟨107463197646786804974821385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71642131764524536649880923 107463197646786804974821385)
  ·
    refine ⟨80597398235090103731116039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107463197646786804974821385 80597398235090103731116039)
    ·
      refine ⟨120896097352635155596674059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80597398235090103731116039 120896097352635155596674059)
      ·
        refine ⟨181344146028952733395011089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120896097352635155596674059 181344146028952733395011089)
        ·
          refine ⟨136008109521714550046258317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181344146028952733395011089 136008109521714550046258317)
          ·
            refine ⟨51003041070642956267346869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136008109521714550046258317 51003041070642956267346869)
            ·
              refine ⟨4781535100372777150063769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51003041070642956267346869 4781535100372777150063769)
              ·
                refine ⟨3586151325279582862547827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4781535100372777150063769 3586151325279582862547827)
                ·
                  refine ⟨5379226987919374293821741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3586151325279582862547827 5379226987919374293821741)
                  ·
                    refine ⟨2017210120469765360183153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5379226987919374293821741 2017210120469765360183153)
                    ·
                      refine ⟨1512907590352324020137365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2017210120469765360183153 1512907590352324020137365)
                      ·
                        rfl

theorem cell23_2946377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 3, 2].length) (baseStart_2946377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946377 prefixEnd_2946377 := by exact prefixLift 2946377
  have htrace : WordTrace (prefixWord ++ tailWord_2946377) baseStart_2946377 baseEnd_2946377 := by
    simpa [prefixWord, tailWord_2946377, baseEnd_2946377] using wordTrace_append hprefix tailTrace_2946377
  have hstable : (prefixWord ++ tailWord_2946377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946377).length < 2 ^ (prefixWord ++ tailWord_2946377).sum := by decide
  have hdescent : baseEnd_2946377 < baseStart_2946377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946393 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 2, 1, 5]
def baseStart_2946393 : Nat := 118140960795 + 2946393 * 2 ^ 59
def prefixEnd_2946393 : Nat := 4983230072969 + 3 ^ 40 * 2946393 * 2
def baseEnd_2946393 : Nat := 1512915806042795957537291

theorem tailTrace_2946393 : CollatzResearch.WordTrace tailWord_2946393 prefixEnd_2946393 1512915806042795957537291 := by
  unfold tailWord_2946393
  simp only [CollatzResearch.WordTrace]
  refine ⟨107463781214728839707403833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71642520809819226471602555 107463781214728839707403833)
  ·
    refine ⟨80597835911046629780552875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107463781214728839707403833 80597835911046629780552875)
    ·
      refine ⟨120896753866569944670829313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80597835911046629780552875 120896753866569944670829313)
      ·
        refine ⟨90672565399927458503121985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120896753866569944670829313 90672565399927458503121985)
        ·
          refine ⟨68004424049945593877341489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90672565399927458503121985 68004424049945593877341489)
          ·
            refine ⟨51003318037459195408006117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68004424049945593877341489 51003318037459195408006117)
            ·
              refine ⟨9563122132023599139001147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51003318037459195408006117 9563122132023599139001147)
              ·
                refine ⟨14344683198035398708501721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9563122132023599139001147 14344683198035398708501721)
                ·
                  refine ⟨10758512398526549031376291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14344683198035398708501721 10758512398526549031376291)
                  ·
                    refine ⟨16137768597789823547064437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10758512398526549031376291 16137768597789823547064437)
                    ·
                      refine ⟨1512915806042795957537291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16137768597789823547064437 1512915806042795957537291)
                      ·
                        rfl

theorem cell23_2946393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_2946393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946393 prefixEnd_2946393 := by exact prefixLift 2946393
  have htrace : WordTrace (prefixWord ++ tailWord_2946393) baseStart_2946393 baseEnd_2946393 := by
    simpa [prefixWord, tailWord_2946393, baseEnd_2946393] using wordTrace_append hprefix tailTrace_2946393
  have hstable : (prefixWord ++ tailWord_2946393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946393).length < 2 ^ (prefixWord ++ tailWord_2946393).sum := by decide
  have hdescent : baseEnd_2946393 < baseStart_2946393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946443 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 1, 7]
def baseStart_2946443 : Nat := 118140960795 + 2946443 * 2 ^ 59
def prefixEnd_2946443 : Nat := 4983230072969 + 3 ^ 40 * 2946443 * 2
def baseEnd_2946443 : Nat := 504313826691840253970687

theorem tailTrace_2946443 : CollatzResearch.WordTrace tailWord_2946443 prefixEnd_2946443 504313826691840253970687 := by
  unfold tailWord_2946443
  simp only [CollatzResearch.WordTrace]
  refine ⟨107465604864547698246723983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71643736576365132164482655 107465604864547698246723983)
  ·
    refine ⟨161198407296821547370085975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107465604864547698246723983 161198407296821547370085975)
    ·
      refine ⟨241797610945232321055128963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161198407296821547370085975 241797610945232321055128963)
      ·
        refine ⟨362696416417848481582693445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241797610945232321055128963 362696416417848481582693445)
        ·
          refine ⟨68005578078346590296755021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 362696416417848481582693445 68005578078346590296755021)
          ·
            refine ⟨25502091779379971361283133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68005578078346590296755021 25502091779379971361283133)
            ·
              refine ⟨9563284417267489260481175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25502091779379971361283133 9563284417267489260481175)
              ·
                refine ⟨14344926625901233890721763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9563284417267489260481175 14344926625901233890721763)
                ·
                  refine ⟨21517389938851850836082645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14344926625901233890721763 21517389938851850836082645)
                  ·
                    refine ⟨504313826691840253970687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21517389938851850836082645 504313826691840253970687)
                    ·
                      rfl

theorem cell23_2946443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 7].length) (baseStart_2946443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946443 prefixEnd_2946443 := by exact prefixLift 2946443
  have htrace : WordTrace (prefixWord ++ tailWord_2946443) baseStart_2946443 baseEnd_2946443 := by
    simpa [prefixWord, tailWord_2946443, baseEnd_2946443] using wordTrace_append hprefix tailTrace_2946443
  have hstable : (prefixWord ++ tailWord_2946443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946443).length < 2 ^ (prefixWord ++ tailWord_2946443).sum := by decide
  have hdescent : baseEnd_2946443 < baseStart_2946443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946453 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_2946453 : Nat := 118140960795 + 2946453 * 2 ^ 59
def prefixEnd_2946453 : Nat := 4983230072969 + 3 ^ 40 * 2946453 * 2
def baseEnd_2946453 : Nat := 1512946614882065722787015

theorem tailTrace_2946453 : CollatzResearch.WordTrace tailWord_2946453 prefixEnd_2946453 1512946614882065722787015 := by
  unfold tailWord_2946453
  simp only [CollatzResearch.WordTrace]
  refine ⟨107465969594511469954588013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71643979729674313303058675 107465969594511469954588013)
  ·
    refine ⟨40299738597941801232970505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107465969594511469954588013 40299738597941801232970505)
    ·
      refine ⟨30224803948456350924727879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40299738597941801232970505 30224803948456350924727879)
      ·
        refine ⟨45337205922684526387091819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30224803948456350924727879 45337205922684526387091819)
        ·
          refine ⟨68005808884026789580637729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45337205922684526387091819 68005808884026789580637729)
          ·
            refine ⟨51004356663020092185478297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68005808884026789580637729 51004356663020092185478297)
            ·
              refine ⟨38253267497265069139108723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51004356663020092185478297 38253267497265069139108723)
              ·
                refine ⟨57379901245897603708663085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38253267497265069139108723 57379901245897603708663085)
                ·
                  refine ⟨21517462967211601390748657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57379901245897603708663085 21517462967211601390748657)
                  ·
                    refine ⟨16138097225408701043061493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21517462967211601390748657 16138097225408701043061493)
                    ·
                      refine ⟨1512946614882065722787015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16138097225408701043061493 1512946614882065722787015)
                      ·
                        rfl

theorem cell23_2946453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_2946453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946453 prefixEnd_2946453 := by exact prefixLift 2946453
  have htrace : WordTrace (prefixWord ++ tailWord_2946453) baseStart_2946453 baseEnd_2946453 := by
    simpa [prefixWord, tailWord_2946453, baseEnd_2946453] using wordTrace_append hprefix tailTrace_2946453
  have hstable : (prefixWord ++ tailWord_2946453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946453).length < 2 ^ (prefixWord ++ tailWord_2946453).sum := by decide
  have hdescent : baseEnd_2946453 < baseStart_2946453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946480 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 1, 6, 2]
def baseStart_2946480 : Nat := 118140960795 + 2946480 * 2 ^ 59
def prefixEnd_2946480 : Nat := 4983230072969 + 3 ^ 40 * 2946480 * 2
def baseEnd_2946480 : Nat := 1512960478859737117149391

theorem tailTrace_2946480 : CollatzResearch.WordTrace tailWord_2946480 prefixEnd_2946480 1512960478859737117149391 := by
  unfold tailWord_2946480
  simp only [CollatzResearch.WordTrace]
  refine ⟨53733477182706826782910447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71644636243609102377213929 53733477182706826782910447)
  ·
    refine ⟨80600215774060240174365671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53733477182706826782910447 80600215774060240174365671)
    ·
      refine ⟨120900323661090360261548507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80600215774060240174365671 120900323661090360261548507)
      ·
        refine ⟨181350485491635540392322761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120900323661090360261548507 181350485491635540392322761)
        ·
          refine ⟨136012864118726655294242071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181350485491635540392322761 136012864118726655294242071)
          ·
            refine ⟨204019296178089982941363107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136012864118726655294242071 204019296178089982941363107)
            ·
              refine ⟨306028944267134974412044661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204019296178089982941363107 306028944267134974412044661)
              ·
                refine ⟨28690213525043903851129187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 306028944267134974412044661 28690213525043903851129187)
                ·
                  refine ⟨43035320287565855776693781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28690213525043903851129187 43035320287565855776693781)
                  ·
                    refine ⟨2017280638479649489532521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43035320287565855776693781 2017280638479649489532521)
                    ·
                      refine ⟨1512960478859737117149391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2017280638479649489532521 1512960478859737117149391)
                      ·
                        rfl

theorem cell23_2946480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 1, 6, 2].length) (baseStart_2946480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946480 prefixEnd_2946480 := by exact prefixLift 2946480
  have htrace : WordTrace (prefixWord ++ tailWord_2946480) baseStart_2946480 baseEnd_2946480 := by
    simpa [prefixWord, tailWord_2946480, baseEnd_2946480] using wordTrace_append hprefix tailTrace_2946480
  have hstable : (prefixWord ++ tailWord_2946480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946480).length < 2 ^ (prefixWord ++ tailWord_2946480).sum := by decide
  have hdescent : baseEnd_2946480 < baseStart_2946480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946503 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 10]
def baseStart_2946503 : Nat := 118140960795 + 2946503 * 2 ^ 59
def prefixEnd_2946503 : Nat := 4983230072969 + 3 ^ 40 * 2946503 * 2
def baseEnd_2946503 : Nat := 168108032101643391906865

theorem tailTrace_2946503 : CollatzResearch.WordTrace tailWord_2946503 prefixEnd_2946503 168108032101643391906865 := by
  unfold tailWord_2946503
  simp only [CollatzResearch.WordTrace]
  refine ⟨107467793244330328493908163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71645195496220218995938775 107467793244330328493908163)
  ·
    refine ⟨161201689866495492740862245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107467793244330328493908163 161201689866495492740862245)
    ·
      refine ⟨30225316849967904888911671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161201689866495492740862245 30225316849967904888911671)
      ·
        refine ⟨45337975274951857333367507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30225316849967904888911671 45337975274951857333367507)
        ·
          refine ⟨68006962912427786000051261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45337975274951857333367507 68006962912427786000051261)
          ·
            refine ⟨25502611092160419750019223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68006962912427786000051261 25502611092160419750019223)
            ·
              refine ⟨38253916638240629625028835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25502611092160419750019223 38253916638240629625028835)
              ·
                refine ⟨57380874957360944437543253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38253916638240629625028835 57380874957360944437543253)
                ·
                  refine ⟨168108032101643391906865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 57380874957360944437543253 168108032101643391906865)
                  ·
                    rfl

theorem cell23_2946503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 10].length) (baseStart_2946503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946503 prefixEnd_2946503 := by exact prefixLift 2946503
  have htrace : WordTrace (prefixWord ++ tailWord_2946503) baseStart_2946503 baseEnd_2946503 := by
    simpa [prefixWord, tailWord_2946503, baseEnd_2946503] using wordTrace_append hprefix tailTrace_2946503
  have hstable : (prefixWord ++ tailWord_2946503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946503).length < 2 ^ (prefixWord ++ tailWord_2946503).sum := by decide
  have hdescent : baseEnd_2946503 < baseStart_2946503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946517 : List Nat := [1, 3, 2, 3, 1, 1, 3, 2, 2, 2, 3]
def baseStart_2946517 : Nat := 118140960795 + 2946517 * 2 ^ 59
def prefixEnd_2946517 : Nat := 4983230072969 + 3 ^ 40 * 2946517 * 2
def baseEnd_2946517 : Nat := 1512979477643953472386721

theorem tailTrace_2946517 : CollatzResearch.WordTrace tailWord_2946517 prefixEnd_2946517 1512979477643953472386721 := by
  unfold tailWord_2946517
  simp only [CollatzResearch.WordTrace]
  refine ⟨107468303866279608884917805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71645535910853072589945203 107468303866279608884917805)
  ·
    refine ⟨40300613949854853331844177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107468303866279608884917805 40300613949854853331844177)
    ·
      refine ⟨30225460462391139998883133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40300613949854853331844177 30225460462391139998883133)
      ·
        refine ⟨11334547673396677499581175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30225460462391139998883133 11334547673396677499581175)
        ·
          refine ⟨17001821510095016249371763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11334547673396677499581175 17001821510095016249371763)
          ·
            refine ⟨25502732265142524374057645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17001821510095016249371763 25502732265142524374057645)
            ·
              refine ⟨9563524599428446640271617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25502732265142524374057645 9563524599428446640271617)
              ·
                refine ⟨7172643449571334980203713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9563524599428446640271617 7172643449571334980203713)
                ·
                  refine ⟨5379482587178501235152785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7172643449571334980203713 5379482587178501235152785)
                  ·
                    refine ⟨4034611940383875926364589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5379482587178501235152785 4034611940383875926364589)
                    ·
                      refine ⟨1512979477643953472386721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4034611940383875926364589 1512979477643953472386721)
                      ·
                        rfl

theorem cell23_2946517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_2946517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946517 prefixEnd_2946517 := by exact prefixLift 2946517
  have htrace : WordTrace (prefixWord ++ tailWord_2946517) baseStart_2946517 baseEnd_2946517 := by
    simpa [prefixWord, tailWord_2946517, baseEnd_2946517] using wordTrace_append hprefix tailTrace_2946517
  have hstable : (prefixWord ++ tailWord_2946517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946517).length < 2 ^ (prefixWord ++ tailWord_2946517).sum := by decide
  have hdescent : baseEnd_2946517 < baseStart_2946517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946581 : List Nat := [1, 3, 2, 1, 3, 3, 1, 4, 1, 1, 3]
def baseStart_2946581 : Nat := 118140960795 + 2946581 * 2 ^ 59
def prefixEnd_2946581 : Nat := 4983230072969 + 3 ^ 40 * 2946581 * 2
def baseEnd_2946581 : Nat := 1513012340405841221986427

theorem tailTrace_2946581 : CollatzResearch.WordTrace tailWord_2946581 prefixEnd_2946581 1513012340405841221986427 := by
  unfold tailWord_2946581
  simp only [CollatzResearch.WordTrace]
  refine ⟨107470638138047747815247597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71647092092031831876831731 107470638138047747815247597)
  ·
    refine ⟨40301489301767905430717849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107470638138047747815247597 40301489301767905430717849)
    ·
      refine ⟨30226116976325929073038387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40301489301767905430717849 30226116976325929073038387)
      ·
        refine ⟨45339175464488893609557581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30226116976325929073038387 45339175464488893609557581)
        ·
          refine ⟨17002190799183335103584093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45339175464488893609557581 17002190799183335103584093)
          ·
            refine ⟨6375821549693750663844035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17002190799183335103584093 6375821549693750663844035)
            ·
              refine ⟨9563732324540625995766053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6375821549693750663844035 9563732324540625995766053)
              ·
                refine ⟨1793199810851367374206135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9563732324540625995766053 1793199810851367374206135)
                ·
                  refine ⟨2689799716277051061309203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1793199810851367374206135 2689799716277051061309203)
                  ·
                    refine ⟨4034699574415576591963805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2689799716277051061309203 4034699574415576591963805)
                    ·
                      refine ⟨1513012340405841221986427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4034699574415576591963805 1513012340405841221986427)
                      ·
                        rfl

theorem cell23_2946581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 1, 1, 3].length) (baseStart_2946581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946581 prefixEnd_2946581 := by exact prefixLift 2946581
  have htrace : WordTrace (prefixWord ++ tailWord_2946581) baseStart_2946581 baseEnd_2946581 := by
    simpa [prefixWord, tailWord_2946581, baseEnd_2946581] using wordTrace_append hprefix tailTrace_2946581
  have hstable : (prefixWord ++ tailWord_2946581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946581).length < 2 ^ (prefixWord ++ tailWord_2946581).sum := by decide
  have hdescent : baseEnd_2946581 < baseStart_2946581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946617 : List Nat := [1, 2, 1, 5, 1, 2, 2, 2, 1, 2, 4]
def baseStart_2946617 : Nat := 118140960795 + 2946617 * 2 ^ 59
def prefixEnd_2946617 : Nat := 4983230072969 + 3 ^ 40 * 2946617 * 2
def baseEnd_2946617 : Nat := 1513030825709403081136261

theorem tailTrace_2946617 : CollatzResearch.WordTrace tailWord_2946617 prefixEnd_2946617 1513030825709403081136261 := by
  unfold tailWord_2946617
  simp only [CollatzResearch.WordTrace]
  refine ⟨107471951165917325963558105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71647967443944883975705403 107471951165917325963558105)
  ·
    refine ⟨80603963374437994472668579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107471951165917325963558105 80603963374437994472668579)
    ·
      refine ⟨120905945061656991709002869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80603963374437994472668579 120905945061656991709002869)
      ·
        refine ⟨11334932349530342972719019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120905945061656991709002869 11334932349530342972719019)
        ·
          refine ⟨17002398524295514459078529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11334932349530342972719019 17002398524295514459078529)
          ·
            refine ⟨12751798893221635844308897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17002398524295514459078529 12751798893221635844308897)
            ·
              refine ⟨9563849169916226883231673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12751798893221635844308897 9563849169916226883231673)
              ·
                refine ⟨7172886877437170162423755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9563849169916226883231673 7172886877437170162423755)
                ·
                  refine ⟨10759330316155755243635633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7172886877437170162423755 10759330316155755243635633)
                  ·
                    refine ⟨8069497737116816432726725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10759330316155755243635633 8069497737116816432726725)
                    ·
                      refine ⟨1513030825709403081136261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8069497737116816432726725 1513030825709403081136261)
                      ·
                        rfl

theorem cell23_2946617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_2946617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946617 prefixEnd_2946617 := by exact prefixLift 2946617
  have htrace : WordTrace (prefixWord ++ tailWord_2946617) baseStart_2946617 baseEnd_2946617 := by
    simpa [prefixWord, tailWord_2946617, baseEnd_2946617] using wordTrace_append hprefix tailTrace_2946617
  have hstable : (prefixWord ++ tailWord_2946617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946617).length < 2 ^ (prefixWord ++ tailWord_2946617).sum := by decide
  have hdescent : baseEnd_2946617 < baseStart_2946617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946631 : List Nat := [1, 1, 4, 1, 5, 2, 1, 2, 2, 4]
def baseStart_2946631 : Nat := 118140960795 + 2946631 * 2 ^ 59
def prefixEnd_2946631 : Nat := 4983230072969 + 3 ^ 40 * 2946631 * 2
def baseEnd_2946631 : Nat := 504346004812855342120399

theorem tailTrace_2946631 : CollatzResearch.WordTrace tailWord_2946631 prefixEnd_2946631 504346004812855342120399 := by
  unfold tailWord_2946631
  simp only [CollatzResearch.WordTrace]
  refine ⟨107472461787866606354567747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71648307858577737569711831 107472461787866606354567747)
  ·
    refine ⟨161208692681799909531851621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107472461787866606354567747 161208692681799909531851621)
    ·
      refine ⟨30226629877837483037222179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161208692681799909531851621 30226629877837483037222179)
      ·
        refine ⟨45339944816756224555833269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30226629877837483037222179 45339944816756224555833269)
        ·
          refine ⟨4250619826570896052109369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45339944816756224555833269 4250619826570896052109369)
          ·
            refine ⟨3187964869928172039082027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4250619826570896052109369 3187964869928172039082027)
            ·
              refine ⟨4781947304892258058623041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3187964869928172039082027 4781947304892258058623041)
              ·
                refine ⟨3586460478669193543967281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4781947304892258058623041 3586460478669193543967281)
                ·
                  refine ⟨2689845359001895157975461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3586460478669193543967281 2689845359001895157975461)
                  ·
                    refine ⟨504346004812855342120399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2689845359001895157975461 504346004812855342120399)
                    ·
                      rfl

theorem cell23_2946631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_2946631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946631 prefixEnd_2946631 := by exact prefixLift 2946631
  have htrace : WordTrace (prefixWord ++ tailWord_2946631) baseStart_2946631 baseEnd_2946631 := by
    simpa [prefixWord, tailWord_2946631, baseEnd_2946631] using wordTrace_append hprefix tailTrace_2946631
  have hstable : (prefixWord ++ tailWord_2946631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946631).length < 2 ^ (prefixWord ++ tailWord_2946631).sum := by decide
  have hdescent : baseEnd_2946631 < baseStart_2946631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946650 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5]
def baseStart_2946650 : Nat := 118140960795 + 2946650 * 2 ^ 59
def prefixEnd_2946650 : Nat := 4983230072969 + 3 ^ 40 * 2946650 * 2
def baseEnd_2946650 : Nat := 1513047770571001452023609

theorem tailTrace_2946650 : CollatzResearch.WordTrace tailWord_2946650 prefixEnd_2946650 1513047770571001452023609 := by
  unfold tailWord_2946650
  simp only [CollatzResearch.WordTrace]
  refine ⟨26868288693699443149877351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71648769849865181733006269 26868288693699443149877351)
  ·
    refine ⟨40302433040549164724816027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26868288693699443149877351 40302433040549164724816027)
    ·
      refine ⟨60453649560823747087224041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40302433040549164724816027 60453649560823747087224041)
      ·
        refine ⟨45340237170617810315418031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60453649560823747087224041 45340237170617810315418031)
        ·
          refine ⟨68010355755926715473127047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45340237170617810315418031 68010355755926715473127047)
          ·
            refine ⟨102015533633890073209690571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68010355755926715473127047 102015533633890073209690571)
            ·
              refine ⟨153023300450835109814535857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102015533633890073209690571 153023300450835109814535857)
              ·
                refine ⟨114767475338126332360901893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153023300450835109814535857 114767475338126332360901893)
                ·
                  refine ⟨21518901625898687317669105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114767475338126332360901893 21518901625898687317669105)
                  ·
                    refine ⟨16139176219424015488251829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21518901625898687317669105 16139176219424015488251829)
                    ·
                      refine ⟨1513047770571001452023609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16139176219424015488251829 1513047770571001452023609)
                      ·
                        rfl

theorem cell23_2946650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_2946650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946650 prefixEnd_2946650 := by exact prefixLift 2946650
  have htrace : WordTrace (prefixWord ++ tailWord_2946650) baseStart_2946650 baseEnd_2946650 := by
    simpa [prefixWord, tailWord_2946650, baseEnd_2946650] using wordTrace_append hprefix tailTrace_2946650
  have hstable : (prefixWord ++ tailWord_2946650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946650).length < 2 ^ (prefixWord ++ tailWord_2946650).sum := by decide
  have hdescent : baseEnd_2946650 < baseStart_2946650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946758 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_2946758 : Nat := 118140960795 + 2946758 * 2 ^ 59
def prefixEnd_2946758 : Nat := 4983230072969 + 3 ^ 40 * 2946758 * 2
def baseEnd_2946758 : Nat := 1513103226481687029473113

theorem tailTrace_2946758 : CollatzResearch.WordTrace tailWord_2946758 prefixEnd_2946758 1513103226481687029473113 := by
  unfold tailWord_2946758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3358659183075203345138779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71651395905604338029627285 3358659183075203345138779)
  ·
    refine ⟨5037988774612805017708169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3358659183075203345138779 5037988774612805017708169)
    ·
      refine ⟨3778491580959603763281127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5037988774612805017708169 3778491580959603763281127)
      ·
        refine ⟨5667737371439405644921691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3778491580959603763281127 5667737371439405644921691)
        ·
          refine ⟨8501606057159108467382537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5667737371439405644921691 8501606057159108467382537)
          ·
            refine ⟨6376204542869331350536903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8501606057159108467382537 6376204542869331350536903)
            ·
              refine ⟨9564306814303997025805355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6376204542869331350536903 9564306814303997025805355)
              ·
                refine ⟨14346460221455995538708033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9564306814303997025805355 14346460221455995538708033)
                ·
                  refine ⟨10759845166091996654031025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14346460221455995538708033 10759845166091996654031025)
                  ·
                    refine ⟨8069883874568997490523269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10759845166091996654031025 8069883874568997490523269)
                    ·
                      refine ⟨1513103226481687029473113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8069883874568997490523269 1513103226481687029473113)
                      ·
                        rfl

theorem cell23_2946758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_2946758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946758 prefixEnd_2946758 := by exact prefixLift 2946758
  have htrace : WordTrace (prefixWord ++ tailWord_2946758) baseStart_2946758 baseEnd_2946758 := by
    simpa [prefixWord, tailWord_2946758, baseEnd_2946758] using wordTrace_append hprefix tailTrace_2946758
  have hstable : (prefixWord ++ tailWord_2946758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946758).length < 2 ^ (prefixWord ++ tailWord_2946758).sum := by decide
  have hdescent : baseEnd_2946758 < baseStart_2946758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946767 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 4]
def baseStart_2946767 : Nat := 118140960795 + 2946767 * 2 ^ 59
def prefixEnd_2946767 : Nat := 4983230072969 + 3 ^ 40 * 2946767 * 2
def baseEnd_2946767 : Nat := 1513107847807577494260571

theorem tailTrace_2946767 : CollatzResearch.WordTrace tailWord_2946767 prefixEnd_2946767 1513107847807577494260571 := by
  unfold tailWord_2946767
  simp only [CollatzResearch.WordTrace]
  refine ⟨107477422115373901581518555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71651614743582601054345703 107477422115373901581518555)
  ·
    refine ⟨161216133173060852372277833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107477422115373901581518555 161216133173060852372277833)
    ·
      refine ⟨120912099879795639279208375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161216133173060852372277833 120912099879795639279208375)
      ·
        refine ⟨181368149819693458918812563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120912099879795639279208375 181368149819693458918812563)
        ·
          refine ⟨272052224729540188378218845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181368149819693458918812563 272052224729540188378218845)
          ·
            refine ⟨102019584273577570641832067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 272052224729540188378218845 102019584273577570641832067)
            ·
              refine ⟨153029376410366355962748101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102019584273577570641832067 153029376410366355962748101)
              ·
                refine ⟨28693008076943691743015269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153029376410366355962748101 28693008076943691743015269)
                ·
                  refine ⟨5379939014426942201815363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28693008076943691743015269 5379939014426942201815363)
                  ·
                    refine ⟨8069908521640413302723045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5379939014426942201815363 8069908521640413302723045)
                    ·
                      refine ⟨1513107847807577494260571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8069908521640413302723045 1513107847807577494260571)
                      ·
                        rfl

theorem cell23_2946767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 4].length) (baseStart_2946767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946767 prefixEnd_2946767 := by exact prefixLift 2946767
  have htrace : WordTrace (prefixWord ++ tailWord_2946767) baseStart_2946767 baseEnd_2946767 := by
    simpa [prefixWord, tailWord_2946767, baseEnd_2946767] using wordTrace_append hprefix tailTrace_2946767
  have hstable : (prefixWord ++ tailWord_2946767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946767).length < 2 ^ (prefixWord ++ tailWord_2946767).sum := by decide
  have hdescent : baseEnd_2946767 < baseStart_2946767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946781 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 1, 7]
def baseStart_2946781 : Nat := 118140960795 + 2946781 * 2 ^ 59
def prefixEnd_2946781 : Nat := 4983230072969 + 3 ^ 40 * 2946781 * 2
def baseEnd_2946781 : Nat := 504371678845580146495169

theorem tailTrace_2946781 : CollatzResearch.WordTrace tailWord_2946781 prefixEnd_2946781 504371678845580146495169 := by
  unfold tailWord_2946781
  simp only [CollatzResearch.WordTrace]
  refine ⟨107477932737323181972528197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71651955158215454648352131 107477932737323181972528197)
  ·
    refine ⟨20152112388248096619849037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107477932737323181972528197 20152112388248096619849037)
    ·
      refine ⟨7557042145593036232443389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20152112388248096619849037 7557042145593036232443389)
      ·
        refine ⟨2833890804597388587166271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7557042145593036232443389 2833890804597388587166271)
        ·
          refine ⟨4250836206896082880749407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2833890804597388587166271 4250836206896082880749407)
          ·
            refine ⟨6376254310344124321124111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4250836206896082880749407 6376254310344124321124111)
            ·
              refine ⟨9564381465516186481686167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6376254310344124321124111 9564381465516186481686167)
              ·
                refine ⟨14346572198274279722529251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9564381465516186481686167 14346572198274279722529251)
                ·
                  refine ⟨21519858297411419583793877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14346572198274279722529251 21519858297411419583793877)
                  ·
                    refine ⟨504371678845580146495169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21519858297411419583793877 504371678845580146495169)
                    ·
                      rfl

theorem cell23_2946781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_2946781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946781 prefixEnd_2946781 := by exact prefixLift 2946781
  have htrace : WordTrace (prefixWord ++ tailWord_2946781) baseStart_2946781 baseEnd_2946781 := by
    simpa [prefixWord, tailWord_2946781, baseEnd_2946781] using wordTrace_append hprefix tailTrace_2946781
  have hstable : (prefixWord ++ tailWord_2946781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946781).length < 2 ^ (prefixWord ++ tailWord_2946781).sum := by decide
  have hdescent : baseEnd_2946781 < baseStart_2946781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946784 : List Nat := [2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 4]
def baseStart_2946784 : Nat := 118140960795 + 2946784 * 2 ^ 59
def prefixEnd_2946784 : Nat := 4983230072969 + 3 ^ 40 * 2946784 * 2
def baseEnd_2946784 : Nat := 1513116576978703927747993

theorem tailTrace_2946784 : CollatzResearch.WordTrace tailWord_2946784 prefixEnd_2946784 1513116576978703927747993 := by
  unfold tailWord_2946784
  simp only [CollatzResearch.WordTrace]
  refine ⟨53739021078156156742443703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71652028104208208989924937 53739021078156156742443703)
  ·
    refine ⟨80608531617234235113665555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53739021078156156742443703 80608531617234235113665555)
    ·
      refine ⟨120912797425851352670498333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80608531617234235113665555 120912797425851352670498333)
      ·
        refine ⟨45342299034694257251436875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120912797425851352670498333 45342299034694257251436875)
        ·
          refine ⟨68013448552041385877155313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45342299034694257251436875 68013448552041385877155313)
          ·
            refine ⟨51010086414031039407866485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68013448552041385877155313 51010086414031039407866485)
            ·
              refine ⟨4782195601315409944487483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51010086414031039407866485 4782195601315409944487483)
              ·
                refine ⟨7173293401973114916731225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4782195601315409944487483 7173293401973114916731225)
                ·
                  refine ⟨5379970051479836187548419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7173293401973114916731225 5379970051479836187548419)
                  ·
                    refine ⟨8069955077219754281322629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5379970051479836187548419 8069955077219754281322629)
                    ·
                      refine ⟨1513116576978703927747993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8069955077219754281322629 1513116576978703927747993)
                      ·
                        rfl

theorem cell23_2946784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_2946784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946784 prefixEnd_2946784 := by exact prefixLift 2946784
  have htrace : WordTrace (prefixWord ++ tailWord_2946784) baseStart_2946784 baseEnd_2946784 := by
    simpa [prefixWord, tailWord_2946784, baseEnd_2946784] using wordTrace_append hprefix tailTrace_2946784
  have hstable : (prefixWord ++ tailWord_2946784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946784).length < 2 ^ (prefixWord ++ tailWord_2946784).sum := by decide
  have hdescent : baseEnd_2946784 < baseStart_2946784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946862 : List Nat := [4, 1, 3, 2, 2, 1, 3, 2, 1, 4]
def baseStart_2946862 : Nat := 118140960795 + 2946862 * 2 ^ 59
def prefixEnd_2946862 : Nat := 4983230072969 + 3 ^ 40 * 2946862 * 2
def baseEnd_2946862 : Nat := 504385542823251540857545

theorem tailTrace_2946862 : CollatzResearch.WordTrace tailWord_2946862 prefixEnd_2946862 504385542823251540857545 := by
  unfold tailWord_2946862
  simp only [CollatzResearch.WordTrace]
  refine ⟨13435110881253716600778355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71653924700019821870817893 13435110881253716600778355)
  ·
    refine ⟨20152666321880574901167533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13435110881253716600778355 20152666321880574901167533)
    ·
      refine ⟨7557249870705215587937825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20152666321880574901167533 7557249870705215587937825)
      ·
        refine ⟨5667937403028911690953369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7557249870705215587937825 5667937403028911690953369)
        ·
          refine ⟨4250953052271683768215027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5667937403028911690953369 4250953052271683768215027)
          ·
            refine ⟨6376429578407525652322541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4250953052271683768215027 6376429578407525652322541)
            ·
              refine ⟨2391161091902822119620953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6376429578407525652322541 2391161091902822119620953)
              ·
                refine ⟨1793370818927116589715715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2391161091902822119620953 1793370818927116589715715)
                ·
                  refine ⟨2690056228390674884573573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1793370818927116589715715 2690056228390674884573573)
                  ·
                    refine ⟨504385542823251540857545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2690056228390674884573573 504385542823251540857545)
                    ·
                      rfl

theorem cell23_2946862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_2946862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946862 prefixEnd_2946862 := by exact prefixLift 2946862
  have htrace : WordTrace (prefixWord ++ tailWord_2946862) baseStart_2946862 baseEnd_2946862 := by
    simpa [prefixWord, tailWord_2946862, baseEnd_2946862] using wordTrace_append hprefix tailTrace_2946862
  have hstable : (prefixWord ++ tailWord_2946862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946862).length < 2 ^ (prefixWord ++ tailWord_2946862).sum := by decide
  have hdescent : baseEnd_2946862 < baseStart_2946862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946911 : List Nat := [1, 1, 2, 3, 1, 6, 1, 1, 1, 1, 5]
def baseStart_2946911 : Nat := 118140960795 + 2946911 * 2 ^ 59
def prefixEnd_2946911 : Nat := 4983230072969 + 3 ^ 40 * 2946911 * 2
def baseEnd_2946911 : Nat := 1513181789021824930859909

theorem tailTrace_2946911 : CollatzResearch.WordTrace tailWord_2946911 prefixEnd_2946911 1513181789021824930859909 := by
  unfold tailWord_2946911
  simp only [CollatzResearch.WordTrace]
  refine ⟨107482674226852214174760587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71655116151234809449840391 107482674226852214174760587)
  ·
    refine ⟨161224011340278321262140881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107482674226852214174760587 161224011340278321262140881)
    ·
      refine ⟨120918008505208740946605661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161224011340278321262140881 120918008505208740946605661)
      ·
        refine ⟨45344253189453277854977123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120918008505208740946605661 45344253189453277854977123)
        ·
          refine ⟨68016379784179916782465685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45344253189453277854977123 68016379784179916782465685)
          ·
            refine ⟨3188267802383433599178079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68016379784179916782465685 3188267802383433599178079)
            ·
              refine ⟨4782401703575150398767119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3188267802383433599178079 4782401703575150398767119)
              ·
                refine ⟨7173602555362725598150679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4782401703575150398767119 7173602555362725598150679)
                ·
                  refine ⟨10760403833044088397226019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7173602555362725598150679 10760403833044088397226019)
                  ·
                    refine ⟨16140605749566132595839029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10760403833044088397226019 16140605749566132595839029)
                    ·
                      refine ⟨1513181789021824930859909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16140605749566132595839029 1513181789021824930859909)
                      ·
                        rfl

theorem cell23_2946911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_2946911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946911 prefixEnd_2946911 := by exact prefixLift 2946911
  have htrace : WordTrace (prefixWord ++ tailWord_2946911) baseStart_2946911 baseEnd_2946911 := by
    simpa [prefixWord, tailWord_2946911, baseEnd_2946911] using wordTrace_append hprefix tailTrace_2946911
  have hstable : (prefixWord ++ tailWord_2946911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946911).length < 2 ^ (prefixWord ++ tailWord_2946911).sum := by decide
  have hdescent : baseEnd_2946911 < baseStart_2946911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946914 : List Nat := [3, 3, 2, 1, 2, 12]
def baseStart_2946914 : Nat := 118140960795 + 2946914 * 2 ^ 59
def prefixEnd_2946914 : Nat := 4983230072969 + 3 ^ 40 * 2946914 * 2
def baseEnd_2946914 : Nat := 6227091890797483206265

theorem tailTrace_2946914 : CollatzResearch.WordTrace tailWord_2946914 prefixEnd_2946914 6227091890797483206265 := by
  unfold tailWord_2946914
  simp only [CollatzResearch.WordTrace]
  refine ⟨26870695911460336421779949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71655189097227563791413197 26870695911460336421779949)
  ·
    refine ⟨10076510966797626158167481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26870695911460336421779949 10076510966797626158167481)
    ·
      refine ⟨7557383225098219618625611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10076510966797626158167481 7557383225098219618625611)
      ·
        refine ⟨11336074837647329427938417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7557383225098219618625611 11336074837647329427938417)
        ·
          refine ⟨8502056128235497070953813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11336074837647329427938417 8502056128235497070953813)
          ·
            refine ⟨6227091890797483206265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8502056128235497070953813 6227091890797483206265)
            ·
              rfl

theorem cell23_2946914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 12].length) (baseStart_2946914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946914 prefixEnd_2946914 := by exact prefixLift 2946914
  have htrace : WordTrace (prefixWord ++ tailWord_2946914) baseStart_2946914 baseEnd_2946914 := by
    simpa [prefixWord, tailWord_2946914, baseEnd_2946914] using wordTrace_append hprefix tailTrace_2946914
  have hstable : (prefixWord ++ tailWord_2946914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946914).length < 2 ^ (prefixWord ++ tailWord_2946914).sum := by decide
  have hdescent : baseEnd_2946914 < baseStart_2946914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946941 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 6, 1, 3]
def baseStart_2946941 : Nat := 118140960795 + 2946941 * 2 ^ 59
def prefixEnd_2946941 : Nat := 4983230072969 + 3 ^ 40 * 2946941 * 2
def baseEnd_2946941 : Nat := 1513197193441459813484771

theorem tailTrace_2946941 : CollatzResearch.WordTrace tailWord_2946941 prefixEnd_2946941 1513197193441459813484771 := by
  unfold tailWord_2946941
  simp only [CollatzResearch.WordTrace]
  refine ⟨107483768416743529298352677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71655845611162352865568451 107483768416743529298352677)
  ·
    refine ⟨20153206578139411743441127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107483768416743529298352677 20153206578139411743441127)
    ·
      refine ⟨30229809867209117615161691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20153206578139411743441127 30229809867209117615161691)
      ·
        refine ⟨45344714800813676422742537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30229809867209117615161691 45344714800813676422742537)
        ·
          refine ⟨34008536100610257317056903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45344714800813676422742537 34008536100610257317056903)
          ·
            refine ⟨51012804150915385975585355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34008536100610257317056903 51012804150915385975585355)
            ·
              refine ⟨76519206226373078963378033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51012804150915385975585355 76519206226373078963378033)
              ·
                refine ⟨57389404669779809222533525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76519206226373078963378033 57389404669779809222533525)
                ·
                  refine ⟨2690128343895928557306259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57389404669779809222533525 2690128343895928557306259)
                  ·
                    refine ⟨4035192515843892835959389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2690128343895928557306259 4035192515843892835959389)
                    ·
                      refine ⟨1513197193441459813484771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4035192515843892835959389 1513197193441459813484771)
                      ·
                        rfl

theorem cell23_2946941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_2946941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946941 prefixEnd_2946941 := by exact prefixLift 2946941
  have htrace : WordTrace (prefixWord ++ tailWord_2946941) baseStart_2946941 baseEnd_2946941 := by
    simpa [prefixWord, tailWord_2946941, baseEnd_2946941] using wordTrace_append hprefix tailTrace_2946941
  have hstable : (prefixWord ++ tailWord_2946941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946941).length < 2 ^ (prefixWord ++ tailWord_2946941).sum := by decide
  have hdescent : baseEnd_2946941 < baseStart_2946941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946942 : List Nat := [4, 2, 3, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_2946942 : Nat := 118140960795 + 2946942 * 2 ^ 59
def prefixEnd_2946942 : Nat := 4983230072969 + 3 ^ 40 * 2946942 * 2
def baseEnd_2946942 : Nat := 1513197706922114309572267

theorem tailTrace_2946942 : CollatzResearch.WordTrace tailWord_2946942 prefixEnd_2946942 1513197706922114309572267 := by
  unfold tailWord_2946942
  simp only [CollatzResearch.WordTrace]
  refine ⟨13435475611217488308642385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71655869926493270979426053 13435475611217488308642385)
  ·
    refine ⟨10076606708413116231481789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13435475611217488308642385 10076606708413116231481789)
    ·
      refine ⟨3778727515654918586805671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10076606708413116231481789 3778727515654918586805671)
      ·
        refine ⟨5668091273482377880208507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3778727515654918586805671 5668091273482377880208507)
        ·
          refine ⟨8502136910223566820312761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5668091273482377880208507 8502136910223566820312761)
          ·
            refine ⟨6376602682667675115234571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8502136910223566820312761 6376602682667675115234571)
            ·
              refine ⟨9564904024001512672851857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6376602682667675115234571 9564904024001512672851857)
              ·
                refine ⟨7173678018001134504638893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9564904024001512672851857 7173678018001134504638893)
                ·
                  refine ⟨2690129256750425439239585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7173678018001134504638893 2690129256750425439239585)
                  ·
                    refine ⟨2017596942562819079429689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2690129256750425439239585 2017596942562819079429689)
                    ·
                      refine ⟨1513197706922114309572267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2017596942562819079429689 1513197706922114309572267)
                      ·
                        rfl

theorem cell23_2946942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_2946942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946942 prefixEnd_2946942 := by exact prefixLift 2946942
  have htrace : WordTrace (prefixWord ++ tailWord_2946942) baseStart_2946942 baseEnd_2946942 := by
    simpa [prefixWord, tailWord_2946942, baseEnd_2946942] using wordTrace_append hprefix tailTrace_2946942
  have hstable : (prefixWord ++ tailWord_2946942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946942).length < 2 ^ (prefixWord ++ tailWord_2946942).sum := by decide
  have hdescent : baseEnd_2946942 < baseStart_2946942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946962 : List Nat := [3, 2, 3, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_2946962 : Nat := 118140960795 + 2946962 * 2 ^ 59
def prefixEnd_2946962 : Nat := 4983230072969 + 3 ^ 40 * 2946962 * 2
def baseEnd_2946962 : Nat := 1513207976535204231322175

theorem tailTrace_2946962 : CollatzResearch.WordTrace tailWord_2946962 prefixEnd_2946962 1513207976535204231322175 := by
  unfold tailWord_2946962
  simp only [CollatzResearch.WordTrace]
  refine ⟨26871133587416862471216785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71656356233111633256578093 26871133587416862471216785)
  ·
    refine ⟨20153350190562646853412589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26871133587416862471216785 20153350190562646853412589)
    ·
      refine ⟨7557506321460992570029721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20153350190562646853412589 7557506321460992570029721)
      ·
        refine ⟨5668129741095744427522291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7557506321460992570029721 5668129741095744427522291)
        ·
          refine ⟨8502194611643616641283437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5668129741095744427522291 8502194611643616641283437)
          ·
            refine ⟨3188322979366356240481289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8502194611643616641283437 3188322979366356240481289)
            ·
              refine ⟨2391242234524767180360967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3188322979366356240481289 2391242234524767180360967)
              ·
                refine ⟨3586863351787150770541451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2391242234524767180360967 3586863351787150770541451)
                ·
                  refine ⟨5380295027680726155812177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3586863351787150770541451 5380295027680726155812177)
                  ·
                    refine ⟨4035221270760544616859133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5380295027680726155812177 4035221270760544616859133)
                    ·
                      refine ⟨1513207976535204231322175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4035221270760544616859133 1513207976535204231322175)
                      ·
                        rfl

theorem cell23_2946962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_2946962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946962 prefixEnd_2946962 := by exact prefixLift 2946962
  have htrace : WordTrace (prefixWord ++ tailWord_2946962) baseStart_2946962 baseEnd_2946962 := by
    simpa [prefixWord, tailWord_2946962, baseEnd_2946962] using wordTrace_append hprefix tailTrace_2946962
  have hstable : (prefixWord ++ tailWord_2946962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946962).length < 2 ^ (prefixWord ++ tailWord_2946962).sum := by decide
  have hdescent : baseEnd_2946962 < baseStart_2946962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2946981 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 3, 4, 2]
def baseStart_2946981 : Nat := 118140960795 + 2946981 * 2 ^ 59
def prefixEnd_2946981 : Nat := 4983230072969 + 3 ^ 40 * 2946981 * 2
def baseEnd_2946981 : Nat := 1513217732667639656984587

theorem tailTrace_2946981 : CollatzResearch.WordTrace tailWord_2946981 prefixEnd_2946981 1513217732667639656984587 := by
  unfold tailWord_2946981
  simp only [CollatzResearch.WordTrace]
  refine ⟨107485227336598616129808797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71656818224399077419872531 107485227336598616129808797)
  ·
    refine ⟨40306960251224481048678299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107485227336598616129808797 40306960251224481048678299)
    ·
      refine ⟨60460440376836721573017449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40306960251224481048678299 60460440376836721573017449)
      ·
        refine ⟨45345330282627541179763087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60460440376836721573017449 45345330282627541179763087)
        ·
          refine ⟨68017995423941311769644631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45345330282627541179763087 68017995423941311769644631)
          ·
            refine ⟨102026993135911967654466947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68017995423941311769644631 102026993135911967654466947)
            ·
              refine ⟨153040489703867951481700421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102026993135911967654466947 153040489703867951481700421)
              ·
                refine ⟨28695091819475240902818829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153040489703867951481700421 28695091819475240902818829)
                ·
                  refine ⟨10760659432303215338557061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28695091819475240902818829 10760659432303215338557061)
                  ·
                    refine ⟨2017623643556852875979449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10760659432303215338557061 2017623643556852875979449)
                    ·
                      refine ⟨1513217732667639656984587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2017623643556852875979449 1513217732667639656984587)
                      ·
                        rfl

theorem cell23_2946981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_2946981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2946981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2946981 prefixEnd_2946981 := by exact prefixLift 2946981
  have htrace : WordTrace (prefixWord ++ tailWord_2946981) baseStart_2946981 baseEnd_2946981 := by
    simpa [prefixWord, tailWord_2946981, baseEnd_2946981] using wordTrace_append hprefix tailTrace_2946981
  have hstable : (prefixWord ++ tailWord_2946981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2946981).length < 2 ^ (prefixWord ++ tailWord_2946981).sum := by decide
  have hdescent : baseEnd_2946981 < baseStart_2946981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2946981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947064 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 2, 8]
def baseStart_2947064 : Nat := 118140960795 + 2947064 * 2 ^ 59
def prefixEnd_2947064 : Nat := 4983230072969 + 3 ^ 40 * 2947064 * 2
def baseEnd_2947064 : Nat := 504420117187320944082235

theorem tailTrace_2947064 : CollatzResearch.WordTrace tailWord_2947064 prefixEnd_2947064 504420117187320944082235 := by
  unfold tailWord_2947064
  simp only [CollatzResearch.WordTrace]
  refine ⟨53744127297648960652540123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71658836396865280870053497 53744127297648960652540123)
  ·
    refine ⟨80616190946473440978810185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53744127297648960652540123 80616190946473440978810185)
    ·
      refine ⟨60462143209855080734107639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80616190946473440978810185 60462143209855080734107639)
      ·
        refine ⟨90693214814782621101161459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60462143209855080734107639 90693214814782621101161459)
        ·
          refine ⟨136039822222173931651742189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90693214814782621101161459 136039822222173931651742189)
          ·
            refine ⟨51014933333315224369403321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136039822222173931651742189 51014933333315224369403321)
            ·
              refine ⟨38261199999986418277052491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51014933333315224369403321 38261199999986418277052491)
              ·
                refine ⟨57391799999979627415578737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38261199999986418277052491 57391799999979627415578737)
                ·
                  refine ⟨43043849999984720561684053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57391799999979627415578737 43043849999984720561684053)
                  ·
                    refine ⟨504420117187320944082235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43043849999984720561684053 504420117187320944082235)
                    ·
                      rfl

theorem cell23_2947064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_2947064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947064 prefixEnd_2947064 := by exact prefixLift 2947064
  have htrace : WordTrace (prefixWord ++ tailWord_2947064) baseStart_2947064 baseEnd_2947064 := by
    simpa [prefixWord, tailWord_2947064, baseEnd_2947064] using wordTrace_append hprefix tailTrace_2947064
  have hstable : (prefixWord ++ tailWord_2947064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947064).length < 2 ^ (prefixWord ++ tailWord_2947064).sum := by decide
  have hdescent : baseEnd_2947064 < baseStart_2947064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947105 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 2, 4, 2]
def baseStart_2947105 : Nat := 118140960795 + 2947105 * 2 ^ 59
def prefixEnd_2947105 : Nat := 4983230072969 + 3 ^ 40 * 2947105 * 2
def baseEnd_2947105 : Nat := 1513281404268797171834017

theorem tailTrace_2947105 : CollatzResearch.WordTrace tailWord_2947105 prefixEnd_2947105 1513281404268797171834017 := by
  unfold tailWord_2947105
  simp only [CollatzResearch.WordTrace]
  refine ⟨107489749988149385307322769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71659833325432923538215179 107489749988149385307322769)
  ·
    refine ⟨80617312491112038980492077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107489749988149385307322769 80617312491112038980492077)
    ·
      refine ⟨30231492184167014617684529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80617312491112038980492077 30231492184167014617684529)
      ·
        refine ⟨22673619138125260963263397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30231492184167014617684529 22673619138125260963263397)
        ·
          refine ⟨4251303588398486430611887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22673619138125260963263397 4251303588398486430611887)
          ·
            refine ⟨6376955382597729645917831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4251303588398486430611887 6376955382597729645917831)
            ·
              refine ⟨9565433073896594468876747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6376955382597729645917831 9565433073896594468876747)
              ·
                refine ⟨14348149610844891703315121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9565433073896594468876747 14348149610844891703315121)
                ·
                  refine ⟨10761112208133668777486341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14348149610844891703315121 10761112208133668777486341)
                  ·
                    refine ⟨2017708539025062895778689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10761112208133668777486341 2017708539025062895778689)
                    ·
                      refine ⟨1513281404268797171834017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2017708539025062895778689 1513281404268797171834017)
                      ·
                        rfl

theorem cell23_2947105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_2947105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947105 prefixEnd_2947105 := by exact prefixLift 2947105
  have htrace : WordTrace (prefixWord ++ tailWord_2947105) baseStart_2947105 baseEnd_2947105 := by
    simpa [prefixWord, tailWord_2947105, baseEnd_2947105] using wordTrace_append hprefix tailTrace_2947105
  have hstable : (prefixWord ++ tailWord_2947105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947105).length < 2 ^ (prefixWord ++ tailWord_2947105).sum := by decide
  have hdescent : baseEnd_2947105 < baseStart_2947105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947208 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2947208 : Nat := 118140960795 + 2947208 * 2 ^ 59
def prefixEnd_2947208 : Nat := 4983230072969 + 3 ^ 40 * 2947208 * 2
def baseEnd_2947208 : Nat := 1513334292776210268846043

theorem tailTrace_2947208 : CollatzResearch.WordTrace tailWord_2947208 prefixEnd_2947208 1513334292776210268846043 := by
  unfold tailWord_2947208
  simp only [CollatzResearch.WordTrace]
  refine ⟨53746753353388116949161139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71662337804517489265548185 53746753353388116949161139)
  ·
    refine ⟨80620130030082175423741709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53746753353388116949161139 80620130030082175423741709)
    ·
      refine ⟨30232548761280815783903141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80620130030082175423741709 30232548761280815783903141)
      ·
        refine ⟨5668602892740152959481839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30232548761280815783903141 5668602892740152959481839)
        ·
          refine ⟨8502904339110229439222759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5668602892740152959481839 8502904339110229439222759)
          ·
            refine ⟨12754356508665344158834139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8502904339110229439222759 12754356508665344158834139)
            ·
              refine ⟨19131534762998016238251209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12754356508665344158834139 19131534762998016238251209)
              ·
                refine ⟨14348651072248512178688407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19131534762998016238251209 14348651072248512178688407)
                ·
                  refine ⟨21522976608372768268032611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14348651072248512178688407 21522976608372768268032611)
                  ·
                    refine ⟨32284464912559152402048917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21522976608372768268032611 32284464912559152402048917)
                    ·
                      refine ⟨1513334292776210268846043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32284464912559152402048917 1513334292776210268846043)
                      ·
                        rfl

theorem cell23_2947208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2947208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947208 prefixEnd_2947208 := by exact prefixLift 2947208
  have htrace : WordTrace (prefixWord ++ tailWord_2947208) baseStart_2947208 baseEnd_2947208 := by
    simpa [prefixWord, tailWord_2947208, baseEnd_2947208] using wordTrace_append hprefix tailTrace_2947208
  have hstable : (prefixWord ++ tailWord_2947208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947208).length < 2 ^ (prefixWord ++ tailWord_2947208).sum := by decide
  have hdescent : baseEnd_2947208 < baseStart_2947208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947218 : List Nat := [3, 2, 3, 1, 1, 1, 4, 8]
def baseStart_2947218 : Nat := 118140960795 + 2947218 * 2 ^ 59
def prefixEnd_2947218 : Nat := 4983230072969 + 3 ^ 40 * 2947218 * 2
def baseEnd_2947218 : Nat := 56049608428990934434111

theorem tailTrace_2947218 : CollatzResearch.WordTrace tailWord_2947218 prefixEnd_2947218 56049608428990934434111 := by
  unfold tailWord_2947218
  simp only [CollatzResearch.WordTrace]
  refine ⟨26873467859185001401546577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71662580957826670404124205 26873467859185001401546577)
  ·
    refine ⟨20155100894388751051159933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26873467859185001401546577 20155100894388751051159933)
    ·
      refine ⟨7558162835395781644184975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20155100894388751051159933 7558162835395781644184975)
      ·
        refine ⟨11337244253093672466277463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7558162835395781644184975 11337244253093672466277463)
        ·
          refine ⟨17005866379640508699416195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11337244253093672466277463 17005866379640508699416195)
          ·
            refine ⟨25508799569460763049124293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17005866379640508699416195 25508799569460763049124293)
            ·
              refine ⟨4782899919273893071710805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25508799569460763049124293 4782899919273893071710805)
              ·
                refine ⟨56049608428990934434111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4782899919273893071710805 56049608428990934434111)
                ·
                  rfl

theorem cell23_2947218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 8].length) (baseStart_2947218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947218 prefixEnd_2947218 := by exact prefixLift 2947218
  have htrace : WordTrace (prefixWord ++ tailWord_2947218) baseStart_2947218 baseEnd_2947218 := by
    simpa [prefixWord, tailWord_2947218, baseEnd_2947218] using wordTrace_append hprefix tailTrace_2947218
  have hstable : (prefixWord ++ tailWord_2947218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947218).length < 2 ^ (prefixWord ++ tailWord_2947218).sum := by decide
  have hdescent : baseEnd_2947218 < baseStart_2947218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947221 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_2947221 : Nat := 118140960795 + 2947221 * 2 ^ 59
def prefixEnd_2947221 : Nat := 4983230072969 + 3 ^ 40 * 2947221 * 2
def baseEnd_2947221 : Nat := 1513340968024718717983483

theorem tailTrace_2947221 : CollatzResearch.WordTrace tailWord_2947221 prefixEnd_2947221 1513340968024718717983483 := by
  unfold tailWord_2947221
  simp only [CollatzResearch.WordTrace]
  refine ⟨107493980855729137118545517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71662653903819424745697011 107493980855729137118545517)
  ·
    refine ⟨40310242820898426419454569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107493980855729137118545517 40310242820898426419454569)
    ·
      refine ⟨30232682115673819814590927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40310242820898426419454569 30232682115673819814590927)
      ·
        refine ⟨45349023173510729721886391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30232682115673819814590927 45349023173510729721886391)
        ·
          refine ⟨68023534760266094582829587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45349023173510729721886391 68023534760266094582829587)
          ·
            refine ⟨102035302140399141874244381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68023534760266094582829587 102035302140399141874244381)
            ·
              refine ⟨38263238302649678202841643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102035302140399141874244381 38263238302649678202841643)
              ·
                refine ⟨57394857453974517304262465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38263238302649678202841643 57394857453974517304262465)
                ·
                  refine ⟨43046143090480887978196849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57394857453974517304262465 43046143090480887978196849)
                  ·
                    refine ⟨32284607317860665983647637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43046143090480887978196849 32284607317860665983647637)
                    ·
                      refine ⟨1513340968024718717983483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32284607317860665983647637 1513340968024718717983483)
                      ·
                        rfl

theorem cell23_2947221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_2947221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947221 prefixEnd_2947221 := by exact prefixLift 2947221
  have htrace : WordTrace (prefixWord ++ tailWord_2947221) baseStart_2947221 baseEnd_2947221 := by
    simpa [prefixWord, tailWord_2947221, baseEnd_2947221] using wordTrace_append hprefix tailTrace_2947221
  have hstable : (prefixWord ++ tailWord_2947221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947221).length < 2 ^ (prefixWord ++ tailWord_2947221).sum := by decide
  have hdescent : baseEnd_2947221 < baseStart_2947221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947232 : List Nat := [2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 3]
def baseStart_2947232 : Nat := 118140960795 + 2947232 * 2 ^ 59
def prefixEnd_2947232 : Nat := 4983230072969 + 3 ^ 40 * 2947232 * 2
def baseEnd_2947232 : Nat := 1513346616311918174945933

theorem tailTrace_2947232 : CollatzResearch.WordTrace tailWord_2947232 prefixEnd_2947232 1513346616311918174945933 := by
  unfold tailWord_2947232
  simp only [CollatzResearch.WordTrace]
  refine ⟨53747191029344642998597975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71662921372459523998130633 53747191029344642998597975)
  ·
    refine ⟨80620786544016964497896963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53747191029344642998597975 80620786544016964497896963)
    ·
      refine ⟨120931179816025446746845445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80620786544016964497896963 120931179816025446746845445)
      ·
        refine ⟨22674596215504771265033521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120931179816025446746845445 22674596215504771265033521)
        ·
          refine ⟨17005947161628578448775141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22674596215504771265033521 17005947161628578448775141)
          ·
            refine ⟨3188615092805358459145339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17005947161628578448775141 3188615092805358459145339)
            ·
              refine ⟨4782922639208037688718009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3188615092805358459145339 4782922639208037688718009)
              ·
                refine ⟨3587191979406028266538507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4782922639208037688718009 3587191979406028266538507)
                ·
                  refine ⟨5380787969109042399807761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3587191979406028266538507 5380787969109042399807761)
                  ·
                    refine ⟨4035590976831781799855821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5380787969109042399807761 4035590976831781799855821)
                    ·
                      refine ⟨1513346616311918174945933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4035590976831781799855821 1513346616311918174945933)
                      ·
                        rfl

theorem cell23_2947232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_2947232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947232 prefixEnd_2947232 := by exact prefixLift 2947232
  have htrace : WordTrace (prefixWord ++ tailWord_2947232) baseStart_2947232 baseEnd_2947232 := by
    simpa [prefixWord, tailWord_2947232, baseEnd_2947232] using wordTrace_append hprefix tailTrace_2947232
  have hstable : (prefixWord ++ tailWord_2947232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947232).length < 2 ^ (prefixWord ++ tailWord_2947232).sum := by decide
  have hdescent : baseEnd_2947232 < baseStart_2947232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947242 : List Nat := [3, 1, 5, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_2947242 : Nat := 118140960795 + 2947242 * 2 ^ 59
def prefixEnd_2947242 : Nat := 4983230072969 + 3 ^ 40 * 2947242 * 2
def baseEnd_2947242 : Nat := 1513351751118463135820887

theorem tailTrace_2947242 : CollatzResearch.WordTrace tailWord_2947242 prefixEnd_2947242 1513351751118463135820887 := by
  unfold tailWord_2947242
  simp only [CollatzResearch.WordTrace]
  refine ⟨26873686697163264426264995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71663164525768705136706653 26873686697163264426264995)
  ·
    refine ⟨40310530045744896639397493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26873686697163264426264995 40310530045744896639397493)
    ·
      refine ⟨3779112191788584059943515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40310530045744896639397493 3779112191788584059943515)
      ·
        refine ⟨5668668287682876089915273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3779112191788584059943515 5668668287682876089915273)
        ·
          refine ⟨4251501215762157067436455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5668668287682876089915273 4251501215762157067436455)
          ·
            refine ⟨6377251823643235601154683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4251501215762157067436455 6377251823643235601154683)
            ·
              refine ⟨9565877735464853401732025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6377251823643235601154683 9565877735464853401732025)
              ·
                refine ⟨7174408301598640051299019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9565877735464853401732025 7174408301598640051299019)
                ·
                  refine ⟨10761612452397960076948529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7174408301598640051299019 10761612452397960076948529)
                  ·
                    refine ⟨8071209339298470057711397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10761612452397960076948529 8071209339298470057711397)
                    ·
                      refine ⟨1513351751118463135820887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8071209339298470057711397 1513351751118463135820887)
                      ·
                        rfl

theorem cell23_2947242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_2947242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947242 prefixEnd_2947242 := by exact prefixLift 2947242
  have htrace : WordTrace (prefixWord ++ tailWord_2947242) baseStart_2947242 baseEnd_2947242 := by
    simpa [prefixWord, tailWord_2947242, baseEnd_2947242] using wordTrace_append hprefix tailTrace_2947242
  have hstable : (prefixWord ++ tailWord_2947242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947242).length < 2 ^ (prefixWord ++ tailWord_2947242).sum := by decide
  have hdescent : baseEnd_2947242 < baseStart_2947242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947245 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_2947245 : Nat := 118140960795 + 2947245 * 2 ^ 59
def prefixEnd_2947245 : Nat := 4983230072969 + 3 ^ 40 * 2947245 * 2
def baseEnd_2947245 : Nat := 1513353291560426624083373

theorem tailTrace_2947245 : CollatzResearch.WordTrace tailWord_2947245 prefixEnd_2947245 1513353291560426624083373 := by
  unfold tailWord_2947245
  simp only [CollatzResearch.WordTrace]
  refine ⟨107494856207642189217419189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71663237471761459478279459 107494856207642189217419189)
  ·
    refine ⟨10077642769466455239133049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107494856207642189217419189 10077642769466455239133049)
    ·
      refine ⟨7558232077099841429349787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10077642769466455239133049 7558232077099841429349787)
      ·
        refine ⟨11337348115649762144024681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7558232077099841429349787 11337348115649762144024681)
        ·
          refine ⟨8503011086737321608018511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11337348115649762144024681 8503011086737321608018511)
          ·
            refine ⟨12754516630105982412027767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8503011086737321608018511 12754516630105982412027767)
            ·
              refine ⟨19131774945158973618041651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12754516630105982412027767 19131774945158973618041651)
              ·
                refine ⟨28697662417738460427062477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19131774945158973618041651 28697662417738460427062477)
                ·
                  refine ⟨10761623406651922660148429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28697662417738460427062477 10761623406651922660148429)
                  ·
                    refine ⟨4035608777494470997555661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10761623406651922660148429 4035608777494470997555661)
                    ·
                      refine ⟨1513353291560426624083373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4035608777494470997555661 1513353291560426624083373)
                      ·
                        rfl

theorem cell23_2947245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_2947245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947245 prefixEnd_2947245 := by exact prefixLift 2947245
  have htrace : WordTrace (prefixWord ++ tailWord_2947245) baseStart_2947245 baseEnd_2947245 := by
    simpa [prefixWord, tailWord_2947245, baseEnd_2947245] using wordTrace_append hprefix tailTrace_2947245
  have hstable : (prefixWord ++ tailWord_2947245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947245).length < 2 ^ (prefixWord ++ tailWord_2947245).sum := by decide
  have hdescent : baseEnd_2947245 < baseStart_2947245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947246 : List Nat := [4, 1, 4, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_2947246 : Nat := 118140960795 + 2947246 * 2 ^ 59
def prefixEnd_2947246 : Nat := 4983230072969 + 3 ^ 40 * 2947246 * 2
def baseEnd_2947246 : Nat := 1513353805041081120170869

theorem tailTrace_2947246 : CollatzResearch.WordTrace tailWord_2947246 prefixEnd_2947246 1513353805041081120170869 := by
  unfold tailWord_2947246
  simp only [CollatzResearch.WordTrace]
  refine ⟨13436861585079820798525699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71663261787092377592137061 13436861585079820798525699)
  ·
    refine ⟨20155292377619731197788549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13436861585079820798525699 20155292377619731197788549)
    ·
      refine ⟨3779117320803699599585353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20155292377619731197788549 3779117320803699599585353)
      ·
        refine ⟨2834337990602774699689015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3779117320803699599585353 2834337990602774699689015)
        ·
          refine ⟨4251506985904162049533523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2834337990602774699689015 4251506985904162049533523)
          ·
            refine ⟨6377260478856243074300285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4251506985904162049533523 6377260478856243074300285)
            ·
              refine ⟨2391472679571091152862607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6377260478856243074300285 2391472679571091152862607)
              ·
                refine ⟨3587209019356636729293911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2391472679571091152862607 3587209019356636729293911)
                ·
                  refine ⟨5380813529034955093940867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3587209019356636729293911 5380813529034955093940867)
                  ·
                    refine ⟨8071220293552432640911301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5380813529034955093940867 8071220293552432640911301)
                    ·
                      refine ⟨1513353805041081120170869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8071220293552432640911301 1513353805041081120170869)
                      ·
                        rfl

theorem cell23_2947246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_2947246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947246 prefixEnd_2947246 := by exact prefixLift 2947246
  have htrace : WordTrace (prefixWord ++ tailWord_2947246) baseStart_2947246 baseEnd_2947246 := by
    simpa [prefixWord, tailWord_2947246, baseEnd_2947246] using wordTrace_append hprefix tailTrace_2947246
  have hstable : (prefixWord ++ tailWord_2947246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947246).length < 2 ^ (prefixWord ++ tailWord_2947246).sum := by decide
  have hdescent : baseEnd_2947246 < baseStart_2947246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947249 : List Nat := [1, 2, 2, 5, 2, 1, 3, 1, 1, 2, 3]
def baseStart_2947249 : Nat := 118140960795 + 2947249 * 2 ^ 59
def prefixEnd_2947249 : Nat := 4983230072969 + 3 ^ 40 * 2947249 * 2
def baseEnd_2947249 : Nat := 1513355345483044608433355

theorem tailTrace_2947249 : CollatzResearch.WordTrace tailWord_2947249 prefixEnd_2947249 1513355345483044608433355 := by
  unfold tailWord_2947249
  simp only [CollatzResearch.WordTrace]
  refine ⟨107495002099627697900564801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71663334733085131933709867 107495002099627697900564801)
  ·
    refine ⟨80621251574720773425423601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107495002099627697900564801 80621251574720773425423601)
    ·
      refine ⟨60465938681040580069067701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80621251574720773425423601 60465938681040580069067701)
      ·
        refine ⟨5668681751347554381475097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60465938681040580069067701 5668681751347554381475097)
        ·
          refine ⟨4251511313510665786106323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5668681751347554381475097 4251511313510665786106323)
          ·
            refine ⟨6377266970265998679159485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4251511313510665786106323 6377266970265998679159485)
            ·
              refine ⟨2391475113849749504684807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6377266970265998679159485 2391475113849749504684807)
              ·
                refine ⟨3587212670774624257027211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2391475113849749504684807 3587212670774624257027211)
                ·
                  refine ⟨5380819006161936385540817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3587212670774624257027211 5380819006161936385540817)
                  ·
                    refine ⟨4035614254621452289155613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5380819006161936385540817 4035614254621452289155613)
                    ·
                      refine ⟨1513355345483044608433355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4035614254621452289155613 1513355345483044608433355)
                      ·
                        rfl

theorem cell23_2947249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_2947249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947249 prefixEnd_2947249 := by exact prefixLift 2947249
  have htrace : WordTrace (prefixWord ++ tailWord_2947249) baseStart_2947249 baseEnd_2947249 := by
    simpa [prefixWord, tailWord_2947249, baseEnd_2947249] using wordTrace_append hprefix tailTrace_2947249
  have hstable : (prefixWord ++ tailWord_2947249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947249).length < 2 ^ (prefixWord ++ tailWord_2947249).sum := by decide
  have hdescent : baseEnd_2947249 < baseStart_2947249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947252 : List Nat := [2, 5, 3, 1, 1, 11]
def baseStart_2947252 : Nat := 118140960795 + 2947252 * 2 ^ 59
def prefixEnd_2947252 : Nat := 4983230072969 + 3 ^ 40 * 2947252 * 2
def baseEnd_2947252 : Nat := 6227806114917728792987

theorem tailTrace_2947252 : CollatzResearch.WordTrace tailWord_2947252 prefixEnd_2947252 6227806114917728792987 := by
  unfold tailWord_2947252
  simp only [CollatzResearch.WordTrace]
  refine ⟨53747555759308414706462005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71663407679077886275282673 53747555759308414706462005)
  ·
    refine ⟨5038833352435163878730813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53747555759308414706462005 5038833352435163878730813)
    ·
      refine ⟨1889562507163186454524055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5038833352435163878730813 1889562507163186454524055)
      ·
        refine ⟨2834343760744779681786083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1889562507163186454524055 2834343760744779681786083)
        ·
          refine ⟨4251515641117169522679125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2834343760744779681786083 4251515641117169522679125)
          ·
            refine ⟨6227806114917728792987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4251515641117169522679125 6227806114917728792987)
            ·
              rfl

theorem cell23_2947252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 11].length) (baseStart_2947252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947252 prefixEnd_2947252 := by exact prefixLift 2947252
  have htrace : WordTrace (prefixWord ++ tailWord_2947252) baseStart_2947252 baseEnd_2947252 := by
    simpa [prefixWord, tailWord_2947252, baseEnd_2947252] using wordTrace_append hprefix tailTrace_2947252
  have hstable : (prefixWord ++ tailWord_2947252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947252).length < 2 ^ (prefixWord ++ tailWord_2947252).sum := by decide
  have hdescent : baseEnd_2947252 < baseStart_2947252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947278 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 1, 8]
def baseStart_2947278 : Nat := 118140960795 + 2947278 * 2 ^ 59
def prefixEnd_2947278 : Nat := 4983230072969 + 3 ^ 40 * 2947278 * 2
def baseEnd_2947278 : Nat := 504456745474008331656907

theorem tailTrace_2947278 : CollatzResearch.WordTrace tailWord_2947278 prefixEnd_2947278 504456745474008331656907 := by
  unfold tailWord_2947278
  simp only [CollatzResearch.WordTrace]
  refine ⟨13437007477065329481671311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71664039877681757235580325 13437007477065329481671311)
  ·
    refine ⟨20155511215597994222506967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13437007477065329481671311 20155511215597994222506967)
    ·
      refine ⟨30233266823396991333760451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20155511215597994222506967 30233266823396991333760451)
      ·
        refine ⟨45349900235095487000640677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30233266823396991333760451 45349900235095487000640677)
        ·
          refine ⟨8503106294080403812620127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45349900235095487000640677 8503106294080403812620127)
          ·
            refine ⟨12754659441120605718930191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8503106294080403812620127 12754659441120605718930191)
            ·
              refine ⟨19131989161680908578395287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12754659441120605718930191 19131989161680908578395287)
              ·
                refine ⟨28697983742521362867592931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19131989161680908578395287 28697983742521362867592931)
                ·
                  refine ⟨43046975613782044301389397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28697983742521362867592931 43046975613782044301389397)
                  ·
                    refine ⟨504456745474008331656907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43046975613782044301389397 504456745474008331656907)
                    ·
                      rfl

theorem cell23_2947278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_2947278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947278 prefixEnd_2947278 := by exact prefixLift 2947278
  have htrace : WordTrace (prefixWord ++ tailWord_2947278) baseStart_2947278 baseEnd_2947278 := by
    simpa [prefixWord, tailWord_2947278, baseEnd_2947278] using wordTrace_append hprefix tailTrace_2947278
  have hstable : (prefixWord ++ tailWord_2947278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947278).length < 2 ^ (prefixWord ++ tailWord_2947278).sum := by decide
  have hdescent : baseEnd_2947278 < baseStart_2947278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947291 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 9]
def baseStart_2947291 : Nat := 118140960795 + 2947291 * 2 ^ 59
def prefixEnd_2947291 : Nat := 4983230072969 + 3 ^ 40 * 2947291 * 2
def baseEnd_2947291 : Nat := 168152990185614827123129

theorem tailTrace_2947291 : CollatzResearch.WordTrace tailWord_2947291 prefixEnd_2947291 168152990185614827123129 := by
  unfold tailWord_2947291
  simp only [CollatzResearch.WordTrace]
  refine ⟨107496533965475539073593727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71664355976983692715729151 107496533965475539073593727)
  ·
    refine ⟨161244800948213308610390591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107496533965475539073593727 161244800948213308610390591)
    ·
      refine ⟨241867201422319962915585887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161244800948213308610390591 241867201422319962915585887)
      ·
        refine ⟨362800802133479944373378831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241867201422319962915585887 362800802133479944373378831)
        ·
          refine ⟨544201203200219916560068247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362800802133479944373378831 544201203200219916560068247)
          ·
            refine ⟨816301804800329874840102371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544201203200219916560068247 816301804800329874840102371)
            ·
              refine ⟨1224452707200494812260153557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816301804800329874840102371 1224452707200494812260153557)
              ·
                refine ⟨28698110325011597162347349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1224452707200494812260153557 28698110325011597162347349)
                ·
                  refine ⟨168152990185614827123129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28698110325011597162347349 168152990185614827123129)
                  ·
                    rfl

theorem cell23_2947291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 9].length) (baseStart_2947291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947291 prefixEnd_2947291 := by exact prefixLift 2947291
  have htrace : WordTrace (prefixWord ++ tailWord_2947291) baseStart_2947291 baseEnd_2947291 := by
    simpa [prefixWord, tailWord_2947291, baseEnd_2947291] using wordTrace_append hprefix tailTrace_2947291
  have hstable : (prefixWord ++ tailWord_2947291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947291).length < 2 ^ (prefixWord ++ tailWord_2947291).sum := by decide
  have hdescent : baseEnd_2947291 < baseStart_2947291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947336 : List Nat := [2, 1, 3, 2, 3, 2, 3, 1, 2, 2, 2]
def baseStart_2947336 : Nat := 118140960795 + 2947336 * 2 ^ 59
def prefixEnd_2947336 : Nat := 4983230072969 + 3 ^ 40 * 2947336 * 2
def baseEnd_2947336 : Nat := 1513400018299985768045455

theorem tailTrace_2947336 : CollatzResearch.WordTrace tailWord_2947336 prefixEnd_2947336 1513400018299985768045455 := by
  unfold tailWord_2947336
  simp only [CollatzResearch.WordTrace]
  refine ⟨53749087625156255879490931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71665450166875007839321241 53749087625156255879490931)
  ·
    refine ⟨80623631437734383819236397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53749087625156255879490931 80623631437734383819236397)
    ·
      refine ⟨30233861789150393932213649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80623631437734383819236397 30233861789150393932213649)
      ·
        refine ⟨22675396341862795449160237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30233861789150393932213649 22675396341862795449160237)
        ·
          refine ⟨8503273628198548293435089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22675396341862795449160237 8503273628198548293435089)
          ·
            refine ⟨6377455221148911220076317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8503273628198548293435089 6377455221148911220076317)
            ·
              refine ⟨2391545707930841707528619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6377455221148911220076317 2391545707930841707528619)
              ·
                refine ⟨3587318561896262561292929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2391545707930841707528619 3587318561896262561292929)
                ·
                  refine ⟨2690488921422196920969697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3587318561896262561292929 2690488921422196920969697)
                  ·
                    refine ⟨2017866691066647690727273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2690488921422196920969697 2017866691066647690727273)
                    ·
                      refine ⟨1513400018299985768045455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2017866691066647690727273 1513400018299985768045455)
                      ·
                        rfl

theorem cell23_2947336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_2947336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947336 prefixEnd_2947336 := by exact prefixLift 2947336
  have htrace : WordTrace (prefixWord ++ tailWord_2947336) baseStart_2947336 baseEnd_2947336 := by
    simpa [prefixWord, tailWord_2947336, baseEnd_2947336] using wordTrace_append hprefix tailTrace_2947336
  have hstable : (prefixWord ++ tailWord_2947336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947336).length < 2 ^ (prefixWord ++ tailWord_2947336).sum := by decide
  have hdescent : baseEnd_2947336 < baseStart_2947336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947338 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 1, 7]
def baseStart_2947338 : Nat := 118140960795 + 2947338 * 2 ^ 59
def prefixEnd_2947338 : Nat := 4983230072969 + 3 ^ 40 * 2947338 * 2
def baseEnd_2947338 : Nat := 504467015087098253406815

theorem tailTrace_2947338 : CollatzResearch.WordTrace tailWord_2947338 prefixEnd_2947338 504467015087098253406815 := by
  unfold tailWord_2947338
  simp only [CollatzResearch.WordTrace]
  refine ⟨26874562049076316525138667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71665498797536844067036445 26874562049076316525138667)
  ·
    refine ⟨40311843073614474787708001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26874562049076316525138667 40311843073614474787708001)
    ·
      refine ⟨30233882305210856090781001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40311843073614474787708001 30233882305210856090781001)
      ·
        refine ⟨22675411728908142068085751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30233882305210856090781001 22675411728908142068085751)
        ·
          refine ⟨34013117593362213102128627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22675411728908142068085751 34013117593362213102128627)
          ·
            refine ⟨51019676390043319653192941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34013117593362213102128627 51019676390043319653192941)
            ·
              refine ⟨19132378646266244869947353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51019676390043319653192941 19132378646266244869947353)
              ·
                refine ⟨14349283984699683652460515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19132378646266244869947353 14349283984699683652460515)
                ·
                  refine ⟨21523925977049525478690773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14349283984699683652460515 21523925977049525478690773)
                  ·
                    refine ⟨504467015087098253406815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21523925977049525478690773 504467015087098253406815)
                    ·
                      rfl

theorem cell23_2947338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_2947338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947338 prefixEnd_2947338 := by exact prefixLift 2947338
  have htrace : WordTrace (prefixWord ++ tailWord_2947338) baseStart_2947338 baseEnd_2947338 := by
    simpa [prefixWord, tailWord_2947338, baseEnd_2947338] using wordTrace_append hprefix tailTrace_2947338
  have hstable : (prefixWord ++ tailWord_2947338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947338).length < 2 ^ (prefixWord ++ tailWord_2947338).sum := by decide
  have hdescent : baseEnd_2947338 < baseStart_2947338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947375 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 4, 4, 2]
def baseStart_2947375 : Nat := 118140960795 + 2947375 * 2 ^ 59
def prefixEnd_2947375 : Nat := 4983230072969 + 3 ^ 40 * 2947375 * 2
def baseEnd_2947375 : Nat := 1513420044045511115457775

theorem tailTrace_2947375 : CollatzResearch.WordTrace tailWord_2947375 prefixEnd_2947375 1513420044045511115457775 := by
  unfold tailWord_2947375
  simp only [CollatzResearch.WordTrace]
  refine ⟨107499597697171221419651579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71666398464780814279767719 107499597697171221419651579)
  ·
    refine ⟨161249396545756832129477369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107499597697171221419651579 161249396545756832129477369)
    ·
      refine ⟨120937047409317624097108027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161249396545756832129477369 120937047409317624097108027)
      ·
        refine ⟨181405571113976436145662041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120937047409317624097108027 181405571113976436145662041)
        ·
          refine ⟨136054178335482327109246531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181405571113976436145662041 136054178335482327109246531)
          ·
            refine ⟨204081267503223490663869797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136054178335482327109246531 204081267503223490663869797)
            ·
              refine ⟨38265237656854404499475587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204081267503223490663869797 38265237656854404499475587)
              ·
                refine ⟨57397856485281606749213381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38265237656854404499475587 57397856485281606749213381)
                ·
                  refine ⟨10762098090990301265477509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57397856485281606749213381 10762098090990301265477509)
                  ·
                    refine ⟨2017893392060681487277033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10762098090990301265477509 2017893392060681487277033)
                    ·
                      refine ⟨1513420044045511115457775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2017893392060681487277033 1513420044045511115457775)
                      ·
                        rfl

theorem cell23_2947375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 4, 2].length) (baseStart_2947375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947375 prefixEnd_2947375 := by exact prefixLift 2947375
  have htrace : WordTrace (prefixWord ++ tailWord_2947375) baseStart_2947375 baseEnd_2947375 := by
    simpa [prefixWord, tailWord_2947375, baseEnd_2947375] using wordTrace_append hprefix tailTrace_2947375
  have hstable : (prefixWord ++ tailWord_2947375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947375).length < 2 ^ (prefixWord ++ tailWord_2947375).sum := by decide
  have hdescent : baseEnd_2947375 < baseStart_2947375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947412 : List Nat := [2, 4, 1, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_2947412 : Nat := 118140960795 + 2947412 * 2 ^ 59
def prefixEnd_2947412 : Nat := 4983230072969 + 3 ^ 40 * 2947412 * 2
def baseEnd_2947412 : Nat := 1513439042829727470695105

theorem tailTrace_2947412 : CollatzResearch.WordTrace tailWord_2947412 prefixEnd_2947412 1513439042829727470695105 := by
  unfold tailWord_2947412
  simp only [CollatzResearch.WordTrace]
  refine ⟨53750473599018588369374245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71667298132024784492498993 53750473599018588369374245)
  ·
    refine ⟨10078213799815985319257671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53750473599018588369374245 10078213799815985319257671)
    ·
      refine ⟨15117320699723977978886507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10078213799815985319257671 15117320699723977978886507)
      ·
        refine ⟨22675981049585966968329761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15117320699723977978886507 22675981049585966968329761)
        ·
          refine ⟨17006985787189475226247321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22675981049585966968329761 17006985787189475226247321)
          ·
            refine ⟨12755239340392106419685491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17006985787189475226247321 12755239340392106419685491)
            ·
              refine ⟨19132859010588159629528237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12755239340392106419685491 19132859010588159629528237)
              ·
                refine ⟨7174822128970559861073089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19132859010588159629528237 7174822128970559861073089)
                ·
                  refine ⟨5381116596727919895804817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7174822128970559861073089 5381116596727919895804817)
                  ·
                    refine ⟨4035837447545939921853613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5381116596727919895804817 4035837447545939921853613)
                    ·
                      refine ⟨1513439042829727470695105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4035837447545939921853613 1513439042829727470695105)
                      ·
                        rfl

theorem cell23_2947412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_2947412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947412 prefixEnd_2947412 := by exact prefixLift 2947412
  have htrace : WordTrace (prefixWord ++ tailWord_2947412) baseStart_2947412 baseEnd_2947412 := by
    simpa [prefixWord, tailWord_2947412, baseEnd_2947412] using wordTrace_append hprefix tailTrace_2947412
  have hstable : (prefixWord ++ tailWord_2947412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947412).length < 2 ^ (prefixWord ++ tailWord_2947412).sum := by decide
  have hdescent : baseEnd_2947412 < baseStart_2947412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947418 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8]
def baseStart_2947418 : Nat := 118140960795 + 2947418 * 2 ^ 59
def prefixEnd_2947418 : Nat := 4983230072969 + 3 ^ 40 * 2947418 * 2
def baseEnd_2947418 : Nat := 1513442123713654447220077

theorem tailTrace_2947418 : CollatzResearch.WordTrace tailWord_2947418 prefixEnd_2947418 1513442123713654447220077 := by
  unfold tailWord_2947418
  simp only [CollatzResearch.WordTrace]
  refine ⟨26875291509003859940866727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71667444024010293175644605 26875291509003859940866727)
  ·
    refine ⟨40312937263505789911300091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26875291509003859940866727 40312937263505789911300091)
    ·
      refine ⟨60469405895258684866950137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40312937263505789911300091 60469405895258684866950137)
      ·
        refine ⟨45352054421444013650212603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60469405895258684866950137 45352054421444013650212603)
        ·
          refine ⟨68028081632166020475318905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45352054421444013650212603 68028081632166020475318905)
          ·
            refine ⟨51021061224124515356489179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68028081632166020475318905 51021061224124515356489179)
            ·
              refine ⟨76531591836186773034733769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51021061224124515356489179 76531591836186773034733769)
              ·
                refine ⟨57398693877140079776050327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76531591836186773034733769 57398693877140079776050327)
                ·
                  refine ⟨86098040815710119664075491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57398693877140079776050327 86098040815710119664075491)
                  ·
                    refine ⟨129147061223565179496113237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86098040815710119664075491 129147061223565179496113237)
                    ·
                      refine ⟨1513442123713654447220077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 129147061223565179496113237 1513442123713654447220077)
                      ·
                        rfl

theorem cell23_2947418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_2947418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947418 prefixEnd_2947418 := by exact prefixLift 2947418
  have htrace : WordTrace (prefixWord ++ tailWord_2947418) baseStart_2947418 baseEnd_2947418 := by
    simpa [prefixWord, tailWord_2947418, baseEnd_2947418] using wordTrace_append hprefix tailTrace_2947418
  have hstable : (prefixWord ++ tailWord_2947418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947418).length < 2 ^ (prefixWord ++ tailWord_2947418).sum := by decide
  have hdescent : baseEnd_2947418 < baseStart_2947418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947432 : List Nat := [2, 1, 4, 2, 2, 2, 2, 2, 6]
def baseStart_2947432 : Nat := 118140960795 + 2947432 * 2 ^ 59
def prefixEnd_2947432 : Nat := 4983230072969 + 3 ^ 40 * 2947432 * 2
def baseEnd_2947432 : Nat := 168161034715868599160557

theorem tailTrace_2947432 : CollatzResearch.WordTrace tailWord_2947432 prefixEnd_2947432 168161034715868599160557 := by
  unfold tailWord_2947432
  simp only [CollatzResearch.WordTrace]
  refine ⟨53750838328982360077238275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71667784438643146769651033 53750838328982360077238275)
  ·
    refine ⟨80626257493473540115857413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53750838328982360077238275 80626257493473540115857413)
    ·
      refine ⟨15117423280026288771723265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80626257493473540115857413 15117423280026288771723265)
      ·
        refine ⟨11338067460019716578792449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15117423280026288771723265 11338067460019716578792449)
        ·
          refine ⟨8503550595014787434094337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11338067460019716578792449 8503550595014787434094337)
          ·
            refine ⟨6377662946261090575570753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8503550595014787434094337 6377662946261090575570753)
            ·
              refine ⟨4783247209695817931678065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6377662946261090575570753 4783247209695817931678065)
              ·
                refine ⟨3587435407271863448758549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4783247209695817931678065 3587435407271863448758549)
                ·
                  refine ⟨168161034715868599160557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3587435407271863448758549 168161034715868599160557)
                  ·
                    rfl

theorem cell23_2947432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 6].length) (baseStart_2947432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947432 prefixEnd_2947432 := by exact prefixLift 2947432
  have htrace : WordTrace (prefixWord ++ tailWord_2947432) baseStart_2947432 baseEnd_2947432 := by
    simpa [prefixWord, tailWord_2947432, baseEnd_2947432] using wordTrace_append hprefix tailTrace_2947432
  have hstable : (prefixWord ++ tailWord_2947432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947432).length < 2 ^ (prefixWord ++ tailWord_2947432).sum := by decide
  have hdescent : baseEnd_2947432 < baseStart_2947432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947459 : List Nat := [1, 1, 1, 3, 6, 1, 1, 2, 3, 1, 3]
def baseStart_2947459 : Nat := 118140960795 + 2947459 * 2 ^ 59
def prefixEnd_2947459 : Nat := 4983230072969 + 3 ^ 40 * 2947459 * 2
def baseEnd_2947459 : Nat := 1513463176420488786807389

theorem tailTrace_2947459 : CollatzResearch.WordTrace tailWord_2947459 prefixEnd_2947459 1513463176420488786807389 := by
  unfold tailWord_2947459
  simp only [CollatzResearch.WordTrace]
  refine ⟨107502661428866903765709431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71668440952577935843806287 107502661428866903765709431)
  ·
    refine ⟨161253992143300355648564147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107502661428866903765709431 161253992143300355648564147)
    ·
      refine ⟨241880988214950533472846221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161253992143300355648564147 241880988214950533472846221)
      ·
        refine ⟨90705370580606450052317333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241880988214950533472846221 90705370580606450052317333)
        ·
          refine ⟨4251814245965927346202375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90705370580606450052317333 4251814245965927346202375)
          ·
            refine ⟨6377721368948891019303563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4251814245965927346202375 6377721368948891019303563)
            ·
              refine ⟨9566582053423336528955345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6377721368948891019303563 9566582053423336528955345)
              ·
                refine ⟨7174936540067502396716509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9566582053423336528955345 7174936540067502396716509)
                ·
                  refine ⟨2690601202525313398768691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7174936540067502396716509 2690601202525313398768691)
                  ·
                    refine ⟨4035901803787970098153037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2690601202525313398768691 4035901803787970098153037)
                    ·
                      refine ⟨1513463176420488786807389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4035901803787970098153037 1513463176420488786807389)
                      ·
                        rfl

theorem cell23_2947459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 1, 3].length) (baseStart_2947459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947459 prefixEnd_2947459 := by exact prefixLift 2947459
  have htrace : WordTrace (prefixWord ++ tailWord_2947459) baseStart_2947459 baseEnd_2947459 := by
    simpa [prefixWord, tailWord_2947459, baseEnd_2947459] using wordTrace_append hprefix tailTrace_2947459
  have hstable : (prefixWord ++ tailWord_2947459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947459).length < 2 ^ (prefixWord ++ tailWord_2947459).sum := by decide
  have hdescent : baseEnd_2947459 < baseStart_2947459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947509 : List Nat := [1, 3, 3, 2, 3, 2, 1, 1, 1, 6]
def baseStart_2947509 : Nat := 118140960795 + 2947509 * 2 ^ 59
def prefixEnd_2947509 : Nat := 4983230072969 + 3 ^ 40 * 2947509 * 2
def baseEnd_2947509 : Nat := 504496283484404530394053

theorem tailTrace_2947509 : CollatzResearch.WordTrace tailWord_2947509 prefixEnd_2947509 504496283484404530394053 := by
  unfold tailWord_2947509
  simp only [CollatzResearch.WordTrace]
  refine ⟨107504485078685762305029581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71669656719123841536686387 107504485078685762305029581)
  ·
    refine ⟨40314181904507160864386093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107504485078685762305029581 40314181904507160864386093)
    ·
      refine ⟨15117818214190185324144785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40314181904507160864386093 15117818214190185324144785)
      ·
        refine ⟨11338363660642638993108589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15117818214190185324144785 11338363660642638993108589)
        ·
          refine ⟨4251886372740989622415721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11338363660642638993108589 4251886372740989622415721)
          ·
            refine ⟨3188914779555742216811791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4251886372740989622415721 3188914779555742216811791)
            ·
              refine ⟨4783372169333613325217687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3188914779555742216811791 4783372169333613325217687)
              ·
                refine ⟨7175058254000419987826531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4783372169333613325217687 7175058254000419987826531)
                ·
                  refine ⟨10762587381000629981739797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7175058254000419987826531 10762587381000629981739797)
                  ·
                    refine ⟨504496283484404530394053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10762587381000629981739797 504496283484404530394053)
                    ·
                      rfl

theorem cell23_2947509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_2947509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947509 prefixEnd_2947509 := by exact prefixLift 2947509
  have htrace : WordTrace (prefixWord ++ tailWord_2947509) baseStart_2947509 baseEnd_2947509 := by
    simpa [prefixWord, tailWord_2947509, baseEnd_2947509] using wordTrace_append hprefix tailTrace_2947509
  have hstable : (prefixWord ++ tailWord_2947509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947509).length < 2 ^ (prefixWord ++ tailWord_2947509).sum := by decide
  have hdescent : baseEnd_2947509 < baseStart_2947509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947515 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 3]
def baseStart_2947515 : Nat := 118140960795 + 2947515 * 2 ^ 59
def prefixEnd_2947515 : Nat := 4983230072969 + 3 ^ 40 * 2947515 * 2
def baseEnd_2947515 : Nat := 1513491931337140567707131

theorem tailTrace_2947515 : CollatzResearch.WordTrace tailWord_2947515 prefixEnd_2947515 1513491931337140567707131 := by
  unfold tailWord_2947515
  simp only [CollatzResearch.WordTrace]
  refine ⟨107504703916664025329747999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71669802611109350219831999 107504703916664025329747999)
  ·
    refine ⟨161257055874996037994621999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107504703916664025329747999 161257055874996037994621999)
    ·
      refine ⟨241885583812494056991932999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161257055874996037994621999 241885583812494056991932999)
      ·
        refine ⟨362828375718741085487899499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241885583812494056991932999 362828375718741085487899499)
        ·
          refine ⟨544242563578111628231849249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362828375718741085487899499 544242563578111628231849249)
          ·
            refine ⟨408181922683583721173886937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 544242563578111628231849249 408181922683583721173886937)
            ·
              refine ⟨306136442012687790880415203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408181922683583721173886937 306136442012687790880415203)
              ·
                refine ⟨459204663019031686320622805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306136442012687790880415203 459204663019031686320622805)
                ·
                  refine ⟨10762609289508555148139597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 459204663019031686320622805 10762609289508555148139597)
                  ·
                    refine ⟨4035978483565708180552349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10762609289508555148139597 4035978483565708180552349)
                    ·
                      refine ⟨1513491931337140567707131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4035978483565708180552349 1513491931337140567707131)
                      ·
                        rfl

theorem cell23_2947515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 3].length) (baseStart_2947515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947515 prefixEnd_2947515 := by exact prefixLift 2947515
  have htrace : WordTrace (prefixWord ++ tailWord_2947515) baseStart_2947515 baseEnd_2947515 := by
    simpa [prefixWord, tailWord_2947515, baseEnd_2947515] using wordTrace_append hprefix tailTrace_2947515
  have hstable : (prefixWord ++ tailWord_2947515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947515).length < 2 ^ (prefixWord ++ tailWord_2947515).sum := by decide
  have hdescent : baseEnd_2947515 < baseStart_2947515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947516 : List Nat := [2, 2, 2, 4, 1, 1, 2, 2, 3, 2, 2]
def baseStart_2947516 : Nat := 118140960795 + 2947516 * 2 ^ 59
def prefixEnd_2947516 : Nat := 4983230072969 + 3 ^ 40 * 2947516 * 2
def baseEnd_2947516 : Nat := 1513492444817795063794627

theorem tailTrace_2947516 : CollatzResearch.WordTrace tailWord_2947516 prefixEnd_2947516 1513492444817795063794627 := by
  unfold tailWord_2947516
  simp only [CollatzResearch.WordTrace]
  refine ⟨53752370194830201250267201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71669826926440268333689601 53752370194830201250267201)
  ·
    refine ⟨40314277646122650937700401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53752370194830201250267201 40314277646122650937700401)
    ·
      refine ⟨30235708234591988203275301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40314277646122650937700401 30235708234591988203275301)
      ·
        refine ⟨5669195293985997788114119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30235708234591988203275301 5669195293985997788114119)
        ·
          refine ⟨8503792940978996682171179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5669195293985997788114119 8503792940978996682171179)
          ·
            refine ⟨12755689411468495023256769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8503792940978996682171179 12755689411468495023256769)
            ·
              refine ⟨9566767058601371267442577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12755689411468495023256769 9566767058601371267442577)
              ·
                refine ⟨7175075293951028450581933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9566767058601371267442577 7175075293951028450581933)
                ·
                  refine ⟨2690653235231635668968225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7175075293951028450581933 2690653235231635668968225)
                  ·
                    refine ⟨2017989926423726751726169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2690653235231635668968225 2017989926423726751726169)
                    ·
                      refine ⟨1513492444817795063794627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2017989926423726751726169 1513492444817795063794627)
                      ·
                        rfl

theorem cell23_2947516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_2947516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947516 prefixEnd_2947516 := by exact prefixLift 2947516
  have htrace : WordTrace (prefixWord ++ tailWord_2947516) baseStart_2947516 baseEnd_2947516 := by
    simpa [prefixWord, tailWord_2947516, baseEnd_2947516] using wordTrace_append hprefix tailTrace_2947516
  have hstable : (prefixWord ++ tailWord_2947516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947516).length < 2 ^ (prefixWord ++ tailWord_2947516).sum := by decide
  have hdescent : baseEnd_2947516 < baseStart_2947516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947545 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 2, 2, 5]
def baseStart_2947545 : Nat := 118140960795 + 2947545 * 2 ^ 59
def prefixEnd_2947545 : Nat := 4983230072969 + 3 ^ 40 * 2947545 * 2
def baseEnd_2947545 : Nat := 1513507335756775450331993

theorem tailTrace_2947545 : CollatzResearch.WordTrace tailWord_2947545 prefixEnd_2947545 1513507335756775450331993 := by
  unfold tailWord_2947545
  simp only [CollatzResearch.WordTrace]
  refine ⟨107505798106555340453340089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71670532071036893635560059 107505798106555340453340089)
  ·
    refine ⟨80629348579916505340005067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107505798106555340453340089 80629348579916505340005067)
    ·
      refine ⟨120944022869874758010007601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80629348579916505340005067 120944022869874758010007601)
      ·
        refine ⟨90708017152406068507505701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120944022869874758010007601 90708017152406068507505701)
        ·
          refine ⟨17007753216076137845157319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90708017152406068507505701 17007753216076137845157319)
          ·
            refine ⟨25511629824114206767735979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17007753216076137845157319 25511629824114206767735979)
            ·
              refine ⟨38267444736171310151603969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25511629824114206767735979 38267444736171310151603969)
              ·
                refine ⟨28700583552128482613702977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38267444736171310151603969 28700583552128482613702977)
                ·
                  refine ⟨21525437664096361960277233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28700583552128482613702977 21525437664096361960277233)
                  ·
                    refine ⟨16144078248072271470207925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21525437664096361960277233 16144078248072271470207925)
                    ·
                      refine ⟨1513507335756775450331993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16144078248072271470207925 1513507335756775450331993)
                      ·
                        rfl

theorem cell23_2947545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_2947545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947545 prefixEnd_2947545 := by exact prefixLift 2947545
  have htrace : WordTrace (prefixWord ++ tailWord_2947545) baseStart_2947545 baseEnd_2947545 := by
    simpa [prefixWord, tailWord_2947545, baseEnd_2947545] using wordTrace_append hprefix tailTrace_2947545
  have hstable : (prefixWord ++ tailWord_2947545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947545).length < 2 ^ (prefixWord ++ tailWord_2947545).sum := by decide
  have hdescent : baseEnd_2947545 < baseStart_2947545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947549 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_2947549 : Nat := 118140960795 + 2947549 * 2 ^ 59
def prefixEnd_2947549 : Nat := 4983230072969 + 3 ^ 40 * 2947549 * 2
def baseEnd_2947549 : Nat := 1513509389679393434681975

theorem tailTrace_2947549 : CollatzResearch.WordTrace tailWord_2947549 prefixEnd_2947549 1513509389679393434681975 := by
  unfold tailWord_2947549
  simp only [CollatzResearch.WordTrace]
  refine ⟨107505943998540849136485701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71670629332360566090990467 107505943998540849136485701)
  ·
    refine ⟨20157364499726409213091069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107505943998540849136485701 20157364499726409213091069)
    ·
      refine ⟨7559011687397403454909151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20157364499726409213091069 7559011687397403454909151)
      ·
        refine ⟨11338517531096105182363727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7559011687397403454909151 11338517531096105182363727)
        ·
          refine ⟨17007776296644157773545591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11338517531096105182363727 17007776296644157773545591)
          ·
            refine ⟨25511664444966236660318387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17007776296644157773545591 25511664444966236660318387)
            ·
              refine ⟨38267496667449354990477581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25511664444966236660318387 38267496667449354990477581)
              ·
                refine ⟨14350311250293508121429093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38267496667449354990477581 14350311250293508121429093)
                ·
                  refine ⟨2690683359430032772767955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14350311250293508121429093 2690683359430032772767955)
                  ·
                    refine ⟨4036025039145049159151933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2690683359430032772767955 4036025039145049159151933)
                    ·
                      refine ⟨1513509389679393434681975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4036025039145049159151933 1513509389679393434681975)
                      ·
                        rfl

theorem cell23_2947549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_2947549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947549 prefixEnd_2947549 := by exact prefixLift 2947549
  have htrace : WordTrace (prefixWord ++ tailWord_2947549) baseStart_2947549 baseEnd_2947549 := by
    simpa [prefixWord, tailWord_2947549, baseEnd_2947549] using wordTrace_append hprefix tailTrace_2947549
  have hstable : (prefixWord ++ tailWord_2947549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947549).length < 2 ^ (prefixWord ++ tailWord_2947549).sum := by decide
  have hdescent : baseEnd_2947549 < baseStart_2947549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947559 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 3, 3, 2]
def baseStart_2947559 : Nat := 118140960795 + 2947559 * 2 ^ 59
def prefixEnd_2947559 : Nat := 4983230072969 + 3 ^ 40 * 2947559 * 2
def baseEnd_2947559 : Nat := 1513514524485938395556929

theorem tailTrace_2947559 : CollatzResearch.WordTrace tailWord_2947559 prefixEnd_2947559 1513514524485938395556929 := by
  unfold tailWord_2947559
  simp only [CollatzResearch.WordTrace]
  refine ⟨107506308728504620844349731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71670872485669747229566487 107506308728504620844349731)
  ·
    refine ⟨161259463092756931266524597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107506308728504620844349731 161259463092756931266524597)
    ·
      refine ⟨15118074664945962306236681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161259463092756931266524597 15118074664945962306236681)
      ·
        refine ⟨11338555998709471729677511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15118074664945962306236681 11338555998709471729677511)
        ·
          refine ⟨17007833998064207594516267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11338555998709471729677511 17007833998064207594516267)
          ·
            refine ⟨25511750997096311391774401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17007833998064207594516267 25511750997096311391774401)
            ·
              refine ⟨19133813247822233543830801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25511750997096311391774401 19133813247822233543830801)
              ·
                refine ⟨14350359935866675157873101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19133813247822233543830801 14350359935866675157873101)
                ·
                  refine ⟨5381384975950003184202413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14350359935866675157873101 5381384975950003184202413)
                  ·
                    refine ⟨2018019365981251194075905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5381384975950003184202413 2018019365981251194075905)
                    ·
                      refine ⟨1513514524485938395556929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2018019365981251194075905 1513514524485938395556929)
                      ·
                        rfl

theorem cell23_2947559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_2947559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947559 prefixEnd_2947559 := by exact prefixLift 2947559
  have htrace : WordTrace (prefixWord ++ tailWord_2947559) baseStart_2947559 baseEnd_2947559 := by
    simpa [prefixWord, tailWord_2947559, baseEnd_2947559] using wordTrace_append hprefix tailTrace_2947559
  have hstable : (prefixWord ++ tailWord_2947559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947559).length < 2 ^ (prefixWord ++ tailWord_2947559).sum := by decide
  have hdescent : baseEnd_2947559 < baseStart_2947559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947566 : List Nat := [4, 1, 2, 1, 2, 3, 1, 3, 2, 1, 3]
def baseStart_2947566 : Nat := 118140960795 + 2947566 * 2 ^ 59
def prefixEnd_2947566 : Nat := 4983230072969 + 3 ^ 40 * 2947566 * 2
def baseEnd_2947566 : Nat := 1513518118850519868169397

theorem tailTrace_2947566 : CollatzResearch.WordTrace tailWord_2947566 prefixEnd_2947566 1513518118850519868169397 := by
  unfold tailWord_2947566
  simp only [CollatzResearch.WordTrace]
  refine ⟨13438320504934907629981819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71671042692986174026569701 13438320504934907629981819)
  ·
    refine ⟨20157480757402361444972729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13438320504934907629981819 20157480757402361444972729)
    ·
      refine ⟨15118110568051771083729547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20157480757402361444972729 15118110568051771083729547)
      ·
        refine ⟨22677165852077656625594321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15118110568051771083729547 22677165852077656625594321)
        ·
          refine ⟨17007874389058242469195741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22677165852077656625594321 17007874389058242469195741)
          ·
            refine ⟨6377952895896840925948403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17007874389058242469195741 6377952895896840925948403)
            ·
              refine ⟨9566929343845261388922605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6377952895896840925948403 9566929343845261388922605)
              ·
                refine ⟨3587598503941973020845977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9566929343845261388922605 3587598503941973020845977)
                ·
                  refine ⟨2690698877956479765634483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3587598503941973020845977 2690698877956479765634483)
                  ·
                    refine ⟨4036048316934719648451725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2690698877956479765634483 4036048316934719648451725)
                    ·
                      refine ⟨1513518118850519868169397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4036048316934719648451725 1513518118850519868169397)
                      ·
                        rfl

theorem cell23_2947566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_2947566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947566 prefixEnd_2947566 := by exact prefixLift 2947566
  have htrace : WordTrace (prefixWord ++ tailWord_2947566) baseStart_2947566 baseEnd_2947566 := by
    simpa [prefixWord, tailWord_2947566, baseEnd_2947566] using wordTrace_append hprefix tailTrace_2947566
  have hstable : (prefixWord ++ tailWord_2947566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947566).length < 2 ^ (prefixWord ++ tailWord_2947566).sum := by decide
  have hdescent : baseEnd_2947566 < baseStart_2947566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947589 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 6, 2, 2]
def baseStart_2947589 : Nat := 118140960795 + 2947589 * 2 ^ 59
def prefixEnd_2947589 : Nat := 4983230072969 + 3 ^ 40 * 2947589 * 2
def baseEnd_2947589 : Nat := 1513529928905573278181791

theorem tailTrace_2947589 : CollatzResearch.WordTrace tailWord_2947589 prefixEnd_2947589 1513529928905573278181791 := by
  unfold tailWord_2947589
  simp only [CollatzResearch.WordTrace]
  refine ⟨107507402918395935967941821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71671601945597290645294547 107507402918395935967941821)
  ·
    refine ⟨40315276094398475987978183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107507402918395935967941821 40315276094398475987978183)
    ·
      refine ⟨60472914141597713981967275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40315276094398475987978183 60472914141597713981967275)
      ·
        refine ⟨90709371212396570972950913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60472914141597713981967275 90709371212396570972950913)
        ·
          refine ⟨68032028409297428229713185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90709371212396570972950913 68032028409297428229713185)
          ·
            refine ⟨51024021306973071172284889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68032028409297428229713185 51024021306973071172284889)
            ·
              refine ⟨38268015980229803379213667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51024021306973071172284889 38268015980229803379213667)
              ·
                refine ⟨57402023970344705068820501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38268015980229803379213667 57402023970344705068820501)
                ·
                  refine ⟨2690719873609908050100961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57402023970344705068820501 2690719873609908050100961)
                  ·
                    refine ⟨2018039905207431037575721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2690719873609908050100961 2018039905207431037575721)
                    ·
                      refine ⟨1513529928905573278181791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2018039905207431037575721 1513529928905573278181791)
                      ·
                        rfl

theorem cell23_2947589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 2, 2].length) (baseStart_2947589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947589 prefixEnd_2947589 := by exact prefixLift 2947589
  have htrace : WordTrace (prefixWord ++ tailWord_2947589) baseStart_2947589 baseEnd_2947589 := by
    simpa [prefixWord, tailWord_2947589, baseEnd_2947589] using wordTrace_append hprefix tailTrace_2947589
  have hstable : (prefixWord ++ tailWord_2947589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947589).length < 2 ^ (prefixWord ++ tailWord_2947589).sum := by decide
  have hdescent : baseEnd_2947589 < baseStart_2947589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947615 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 8]
def baseStart_2947615 : Nat := 118140960795 + 2947615 * 2 ^ 59
def prefixEnd_2947615 : Nat := 4983230072969 + 3 ^ 40 * 2947615 * 2
def baseEnd_2947615 : Nat := 1513543279402590176456671

theorem tailTrace_2947615 : CollatzResearch.WordTrace tailWord_2947615 prefixEnd_2947615 1513543279402590176456671 := by
  unfold tailWord_2947615
  simp only [CollatzResearch.WordTrace]
  refine ⟨107508351216301742408388299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71672234144201161605592199 107508351216301742408388299)
  ·
    refine ⟨161262526824452613612582449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107508351216301742408388299 161262526824452613612582449)
    ·
      refine ⟨120946895118339460209436837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161262526824452613612582449 120946895118339460209436837)
      ·
        refine ⟨22677542834688648789269407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120946895118339460209436837 22677542834688648789269407)
        ·
          refine ⟨34016314252032973183904111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22677542834688648789269407 34016314252032973183904111)
          ·
            refine ⟨51024471378049459775856167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34016314252032973183904111 51024471378049459775856167)
            ·
              refine ⟨76536707067074189663784251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51024471378049459775856167 76536707067074189663784251)
              ·
                refine ⟨114805060600611284495676377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76536707067074189663784251 114805060600611284495676377)
                ·
                  refine ⟨86103795450458463371757283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114805060600611284495676377 86103795450458463371757283)
                  ·
                    refine ⟨129155693175687695057635925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86103795450458463371757283 129155693175687695057635925)
                    ·
                      refine ⟨1513543279402590176456671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 129155693175687695057635925 1513543279402590176456671)
                      ·
                        rfl

theorem cell23_2947615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_2947615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947615 prefixEnd_2947615 := by exact prefixLift 2947615
  have htrace : WordTrace (prefixWord ++ tailWord_2947615) baseStart_2947615 baseEnd_2947615 := by
    simpa [prefixWord, tailWord_2947615, baseEnd_2947615] using wordTrace_append hprefix tailTrace_2947615
  have hstable : (prefixWord ++ tailWord_2947615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947615).length < 2 ^ (prefixWord ++ tailWord_2947615).sum := by decide
  have hdescent : baseEnd_2947615 < baseStart_2947615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947642 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 1, 7]
def baseStart_2947642 : Nat := 118140960795 + 2947642 * 2 ^ 59
def prefixEnd_2947642 : Nat := 4983230072969 + 3 ^ 40 * 2947642 * 2
def baseEnd_2947642 : Nat := 504519047793420523606349

theorem tailTrace_2947642 : CollatzResearch.WordTrace tailWord_2947642 prefixEnd_2947642 504519047793420523606349 := by
  unfold tailWord_2947642
  simp only [CollatzResearch.WordTrace]
  refine ⟨26877333996800981504905295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71672890658135950679747453 26877333996800981504905295)
  ·
    refine ⟨40316000995201472257357943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26877333996800981504905295 40316000995201472257357943)
    ·
      refine ⟨60474001492802208386036915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40316000995201472257357943 60474001492802208386036915)
      ·
        refine ⟨90711002239203312579055373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60474001492802208386036915 90711002239203312579055373)
        ·
          refine ⟨34016625839701242217145765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90711002239203312579055373 34016625839701242217145765)
          ·
            refine ⟨6378117344943982915714831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34016625839701242217145765 6378117344943982915714831)
            ·
              refine ⟨9567176017415974373572247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6378117344943982915714831 9567176017415974373572247)
              ·
                refine ⟨14350764026123961560358371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9567176017415974373572247 14350764026123961560358371)
                ·
                  refine ⟨21526146039185942340537557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14350764026123961560358371 21526146039185942340537557)
                  ·
                    refine ⟨504519047793420523606349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21526146039185942340537557 504519047793420523606349)
                    ·
                      rfl

theorem cell23_2947642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_2947642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947642 prefixEnd_2947642 := by exact prefixLift 2947642
  have htrace : WordTrace (prefixWord ++ tailWord_2947642) baseStart_2947642 baseEnd_2947642 := by
    simpa [prefixWord, tailWord_2947642, baseEnd_2947642] using wordTrace_append hprefix tailTrace_2947642
  have hstable : (prefixWord ++ tailWord_2947642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947642).length < 2 ^ (prefixWord ++ tailWord_2947642).sum := by decide
  have hdescent : baseEnd_2947642 < baseStart_2947642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947675 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 10]
def baseStart_2947675 : Nat := 118140960795 + 2947675 * 2 ^ 59
def prefixEnd_2947675 : Nat := 4983230072969 + 3 ^ 40 * 2947675 * 2
def baseEnd_2947675 : Nat := 1513574088241859941706395

theorem tailTrace_2947675 : CollatzResearch.WordTrace tailWord_2947675 prefixEnd_2947675 1513574088241859941706395 := by
  unfold tailWord_2947675
  simp only [CollatzResearch.WordTrace]
  refine ⟨107510539596084372655572479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71673693064056248437048319 107510539596084372655572479)
  ·
    refine ⟨161265809394126558983358719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107510539596084372655572479 161265809394126558983358719)
    ·
      refine ⟨241898714091189838475038079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161265809394126558983358719 241898714091189838475038079)
      ·
        refine ⟨362848071136784757712557119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241898714091189838475038079 362848071136784757712557119)
        ·
          refine ⟨544272106705177136568835679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362848071136784757712557119 544272106705177136568835679)
          ·
            refine ⟨816408160057765704853253519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544272106705177136568835679 816408160057765704853253519)
            ·
              refine ⟨1224612240086648557279880279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816408160057765704853253519 1224612240086648557279880279)
              ·
                refine ⟨1836918360129972835919820419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1224612240086648557279880279 1836918360129972835919820419)
                ·
                  refine ⟨2755377540194959253879730629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1836918360129972835919820419 2755377540194959253879730629)
                  ·
                    refine ⟨516633288786554860102449493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2755377540194959253879730629 516633288786554860102449493)
                    ·
                      refine ⟨1513574088241859941706395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 516633288786554860102449493 1513574088241859941706395)
                      ·
                        rfl

theorem cell23_2947675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 10].length) (baseStart_2947675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947675 prefixEnd_2947675 := by exact prefixLift 2947675
  have htrace : WordTrace (prefixWord ++ tailWord_2947675) baseStart_2947675 baseEnd_2947675 := by
    simpa [prefixWord, tailWord_2947675, baseEnd_2947675] using wordTrace_append hprefix tailTrace_2947675
  have hstable : (prefixWord ++ tailWord_2947675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947675).length < 2 ^ (prefixWord ++ tailWord_2947675).sum := by decide
  have hdescent : baseEnd_2947675 < baseStart_2947675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947716 : List Nat := [2, 3, 2, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_2947716 : Nat := 118140960795 + 2947716 * 2 ^ 59
def prefixEnd_2947716 : Nat := 4983230072969 + 3 ^ 40 * 2947716 * 2
def baseEnd_2947716 : Nat := 1513595140948694281293707

theorem tailTrace_2947716 : CollatzResearch.WordTrace tailWord_2947716 prefixEnd_2947716 1513595140948694281293707 := by
  unfold tailWord_2947716
  simp only [CollatzResearch.WordTrace]
  refine ⟨53756017494467918328907501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71674689992623891105210001 53756017494467918328907501)
  ·
    refine ⟨20158506560425469373340313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53756017494467918328907501 20158506560425469373340313)
    ·
      refine ⟨15118879920319102030005235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20158506560425469373340313 15118879920319102030005235)
      ·
        refine ⟨22678319880478653045007853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15118879920319102030005235 22678319880478653045007853)
        ·
          refine ⟨8504369955179494891877945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22678319880478653045007853 8504369955179494891877945)
          ·
            refine ⟨6378277466384621168908459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8504369955179494891877945 6378277466384621168908459)
            ·
              refine ⟨9567416199576931753362689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6378277466384621168908459 9567416199576931753362689)
              ·
                refine ⟨7175562149682698815022017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9567416199576931753362689 7175562149682698815022017)
                ·
                  refine ⟨5381671612262024111266513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7175562149682698815022017 5381671612262024111266513)
                  ·
                    refine ⟨4036253709196518083449885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5381671612262024111266513 4036253709196518083449885)
                    ·
                      refine ⟨1513595140948694281293707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4036253709196518083449885 1513595140948694281293707)
                      ·
                        rfl

theorem cell23_2947716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_2947716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947716 prefixEnd_2947716 := by exact prefixLift 2947716
  have htrace : WordTrace (prefixWord ++ tailWord_2947716) baseStart_2947716 baseEnd_2947716 := by
    simpa [prefixWord, tailWord_2947716, baseEnd_2947716] using wordTrace_append hprefix tailTrace_2947716
  have hstable : (prefixWord ++ tailWord_2947716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947716).length < 2 ^ (prefixWord ++ tailWord_2947716).sum := by decide
  have hdescent : baseEnd_2947716 < baseStart_2947716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947780 : List Nat := [2, 3, 3, 1, 1, 3, 1, 4, 1, 1, 3]
def baseStart_2947780 : Nat := 118140960795 + 2947780 * 2 ^ 59
def prefixEnd_2947780 : Nat := 4983230072969 + 3 ^ 40 * 2947780 * 2
def baseEnd_2947780 : Nat := 1513628003710582030893413

theorem tailTrace_2947780 : CollatzResearch.WordTrace tailWord_2947780 prefixEnd_2947780 1513628003710582030893413 := by
  unfold tailWord_2947780
  simp only [CollatzResearch.WordTrace]
  refine ⟨53757184630351987794072397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71676246173802650392096529 53757184630351987794072397)
  ·
    refine ⟨20158944236381995422777149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53757184630351987794072397 20158944236381995422777149)
    ·
      refine ⟨7559604088643248283541431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20158944236381995422777149 7559604088643248283541431)
      ·
        refine ⟨11339406132964872425312147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7559604088643248283541431 11339406132964872425312147)
        ·
          refine ⟨17009109199447308637968221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11339406132964872425312147 17009109199447308637968221)
          ·
            refine ⟨6378415949792740739238083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17009109199447308637968221 6378415949792740739238083)
            ·
              refine ⟨9567623924689111108857125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6378415949792740739238083 9567623924689111108857125)
              ·
                refine ⟨1793929485879208332910711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9567623924689111108857125 1793929485879208332910711)
                ·
                  refine ⟨2690894228818812499366067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1793929485879208332910711 2690894228818812499366067)
                  ·
                    refine ⟨4036341343228218749049101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2690894228818812499366067 4036341343228218749049101)
                    ·
                      refine ⟨1513628003710582030893413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4036341343228218749049101 1513628003710582030893413)
                      ·
                        rfl

theorem cell23_2947780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_2947780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947780 prefixEnd_2947780 := by exact prefixLift 2947780
  have htrace : WordTrace (prefixWord ++ tailWord_2947780) baseStart_2947780 baseEnd_2947780 := by
    simpa [prefixWord, tailWord_2947780, baseEnd_2947780] using wordTrace_append hprefix tailTrace_2947780
  have hstable : (prefixWord ++ tailWord_2947780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947780).length < 2 ^ (prefixWord ++ tailWord_2947780).sum := by decide
  have hdescent : baseEnd_2947780 < baseStart_2947780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947799 : List Nat := [1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 4]
def baseStart_2947799 : Nat := 118140960795 + 2947799 * 2 ^ 59
def prefixEnd_2947799 : Nat := 4983230072969 + 3 ^ 40 * 2947799 * 2
def baseEnd_2947799 : Nat := 1513637759843017456555825

theorem tailTrace_2947799 : CollatzResearch.WordTrace tailWord_2947799 prefixEnd_2947799 1513637759843017456555825 := by
  unfold tailWord_2947799
  simp only [CollatzResearch.WordTrace]
  refine ⟨107515062247635141833086451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71676708165090094555390967 107515062247635141833086451)
  ·
    refine ⟨161272593371452712749629677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107515062247635141833086451 161272593371452712749629677)
    ·
      refine ⟨60477222514294767281111129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161272593371452712749629677 60477222514294767281111129)
      ·
        refine ⟨45357916885721075460833347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60477222514294767281111129 45357916885721075460833347)
        ·
          refine ⟨68036875328581613191250021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45357916885721075460833347 68036875328581613191250021)
          ·
            refine ⟨12756914124109052473359379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68036875328581613191250021 12756914124109052473359379)
            ·
              refine ⟨19135371186163578710039069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12756914124109052473359379 19135371186163578710039069)
              ·
                refine ⟨7175764194811342016264651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19135371186163578710039069 7175764194811342016264651)
                ·
                  refine ⟨10763646292217013024396977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7175764194811342016264651 10763646292217013024396977)
                  ·
                    refine ⟨8072734719162759768297733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10763646292217013024396977 8072734719162759768297733)
                    ·
                      refine ⟨1513637759843017456555825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8072734719162759768297733 1513637759843017456555825)
                      ·
                        rfl

theorem cell23_2947799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_2947799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947799 prefixEnd_2947799 := by exact prefixLift 2947799
  have htrace : WordTrace (prefixWord ++ tailWord_2947799) baseStart_2947799 baseEnd_2947799 := by
    simpa [prefixWord, tailWord_2947799, baseEnd_2947799] using wordTrace_append hprefix tailTrace_2947799
  have hstable : (prefixWord ++ tailWord_2947799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947799).length < 2 ^ (prefixWord ++ tailWord_2947799).sum := by decide
  have hdescent : baseEnd_2947799 < baseStart_2947799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947823 : List Nat := [1, 1, 2, 1, 5, 2, 4, 1, 1, 2, 3]
def baseStart_2947823 : Nat := 118140960795 + 2947823 * 2 ^ 59
def prefixEnd_2947823 : Nat := 4983230072969 + 3 ^ 40 * 2947823 * 2
def baseEnd_2947823 : Nat := 1513650083378725362655715

theorem tailTrace_2947823 : CollatzResearch.WordTrace tailWord_2947823 prefixEnd_2947823 1513650083378725362655715 := by
  unfold tailWord_2947823
  simp only [CollatzResearch.WordTrace]
  refine ⟨107515937599548193931960123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71677291733032129287973415 107515937599548193931960123)
  ·
    refine ⟨161273906399322290897940185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107515937599548193931960123 161273906399322290897940185)
    ·
      refine ⟨120955429799491718173455139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161273906399322290897940185 120955429799491718173455139)
      ·
        refine ⟨181433144699237577260182709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120955429799491718173455139 181433144699237577260182709)
        ·
          refine ⟨17009357315553522868142129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 181433144699237577260182709 17009357315553522868142129)
          ·
            refine ⟨12757017986665142151106597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17009357315553522868142129 12757017986665142151106597)
            ·
              refine ⟨2391940872499714153332487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12757017986665142151106597 2391940872499714153332487)
              ·
                refine ⟨3587911308749571229998731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2391940872499714153332487 3587911308749571229998731)
                ·
                  refine ⟨5381866963124356844998097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3587911308749571229998731 5381866963124356844998097)
                  ·
                    refine ⟨4036400222343267633748573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5381866963124356844998097 4036400222343267633748573)
                    ·
                      refine ⟨1513650083378725362655715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4036400222343267633748573 1513650083378725362655715)
                      ·
                        rfl

theorem cell23_2947823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 1, 2, 3].length) (baseStart_2947823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947823 prefixEnd_2947823 := by exact prefixLift 2947823
  have htrace : WordTrace (prefixWord ++ tailWord_2947823) baseStart_2947823 baseEnd_2947823 := by
    simpa [prefixWord, tailWord_2947823, baseEnd_2947823] using wordTrace_append hprefix tailTrace_2947823
  have hstable : (prefixWord ++ tailWord_2947823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947823).length < 2 ^ (prefixWord ++ tailWord_2947823).sum := by decide
  have hdescent : baseEnd_2947823 < baseStart_2947823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2947950 : List Nat := [4, 1, 2, 3, 2, 1, 1, 4, 5]
def baseStart_2947950 : Nat := 118140960795 + 2947950 * 2 ^ 59
def prefixEnd_2947950 : Nat := 4983230072969 + 3 ^ 40 * 2947950 * 2
def baseEnd_2947950 : Nat := 168190588380205151751959

theorem tailTrace_2947950 : CollatzResearch.WordTrace tailWord_2947950 prefixEnd_2947950 168190588380205151751959 := by
  unfold tailWord_2947950
  simp only [CollatzResearch.WordTrace]
  refine ⟨13440071208761011827729163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71680379780058729747888869 13440071208761011827729163)
  ·
    refine ⟨20160106813141517741593745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13440071208761011827729163 20160106813141517741593745)
    ·
      refine ⟨15120080109856138306195309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20160106813141517741593745 15120080109856138306195309)
      ·
        refine ⟨5670030041196051864823241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15120080109856138306195309 5670030041196051864823241)
        ·
          refine ⟨4252522530897038898617431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5670030041196051864823241 4252522530897038898617431)
          ·
            refine ⟨6378783796345558347926147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4252522530897038898617431 6378783796345558347926147)
            ·
              refine ⟨9568175694518337521889221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6378783796345558347926147 9568175694518337521889221)
              ·
                refine ⟨1794032942722188285354229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9568175694518337521889221 1794032942722188285354229)
                ·
                  refine ⟨168190588380205151751959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1794032942722188285354229 168190588380205151751959)
                  ·
                    rfl

theorem cell23_2947950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_2947950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2947950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2947950 prefixEnd_2947950 := by exact prefixLift 2947950
  have htrace : WordTrace (prefixWord ++ tailWord_2947950) baseStart_2947950 baseEnd_2947950 := by
    simpa [prefixWord, tailWord_2947950, baseEnd_2947950] using wordTrace_append hprefix tailTrace_2947950
  have hstable : (prefixWord ++ tailWord_2947950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2947950).length < 2 ^ (prefixWord ++ tailWord_2947950).sum := by decide
  have hdescent : baseEnd_2947950 < baseStart_2947950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2947950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948009 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 1, 1, 8]
def baseStart_2948009 : Nat := 118140960795 + 2948009 * 2 ^ 59
def prefixEnd_2948009 : Nat := 4983230072969 + 3 ^ 40 * 2948009 * 2
def baseEnd_2948009 : Nat := 1513745590780461634929859

theorem tailTrace_2948009 : CollatzResearch.WordTrace tailWord_2948009 prefixEnd_2948009 1513745590780461634929859 := by
  unfold tailWord_2948009
  simp only [CollatzResearch.WordTrace]
  refine ⟨107522721576874347698231081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71681814384582898465487387 107522721576874347698231081)
  ·
    refine ⟨80642041182655760773673311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107522721576874347698231081 80642041182655760773673311)
    ·
      refine ⟨120963061773983641160509967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80642041182655760773673311 120963061773983641160509967)
      ·
        refine ⟨181444592660975461740764951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120963061773983641160509967 181444592660975461740764951)
        ·
          refine ⟨272166888991463192611147427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181444592660975461740764951 272166888991463192611147427)
          ·
            refine ⟨408250333487194788916721141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272166888991463192611147427 408250333487194788916721141)
            ·
              refine ⟨38273468764424511460942607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 408250333487194788916721141 38273468764424511460942607)
              ·
                refine ⟨57410203146636767191413911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38273468764424511460942607 57410203146636767191413911)
                ·
                  refine ⟨86115304719955150787120867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57410203146636767191413911 86115304719955150787120867)
                  ·
                    refine ⟨129172957079932726180681301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86115304719955150787120867 129172957079932726180681301)
                    ·
                      refine ⟨1513745590780461634929859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 129172957079932726180681301 1513745590780461634929859)
                      ·
                        rfl

theorem cell23_2948009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_2948009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948009 prefixEnd_2948009 := by exact prefixLift 2948009
  have htrace : WordTrace (prefixWord ++ tailWord_2948009) baseStart_2948009 baseEnd_2948009 := by
    simpa [prefixWord, tailWord_2948009, baseEnd_2948009] using wordTrace_append hprefix tailTrace_2948009
  have hstable : (prefixWord ++ tailWord_2948009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948009).length < 2 ^ (prefixWord ++ tailWord_2948009).sum := by decide
  have hdescent : baseEnd_2948009 < baseStart_2948009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948019 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 2, 9]
def baseStart_2948019 : Nat := 118140960795 + 2948019 * 2 ^ 59
def prefixEnd_2948019 : Nat := 4983230072969 + 3 ^ 40 * 2948019 * 2
def baseEnd_2948019 : Nat := 504583575195668865268271

theorem tailTrace_2948019 : CollatzResearch.WordTrace tailWord_2948019 prefixEnd_2948019 504583575195668865268271 := by
  unfold tailWord_2948019
  simp only [CollatzResearch.WordTrace]
  refine ⟨107523086306838119406095111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71682057537892079604063407 107523086306838119406095111)
  ·
    refine ⟨161284629460257179109142667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107523086306838119406095111 161284629460257179109142667)
    ·
      refine ⟨241926944190385768663714001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161284629460257179109142667 241926944190385768663714001)
      ·
        refine ⟨181445208142789326497785501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241926944190385768663714001 181445208142789326497785501)
        ·
          refine ⟨68041953053545997436669563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181445208142789326497785501 68041953053545997436669563)
          ·
            refine ⟨102062929580318996155004345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68041953053545997436669563 102062929580318996155004345)
            ·
              refine ⟨76547197185239247116253259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102062929580318996155004345 76547197185239247116253259)
              ·
                refine ⟨114820795777858870674379889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76547197185239247116253259 114820795777858870674379889)
                ·
                  refine ⟨86115596833394153005784917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114820795777858870674379889 86115596833394153005784917)
                  ·
                    refine ⟨504583575195668865268271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 86115596833394153005784917 504583575195668865268271)
                    ·
                      rfl

theorem cell23_2948019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 9].length) (baseStart_2948019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948019 prefixEnd_2948019 := by exact prefixLift 2948019
  have htrace : WordTrace (prefixWord ++ tailWord_2948019) baseStart_2948019 baseEnd_2948019 := by
    simpa [prefixWord, tailWord_2948019, baseEnd_2948019] using wordTrace_append hprefix tailTrace_2948019
  have hstable : (prefixWord ++ tailWord_2948019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948019).length < 2 ^ (prefixWord ++ tailWord_2948019).sum := by decide
  have hdescent : baseEnd_2948019 < baseStart_2948019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948020 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_2948020 : Nat := 118140960795 + 2948020 * 2 ^ 59
def prefixEnd_2948020 : Nat := 4983230072969 + 3 ^ 40 * 2948020 * 2
def baseEnd_2948020 : Nat := 1513751239067661091892309

theorem tailTrace_2948020 : CollatzResearch.WordTrace tailWord_2948020 prefixEnd_2948020 1513751239067661091892309 := by
  unfold tailWord_2948020
  simp only [CollatzResearch.WordTrace]
  refine ⟨53761561389917248288440757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71682081853222997717921009 53761561389917248288440757)
  ·
    refine ⟨5040146380304742027041321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53761561389917248288440757 5040146380304742027041321)
    ·
      refine ⟨3780109785228556520280991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5040146380304742027041321 3780109785228556520280991)
      ·
        refine ⟨5670164677842834780421487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3780109785228556520280991 5670164677842834780421487)
        ·
          refine ⟨8505247016764252170632231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5670164677842834780421487 8505247016764252170632231)
          ·
            refine ⟨12757870525146378255948347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8505247016764252170632231 12757870525146378255948347)
            ·
              refine ⟨19136805787719567383922521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12757870525146378255948347 19136805787719567383922521)
              ·
                refine ⟨14352604340789675537941891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19136805787719567383922521 14352604340789675537941891)
                ·
                  refine ⟨21528906511184513306912837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14352604340789675537941891 21528906511184513306912837)
                  ·
                    refine ⟨4036669970847096245046157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21528906511184513306912837 4036669970847096245046157)
                    ·
                      refine ⟨1513751239067661091892309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4036669970847096245046157 1513751239067661091892309)
                      ·
                        rfl

theorem cell23_2948020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_2948020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948020 prefixEnd_2948020 := by exact prefixLift 2948020
  have htrace : WordTrace (prefixWord ++ tailWord_2948020) baseStart_2948020 baseEnd_2948020 := by
    simpa [prefixWord, tailWord_2948020, baseEnd_2948020] using wordTrace_append hprefix tailTrace_2948020
  have hstable : (prefixWord ++ tailWord_2948020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948020).length < 2 ^ (prefixWord ++ tailWord_2948020).sum := by decide
  have hdescent : baseEnd_2948020 < baseStart_2948020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948043 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 1, 5, 2]
def baseStart_2948043 : Nat := 118140960795 + 2948043 * 2 ^ 59
def prefixEnd_2948043 : Nat := 4983230072969 + 3 ^ 40 * 2948043 * 2
def baseEnd_2948043 : Nat := 1513763049122714501904703

theorem tailTrace_2948043 : CollatzResearch.WordTrace tailWord_2948043 prefixEnd_2948043 1513763049122714501904703 := by
  unfold tailWord_2948043
  simp only [CollatzResearch.WordTrace]
  refine ⟨107523961658751171504968783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71682641105834114336645855 107523961658751171504968783)
  ·
    refine ⟨161285942488126757257453175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107523961658751171504968783 161285942488126757257453175)
    ·
      refine ⟨241928913732190135886179763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161285942488126757257453175 241928913732190135886179763)
      ·
        refine ⟨362893370598285203829269645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241928913732190135886179763 362893370598285203829269645)
        ·
          refine ⟨136085013974356951435976117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 362893370598285203829269645 136085013974356951435976117)
          ·
            refine ⟨12757970060095964197122761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136085013974356951435976117 12757970060095964197122761)
            ·
              refine ⟨9568477545071973147842071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12757970060095964197122761 9568477545071973147842071)
              ·
                refine ⟨14352716317607959721763107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9568477545071973147842071 14352716317607959721763107)
                ·
                  refine ⟨21529074476411939582644661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14352716317607959721763107 21529074476411939582644661)
                  ·
                    refine ⟨2018350732163619335872937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21529074476411939582644661 2018350732163619335872937)
                    ·
                      refine ⟨1513763049122714501904703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2018350732163619335872937 1513763049122714501904703)
                      ·
                        rfl

theorem cell23_2948043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 5, 2].length) (baseStart_2948043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948043 prefixEnd_2948043 := by exact prefixLift 2948043
  have htrace : WordTrace (prefixWord ++ tailWord_2948043) baseStart_2948043 baseEnd_2948043 := by
    simpa [prefixWord, tailWord_2948043, baseEnd_2948043] using wordTrace_append hprefix tailTrace_2948043
  have hstable : (prefixWord ++ tailWord_2948043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948043).length < 2 ^ (prefixWord ++ tailWord_2948043).sum := by decide
  have hdescent : baseEnd_2948043 < baseStart_2948043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948076 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 3]
def baseStart_2948076 : Nat := 118140960795 + 2948076 * 2 ^ 59
def prefixEnd_2948076 : Nat := 4983230072969 + 3 ^ 40 * 2948076 * 2
def baseEnd_2948076 : Nat := 1513779993984312872792051

theorem tailTrace_2948076 : CollatzResearch.WordTrace tailWord_2948076 prefixEnd_2948076 1513779993984312872792051 := by
  unfold tailWord_2948076
  simp only [CollatzResearch.WordTrace]
  refine ⟨53762582633815809070460041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71683443511754412093946721 53762582633815809070460041)
  ·
    refine ⟨40321936975361856802845031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53762582633815809070460041 40321936975361856802845031)
    ·
      refine ⟨60482905463042785204267547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40321936975361856802845031 60482905463042785204267547)
      ·
        refine ⟨90724358194564177806401321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60482905463042785204267547 90724358194564177806401321)
        ·
          refine ⟨68043268645923133354800991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90724358194564177806401321 68043268645923133354800991)
          ·
            refine ⟨102064902968884700032201487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68043268645923133354800991 102064902968884700032201487)
            ·
              refine ⟨153097354453327050048302231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102064902968884700032201487 153097354453327050048302231)
              ·
                refine ⟨229646031679990575072453347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153097354453327050048302231 229646031679990575072453347)
                ·
                  refine ⟨344469047519985862608680021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 229646031679990575072453347 344469047519985862608680021)
                  ·
                    refine ⟨4036746650624834327445469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 344469047519985862608680021 4036746650624834327445469)
                    ·
                      refine ⟨1513779993984312872792051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4036746650624834327445469 1513779993984312872792051)
                      ·
                        rfl

theorem cell23_2948076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_2948076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948076 prefixEnd_2948076 := by exact prefixLift 2948076
  have htrace : WordTrace (prefixWord ++ tailWord_2948076) baseStart_2948076 baseEnd_2948076 := by
    simpa [prefixWord, tailWord_2948076, baseEnd_2948076] using wordTrace_append hprefix tailTrace_2948076
  have hstable : (prefixWord ++ tailWord_2948076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948076).length < 2 ^ (prefixWord ++ tailWord_2948076).sum := by decide
  have hdescent : baseEnd_2948076 < baseStart_2948076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948090 : List Nat := [3, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2]
def baseStart_2948090 : Nat := 118140960795 + 2948090 * 2 ^ 59
def prefixEnd_2948090 : Nat := 4983230072969 + 3 ^ 40 * 2948090 * 2
def baseEnd_2948090 : Nat := 1513787182713475818016987

theorem tailTrace_2948090 : CollatzResearch.WordTrace tailWord_2948090 prefixEnd_2948090 1513787182713475818016987 := by
  unfold tailWord_2948090
  simp only [CollatzResearch.WordTrace]
  refine ⟨26881418972395224632982431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71683783926387265687953149 26881418972395224632982431)
  ·
    refine ⟨40322128458592836949473647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26881418972395224632982431 40322128458592836949473647)
    ·
      refine ⟨60483192687889255424210471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40322128458592836949473647 60483192687889255424210471)
      ·
        refine ⟨90724789031833883136315707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60483192687889255424210471 90724789031833883136315707)
        ·
          refine ⟨136087183547750824704473561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90724789031833883136315707 136087183547750824704473561)
          ·
            refine ⟨102065387660813118528355171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136087183547750824704473561 102065387660813118528355171)
            ·
              refine ⟨153098081491219677792532757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102065387660813118528355171 153098081491219677792532757)
              ·
                refine ⟨7176472569900922396524973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153098081491219677792532757 7176472569900922396524973)
                ·
                  refine ⟨2691177213712845898696865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7176472569900922396524973 2691177213712845898696865)
                  ·
                    refine ⟨2018382910284634424022649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2691177213712845898696865 2018382910284634424022649)
                    ·
                      refine ⟨1513787182713475818016987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2018382910284634424022649 1513787182713475818016987)
                      ·
                        rfl

theorem cell23_2948090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2].length) (baseStart_2948090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948090 prefixEnd_2948090 := by exact prefixLift 2948090
  have htrace : WordTrace (prefixWord ++ tailWord_2948090) baseStart_2948090 baseEnd_2948090 := by
    simpa [prefixWord, tailWord_2948090, baseEnd_2948090] using wordTrace_append hprefix tailTrace_2948090
  have hstable : (prefixWord ++ tailWord_2948090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948090).length < 2 ^ (prefixWord ++ tailWord_2948090).sum := by decide
  have hdescent : baseEnd_2948090 < baseStart_2948090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948094 : List Nat := [4, 2, 2, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_2948094 : Nat := 118140960795 + 2948094 * 2 ^ 59
def prefixEnd_2948094 : Nat := 4983230072969 + 3 ^ 40 * 2948094 * 2
def baseEnd_2948094 : Nat := 1513789236636093802366969

theorem tailTrace_2948094 : CollatzResearch.WordTrace tailWord_2948094 prefixEnd_2948094 1513789236636093802366969 := by
  unfold tailWord_2948094
  simp only [CollatzResearch.WordTrace]
  refine ⟨13440727722695800901884417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71683881187710938143383557 13440727722695800901884417)
  ·
    refine ⟨10080545792021850676413313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13440727722695800901884417 10080545792021850676413313)
    ·
      refine ⟨7560409344016388007309985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10080545792021850676413313 7560409344016388007309985)
      ·
        refine ⟨5670307008012291005482489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7560409344016388007309985 5670307008012291005482489)
        ·
          refine ⟨4252730256009218254111867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5670307008012291005482489 4252730256009218254111867)
          ·
            refine ⟨6379095384013827381167801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4252730256009218254111867 6379095384013827381167801)
            ·
              refine ⟨4784321538010370535875851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6379095384013827381167801 4784321538010370535875851)
              ·
                refine ⟨7176482307015555803813777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4784321538010370535875851 7176482307015555803813777)
                ·
                  refine ⟨5382361730261666852860333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7176482307015555803813777 5382361730261666852860333)
                  ·
                    refine ⟨2018385648848125069822625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5382361730261666852860333 2018385648848125069822625)
                    ·
                      refine ⟨1513789236636093802366969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2018385648848125069822625 1513789236636093802366969)
                      ·
                        rfl

theorem cell23_2948094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_2948094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948094 prefixEnd_2948094 := by exact prefixLift 2948094
  have htrace : WordTrace (prefixWord ++ tailWord_2948094) baseStart_2948094 baseEnd_2948094 := by
    simpa [prefixWord, tailWord_2948094, baseEnd_2948094] using wordTrace_append hprefix tailTrace_2948094
  have hstable : (prefixWord ++ tailWord_2948094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948094).length < 2 ^ (prefixWord ++ tailWord_2948094).sum := by decide
  have hdescent : baseEnd_2948094 < baseStart_2948094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948103 : List Nat := [1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 4]
def baseStart_2948103 : Nat := 118140960795 + 2948103 * 2 ^ 59
def prefixEnd_2948103 : Nat := 4983230072969 + 3 ^ 40 * 2948103 * 2
def baseEnd_2948103 : Nat := 1513793857961984267154427

theorem tailTrace_2948103 : CollatzResearch.WordTrace tailWord_2948103 prefixEnd_2948103 1513793857961984267154427 := by
  unfold tailWord_2948103
  simp only [CollatzResearch.WordTrace]
  refine ⟨107526150038533801752152963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71684100025689201168101975 107526150038533801752152963)
  ·
    refine ⟨161289225057800702628229445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107526150038533801752152963 161289225057800702628229445)
    ·
      refine ⟨30241729698337631742793021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161289225057800702628229445 30241729698337631742793021)
      ·
        refine ⟨11340648636876611903547383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30241729698337631742793021 11340648636876611903547383)
        ·
          refine ⟨17010972955314917855321075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11340648636876611903547383 17010972955314917855321075)
          ·
            refine ⟨25516459432972376782981613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17010972955314917855321075 25516459432972376782981613)
            ·
              refine ⟨9568672287364641293618105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25516459432972376782981613 9568672287364641293618105)
              ·
                refine ⟨7176504215523480970213579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9568672287364641293618105 7176504215523480970213579)
                ·
                  refine ⟨10764756323285221455320369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7176504215523480970213579 10764756323285221455320369)
                  ·
                    refine ⟨8073567242463916091490277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10764756323285221455320369 8073567242463916091490277)
                    ·
                      refine ⟨1513793857961984267154427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8073567242463916091490277 1513793857961984267154427)
                      ·
                        rfl

theorem cell23_2948103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_2948103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948103 prefixEnd_2948103 := by exact prefixLift 2948103
  have htrace : WordTrace (prefixWord ++ tailWord_2948103) baseStart_2948103 baseEnd_2948103 := by
    simpa [prefixWord, tailWord_2948103, baseEnd_2948103] using wordTrace_append hprefix tailTrace_2948103
  have hstable : (prefixWord ++ tailWord_2948103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948103).length < 2 ^ (prefixWord ++ tailWord_2948103).sum := by decide
  have hdescent : baseEnd_2948103 < baseStart_2948103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948110 : List Nat := [4, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5]
def baseStart_2948110 : Nat := 118140960795 + 2948110 * 2 ^ 59
def prefixEnd_2948110 : Nat := 4983230072969 + 3 ^ 40 * 2948110 * 2
def baseEnd_2948110 : Nat := 1513797452326565739766895

theorem tailTrace_2948110 : CollatzResearch.WordTrace tailWord_2948110 prefixEnd_2948110 1513797452326565739766895 := by
  unfold tailWord_2948110
  simp only [CollatzResearch.WordTrace]
  refine ⟨13440800668688555243457223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71684270233005627965105189 13440800668688555243457223)
  ·
    refine ⟨20161201003032832865185835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13440800668688555243457223 20161201003032832865185835)
    ·
      refine ⟨30241801504549249297778753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20161201003032832865185835 30241801504549249297778753)
      ·
        refine ⟨22681351128411936973334065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30241801504549249297778753 22681351128411936973334065)
        ·
          refine ⟨17011013346308952730000549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22681351128411936973334065 17011013346308952730000549)
          ·
            refine ⟨3189565002432928636875103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17011013346308952730000549 3189565002432928636875103)
            ·
              refine ⟨4784347503649392955312655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3189565002432928636875103 4784347503649392955312655)
              ·
                refine ⟨7176521255474089432968983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4784347503649392955312655 7176521255474089432968983)
                ·
                  refine ⟨10764781883211134149453475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7176521255474089432968983 10764781883211134149453475)
                  ·
                    refine ⟨16147172824816701224180213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10764781883211134149453475 16147172824816701224180213)
                    ·
                      refine ⟨1513797452326565739766895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16147172824816701224180213 1513797452326565739766895)
                      ·
                        rfl

theorem cell23_2948110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_2948110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948110 prefixEnd_2948110 := by exact prefixLift 2948110
  have htrace : WordTrace (prefixWord ++ tailWord_2948110) baseStart_2948110 baseEnd_2948110 := by
    simpa [prefixWord, tailWord_2948110, baseEnd_2948110] using wordTrace_append hprefix tailTrace_2948110
  have hstable : (prefixWord ++ tailWord_2948110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948110).length < 2 ^ (prefixWord ++ tailWord_2948110).sum := by decide
  have hdescent : baseEnd_2948110 < baseStart_2948110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948123 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 8, 1, 3]
def baseStart_2948123 : Nat := 118140960795 + 2948123 * 2 ^ 59
def prefixEnd_2948123 : Nat := 4983230072969 + 3 ^ 40 * 2948123 * 2
def baseEnd_2948123 : Nat := 1513804127575074188904335

theorem tailTrace_2948123 : CollatzResearch.WordTrace tailWord_2948123 prefixEnd_2948123 1513804127575074188904335 := by
  unfold tailWord_2948123
  simp only [CollatzResearch.WordTrace]
  refine ⟨107526879498461345167881023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71684586332307563445254015 107526879498461345167881023)
  ·
    refine ⟨161290319247692017751821535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107526879498461345167881023 161290319247692017751821535)
    ·
      refine ⟨241935478871538026627732303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161290319247692017751821535 241935478871538026627732303)
      ·
        refine ⟨362903218307307039941598455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241935478871538026627732303 362903218307307039941598455)
        ·
          refine ⟨544354827460960559912397683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362903218307307039941598455 544354827460960559912397683)
          ·
            refine ⟨816532241191440839868596525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544354827460960559912397683 816532241191440839868596525)
            ·
              refine ⟨306199590446790314950723697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 816532241191440839868596525 306199590446790314950723697)
              ·
                refine ⟨229649692835092736213042773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 306199590446790314950723697 229649692835092736213042773)
                ·
                  refine ⟨2691207337911243002496595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 229649692835092736213042773 2691207337911243002496595)
                  ·
                    refine ⟨4036811006866864503744893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2691207337911243002496595 4036811006866864503744893)
                    ·
                      refine ⟨1513804127575074188904335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4036811006866864503744893 1513804127575074188904335)
                      ·
                        rfl

theorem cell23_2948123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 1, 3].length) (baseStart_2948123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948123 prefixEnd_2948123 := by exact prefixLift 2948123
  have htrace : WordTrace (prefixWord ++ tailWord_2948123) baseStart_2948123 baseEnd_2948123 := by
    simpa [prefixWord, tailWord_2948123, baseEnd_2948123] using wordTrace_append hprefix tailTrace_2948123
  have hstable : (prefixWord ++ tailWord_2948123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948123).length < 2 ^ (prefixWord ++ tailWord_2948123).sum := by decide
  have hdescent : baseEnd_2948123 < baseStart_2948123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948140 : List Nat := [2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 3]
def baseStart_2948140 : Nat := 118140960795 + 2948140 * 2 ^ 59
def prefixEnd_2948140 : Nat := 4983230072969 + 3 ^ 40 * 2948140 * 2
def baseEnd_2948140 : Nat := 1513812856746200622391757

theorem tailTrace_2948140 : CollatzResearch.WordTrace tailWord_2948140 prefixEnd_2948140 1513812856746200622391757 := by
  unfold tailWord_2948140
  simp only [CollatzResearch.WordTrace]
  refine ⟨53763749769699878535624937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71684999692933171380833249 53763749769699878535624937)
  ·
    refine ⟨40322812327274908901718703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53763749769699878535624937 40322812327274908901718703)
    ·
      refine ⟨60484218490912363352578055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40322812327274908901718703 60484218490912363352578055)
      ·
        refine ⟨90726327736368545028867083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60484218490912363352578055 90726327736368545028867083)
        ·
          refine ⟨136089491604552817543300625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90726327736368545028867083 136089491604552817543300625)
          ·
            refine ⟨102067118703414613157475469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136089491604552817543300625 102067118703414613157475469)
            ·
              refine ⟨38275169513780479934053301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102067118703414613157475469 38275169513780479934053301)
              ·
                refine ⟨3588297141916919993817497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38275169513780479934053301 3588297141916919993817497)
                ·
                  refine ⟨2691222856437689995363123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3588297141916919993817497 2691222856437689995363123)
                  ·
                    refine ⟨4036834284656534993044685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2691222856437689995363123 4036834284656534993044685)
                    ·
                      refine ⟨1513812856746200622391757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4036834284656534993044685 1513812856746200622391757)
                      ·
                        rfl

theorem cell23_2948140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 3].length) (baseStart_2948140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948140 prefixEnd_2948140 := by exact prefixLift 2948140
  have htrace : WordTrace (prefixWord ++ tailWord_2948140) baseStart_2948140 baseEnd_2948140 := by
    simpa [prefixWord, tailWord_2948140, baseEnd_2948140] using wordTrace_append hprefix tailTrace_2948140
  have hstable : (prefixWord ++ tailWord_2948140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948140).length < 2 ^ (prefixWord ++ tailWord_2948140).sum := by decide
  have hdescent : baseEnd_2948140 < baseStart_2948140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948161 : List Nat := [1, 2, 5, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_2948161 : Nat := 118140960795 + 2948161 * 2 ^ 59
def prefixEnd_2948161 : Nat := 4983230072969 + 3 ^ 40 * 2948161 * 2
def baseEnd_2948161 : Nat := 1513823639839945040229161

theorem tailTrace_2948161 : CollatzResearch.WordTrace tailWord_2948161 prefixEnd_2948161 1513823639839945040229161 := by
  unfold tailWord_2948161
  simp only [CollatzResearch.WordTrace]
  refine ⟨107528265472323677657764337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71685510314882451771842891 107528265472323677657764337)
  ·
    refine ⟨80646199104242758243323253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107528265472323677657764337 80646199104242758243323253)
    ·
      refine ⟨7560581166022758585311555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80646199104242758243323253 7560581166022758585311555)
      ·
        refine ⟨11340871749034137877967333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7560581166022758585311555 11340871749034137877967333)
        ·
          refine ⟨2126413452943900852118875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11340871749034137877967333 2126413452943900852118875)
          ·
            refine ⟨3189620179415851278178313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2126413452943900852118875 3189620179415851278178313)
            ·
              refine ⟨2392215134561888458633735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3189620179415851278178313 2392215134561888458633735)
              ·
                refine ⟨3588322701842832687950603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2392215134561888458633735 3588322701842832687950603)
                ·
                  refine ⟨5382484052764249031925905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3588322701842832687950603 5382484052764249031925905)
                  ·
                    refine ⟨4036863039573186773944429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5382484052764249031925905 4036863039573186773944429)
                    ·
                      refine ⟨1513823639839945040229161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4036863039573186773944429 1513823639839945040229161)
                      ·
                        rfl

theorem cell23_2948161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_2948161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948161 prefixEnd_2948161 := by exact prefixLift 2948161
  have htrace : WordTrace (prefixWord ++ tailWord_2948161) baseStart_2948161 baseEnd_2948161 := by
    simpa [prefixWord, tailWord_2948161, baseEnd_2948161] using wordTrace_append hprefix tailTrace_2948161
  have hstable : (prefixWord ++ tailWord_2948161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948161).length < 2 ^ (prefixWord ++ tailWord_2948161).sum := by decide
  have hdescent : baseEnd_2948161 < baseStart_2948161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948167 : List Nat := [1, 1, 4, 1, 3, 3, 1, 3, 1, 3, 2]
def baseStart_2948167 : Nat := 118140960795 + 2948167 * 2 ^ 59
def prefixEnd_2948167 : Nat := 4983230072969 + 3 ^ 40 * 2948167 * 2
def baseEnd_2948167 : Nat := 1513826720723872016754133

theorem tailTrace_2948167 : CollatzResearch.WordTrace tailWord_2948167 prefixEnd_2948167 1513826720723872016754133 := by
  unfold tailWord_2948167
  simp only [CollatzResearch.WordTrace]
  refine ⟨107528484310301940682482755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71685656206867960454988503 107528484310301940682482755)
  ·
    refine ⟨161292726465452911023724133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107528484310301940682482755 161292726465452911023724133)
    ·
      refine ⟨30242386212272420816948275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161292726465452911023724133 30242386212272420816948275)
      ·
        refine ⟨45363579318408631225422413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30242386212272420816948275 45363579318408631225422413)
        ·
          refine ⟨17011342244403236709533405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45363579318408631225422413 17011342244403236709533405)
          ·
            refine ⟨6379253341651213766075027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17011342244403236709533405 6379253341651213766075027)
            ·
              refine ⟨9568880012476820649112541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6379253341651213766075027 9568880012476820649112541)
              ·
                refine ⟨3588330004678807743417203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9568880012476820649112541 3588330004678807743417203)
                ·
                  refine ⟨5382495007018211615125805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3588330004678807743417203 5382495007018211615125805)
                  ·
                    refine ⟨2018435627631829355672177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5382495007018211615125805 2018435627631829355672177)
                    ·
                      refine ⟨1513826720723872016754133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2018435627631829355672177 1513826720723872016754133)
                      ·
                        rfl

theorem cell23_2948167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_2948167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948167 prefixEnd_2948167 := by exact prefixLift 2948167
  have htrace : WordTrace (prefixWord ++ tailWord_2948167) baseStart_2948167 baseEnd_2948167 := by
    simpa [prefixWord, tailWord_2948167, baseEnd_2948167] using wordTrace_append hprefix tailTrace_2948167
  have hstable : (prefixWord ++ tailWord_2948167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948167).length < 2 ^ (prefixWord ++ tailWord_2948167).sum := by decide
  have hdescent : baseEnd_2948167 < baseStart_2948167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948180 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 3, 4, 2]
def baseStart_2948180 : Nat := 118140960795 + 2948180 * 2 ^ 59
def prefixEnd_2948180 : Nat := 4983230072969 + 3 ^ 40 * 2948180 * 2
def baseEnd_2948180 : Nat := 1513833395972380465891573

theorem tailTrace_2948180 : CollatzResearch.WordTrace tailWord_2948180 prefixEnd_2948180 1513833395972380465891573 := by
  unfold tailWord_2948180
  simp only [CollatzResearch.WordTrace]
  refine ⟨53764479229627421951352997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71685972306169895935137329 53764479229627421951352997)
  ·
    refine ⟨10080839855555141615878687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53764479229627421951352997 10080839855555141615878687)
    ·
      refine ⟨15121259783332712423818031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10080839855555141615878687 15121259783332712423818031)
      ·
        refine ⟨22681889674999068635727047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15121259783332712423818031 22681889674999068635727047)
        ·
          refine ⟨34022834512498602953590571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22681889674999068635727047 34022834512498602953590571)
          ·
            refine ⟨51034251768747904430385857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34022834512498602953590571 51034251768747904430385857)
            ·
              refine ⟨38275688826560928322789393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51034251768747904430385857 38275688826560928322789393)
              ·
                refine ⟨28706766619920696242092045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38275688826560928322789393 28706766619920696242092045)
                ·
                  refine ⟨10765037482470261090784517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28706766619920696242092045 10765037482470261090784517)
                  ·
                    refine ⟨2018444527963173954522097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10765037482470261090784517 2018444527963173954522097)
                    ·
                      refine ⟨1513833395972380465891573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2018444527963173954522097 1513833395972380465891573)
                      ·
                        rfl

theorem cell23_2948180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_2948180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948180 prefixEnd_2948180 := by exact prefixLift 2948180
  have htrace : WordTrace (prefixWord ++ tailWord_2948180) baseStart_2948180 baseEnd_2948180 := by
    simpa [prefixWord, tailWord_2948180, baseEnd_2948180] using wordTrace_append hprefix tailTrace_2948180
  have hstable : (prefixWord ++ tailWord_2948180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948180).length < 2 ^ (prefixWord ++ tailWord_2948180).sum := by decide
  have hdescent : baseEnd_2948180 < baseStart_2948180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948193 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_2948193 : Nat := 118140960795 + 2948193 * 2 ^ 59
def prefixEnd_2948193 : Nat := 4983230072969 + 3 ^ 40 * 2948193 * 2
def baseEnd_2948193 : Nat := 1513840071220888915029013

theorem tailTrace_2948193 : CollatzResearch.WordTrace tailWord_2948193 prefixEnd_2948193 1513840071220888915029013 := by
  unfold tailWord_2948193
  simp only [CollatzResearch.WordTrace]
  refine ⟨107529432608207747122929233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71686288405471831415286155 107529432608207747122929233)
  ·
    refine ⟨80647074456155810342196925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107529432608207747122929233 80647074456155810342196925)
    ·
      refine ⟨30242652921058428878323847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80647074456155810342196925 30242652921058428878323847)
      ·
        refine ⟨45363979381587643317485771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30242652921058428878323847 45363979381587643317485771)
        ·
          refine ⟨68045969072381464976228657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45363979381587643317485771 68045969072381464976228657)
          ·
            refine ⟨51034476804286098732171493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68045969072381464976228657 51034476804286098732171493)
            ·
              refine ⟨9568964400803643512282155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51034476804286098732171493 9568964400803643512282155)
              ·
                refine ⟨14353446601205465268423233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9568964400803643512282155 14353446601205465268423233)
                ·
                  refine ⟨10765084950904098951317425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14353446601205465268423233 10765084950904098951317425)
                  ·
                    refine ⟨8073813713178074213488069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10765084950904098951317425 8073813713178074213488069)
                    ·
                      refine ⟨1513840071220888915029013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8073813713178074213488069 1513840071220888915029013)
                      ·
                        rfl

theorem cell23_2948193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_2948193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948193 prefixEnd_2948193 := by exact prefixLift 2948193
  have htrace : WordTrace (prefixWord ++ tailWord_2948193) baseStart_2948193 baseEnd_2948193 := by
    simpa [prefixWord, tailWord_2948193, baseEnd_2948193] using wordTrace_append hprefix tailTrace_2948193
  have hstable : (prefixWord ++ tailWord_2948193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948193).length < 2 ^ (prefixWord ++ tailWord_2948193).sum := by decide
  have hdescent : baseEnd_2948193 < baseStart_2948193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948233 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 4, 5]
def baseStart_2948233 : Nat := 118140960795 + 2948233 * 2 ^ 59
def prefixEnd_2948233 : Nat := 4983230072969 + 3 ^ 40 * 2948233 * 2
def baseEnd_2948233 : Nat := 504620203482356252842943

theorem tailTrace_2948233 : CollatzResearch.WordTrace tailWord_2948233 prefixEnd_2948233 504620203482356252842943 := by
  unfold tailWord_2948233
  simp only [CollatzResearch.WordTrace]
  refine ⟨107530891528062833954385353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71687261018708555969590235 107530891528062833954385353)
  ·
    refine ⟨80648168646047125465789015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107530891528062833954385353 80648168646047125465789015)
    ·
      refine ⟨120972252969070688198683523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80648168646047125465789015 120972252969070688198683523)
      ·
        refine ⟨181458379453606032298025285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120972252969070688198683523 181458379453606032298025285)
        ·
          refine ⟨34023446147551131055879741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181458379453606032298025285 34023446147551131055879741)
          ·
            refine ⟨12758792305331674145954903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34023446147551131055879741 12758792305331674145954903)
            ·
              refine ⟨19138188457997511218932355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12758792305331674145954903 19138188457997511218932355)
              ·
                refine ⟨28707282686996266828398533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19138188457997511218932355 28707282686996266828398533)
                ·
                  refine ⟨5382615503811800030324725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28707282686996266828398533 5382615503811800030324725)
                  ·
                    refine ⟨504620203482356252842943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5382615503811800030324725 504620203482356252842943)
                    ·
                      rfl

theorem cell23_2948233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 5].length) (baseStart_2948233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948233 prefixEnd_2948233 := by exact prefixLift 2948233
  have htrace : WordTrace (prefixWord ++ tailWord_2948233) baseStart_2948233 baseEnd_2948233 := by
    simpa [prefixWord, tailWord_2948233, baseEnd_2948233] using wordTrace_append hprefix tailTrace_2948233
  have hstable : (prefixWord ++ tailWord_2948233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948233).length < 2 ^ (prefixWord ++ tailWord_2948233).sum := by decide
  have hdescent : baseEnd_2948233 < baseStart_2948233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948393 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 7]
def baseStart_2948393 : Nat := 118140960795 + 2948393 * 2 ^ 59
def prefixEnd_2948393 : Nat := 4983230072969 + 3 ^ 40 * 2948393 * 2
def baseEnd_2948393 : Nat := 1513942767351788132528093

theorem tailTrace_2948393 : CollatzResearch.WordTrace tailWord_2948393 prefixEnd_2948393 1513942767351788132528093 := by
  unfold tailWord_2948393
  simp only [CollatzResearch.WordTrace]
  refine ⟨107536727207483181280209833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71691151471655454186806555 107536727207483181280209833)
  ·
    refine ⟨80652545405612385960157375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107536727207483181280209833 80652545405612385960157375)
    ·
      refine ⟨120978818108418578940236063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80652545405612385960157375 120978818108418578940236063)
      ·
        refine ⟨181468227162627868410354095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120978818108418578940236063 181468227162627868410354095)
        ·
          refine ⟨272202340743941802615531143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181468227162627868410354095 272202340743941802615531143)
          ·
            refine ⟨408303511115912703923296715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272202340743941802615531143 408303511115912703923296715)
            ·
              refine ⟨612455266673869055884945073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408303511115912703923296715 612455266673869055884945073)
              ·
                refine ⟨459341450005401791913708805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 612455266673869055884945073 459341450005401791913708805)
                ·
                  refine ⟨86126521876012835983820401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 459341450005401791913708805 86126521876012835983820401)
                  ·
                    refine ⟨64594891407009626987865301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86126521876012835983820401 64594891407009626987865301)
                    ·
                      refine ⟨1513942767351788132528093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64594891407009626987865301 1513942767351788132528093)
                      ·
                        rfl

theorem cell23_2948393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_2948393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948393 prefixEnd_2948393 := by exact prefixLift 2948393
  have htrace : WordTrace (prefixWord ++ tailWord_2948393) baseStart_2948393 baseEnd_2948393 := by
    simpa [prefixWord, tailWord_2948393, baseEnd_2948393] using wordTrace_append hprefix tailTrace_2948393
  have hstable : (prefixWord ++ tailWord_2948393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948393).length < 2 ^ (prefixWord ++ tailWord_2948393).sum := by decide
  have hdescent : baseEnd_2948393 < baseStart_2948393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948394 : List Nat := [3, 1, 4, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_2948394 : Nat := 118140960795 + 2948394 * 2 ^ 59
def prefixEnd_2948394 : Nat := 4983230072969 + 3 ^ 40 * 2948394 * 2
def baseEnd_2948394 : Nat := 1513943280832442628615589

theorem tailTrace_2948394 : CollatzResearch.WordTrace tailWord_2948394 prefixEnd_2948394 1513943280832442628615589 := by
  unfold tailWord_2948394
  simp only [CollatzResearch.WordTrace]
  refine ⟨26884190920119889612749059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71691175786986372300664157 26884190920119889612749059)
  ·
    refine ⟨40326286380179834419123589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26884190920119889612749059 40326286380179834419123589)
    ·
      refine ⟨7561178696283718953585673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40326286380179834419123589 7561178696283718953585673)
      ·
        refine ⟨5670884022212789215189255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7561178696283718953585673 5670884022212789215189255)
        ·
          refine ⟨8506326033319183822783883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5670884022212789215189255 8506326033319183822783883)
          ·
            refine ⟨12759489049978775734175825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8506326033319183822783883 12759489049978775734175825)
            ·
              refine ⟨9569616787484081800631869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12759489049978775734175825 9569616787484081800631869)
              ·
                refine ⟨3588606295306530675236951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9569616787484081800631869 3588606295306530675236951)
                ·
                  refine ⟨5382909442959796012855427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3588606295306530675236951 5382909442959796012855427)
                  ·
                    refine ⟨8074364164439694019283141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5382909442959796012855427 8074364164439694019283141)
                    ·
                      refine ⟨1513943280832442628615589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8074364164439694019283141 1513943280832442628615589)
                      ·
                        rfl

theorem cell23_2948394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_2948394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948394 prefixEnd_2948394 := by exact prefixLift 2948394
  have htrace : WordTrace (prefixWord ++ tailWord_2948394) baseStart_2948394 baseEnd_2948394 := by
    simpa [prefixWord, tailWord_2948394, baseEnd_2948394] using wordTrace_append hprefix tailTrace_2948394
  have hstable : (prefixWord ++ tailWord_2948394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948394).length < 2 ^ (prefixWord ++ tailWord_2948394).sum := by decide
  have hdescent : baseEnd_2948394 < baseStart_2948394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948404 : List Nat := [2, 5, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_2948404 : Nat := 118140960795 + 2948404 * 2 ^ 59
def prefixEnd_2948404 : Nat := 4983230072969 + 3 ^ 40 * 2948404 * 2
def baseEnd_2948404 : Nat := 504649471879662529830181

theorem tailTrace_2948404 : CollatzResearch.WordTrace tailWord_2948404 prefixEnd_2948404 504649471879662529830181 := by
  unfold tailWord_2948404
  simp only [CollatzResearch.WordTrace]
  refine ⟨53768564205221665079430133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71691418940295553439240177 53768564205221665079430133)
  ·
    refine ⟨5040802894239531101196575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53768564205221665079430133 5040802894239531101196575)
    ·
      refine ⟨7561204341359296651794863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5040802894239531101196575 7561204341359296651794863)
      ·
        refine ⟨11341806512038944977692295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7561204341359296651794863 11341806512038944977692295)
        ·
          refine ⟨17012709768058417466538443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11341806512038944977692295 17012709768058417466538443)
          ·
            refine ⟨25519064652087626199807665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17012709768058417466538443 25519064652087626199807665)
            ·
              refine ⟨19139298489065719649855749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25519064652087626199807665 19139298489065719649855749)
              ·
                refine ⟨3588618466699822434347953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19139298489065719649855749 3588618466699822434347953)
                ·
                  refine ⟨2691463850024866825760965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3588618466699822434347953 2691463850024866825760965)
                  ·
                    refine ⟨504649471879662529830181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2691463850024866825760965 504649471879662529830181)
                    ·
                      rfl

theorem cell23_2948404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_2948404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948404 prefixEnd_2948404 := by exact prefixLift 2948404
  have htrace : WordTrace (prefixWord ++ tailWord_2948404) baseStart_2948404 baseEnd_2948404 := by
    simpa [prefixWord, tailWord_2948404, baseEnd_2948404] using wordTrace_append hprefix tailTrace_2948404
  have hstable : (prefixWord ++ tailWord_2948404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948404).length < 2 ^ (prefixWord ++ tailWord_2948404).sum := by decide
  have hdescent : baseEnd_2948404 < baseStart_2948404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948417 : List Nat := [1, 2, 5, 2, 1, 2, 2, 8]
def baseStart_2948417 : Nat := 118140960795 + 2948417 * 2 ^ 59
def prefixEnd_2948417 : Nat := 4983230072969 + 3 ^ 40 * 2948417 * 2
def baseEnd_2948417 : Nat := 56072410773610964393629

theorem tailTrace_2948417 : CollatzResearch.WordTrace tailWord_2948417 prefixEnd_2948417 56072410773610964393629 := by
  unfold tailWord_2948417
  simp only [CollatzResearch.WordTrace]
  refine ⟨107537602559396233379083505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71691735039597488919389003 107537602559396233379083505)
  ·
    refine ⟨80653201919547175034312629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107537602559396233379083505 80653201919547175034312629)
    ·
      refine ⟨7561237679957547659466809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80653201919547175034312629 7561237679957547659466809)
      ·
        refine ⟨5670928259968160744600107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7561237679957547659466809 5670928259968160744600107)
        ·
          refine ⟨8506392389952241116900161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5670928259968160744600107 8506392389952241116900161)
          ·
            refine ⟨6379794292464180837675121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8506392389952241116900161 6379794292464180837675121)
            ·
              refine ⟨4784845719348135628256341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6379794292464180837675121 4784845719348135628256341)
              ·
                refine ⟨56072410773610964393629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4784845719348135628256341 56072410773610964393629)
                ·
                  rfl

theorem cell23_2948417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 8].length) (baseStart_2948417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948417 prefixEnd_2948417 := by exact prefixLift 2948417
  have htrace : WordTrace (prefixWord ++ tailWord_2948417) baseStart_2948417 baseEnd_2948417 := by
    simpa [prefixWord, tailWord_2948417, baseEnd_2948417] using wordTrace_append hprefix tailTrace_2948417
  have hstable : (prefixWord ++ tailWord_2948417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948417).length < 2 ^ (prefixWord ++ tailWord_2948417).sum := by decide
  have hdescent : baseEnd_2948417 < baseStart_2948417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948438 : List Nat := [5, 2, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_2948438 : Nat := 118140960795 + 2948438 * 2 ^ 59
def prefixEnd_2948438 : Nat := 4983230072969 + 3 ^ 40 * 2948438 * 2
def baseEnd_2948438 : Nat := 504655291327080152155129

theorem tailTrace_2948438 : CollatzResearch.WordTrace tailWord_2948438 prefixEnd_2948438 504655291327080152155129 := by
  unfold tailWord_2948438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6721148030770009622849873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71692245661546769310398645 6721148030770009622849873)
  ·
    refine ⟨5040861023077507217137405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6721148030770009622849873 5040861023077507217137405)
    ·
      refine ⟨1890322883654065206426527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5040861023077507217137405 1890322883654065206426527)
      ·
        refine ⟨2835484325481097809639791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1890322883654065206426527 2835484325481097809639791)
        ·
          refine ⟨4253226488221646714459687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2835484325481097809639791 4253226488221646714459687)
          ·
            refine ⟨6379839732332470071689531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4253226488221646714459687 6379839732332470071689531)
            ·
              refine ⟨9569759598498705107534297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6379839732332470071689531 9569759598498705107534297)
              ·
                refine ⟨7177319698874028830650723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9569759598498705107534297 7177319698874028830650723)
                ·
                  refine ⟨10765979548311043245976085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7177319698874028830650723 10765979548311043245976085)
                  ·
                    refine ⟨504655291327080152155129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10765979548311043245976085 504655291327080152155129)
                    ·
                      rfl

theorem cell23_2948438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_2948438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948438 prefixEnd_2948438 := by exact prefixLift 2948438
  have htrace : WordTrace (prefixWord ++ tailWord_2948438) baseStart_2948438 baseEnd_2948438 := by
    simpa [prefixWord, tailWord_2948438, baseEnd_2948438] using wordTrace_append hprefix tailTrace_2948438
  have hstable : (prefixWord ++ tailWord_2948438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948438).length < 2 ^ (prefixWord ++ tailWord_2948438).sum := by decide
  have hdescent : baseEnd_2948438 < baseStart_2948438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948445 : List Nat := [1, 4, 5, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_2948445 : Nat := 118140960795 + 2948445 * 2 ^ 59
def prefixEnd_2948445 : Nat := 4983230072969 + 3 ^ 40 * 2948445 * 2
def baseEnd_2948445 : Nat := 1513969468345821929077855

theorem tailTrace_2948445 : CollatzResearch.WordTrace tailWord_2948445 prefixEnd_2948445 1513969468345821929077855 := by
  unfold tailWord_2948445
  simp only [CollatzResearch.WordTrace]
  refine ⟨107538623803294794161102789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71692415868863196107401859 107538623803294794161102789)
  ·
    refine ⟨20163491963117773905206773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107538623803294794161102789 20163491963117773905206773)
    ·
      refine ⟨1890327371542291303613135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20163491963117773905206773 1890327371542291303613135)
      ·
        refine ⟨2835491057313436955419703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1890327371542291303613135 2835491057313436955419703)
        ·
          refine ⟨4253236585970155433129555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2835491057313436955419703 4253236585970155433129555)
          ·
            refine ⟨6379854878955233149694333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4253236585970155433129555 6379854878955233149694333)
            ·
              refine ⟨2392445579608212431135375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6379854878955233149694333 2392445579608212431135375)
              ·
                refine ⟨3588668369412318646703063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2392445579608212431135375 3588668369412318646703063)
                ·
                  refine ⟨5383002554118477970054595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3588668369412318646703063 5383002554118477970054595)
                  ·
                    refine ⟨8074503831177716955081893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5383002554118477970054595 8074503831177716955081893)
                    ·
                      refine ⟨1513969468345821929077855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8074503831177716955081893 1513969468345821929077855)
                      ·
                        rfl

theorem cell23_2948445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_2948445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948445 prefixEnd_2948445 := by exact prefixLift 2948445
  have htrace : WordTrace (prefixWord ++ tailWord_2948445) baseStart_2948445 baseEnd_2948445 := by
    simpa [prefixWord, tailWord_2948445, baseEnd_2948445] using wordTrace_append hprefix tailTrace_2948445
  have hstable : (prefixWord ++ tailWord_2948445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948445).length < 2 ^ (prefixWord ++ tailWord_2948445).sum := by decide
  have hdescent : baseEnd_2948445 < baseStart_2948445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948461 : List Nat := [1, 5, 1, 1, 1, 4, 2, 2, 2, 1, 3]
def baseStart_2948461 : Nat := 118140960795 + 2948461 * 2 ^ 59
def prefixEnd_2948461 : Nat := 4983230072969 + 3 ^ 40 * 2948461 * 2
def baseEnd_2948461 : Nat := 1513977684036293866477781

theorem tailTrace_2948461 : CollatzResearch.WordTrace tailWord_2948461 prefixEnd_2948461 1513977684036293866477781 := by
  unfold tailWord_2948461
  simp only [CollatzResearch.WordTrace]
  refine ⟨107539207371236828893685237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71692804914157885929123491 107539207371236828893685237)
  ·
    refine ⟨10081800691053452708782991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107539207371236828893685237 10081800691053452708782991)
    ·
      refine ⟨15122701036580179063174487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10081800691053452708782991 15122701036580179063174487)
      ·
        refine ⟨22684051554870268594761731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15122701036580179063174487 22684051554870268594761731)
        ·
          refine ⟨34026077332305402892142597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22684051554870268594761731 34026077332305402892142597)
          ·
            refine ⟨6379889499807263042276737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34026077332305402892142597 6379889499807263042276737)
            ·
              refine ⟨4784917124855447281707553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6379889499807263042276737 4784917124855447281707553)
              ·
                refine ⟨3588687843641585461280665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4784917124855447281707553 3588687843641585461280665)
                ·
                  refine ⟨2691515882731189095960499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3588687843641585461280665 2691515882731189095960499)
                  ·
                    refine ⟨4037273824096783643940749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2691515882731189095960499 4037273824096783643940749)
                    ·
                      refine ⟨1513977684036293866477781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4037273824096783643940749 1513977684036293866477781)
                      ·
                        rfl

theorem cell23_2948461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_2948461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948461 prefixEnd_2948461 := by exact prefixLift 2948461
  have htrace : WordTrace (prefixWord ++ tailWord_2948461) baseStart_2948461 baseEnd_2948461 := by
    simpa [prefixWord, tailWord_2948461, baseEnd_2948461] using wordTrace_append hprefix tailTrace_2948461
  have hstable : (prefixWord ++ tailWord_2948461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948461).length < 2 ^ (prefixWord ++ tailWord_2948461).sum := by decide
  have hdescent : baseEnd_2948461 < baseStart_2948461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948478 : List Nat := [4, 2, 3, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2948478 : Nat := 118140960795 + 2948478 * 2 ^ 59
def prefixEnd_2948478 : Nat := 4983230072969 + 3 ^ 40 * 2948478 * 2
def baseEnd_2948478 : Nat := 1513986413207420299965203

theorem tailTrace_2948478 : CollatzResearch.WordTrace tailWord_2948478 prefixEnd_2948478 1513986413207420299965203 := by
  unfold tailWord_2948478
  simp only [CollatzResearch.WordTrace]
  refine ⟨13442478426521905099631761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71693218274783493864702725 13442478426521905099631761)
  ·
    refine ⟨10081858819891428824723821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13442478426521905099631761 10081858819891428824723821)
    ·
      refine ⟨3780697057459285809271433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10081858819891428824723821 3780697057459285809271433)
      ·
        refine ⟨2835522793094464356953575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3780697057459285809271433 2835522793094464356953575)
        ·
          refine ⟨4253284189641696535430363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2835522793094464356953575 4253284189641696535430363)
          ·
            refine ⟨6379926284462544803145545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4253284189641696535430363 6379926284462544803145545)
            ·
              refine ⟨4784944713346908602359159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6379926284462544803145545 4784944713346908602359159)
              ·
                refine ⟨7177417070020362903538739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4784944713346908602359159 7177417070020362903538739)
                ·
                  refine ⟨10766125605030544355308109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7177417070020362903538739 10766125605030544355308109)
                  ·
                    refine ⟨4037297101886454133240541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10766125605030544355308109 4037297101886454133240541)
                    ·
                      refine ⟨1513986413207420299965203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4037297101886454133240541 1513986413207420299965203)
                      ·
                        rfl

theorem cell23_2948478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2948478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948478 prefixEnd_2948478 := by exact prefixLift 2948478
  have htrace : WordTrace (prefixWord ++ tailWord_2948478) baseStart_2948478 baseEnd_2948478 := by
    simpa [prefixWord, tailWord_2948478, baseEnd_2948478] using wordTrace_append hprefix tailTrace_2948478
  have hstable : (prefixWord ++ tailWord_2948478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948478).length < 2 ^ (prefixWord ++ tailWord_2948478).sum := by decide
  have hdescent : baseEnd_2948478 < baseStart_2948478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948484 : List Nat := [2, 3, 2, 1, 1, 3, 1, 3, 1, 4, 2]
def baseStart_2948484 : Nat := 118140960795 + 2948484 * 2 ^ 59
def prefixEnd_2948484 : Nat := 4983230072969 + 3 ^ 40 * 2948484 * 2
def baseEnd_2948484 : Nat := 1513989494091347276490175

theorem tailTrace_2948484 : CollatzResearch.WordTrace tailWord_2948484 prefixEnd_2948484 1513989494091347276490175 := by
  unfold tailWord_2948484
  simp only [CollatzResearch.WordTrace]
  refine ⟨53770023125076751910886253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71693364166769002547848337 53770023125076751910886253)
  ·
    refine ⟨20163758671903781966582345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53770023125076751910886253 20163758671903781966582345)
    ·
      refine ⟨15122819003927836474936759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20163758671903781966582345 15122819003927836474936759)
      ·
        refine ⟨22684228505891754712405139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15122819003927836474936759 22684228505891754712405139)
        ·
          refine ⟨34026342758837632068607709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22684228505891754712405139 34026342758837632068607709)
          ·
            refine ⟨12759878534564112025727891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34026342758837632068607709 12759878534564112025727891)
            ·
              refine ⟨19139817801846168038591837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12759878534564112025727891 19139817801846168038591837)
              ·
                refine ⟨7177431675692313014471939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19139817801846168038591837 7177431675692313014471939)
                ·
                  refine ⟨10766147513538469521707909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7177431675692313014471939 10766147513538469521707909)
                  ·
                    refine ⟨2018652658788463035320233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10766147513538469521707909 2018652658788463035320233)
                    ·
                      refine ⟨1513989494091347276490175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2018652658788463035320233 1513989494091347276490175)
                      ·
                        rfl

theorem cell23_2948484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_2948484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948484 prefixEnd_2948484 := by exact prefixLift 2948484
  have htrace : WordTrace (prefixWord ++ tailWord_2948484) baseStart_2948484 baseEnd_2948484 := by
    simpa [prefixWord, tailWord_2948484, baseEnd_2948484] using wordTrace_append hprefix tailTrace_2948484
  have hstable : (prefixWord ++ tailWord_2948484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948484).length < 2 ^ (prefixWord ++ tailWord_2948484).sum := by decide
  have hdescent : baseEnd_2948484 < baseStart_2948484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948527 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 1, 7, 2]
def baseStart_2948527 : Nat := 118140960795 + 2948527 * 2 ^ 59
def prefixEnd_2948527 : Nat := 4983230072969 + 3 ^ 40 * 2948527 * 2
def baseEnd_2948527 : Nat := 1514011573759490608252477

theorem tailTrace_2948527 : CollatzResearch.WordTrace tailWord_2948527 prefixEnd_2948527 1514011573759490608252477 := by
  unfold tailWord_2948527
  simp only [CollatzResearch.WordTrace]
  refine ⟨107541614588997722165587835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71694409725998481443725223 107541614588997722165587835)
  ·
    refine ⟨161312421883496583248381753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107541614588997722165587835 161312421883496583248381753)
    ·
      refine ⟨120984316412622437436286315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161312421883496583248381753 120984316412622437436286315)
      ·
        refine ⟨181476474618933656154429473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120984316412622437436286315 181476474618933656154429473)
        ·
          refine ⟨136107355964200242115822105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181476474618933656154429473 136107355964200242115822105)
          ·
            refine ⟨102080516973150181586866579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136107355964200242115822105 102080516973150181586866579)
            ·
              refine ⟨153120775459725272380299869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102080516973150181586866579 153120775459725272380299869)
              ·
                refine ⟨57420290797396977142612451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153120775459725272380299869 57420290797396977142612451)
                ·
                  refine ⟨86130436196095465713918677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57420290797396977142612451 86130436196095465713918677)
                  ·
                    refine ⟨2018682098345987477669969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 86130436196095465713918677 2018682098345987477669969)
                    ·
                      refine ⟨1514011573759490608252477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2018682098345987477669969 1514011573759490608252477)
                      ·
                        rfl

theorem cell23_2948527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 7, 2].length) (baseStart_2948527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948527 prefixEnd_2948527 := by exact prefixLift 2948527
  have htrace : WordTrace (prefixWord ++ tailWord_2948527) baseStart_2948527 baseEnd_2948527 := by
    simpa [prefixWord, tailWord_2948527, baseEnd_2948527] using wordTrace_append hprefix tailTrace_2948527
  have hstable : (prefixWord ++ tailWord_2948527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948527).length < 2 ^ (prefixWord ++ tailWord_2948527).sum := by decide
  have hdescent : baseEnd_2948527 < baseStart_2948527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948567 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 5, 4]
def baseStart_2948567 : Nat := 118140960795 + 2948567 * 2 ^ 59
def prefixEnd_2948567 : Nat := 4983230072969 + 3 ^ 40 * 2948567 * 2
def baseEnd_2948567 : Nat := 504677370995223483917431

theorem tailTrace_2948567 : CollatzResearch.WordTrace tailWord_2948567 prefixEnd_2948567 504677370995223483917431 := by
  unfold tailWord_2948567
  simp only [CollatzResearch.WordTrace]
  refine ⟨107543073508852808997043955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71695382339235205998029303 107543073508852808997043955)
  ·
    refine ⟨161314610263279213495565933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107543073508852808997043955 161314610263279213495565933)
    ·
      refine ⟨60492978848729705060837225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161314610263279213495565933 60492978848729705060837225)
      ·
        refine ⟨45369734136547278795627919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60492978848729705060837225 45369734136547278795627919)
        ·
          refine ⟨68054601204820918193441879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45369734136547278795627919 68054601204820918193441879)
          ·
            refine ⟨102081901807231377290162819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68054601204820918193441879 102081901807231377290162819)
            ·
              refine ⟨153122852710847065935244229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102081901807231377290162819 153122852710847065935244229)
              ·
                refine ⟨28710534883283824862858293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153122852710847065935244229 28710534883283824862858293)
                ·
                  refine ⟨2691612645307858580892965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28710534883283824862858293 2691612645307858580892965)
                  ·
                    refine ⟨504677370995223483917431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2691612645307858580892965 504677370995223483917431)
                    ·
                      rfl

theorem cell23_2948567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 4].length) (baseStart_2948567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948567 prefixEnd_2948567 := by exact prefixLift 2948567
  have htrace : WordTrace (prefixWord ++ tailWord_2948567) baseStart_2948567 baseEnd_2948567 := by
    simpa [prefixWord, tailWord_2948567, baseEnd_2948567] using wordTrace_append hprefix tailTrace_2948567
  have hstable : (prefixWord ++ tailWord_2948567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948567).length < 2 ^ (prefixWord ++ tailWord_2948567).sum := by decide
  have hdescent : baseEnd_2948567 < baseStart_2948567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948634 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2]
def baseStart_2948634 : Nat := 118140960795 + 2948634 * 2 ^ 59
def prefixEnd_2948634 : Nat := 4983230072969 + 3 ^ 40 * 2948634 * 2
def baseEnd_2948634 : Nat := 1514066516189521689614485

theorem tailTrace_2948634 : CollatzResearch.WordTrace tailWord_2948634 prefixEnd_2948634 1514066516189521689614485 := by
  unfold tailWord_2948634
  simp only [CollatzResearch.WordTrace]
  refine ⟨26886379299902519859933239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71697011466406719626488637 26886379299902519859933239)
  ·
    refine ⟨40329568949853779789899859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26886379299902519859933239 40329568949853779789899859)
    ·
      refine ⟨60494353424780669684849789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40329568949853779789899859 60494353424780669684849789)
      ·
        refine ⟨22685382534292751131818671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60494353424780669684849789 22685382534292751131818671)
        ·
          refine ⟨34028073801439126697728007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22685382534292751131818671 34028073801439126697728007)
          ·
            refine ⟨51042110702158690046592011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34028073801439126697728007 51042110702158690046592011)
            ·
              refine ⟨76563166053238035069888017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51042110702158690046592011 76563166053238035069888017)
              ·
                refine ⟨57422374539928526302416013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76563166053238035069888017 57422374539928526302416013)
                ·
                  refine ⟨21533390452473197363406005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57422374539928526302416013 21533390452473197363406005)
                  ·
                    refine ⟨2018755354919362252819313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21533390452473197363406005 2018755354919362252819313)
                    ·
                      refine ⟨1514066516189521689614485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2018755354919362252819313 1514066516189521689614485)
                      ·
                        rfl

theorem cell23_2948634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_2948634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948634 prefixEnd_2948634 := by exact prefixLift 2948634
  have htrace : WordTrace (prefixWord ++ tailWord_2948634) baseStart_2948634 baseEnd_2948634 := by
    simpa [prefixWord, tailWord_2948634, baseEnd_2948634] using wordTrace_append hprefix tailTrace_2948634
  have hstable : (prefixWord ++ tailWord_2948634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948634).length < 2 ^ (prefixWord ++ tailWord_2948634).sum := by decide
  have hdescent : baseEnd_2948634 < baseStart_2948634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948664 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 3, 1, 4]
def baseStart_2948664 : Nat := 118140960795 + 2948664 * 2 ^ 59
def prefixEnd_2948664 : Nat := 4983230072969 + 3 ^ 40 * 2948664 * 2
def baseEnd_2948664 : Nat := 1514081920609156572239347

theorem tailTrace_2948664 : CollatzResearch.WordTrace tailWord_2948664 prefixEnd_2948664 1514081920609156572239347 := by
  unfold tailWord_2948664
  simp only [CollatzResearch.WordTrace]
  refine ⟨53773305694750697281662523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71697740926334263042216697 53773305694750697281662523)
  ·
    refine ⟨80659958542126045922493785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53773305694750697281662523 80659958542126045922493785)
    ·
      refine ⟨60494968906594534441870339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80659958542126045922493785 60494968906594534441870339)
      ·
        refine ⟨90742453359891801662805509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60494968906594534441870339 90742453359891801662805509)
        ·
          refine ⟨17014210004979712811776033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90742453359891801662805509 17014210004979712811776033)
          ·
            refine ⟨12760657503734784608832025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17014210004979712811776033 12760657503734784608832025)
            ·
              refine ⟨9570493127801088456624019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12760657503734784608832025 9570493127801088456624019)
              ·
                refine ⟨14355739691701632684936029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9570493127801088456624019 14355739691701632684936029)
                ·
                  refine ⟨5383402384388112256851011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14355739691701632684936029 5383402384388112256851011)
                  ·
                    refine ⟨8075103576582168385276517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5383402384388112256851011 8075103576582168385276517)
                    ·
                      refine ⟨1514081920609156572239347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8075103576582168385276517 1514081920609156572239347)
                      ·
                        rfl

theorem cell23_2948664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_2948664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948664 prefixEnd_2948664 := by exact prefixLift 2948664
  have htrace : WordTrace (prefixWord ++ tailWord_2948664) baseStart_2948664 baseEnd_2948664 := by
    simpa [prefixWord, tailWord_2948664, baseEnd_2948664] using wordTrace_append hprefix tailTrace_2948664
  have hstable : (prefixWord ++ tailWord_2948664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948664).length < 2 ^ (prefixWord ++ tailWord_2948664).sum := by decide
  have hdescent : baseEnd_2948664 < baseStart_2948664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948708 : List Nat := [2, 3, 1, 1, 2, 4, 3, 1, 2, 4]
def baseStart_2948708 : Nat := 118140960795 + 2948708 * 2 ^ 59
def prefixEnd_2948708 : Nat := 4983230072969 + 3 ^ 40 * 2948708 * 2
def baseEnd_2948708 : Nat := 504701504585984800029715

theorem tailTrace_2948708 : CollatzResearch.WordTrace tailWord_2948708 prefixEnd_2948708 504701504585984800029715 := by
  unfold tailWord_2948708
  simp only [CollatzResearch.WordTrace]
  refine ⟨53774108100670995038963389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71698810800894660051951185 53774108100670995038963389)
  ·
    refine ⟨20165290537751623139611271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53774108100670995038963389 20165290537751623139611271)
    ·
      refine ⟨30247935806627434709416907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20165290537751623139611271 30247935806627434709416907)
      ·
        refine ⟨45371903709941152064125361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30247935806627434709416907 45371903709941152064125361)
        ·
          refine ⟨34028927782455864048094021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45371903709941152064125361 34028927782455864048094021)
          ·
            refine ⟨6380423959210474509017629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34028927782455864048094021 6380423959210474509017629)
            ·
              refine ⟨2392658984703927940881611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6380423959210474509017629 2392658984703927940881611)
              ·
                refine ⟨3588988477055891911322417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2392658984703927940881611 3588988477055891911322417)
                ·
                  refine ⟨2691741357791918933491813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3588988477055891911322417 2691741357791918933491813)
                  ·
                    refine ⟨504701504585984800029715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2691741357791918933491813 504701504585984800029715)
                    ·
                      rfl

theorem cell23_2948708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_2948708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948708 prefixEnd_2948708 := by exact prefixLift 2948708
  have htrace : WordTrace (prefixWord ++ tailWord_2948708) baseStart_2948708 baseEnd_2948708 := by
    simpa [prefixWord, tailWord_2948708, baseEnd_2948708] using wordTrace_append hprefix tailTrace_2948708
  have hstable : (prefixWord ++ tailWord_2948708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948708).length < 2 ^ (prefixWord ++ tailWord_2948708).sum := by decide
  have hdescent : baseEnd_2948708 < baseStart_2948708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948771 : List Nat := [1, 1, 1, 4, 1, 1, 4, 3, 1, 4, 2]
def baseStart_2948771 : Nat := 118140960795 + 2948771 * 2 ^ 59
def prefixEnd_2948771 : Nat := 4983230072969 + 3 ^ 40 * 2948771 * 2
def baseEnd_2948771 : Nat := 1514136863039187653601355

theorem tailTrace_2948771 : CollatzResearch.WordTrace tailWord_2948771 prefixEnd_2948771 1514136863039187653601355 := by
  unfold tailWord_2948771
  simp only [CollatzResearch.WordTrace]
  refine ⟨107550514000113751837470167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71700342666742501224980111 107550514000113751837470167)
  ·
    refine ⟨161325771000170627756205251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107550514000113751837470167 161325771000170627756205251)
    ·
      refine ⟨241988656500255941634307877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161325771000170627756205251 241988656500255941634307877)
      ·
        refine ⟨45372873093797989056432727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241988656500255941634307877 45372873093797989056432727)
        ·
          refine ⟨68059309640696983584649091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45372873093797989056432727 68059309640696983584649091)
          ·
            refine ⟨102088964461045475376973637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68059309640696983584649091 102088964461045475376973637)
            ·
              refine ⟨19141680836446026633182557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102088964461045475376973637 19141680836446026633182557)
              ·
                refine ⟨7178130313667259987443459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19141680836446026633182557 7178130313667259987443459)
                ·
                  refine ⟨10767195470500889981165189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7178130313667259987443459 10767195470500889981165189)
                  ·
                    refine ⟨2018849150718916871468473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10767195470500889981165189 2018849150718916871468473)
                    ·
                      refine ⟨1514136863039187653601355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2018849150718916871468473 1514136863039187653601355)
                      ·
                        rfl

theorem cell23_2948771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_2948771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948771 prefixEnd_2948771 := by exact prefixLift 2948771
  have htrace : WordTrace (prefixWord ++ tailWord_2948771) baseStart_2948771 baseEnd_2948771 := by
    simpa [prefixWord, tailWord_2948771, baseEnd_2948771] using wordTrace_append hprefix tailTrace_2948771
  have hstable : (prefixWord ++ tailWord_2948771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948771).length < 2 ^ (prefixWord ++ tailWord_2948771).sum := by decide
  have hdescent : baseEnd_2948771 < baseStart_2948771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948824 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 1, 7]
def baseStart_2948824 : Nat := 118140960795 + 2948824 * 2 ^ 59
def prefixEnd_2948824 : Nat := 4983230072969 + 3 ^ 40 * 2948824 * 2
def baseEnd_2948824 : Nat := 504721359171291982079537

theorem tailTrace_2948824 : CollatzResearch.WordTrace tailWord_2948824 prefixEnd_2948824 504721359171291982079537 := by
  unfold tailWord_2948824
  simp only [CollatzResearch.WordTrace]
  refine ⟨53776223534460870944574763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71701631379281161259433017 53776223534460870944574763)
  ·
    refine ⟨80664335301691306416862145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53776223534460870944574763 80664335301691306416862145)
    ·
      refine ⟨60498251476268479812646609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80664335301691306416862145 60498251476268479812646609)
      ·
        refine ⟨45373688607201359859484957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60498251476268479812646609 45373688607201359859484957)
        ·
          refine ⟨17015133227700509947306859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45373688607201359859484957 17015133227700509947306859)
          ·
            refine ⟨25522699841550764920960289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17015133227700509947306859 25522699841550764920960289)
            ·
              refine ⟨19142024881163073690720217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25522699841550764920960289 19142024881163073690720217)
              ·
                refine ⟨14356518660872305268040163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19142024881163073690720217 14356518660872305268040163)
                ·
                  refine ⟨21534777991308457902060245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14356518660872305268040163 21534777991308457902060245)
                  ·
                    refine ⟨504721359171291982079537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21534777991308457902060245 504721359171291982079537)
                    ·
                      rfl

theorem cell23_2948824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_2948824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948824 prefixEnd_2948824 := by exact prefixLift 2948824
  have htrace : WordTrace (prefixWord ++ tailWord_2948824) baseStart_2948824 baseEnd_2948824 := by
    simpa [prefixWord, tailWord_2948824, baseEnd_2948824] using wordTrace_append hprefix tailTrace_2948824
  have hstable : (prefixWord ++ tailWord_2948824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948824).length < 2 ^ (prefixWord ++ tailWord_2948824).sum := by decide
  have hdescent : baseEnd_2948824 < baseStart_2948824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948828 : List Nat := [2, 2, 5, 1, 2, 1, 1, 2, 7]
def baseStart_2948828 : Nat := 118140960795 + 2948828 * 2 ^ 59
def prefixEnd_2948828 : Nat := 4983230072969 + 3 ^ 40 * 2948828 * 2
def baseEnd_2948828 : Nat := 168240681270721547843177

theorem tailTrace_2948828 : CollatzResearch.WordTrace tailWord_2948828 prefixEnd_2948828 168240681270721547843177 := by
  unfold tailWord_2948828
  simp only [CollatzResearch.WordTrace]
  refine ⟨53776296480453625286147569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71701728640604833714863425 53776296480453625286147569)
  ·
    refine ⟨40332222360340218964610677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53776296480453625286147569 40332222360340218964610677)
    ·
      refine ⟨3781145846281895527932251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40332222360340218964610677 3781145846281895527932251)
      ·
        refine ⟨5671718769422843291898377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3781145846281895527932251 5671718769422843291898377)
        ·
          refine ⟨4253789077067132468923783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5671718769422843291898377 4253789077067132468923783)
          ·
            refine ⟨6380683615600698703385675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4253789077067132468923783 6380683615600698703385675)
            ·
              refine ⟨9571025423401048055078513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6380683615600698703385675 9571025423401048055078513)
              ·
                refine ⟨7178269067550786041308885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9571025423401048055078513 7178269067550786041308885)
                ·
                  refine ⟨168240681270721547843177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7178269067550786041308885 168240681270721547843177)
                  ·
                    rfl

theorem cell23_2948828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 7].length) (baseStart_2948828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948828 prefixEnd_2948828 := by exact prefixLift 2948828
  have htrace : WordTrace (prefixWord ++ tailWord_2948828) baseStart_2948828 baseEnd_2948828 := by
    simpa [prefixWord, tailWord_2948828, baseEnd_2948828] using wordTrace_append hprefix tailTrace_2948828
  have hstable : (prefixWord ++ tailWord_2948828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948828).length < 2 ^ (prefixWord ++ tailWord_2948828).sum := by decide
  have hdescent : baseEnd_2948828 < baseStart_2948828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948831 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 2, 5, 2]
def baseStart_2948831 : Nat := 118140960795 + 2948831 * 2 ^ 59
def prefixEnd_2948831 : Nat := 4983230072969 + 3 ^ 40 * 2948831 * 2
def baseEnd_2948831 : Nat := 1514167671878457418851079

theorem tailTrace_2948831 : CollatzResearch.WordTrace tailWord_2948831 prefixEnd_2948831 1514167671878457418851079 := by
  unfold tailWord_2948831
  simp only [CollatzResearch.WordTrace]
  refine ⟨107552702379896382084654347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71701801586597588056436231 107552702379896382084654347)
  ·
    refine ⟨161329053569844573126981521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107552702379896382084654347 161329053569844573126981521)
    ·
      refine ⟨120996790177383429845236141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161329053569844573126981521 120996790177383429845236141)
      ·
        refine ⟨45373796316518786191963553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120996790177383429845236141 45373796316518786191963553)
        ·
          refine ⟨34030347237389089643972665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45373796316518786191963553 34030347237389089643972665)
          ·
            refine ⟨25522760428041817232979499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34030347237389089643972665 25522760428041817232979499)
            ·
              refine ⟨38284140642062725849469249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25522760428041817232979499 38284140642062725849469249)
              ·
                refine ⟨28713105481547044387101937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38284140642062725849469249 28713105481547044387101937)
                ·
                  refine ⟨21534829111160283290326453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28713105481547044387101937 21534829111160283290326453)
                  ·
                    refine ⟨2018890229171276558468105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21534829111160283290326453 2018890229171276558468105)
                    ·
                      refine ⟨1514167671878457418851079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2018890229171276558468105 1514167671878457418851079)
                      ·
                        rfl

theorem cell23_2948831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_2948831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948831 prefixEnd_2948831 := by exact prefixLift 2948831
  have htrace : WordTrace (prefixWord ++ tailWord_2948831) baseStart_2948831 baseEnd_2948831 := by
    simpa [prefixWord, tailWord_2948831, baseEnd_2948831] using wordTrace_append hprefix tailTrace_2948831
  have hstable : (prefixWord ++ tailWord_2948831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948831).length < 2 ^ (prefixWord ++ tailWord_2948831).sum := by decide
  have hdescent : baseEnd_2948831 < baseStart_2948831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948878 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2]
def baseStart_2948878 : Nat := 118140960795 + 2948878 * 2 ^ 59
def prefixEnd_2948878 : Nat := 4983230072969 + 3 ^ 40 * 2948878 * 2
def baseEnd_2948878 : Nat := 1514191805469218734963363

theorem tailTrace_2948878 : CollatzResearch.WordTrace tailWord_2948878 prefixEnd_2948878 1514191805469218734963363 := by
  unfold tailWord_2948878
  simp only [CollatzResearch.WordTrace]
  refine ⟨13444302076340763638951911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71702944407150739407743525 13444302076340763638951911)
  ·
    refine ⟨20166453114511145458427867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13444302076340763638951911 20166453114511145458427867)
    ·
      refine ⟨30249679671766718187641801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20166453114511145458427867 30249679671766718187641801)
      ·
        refine ⟨22687259753825038640731351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30249679671766718187641801 22687259753825038640731351)
        ·
          refine ⟨34030889630737557961097027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22687259753825038640731351 34030889630737557961097027)
          ·
            refine ⟨51046334446106336941645541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34030889630737557961097027 51046334446106336941645541)
            ·
              refine ⟨9571187708644938176558539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51046334446106336941645541 9571187708644938176558539)
              ·
                refine ⟨14356781562967407264837809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9571187708644938176558539 14356781562967407264837809)
                ·
                  refine ⟨10767586172225555448628357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14356781562967407264837809 10767586172225555448628357)
                  ·
                    refine ⟨2018922407292291646617817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10767586172225555448628357 2018922407292291646617817)
                    ·
                      refine ⟨1514191805469218734963363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2018922407292291646617817 1514191805469218734963363)
                      ·
                        rfl

theorem cell23_2948878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_2948878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948878 prefixEnd_2948878 := by exact prefixLift 2948878
  have htrace : WordTrace (prefixWord ++ tailWord_2948878) baseStart_2948878 baseEnd_2948878 := by
    simpa [prefixWord, tailWord_2948878, baseEnd_2948878] using wordTrace_append hprefix tailTrace_2948878
  have hstable : (prefixWord ++ tailWord_2948878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948878).length < 2 ^ (prefixWord ++ tailWord_2948878).sum := by decide
  have hdescent : baseEnd_2948878 < baseStart_2948878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948898 : List Nat := [3, 3, 1, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_2948898 : Nat := 118140960795 + 2948898 * 2 ^ 59
def prefixEnd_2948898 : Nat := 4983230072969 + 3 ^ 40 * 2948898 * 2
def baseEnd_2948898 : Nat := 1514202075082308656713271

theorem tailTrace_2948898 : CollatzResearch.WordTrace tailWord_2948898 prefixEnd_2948898 1514202075082308656713271 := by
  unfold tailWord_2948898
  simp only [CollatzResearch.WordTrace]
  refine ⟨26888786517663413131835837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71703430713769101684895565 26888786517663413131835837)
  ·
    refine ⟨10083294944123779924438439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26888786517663413131835837 10083294944123779924438439)
    ·
      refine ⟨15124942416185669886657659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10083294944123779924438439 15124942416185669886657659)
      ·
        refine ⟨22687413624278504829986489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15124942416185669886657659 22687413624278504829986489)
        ·
          refine ⟨17015560218208878622489867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22687413624278504829986489 17015560218208878622489867)
          ·
            refine ⟨25523340327313317933734801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17015560218208878622489867 25523340327313317933734801)
            ·
              refine ⟨19142505245484988450301101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25523340327313317933734801 19142505245484988450301101)
              ·
                refine ⟨7178439467056870668862913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19142505245484988450301101 7178439467056870668862913)
                ·
                  refine ⟨5383829600292653001647185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7178439467056870668862913 5383829600292653001647185)
                  ·
                    refine ⟨4037872200219489751235389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5383829600292653001647185 4037872200219489751235389)
                    ·
                      refine ⟨1514202075082308656713271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4037872200219489751235389 1514202075082308656713271)
                      ·
                        rfl

theorem cell23_2948898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_2948898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948898 prefixEnd_2948898 := by exact prefixLift 2948898
  have htrace : WordTrace (prefixWord ++ tailWord_2948898) baseStart_2948898 baseEnd_2948898 := by
    simpa [prefixWord, tailWord_2948898, baseEnd_2948898] using wordTrace_append hprefix tailTrace_2948898
  have hstable : (prefixWord ++ tailWord_2948898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948898).length < 2 ^ (prefixWord ++ tailWord_2948898).sum := by decide
  have hdescent : baseEnd_2948898 < baseStart_2948898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948918 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 8]
def baseStart_2948918 : Nat := 118140960795 + 2948918 * 2 ^ 59
def prefixEnd_2948918 : Nat := 4983230072969 + 3 ^ 40 * 2948918 * 2
def baseEnd_2948918 : Nat := 168245816077266508718131

theorem tailTrace_2948918 : CollatzResearch.WordTrace tailWord_2948918 prefixEnd_2948918 168245816077266508718131 := by
  unfold tailWord_2948918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6722242220661324746441963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71703917020387463962047605 6722242220661324746441963)
  ·
    refine ⟨10083363330991987119662945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6722242220661324746441963 10083363330991987119662945)
    ·
      refine ⟨7562522498243990339747209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10083363330991987119662945 7562522498243990339747209)
      ·
        refine ⟨5671891873682992754810407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7562522498243990339747209 5671891873682992754810407)
        ·
          refine ⟨8507837810524489132215611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5671891873682992754810407 8507837810524489132215611)
          ·
            refine ⟨12761756715786733698323417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8507837810524489132215611 12761756715786733698323417)
            ·
              refine ⟨9571317536840050273742563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12761756715786733698323417 9571317536840050273742563)
              ·
                refine ⟨14356976305260075410613845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9571317536840050273742563 14356976305260075410613845)
                ·
                  refine ⟨168245816077266508718131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14356976305260075410613845 168245816077266508718131)
                  ·
                    rfl

theorem cell23_2948918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_2948918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948918 prefixEnd_2948918 := by exact prefixLift 2948918
  have htrace : WordTrace (prefixWord ++ tailWord_2948918) baseStart_2948918 baseEnd_2948918 := by
    simpa [prefixWord, tailWord_2948918, baseEnd_2948918] using wordTrace_append hprefix tailTrace_2948918
  have hstable : (prefixWord ++ tailWord_2948918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948918).length < 2 ^ (prefixWord ++ tailWord_2948918).sum := by decide
  have hdescent : baseEnd_2948918 < baseStart_2948918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948922 : List Nat := [3, 1, 1, 1, 5, 2, 3, 2, 1, 4]
def baseStart_2948922 : Nat := 118140960795 + 2948922 * 2 ^ 59
def prefixEnd_2948922 : Nat := 4983230072969 + 3 ^ 40 * 2948922 * 2
def baseEnd_2948922 : Nat := 504738132872672187604387

theorem tailTrace_2948922 : CollatzResearch.WordTrace tailWord_2948922 prefixEnd_2948922 504738132872672187604387 := by
  unfold tailWord_2948922
  simp only [CollatzResearch.WordTrace]
  refine ⟨26889005355641676156554255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71704014281711136417478013 26889005355641676156554255)
  ·
    refine ⟨40333508033462514234831383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26889005355641676156554255 40333508033462514234831383)
    ·
      refine ⟨60500262050193771352247075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40333508033462514234831383 60500262050193771352247075)
      ·
        refine ⟨90750393075290657028370613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60500262050193771352247075 90750393075290657028370613)
        ·
          refine ⟨8507849350808499096409745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90750393075290657028370613 8507849350808499096409745)
          ·
            refine ⟨6380887013106374322307309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8507849350808499096409745 6380887013106374322307309)
            ·
              refine ⟨2392832629914890370865241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6380887013106374322307309 2392832629914890370865241)
              ·
                refine ⟨1794624472436167778148931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2392832629914890370865241 1794624472436167778148931)
                ·
                  refine ⟨2691936708654251667223397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1794624472436167778148931 2691936708654251667223397)
                  ·
                    refine ⟨504738132872672187604387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2691936708654251667223397 504738132872672187604387)
                    ·
                      rfl

theorem cell23_2948922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 1, 4].length) (baseStart_2948922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948922 prefixEnd_2948922 := by exact prefixLift 2948922
  have htrace : WordTrace (prefixWord ++ tailWord_2948922) baseStart_2948922 baseEnd_2948922 := by
    simpa [prefixWord, tailWord_2948922, baseEnd_2948922] using wordTrace_append hprefix tailTrace_2948922
  have hstable : (prefixWord ++ tailWord_2948922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948922).length < 2 ^ (prefixWord ++ tailWord_2948922).sum := by decide
  have hdescent : baseEnd_2948922 < baseStart_2948922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948938 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 4, 3, 2]
def baseStart_2948938 : Nat := 118140960795 + 2948938 * 2 ^ 59
def prefixEnd_2948938 : Nat := 4983230072969 + 3 ^ 40 * 2948938 * 2
def baseEnd_2948938 : Nat := 1514222614308488500213087

theorem tailTrace_2948938 : CollatzResearch.WordTrace tailWord_2948938 prefixEnd_2948938 1514222614308488500213087 := by
  unfold tailWord_2948938
  simp only [CollatzResearch.WordTrace]
  refine ⟨26889151247627184839699867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71704403327005826239199645 26889151247627184839699867)
  ·
    refine ⟨40333726871440777259549801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26889151247627184839699867 40333726871440777259549801)
    ·
      refine ⟨30250295153580582944662351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40333726871440777259549801 30250295153580582944662351)
      ·
        refine ⟨45375442730370874416993527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30250295153580582944662351 45375442730370874416993527)
        ·
          refine ⟨68063164095556311625490291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45375442730370874416993527 68063164095556311625490291)
          ·
            refine ⟨102094746143334467438235437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68063164095556311625490291 102094746143334467438235437)
            ·
              refine ⟨38285529803750425289338289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102094746143334467438235437 38285529803750425289338289)
              ·
                refine ⟨28714147352812818967003717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38285529803750425289338289 28714147352812818967003717)
                ·
                  refine ⟨5383902628652403556313197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28714147352812818967003717 5383902628652403556313197)
                  ·
                    refine ⟨2018963485744651333617449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5383902628652403556313197 2018963485744651333617449)
                    ·
                      refine ⟨1514222614308488500213087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2018963485744651333617449 1514222614308488500213087)
                      ·
                        rfl

theorem cell23_2948938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_2948938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948938 prefixEnd_2948938 := by exact prefixLift 2948938
  have htrace : WordTrace (prefixWord ++ tailWord_2948938) baseStart_2948938 baseEnd_2948938 := by
    simpa [prefixWord, tailWord_2948938, baseEnd_2948938] using wordTrace_append hprefix tailTrace_2948938
  have hstable : (prefixWord ++ tailWord_2948938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948938).length < 2 ^ (prefixWord ++ tailWord_2948938).sum := by decide
  have hdescent : baseEnd_2948938 < baseStart_2948938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948948 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_2948948 : Nat := 118140960795 + 2948948 * 2 ^ 59
def prefixEnd_2948948 : Nat := 4983230072969 + 3 ^ 40 * 2948948 * 2
def baseEnd_2948948 : Nat := 504742583038344487029347

theorem tailTrace_2948948 : CollatzResearch.WordTrace tailWord_2948948 prefixEnd_2948948 504742583038344487029347 := by
  unfold tailWord_2948948
  simp only [CollatzResearch.WordTrace]
  refine ⟨53778484860236255533331749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71704646480315007377775665 53778484860236255533331749)
  ·
    refine ⟨10083465911294297912499703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53778484860236255533331749 10083465911294297912499703)
    ·
      refine ⟨15125198866941446868749555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10083465911294297912499703 15125198866941446868749555)
      ·
        refine ⟨22687798300412170303124333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15125198866941446868749555 22687798300412170303124333)
        ·
          refine ⟨8507924362654563863671625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22687798300412170303124333 8507924362654563863671625)
          ·
            refine ⟨6380943271990922897753719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8507924362654563863671625 6380943271990922897753719)
            ·
              refine ⟨9571414907986384346630579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6380943271990922897753719 9571414907986384346630579)
              ·
                refine ⟨14357122361979576519945869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9571414907986384346630579 14357122361979576519945869)
                ·
                  refine ⟨5383920885742341194979701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14357122361979576519945869 5383920885742341194979701)
                  ·
                    refine ⟨504742583038344487029347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5383920885742341194979701 504742583038344487029347)
                    ·
                      rfl

theorem cell23_2948948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_2948948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948948 prefixEnd_2948948 := by exact prefixLift 2948948
  have htrace : WordTrace (prefixWord ++ tailWord_2948948) baseStart_2948948 baseEnd_2948948 := by
    simpa [prefixWord, tailWord_2948948, baseEnd_2948948] using wordTrace_append hprefix tailTrace_2948948
  have hstable : (prefixWord ++ tailWord_2948948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948948).length < 2 ^ (prefixWord ++ tailWord_2948948).sum := by decide
  have hdescent : baseEnd_2948948 < baseStart_2948948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948961 : List Nat := [1, 2, 3, 1, 1, 1, 5, 2, 1, 6]
def baseStart_2948961 : Nat := 118140960795 + 2948961 * 2 ^ 59
def prefixEnd_2948961 : Nat := 4983230072969 + 3 ^ 40 * 2948961 * 2
def baseEnd_2948961 : Nat := 504744808121180636741827

theorem tailTrace_2948961 : CollatzResearch.WordTrace tailWord_2948961 prefixEnd_2948961 504744808121180636741827 := by
  unfold tailWord_2948961
  simp only [CollatzResearch.WordTrace]
  refine ⟨107557443869425414286886737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71704962579616942857924491 107557443869425414286886737)
  ·
    refine ⟨80668082902069060715165053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107557443869425414286886737 80668082902069060715165053)
    ·
      refine ⟨30250531088275897768186895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80668082902069060715165053 30250531088275897768186895)
      ·
        refine ⟨45375796632413846652280343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30250531088275897768186895 45375796632413846652280343)
        ·
          refine ⟨68063694948620769978420515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45375796632413846652280343 68063694948620769978420515)
          ·
            refine ⟨102095542422931154967630773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68063694948620769978420515 102095542422931154967630773)
            ·
              refine ⟨9571457102149795778215385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102095542422931154967630773 9571457102149795778215385)
              ·
                refine ⟨7178592826612346833661539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9571457102149795778215385 7178592826612346833661539)
                ·
                  refine ⟨10767889239918520250492309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7178592826612346833661539 10767889239918520250492309)
                  ·
                    refine ⟨504744808121180636741827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10767889239918520250492309 504744808121180636741827)
                    ·
                      rfl

theorem cell23_2948961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_2948961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948961 prefixEnd_2948961 := by exact prefixLift 2948961
  have htrace : WordTrace (prefixWord ++ tailWord_2948961) baseStart_2948961 baseEnd_2948961 := by
    simpa [prefixWord, tailWord_2948961, baseEnd_2948961] using wordTrace_append hprefix tailTrace_2948961
  have hstable : (prefixWord ++ tailWord_2948961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948961).length < 2 ^ (prefixWord ++ tailWord_2948961).sum := by decide
  have hdescent : baseEnd_2948961 < baseStart_2948961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2948985 : List Nat := [1, 2, 1, 3, 2, 2, 2, 3, 3, 2, 2]
def baseStart_2948985 : Nat := 118140960795 + 2948985 * 2 ^ 59
def prefixEnd_2948985 : Nat := 4983230072969 + 3 ^ 40 * 2948985 * 2
def baseEnd_2948985 : Nat := 1514246747899249816325371

theorem tailTrace_2948985 : CollatzResearch.WordTrace tailWord_2948985 prefixEnd_2948985 1514246747899249816325371 := by
  unfold tailWord_2948985
  simp only [CollatzResearch.WordTrace]
  refine ⟨107558319221338466385760409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71705546147558977590506939 107558319221338466385760409)
  ·
    refine ⟨80668739416003849789320307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107558319221338466385760409 80668739416003849789320307)
    ·
      refine ⟨121003109124005774683980461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80668739416003849789320307 121003109124005774683980461)
      ·
        refine ⟨45376165921502165506492673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121003109124005774683980461 45376165921502165506492673)
        ·
          refine ⟨34032124441126624129869505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45376165921502165506492673 34032124441126624129869505)
          ·
            refine ⟨25524093330844968097402129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34032124441126624129869505 25524093330844968097402129)
            ·
              refine ⟨19143069998133726073051597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25524093330844968097402129 19143069998133726073051597)
              ·
                refine ⟨7178651249300147277394349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19143069998133726073051597 7178651249300147277394349)
                ·
                  refine ⟨2691994218487555229022881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7178651249300147277394349 2691994218487555229022881)
                  ·
                    refine ⟨2018995663865666421767161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2691994218487555229022881 2018995663865666421767161)
                    ·
                      refine ⟨1514246747899249816325371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2018995663865666421767161 1514246747899249816325371)
                      ·
                        rfl

theorem cell23_2948985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_2948985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2948985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2948985 prefixEnd_2948985 := by exact prefixLift 2948985
  have htrace : WordTrace (prefixWord ++ tailWord_2948985) baseStart_2948985 baseEnd_2948985 := by
    simpa [prefixWord, tailWord_2948985, baseEnd_2948985] using wordTrace_append hprefix tailTrace_2948985
  have hstable : (prefixWord ++ tailWord_2948985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2948985).length < 2 ^ (prefixWord ++ tailWord_2948985).sum := by decide
  have hdescent : baseEnd_2948985 < baseStart_2948985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2948985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949006 : List Nat := [4, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2]
def baseStart_2949006 : Nat := 118140960795 + 2949006 * 2 ^ 59
def prefixEnd_2949006 : Nat := 4983230072969 + 3 ^ 40 * 2949006 * 2
def baseEnd_2949006 : Nat := 1514257530992994234162775

theorem tailTrace_2949006 : CollatzResearch.WordTrace tailWord_2949006 prefixEnd_2949006 1514257530992994234162775 := by
  unfold tailWord_2949006
  simp only [CollatzResearch.WordTrace]
  refine ⟨13444885644282798371534359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71706056769508257981516581 13444885644282798371534359)
  ·
    refine ⟨20167328466424197557301539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13444885644282798371534359 20167328466424197557301539)
    ·
      refine ⟨30250992699636296335952309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20167328466424197557301539 30250992699636296335952309)
      ·
        refine ⟨2836030565590902781495529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30250992699636296335952309 2836030565590902781495529)
        ·
          refine ⟨2127022924193177086121647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2836030565590902781495529 2127022924193177086121647)
          ·
            refine ⟨3190534386289765629182471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2127022924193177086121647 3190534386289765629182471)
            ·
              refine ⟨4785801579434648443773707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3190534386289765629182471 4785801579434648443773707)
              ·
                refine ⟨7178702369151972665660561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4785801579434648443773707 7178702369151972665660561)
                ·
                  refine ⟨5384026776863979499245421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7178702369151972665660561 5384026776863979499245421)
                  ·
                    refine ⟨2019010041323992312217033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5384026776863979499245421 2019010041323992312217033)
                    ·
                      refine ⟨1514257530992994234162775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2019010041323992312217033 1514257530992994234162775)
                      ·
                        rfl

theorem cell23_2949006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_2949006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949006 prefixEnd_2949006 := by exact prefixLift 2949006
  have htrace : WordTrace (prefixWord ++ tailWord_2949006) baseStart_2949006 baseEnd_2949006 := by
    simpa [prefixWord, tailWord_2949006, baseEnd_2949006] using wordTrace_append hprefix tailTrace_2949006
  have hstable : (prefixWord ++ tailWord_2949006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949006).length < 2 ^ (prefixWord ++ tailWord_2949006).sum := by decide
  have hdescent : baseEnd_2949006 < baseStart_2949006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949092 : List Nat := [2, 3, 1, 1, 1, 1, 4, 4, 2, 2, 2]
def baseStart_2949092 : Nat := 118140960795 + 2949092 * 2 ^ 59
def prefixEnd_2949092 : Nat := 4983230072969 + 3 ^ 40 * 2949092 * 2
def baseEnd_2949092 : Nat := 1514301690329280897687379

theorem tailTrace_2949092 : CollatzResearch.WordTrace tailWord_2949092 prefixEnd_2949092 1514301690329280897687379 := by
  unfold tailWord_2949092
  simp only [CollatzResearch.WordTrace]
  refine ⟨53781110915975411829952765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71708147887967215773270353 53781110915975411829952765)
  ·
    refine ⟨20167916593490779436232287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53781110915975411829952765 20167916593490779436232287)
    ·
      refine ⟨30251874890236169154348431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20167916593490779436232287 30251874890236169154348431)
      ·
        refine ⟨45377812335354253731522647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30251874890236169154348431 45377812335354253731522647)
        ·
          refine ⟨68066718503031380597283971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45377812335354253731522647 68066718503031380597283971)
          ·
            refine ⟨102100077754547070895925957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68066718503031380597283971 102100077754547070895925957)
            ·
              refine ⟨19143764578977575792986117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102100077754547070895925957 19143764578977575792986117)
              ·
                refine ⟨3589455858558295461184897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19143764578977575792986117 3589455858558295461184897)
                ·
                  refine ⟨2692091893918721595888673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3589455858558295461184897 2692091893918721595888673)
                  ·
                    refine ⟨2019068920439041196916505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2692091893918721595888673 2019068920439041196916505)
                    ·
                      refine ⟨1514301690329280897687379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2019068920439041196916505 1514301690329280897687379)
                      ·
                        rfl

theorem cell23_2949092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_2949092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949092 prefixEnd_2949092 := by exact prefixLift 2949092
  have htrace : WordTrace (prefixWord ++ tailWord_2949092) baseStart_2949092 baseEnd_2949092 := by
    simpa [prefixWord, tailWord_2949092, baseEnd_2949092] using wordTrace_append hprefix tailTrace_2949092
  have hstable : (prefixWord ++ tailWord_2949092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949092).length < 2 ^ (prefixWord ++ tailWord_2949092).sum := by decide
  have hdescent : baseEnd_2949092 < baseStart_2949092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949149 : List Nat := [1, 4, 2, 2, 2, 3, 2, 2, 5]
def baseStart_2949149 : Nat := 118140960795 + 2949149 * 2 ^ 59
def prefixEnd_2949149 : Nat := 4983230072969 + 3 ^ 40 * 2949149 * 2
def baseEnd_2949149 : Nat := 168258995414065241630513

theorem tailTrace_2949149 : CollatzResearch.WordTrace tailWord_2949149 prefixEnd_2949149 168258995414065241630513 := by
  unfold tailWord_2949149
  simp only [CollatzResearch.WordTrace]
  refine ⟨107564300792744322394730501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71709533861829548263153667 107564300792744322394730501)
  ·
    refine ⟨20168306398639560449011969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107564300792744322394730501 20168306398639560449011969)
    ·
      refine ⟨15126229798979670336758977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20168306398639560449011969 15126229798979670336758977)
      ·
        refine ⟨11344672349234752752569233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15126229798979670336758977 11344672349234752752569233)
        ·
          refine ⟨8508504261926064564426925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11344672349234752752569233 8508504261926064564426925)
          ·
            refine ⟨3190689098222274211660097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8508504261926064564426925 3190689098222274211660097)
            ·
              refine ⟨2393016823666705658745073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3190689098222274211660097 2393016823666705658745073)
              ·
                refine ⟨1794762617750029244058805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2393016823666705658745073 1794762617750029244058805)
                ·
                  refine ⟨168258995414065241630513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1794762617750029244058805 168258995414065241630513)
                  ·
                    rfl

theorem cell23_2949149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_2949149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949149 prefixEnd_2949149 := by exact prefixLift 2949149
  have htrace : WordTrace (prefixWord ++ tailWord_2949149) baseStart_2949149 baseEnd_2949149 := by
    simpa [prefixWord, tailWord_2949149, baseEnd_2949149] using wordTrace_append hprefix tailTrace_2949149
  have hstable : (prefixWord ++ tailWord_2949149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949149).length < 2 ^ (prefixWord ++ tailWord_2949149).sum := by decide
  have hdescent : baseEnd_2949149 < baseStart_2949149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949182 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_2949182 : Nat := 118140960795 + 2949182 * 2 ^ 59
def prefixEnd_2949182 : Nat := 4983230072969 + 3 ^ 40 * 2949182 * 2
def baseEnd_2949182 : Nat := 1514347903588185545561965

theorem tailTrace_2949182 : CollatzResearch.WordTrace tailWord_2949182 prefixEnd_2949182 1514347903588185545561965 := by
  unfold tailWord_2949182
  simp only [CollatzResearch.WordTrace]
  refine ⟨13445688050203096128835225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71710336267749846020454533 13445688050203096128835225)
  ·
    refine ⟨10084266037652322096626419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13445688050203096128835225 10084266037652322096626419)
    ·
      refine ⟨15126399056478483144939629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10084266037652322096626419 15126399056478483144939629)
      ·
        refine ⟨5672399646179431179352361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15126399056478483144939629 5672399646179431179352361)
        ·
          refine ⟨4254299734634573384514271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5672399646179431179352361 4254299734634573384514271)
          ·
            refine ⟨6381449601951860076771407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4254299734634573384514271 6381449601951860076771407)
            ·
              refine ⟨9572174402927790115157111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6381449601951860076771407 9572174402927790115157111)
              ·
                refine ⟨14358261604391685172735667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9572174402927790115157111 14358261604391685172735667)
                ·
                  refine ⟨21537392406587527759103501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14358261604391685172735667 21537392406587527759103501)
                  ·
                    refine ⟨8076522152470322909663813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21537392406587527759103501 8076522152470322909663813)
                    ·
                      refine ⟨1514347903588185545561965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8076522152470322909663813 1514347903588185545561965)
                      ·
                        rfl

theorem cell23_2949182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_2949182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949182 prefixEnd_2949182 := by exact prefixLift 2949182
  have htrace : WordTrace (prefixWord ++ tailWord_2949182) baseStart_2949182 baseEnd_2949182 := by
    simpa [prefixWord, tailWord_2949182, baseEnd_2949182] using wordTrace_append hprefix tailTrace_2949182
  have hstable : (prefixWord ++ tailWord_2949182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949182).length < 2 ^ (prefixWord ++ tailWord_2949182).sum := by decide
  have hdescent : baseEnd_2949182 < baseStart_2949182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949205 : List Nat := [1, 3, 2, 2, 1, 3, 3, 2, 6]
def baseStart_2949205 : Nat := 118140960795 + 2949205 * 2 ^ 59
def prefixEnd_2949205 : Nat := 4983230072969 + 3 ^ 40 * 2949205 * 2
def baseEnd_2949205 : Nat := 168262190404804328397151

theorem tailTrace_2949205 : CollatzResearch.WordTrace tailWord_2949205 prefixEnd_2949205 168262190404804328397151 := by
  unfold tailWord_2949205
  simp only [CollatzResearch.WordTrace]
  refine ⟨107566343280541443958769069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71710895520360962639179379 107566343280541443958769069)
  ·
    refine ⟨40337378730203041484538401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107566343280541443958769069 40337378730203041484538401)
    ·
      refine ⟨30253034047652281113403801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40337378730203041484538401 30253034047652281113403801)
      ·
        refine ⟨22689775535739210835052851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30253034047652281113403801 22689775535739210835052851)
        ·
          refine ⟨34034663303608816252579277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22689775535739210835052851 34034663303608816252579277)
          ·
            refine ⟨12762998738853306094717229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34034663303608816252579277 12762998738853306094717229)
            ·
              refine ⟨4786124527069989785518961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12762998738853306094717229 4786124527069989785518961)
              ·
                refine ⟨3589593395302492339139221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4786124527069989785518961 3589593395302492339139221)
                ·
                  refine ⟨168262190404804328397151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3589593395302492339139221 168262190404804328397151)
                  ·
                    rfl

theorem cell23_2949205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 6].length) (baseStart_2949205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949205 prefixEnd_2949205 := by exact prefixLift 2949205
  have htrace : WordTrace (prefixWord ++ tailWord_2949205) baseStart_2949205 baseEnd_2949205 := by
    simpa [prefixWord, tailWord_2949205, baseEnd_2949205] using wordTrace_append hprefix tailTrace_2949205
  have hstable : (prefixWord ++ tailWord_2949205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949205).length < 2 ^ (prefixWord ++ tailWord_2949205).sum := by decide
  have hdescent : baseEnd_2949205 < baseStart_2949205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949208 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 1, 2, 6]
def baseStart_2949208 : Nat := 118140960795 + 2949208 * 2 ^ 59
def prefixEnd_2949208 : Nat := 4983230072969 + 3 ^ 40 * 2949208 * 2
def baseEnd_2949208 : Nat := 1514361254085202443836845

theorem tailTrace_2949208 : CollatzResearch.WordTrace tailWord_2949208 prefixEnd_2949208 1514361254085202443836845 := by
  unfold tailWord_2949208
  simp only [CollatzResearch.WordTrace]
  refine ⟨53783226349765287735564139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71710968466353716980752185 53783226349765287735564139)
  ·
    refine ⟨80674839524647931603346209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53783226349765287735564139 80674839524647931603346209)
    ·
      refine ⟨60506129643485948702509657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80674839524647931603346209 60506129643485948702509657)
      ·
        refine ⟨45379597232614461526882243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60506129643485948702509657 45379597232614461526882243)
        ·
          refine ⟨68069395848921692290323365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45379597232614461526882243 68069395848921692290323365)
          ·
            refine ⟨12763011721672817304435631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68069395848921692290323365 12763011721672817304435631)
            ·
              refine ⟨19144517582509225956653447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12763011721672817304435631 19144517582509225956653447)
              ·
                refine ⟨28716776373763838934980171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19144517582509225956653447 28716776373763838934980171)
                ·
                  refine ⟨43075164560645758402470257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28716776373763838934980171 43075164560645758402470257)
                  ·
                    refine ⟨32306373420484318801852693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43075164560645758402470257 32306373420484318801852693)
                    ·
                      refine ⟨1514361254085202443836845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32306373420484318801852693 1514361254085202443836845)
                      ·
                        rfl

theorem cell23_2949208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_2949208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949208 prefixEnd_2949208 := by exact prefixLift 2949208
  have htrace : WordTrace (prefixWord ++ tailWord_2949208) baseStart_2949208 baseEnd_2949208 := by
    simpa [prefixWord, tailWord_2949208, baseEnd_2949208] using wordTrace_append hprefix tailTrace_2949208
  have hstable : (prefixWord ++ tailWord_2949208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949208).length < 2 ^ (prefixWord ++ tailWord_2949208).sum := by decide
  have hdescent : baseEnd_2949208 < baseStart_2949208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949225 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 3, 5, 2]
def baseStart_2949225 : Nat := 118140960795 + 2949225 * 2 ^ 59
def prefixEnd_2949225 : Nat := 4983230072969 + 3 ^ 40 * 2949225 * 2
def baseEnd_2949225 : Nat := 1514369983256328877324267

theorem tailTrace_2949225 : CollatzResearch.WordTrace tailWord_2949225 prefixEnd_2949225 1514369983256328877324267 := by
  unfold tailWord_2949225
  simp only [CollatzResearch.WordTrace]
  refine ⟨107567072740468987374497129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71711381826979324916331419 107567072740468987374497129)
  ·
    refine ⟨80675304555351740530872847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107567072740468987374497129 80675304555351740530872847)
    ·
      refine ⟨121012956833027610796309271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80675304555351740530872847 121012956833027610796309271)
      ·
        refine ⟨181519435249541416194463907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121012956833027610796309271 181519435249541416194463907)
        ·
          refine ⟨272279152874312124291695861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181519435249541416194463907 272279152874312124291695861)
          ·
            refine ⟨25526170581966761652346487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 272279152874312124291695861 25526170581966761652346487)
            ·
              refine ⟨38289255872950142478519731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25526170581966761652346487 38289255872950142478519731)
              ·
                refine ⟨57433883809425213717779597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38289255872950142478519731 57433883809425213717779597)
                ·
                  refine ⟨21537706428534455144167349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57433883809425213717779597 21537706428534455144167349)
                  ·
                    refine ⟨2019159977675105169765689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21537706428534455144167349 2019159977675105169765689)
                    ·
                      refine ⟨1514369983256328877324267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2019159977675105169765689 1514369983256328877324267)
                      ·
                        rfl

theorem cell23_2949225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 5, 2].length) (baseStart_2949225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949225 prefixEnd_2949225 := by exact prefixLift 2949225
  have htrace : WordTrace (prefixWord ++ tailWord_2949225) baseStart_2949225 baseEnd_2949225 := by
    simpa [prefixWord, tailWord_2949225, baseEnd_2949225] using wordTrace_append hprefix tailTrace_2949225
  have hstable : (prefixWord ++ tailWord_2949225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949225).length < 2 ^ (prefixWord ++ tailWord_2949225).sum := by decide
  have hdescent : baseEnd_2949225 < baseStart_2949225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949232 : List Nat := [2, 1, 1, 1, 5, 2, 2, 2, 3, 1, 3]
def baseStart_2949232 : Nat := 118140960795 + 2949232 * 2 ^ 59
def prefixEnd_2949232 : Nat := 4983230072969 + 3 ^ 40 * 2949232 * 2
def baseEnd_2949232 : Nat := 1514373577620910349936735

theorem tailTrace_2949232 : CollatzResearch.WordTrace tailWord_2949232 prefixEnd_2949232 1514373577620910349936735 := by
  unfold tailWord_2949232
  simp only [CollatzResearch.WordTrace]
  refine ⟨53783664025721813785000975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71711552034295751713334633 53783664025721813785000975)
  ·
    refine ⟨80675496038582720677501463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53783664025721813785000975 80675496038582720677501463)
    ·
      refine ⟨121013244057874081016252195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80675496038582720677501463 121013244057874081016252195)
      ·
        refine ⟨181519866086811121524378293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121013244057874081016252195 181519866086811121524378293)
        ·
          refine ⟨17017487445638542642910465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 181519866086811121524378293 17017487445638542642910465)
          ·
            refine ⟨12763115584228906982182849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17017487445638542642910465 12763115584228906982182849)
            ·
              refine ⟨9572336688171680236637137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12763115584228906982182849 9572336688171680236637137)
              ·
                refine ⟨7179252516128760177477853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9572336688171680236637137 7179252516128760177477853)
                ·
                  refine ⟨2692219693548285066554195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7179252516128760177477853 2692219693548285066554195)
                  ·
                    refine ⟨4038329540322427599831293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2692219693548285066554195 4038329540322427599831293)
                    ·
                      refine ⟨1514373577620910349936735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4038329540322427599831293 1514373577620910349936735)
                      ·
                        rfl

theorem cell23_2949232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 3, 1, 3].length) (baseStart_2949232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949232 prefixEnd_2949232 := by exact prefixLift 2949232
  have htrace : WordTrace (prefixWord ++ tailWord_2949232) baseStart_2949232 baseEnd_2949232 := by
    simpa [prefixWord, tailWord_2949232, baseEnd_2949232] using wordTrace_append hprefix tailTrace_2949232
  have hstable : (prefixWord ++ tailWord_2949232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949232).length < 2 ^ (prefixWord ++ tailWord_2949232).sum := by decide
  have hdescent : baseEnd_2949232 < baseStart_2949232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949248 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 3, 6]
def baseStart_2949248 : Nat := 118140960795 + 2949248 * 2 ^ 59
def prefixEnd_2949248 : Nat := 4983230072969 + 3 ^ 40 * 2949248 * 2
def baseEnd_2949248 : Nat := 504793931103794095778887

theorem tailTrace_2949248 : CollatzResearch.WordTrace tailWord_2949248 prefixEnd_2949248 504793931103794095778887 := by
  unfold tailWord_2949248
  simp only [CollatzResearch.WordTrace]
  refine ⟨53783955809692831151292199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71711941079590441535056265 53783955809692831151292199)
  ·
    refine ⟨80675933714539246726938299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53783955809692831151292199 80675933714539246726938299)
    ·
      refine ⟨121013900571808870090407449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80675933714539246726938299 121013900571808870090407449)
      ·
        refine ⟨90760425428856652567805587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121013900571808870090407449 90760425428856652567805587)
        ·
          refine ⟨136140638143284978851708381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90760425428856652567805587 136140638143284978851708381)
          ·
            refine ⟨51052739303731867069390643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136140638143284978851708381 51052739303731867069390643)
            ·
              refine ⟨76579108955597800604085965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51052739303731867069390643 76579108955597800604085965)
              ·
                refine ⟨28717165858349175226532237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76579108955597800604085965 28717165858349175226532237)
                ·
                  refine ⟨10768937196880940709949589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28717165858349175226532237 10768937196880940709949589)
                  ·
                    refine ⟨504793931103794095778887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10768937196880940709949589 504793931103794095778887)
                    ·
                      rfl

theorem cell23_2949248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 3, 6].length) (baseStart_2949248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949248 prefixEnd_2949248 := by exact prefixLift 2949248
  have htrace : WordTrace (prefixWord ++ tailWord_2949248) baseStart_2949248 baseEnd_2949248 := by
    simpa [prefixWord, tailWord_2949248, baseEnd_2949248] using wordTrace_append hprefix tailTrace_2949248
  have hstable : (prefixWord ++ tailWord_2949248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949248).length < 2 ^ (prefixWord ++ tailWord_2949248).sum := by decide
  have hdescent : baseEnd_2949248 < baseStart_2949248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949285 : List Nat := [1, 3, 1, 2, 1, 3, 2, 3, 1, 2, 4]
def baseStart_2949285 : Nat := 118140960795 + 2949285 * 2 ^ 59
def prefixEnd_2949285 : Nat := 4983230072969 + 3 ^ 40 * 2949285 * 2
def baseEnd_2949285 : Nat := 1514400792095598642573991

theorem tailTrace_2949285 : CollatzResearch.WordTrace tailWord_2949285 prefixEnd_2949285 1514400792095598642573991 := by
  unfold tailWord_2949285
  simp only [CollatzResearch.WordTrace]
  refine ⟨107569261120251617621681309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71712840746834411747787539 107569261120251617621681309)
  ·
    refine ⟨40338472920094356608130491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107569261120251617621681309 40338472920094356608130491)
    ·
      refine ⟨60507709380141534912195737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40338472920094356608130491 60507709380141534912195737)
      ·
        refine ⟨45380782035106151184146803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60507709380141534912195737 45380782035106151184146803)
        ·
          refine ⟨68071173052659226776220205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45380782035106151184146803 68071173052659226776220205)
          ·
            refine ⟨25526689894747210041082577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68071173052659226776220205 25526689894747210041082577)
            ·
              refine ⟨19145017421060407530811933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25526689894747210041082577 19145017421060407530811933)
              ·
                refine ⟨7179381532897652824054475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19145017421060407530811933 7179381532897652824054475)
                ·
                  refine ⟨10769072299346479236081713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7179381532897652824054475 10769072299346479236081713)
                  ·
                    refine ⟨8076804224509859427061285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10769072299346479236081713 8076804224509859427061285)
                    ·
                      refine ⟨1514400792095598642573991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8076804224509859427061285 1514400792095598642573991)
                      ·
                        rfl

theorem cell23_2949285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_2949285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949285 prefixEnd_2949285 := by exact prefixLift 2949285
  have htrace : WordTrace (prefixWord ++ tailWord_2949285) baseStart_2949285 baseEnd_2949285 := by
    simpa [prefixWord, tailWord_2949285, baseEnd_2949285] using wordTrace_append hprefix tailTrace_2949285
  have hstable : (prefixWord ++ tailWord_2949285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949285).length < 2 ^ (prefixWord ++ tailWord_2949285).sum := by decide
  have hdescent : baseEnd_2949285 < baseStart_2949285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949345 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_2949345 : Nat := 118140960795 + 2949345 * 2 ^ 59
def prefixEnd_2949345 : Nat := 4983230072969 + 3 ^ 40 * 2949345 * 2
def baseEnd_2949345 : Nat := 1514431600934868407823715

theorem tailTrace_2949345 : CollatzResearch.WordTrace tailWord_2949345 prefixEnd_2949345 1514431600934868407823715 := by
  unfold tailWord_2949345
  simp only [CollatzResearch.WordTrace]
  refine ⟨107571449500034247868865489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71714299666689498579243659 107571449500034247868865489)
  ·
    refine ⟨80678587125025685901649117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107571449500034247868865489 80678587125025685901649117)
    ·
      refine ⟨30254470171884632213118419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80678587125025685901649117 30254470171884632213118419)
      ·
        refine ⟨45381705257826948319677629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30254470171884632213118419 45381705257826948319677629)
        ·
          refine ⟨17018139471685105619879111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45381705257826948319677629 17018139471685105619879111)
          ·
            refine ⟨25527209207527658429818667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17018139471685105619879111 25527209207527658429818667)
            ·
              refine ⟨38290813811291487644728001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25527209207527658429818667 38290813811291487644728001)
              ·
                refine ⟨28718110358468615733546001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38290813811291487644728001 28718110358468615733546001)
                ·
                  refine ⟨21538582768851461800159501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28718110358468615733546001 21538582768851461800159501)
                  ·
                    refine ⟨8076968538319298175059813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21538582768851461800159501 8076968538319298175059813)
                    ·
                      refine ⟨1514431600934868407823715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8076968538319298175059813 1514431600934868407823715)
                      ·
                        rfl

theorem cell23_2949345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_2949345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949345 prefixEnd_2949345 := by exact prefixLift 2949345
  have htrace : WordTrace (prefixWord ++ tailWord_2949345) baseStart_2949345 baseEnd_2949345 := by
    simpa [prefixWord, tailWord_2949345, baseEnd_2949345] using wordTrace_append hprefix tailTrace_2949345
  have hstable : (prefixWord ++ tailWord_2949345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949345).length < 2 ^ (prefixWord ++ tailWord_2949345).sum := by decide
  have hdescent : baseEnd_2949345 < baseStart_2949345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949349 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 3, 3, 2]
def baseStart_2949349 : Nat := 118140960795 + 2949349 * 2 ^ 59
def prefixEnd_2949349 : Nat := 4983230072969 + 3 ^ 40 * 2949349 * 2
def baseEnd_2949349 : Nat := 1514433654857486392173697

theorem tailTrace_2949349 : CollatzResearch.WordTrace tailWord_2949349 prefixEnd_2949349 1514433654857486392173697 := by
  unfold tailWord_2949349
  simp only [CollatzResearch.WordTrace]
  refine ⟨107571595392019756552011101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71714396928013171034674067 107571595392019756552011101)
  ·
    refine ⟨40339348272007408707004163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107571595392019756552011101 40339348272007408707004163)
    ·
      refine ⟨60509022408011113060506245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40339348272007408707004163 60509022408011113060506245)
      ·
        refine ⟨11345441701502083698844921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60509022408011113060506245 11345441701502083698844921)
        ·
          refine ⟨8509081276126562774133691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11345441701502083698844921 8509081276126562774133691)
          ·
            refine ⟨12763621914189844161200537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8509081276126562774133691 12763621914189844161200537)
            ·
              refine ⟨9572716435642383120900403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12763621914189844161200537 9572716435642383120900403)
              ·
                refine ⟨14359074653463574681350605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9572716435642383120900403 14359074653463574681350605)
                ·
                  refine ⟨5384652995048840505506477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14359074653463574681350605 5384652995048840505506477)
                  ·
                    refine ⟨2019244873143315189564929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5384652995048840505506477 2019244873143315189564929)
                    ·
                      refine ⟨1514433654857486392173697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2019244873143315189564929 1514433654857486392173697)
                      ·
                        rfl

theorem cell23_2949349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_2949349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949349 prefixEnd_2949349 := by exact prefixLift 2949349
  have htrace : WordTrace (prefixWord ++ tailWord_2949349) baseStart_2949349 baseEnd_2949349 := by
    simpa [prefixWord, tailWord_2949349, baseEnd_2949349] using wordTrace_append hprefix tailTrace_2949349
  have hstable : (prefixWord ++ tailWord_2949349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949349).length < 2 ^ (prefixWord ++ tailWord_2949349).sum := by decide
  have hdescent : baseEnd_2949349 < baseStart_2949349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949375 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 4]
def baseStart_2949375 : Nat := 118140960795 + 2949375 * 2 ^ 59
def prefixEnd_2949375 : Nat := 4983230072969 + 3 ^ 40 * 2949375 * 2
def baseEnd_2949375 : Nat := 1514447005354503290448577

theorem tailTrace_2949375 : CollatzResearch.WordTrace tailWord_2949375 prefixEnd_2949375 1514447005354503290448577 := by
  unfold tailWord_2949375
  simp only [CollatzResearch.WordTrace]
  refine ⟨107572543689925562992457579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71715029126617041994971719 107572543689925562992457579)
  ·
    refine ⟨161358815534888344488686369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107572543689925562992457579 161358815534888344488686369)
    ·
      refine ⟨121019111651166258366514777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161358815534888344488686369 121019111651166258366514777)
      ·
        refine ⟨90764333738374693774886083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121019111651166258366514777 90764333738374693774886083)
        ·
          refine ⟨136146500607562040662329125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90764333738374693774886083 136146500607562040662329125)
          ·
            refine ⟨25527468863917882624186711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136146500607562040662329125 25527468863917882624186711)
            ·
              refine ⟨38291203295876823936280067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25527468863917882624186711 38291203295876823936280067)
              ·
                refine ⟨57436804943815235904420101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38291203295876823936280067 57436804943815235904420101)
                ·
                  refine ⟨10769400926965356732078769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57436804943815235904420101 10769400926965356732078769)
                  ·
                    refine ⟨8077050695224017549059077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10769400926965356732078769 8077050695224017549059077)
                    ·
                      refine ⟨1514447005354503290448577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8077050695224017549059077 1514447005354503290448577)
                      ·
                        rfl

theorem cell23_2949375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_2949375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949375 prefixEnd_2949375 := by exact prefixLift 2949375
  have htrace : WordTrace (prefixWord ++ tailWord_2949375) baseStart_2949375 baseEnd_2949375 := by
    simpa [prefixWord, tailWord_2949375, baseEnd_2949375] using wordTrace_append hprefix tailTrace_2949375
  have hstable : (prefixWord ++ tailWord_2949375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949375).length < 2 ^ (prefixWord ++ tailWord_2949375).sum := by decide
  have hdescent : baseEnd_2949375 < baseStart_2949375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949379 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 4, 2, 2]
def baseStart_2949379 : Nat := 118140960795 + 2949379 * 2 ^ 59
def prefixEnd_2949379 : Nat := 4983230072969 + 3 ^ 40 * 2949379 * 2
def baseEnd_2949379 : Nat := 1514449059277121274798559

theorem tailTrace_2949379 : CollatzResearch.WordTrace tailWord_2949379 prefixEnd_2949379 1514449059277121274798559 := by
  unfold tailWord_2949379
  simp only [CollatzResearch.WordTrace]
  refine ⟨107572689581911071675603191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71715126387940714450402127 107572689581911071675603191)
  ·
    refine ⟨161359034372866607513404787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107572689581911071675603191 161359034372866607513404787)
    ·
      refine ⟨242038551559299911270107181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161359034372866607513404787 242038551559299911270107181)
      ·
        refine ⟨90764456834737466726290193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242038551559299911270107181 90764456834737466726290193)
        ·
          refine ⟨68073342626053100044717645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90764456834737466726290193 68073342626053100044717645)
          ·
            refine ⟨25527503484769912516769117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68073342626053100044717645 25527503484769912516769117)
            ·
              refine ⟨9572813806788717193788419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25527503484769912516769117 9572813806788717193788419)
              ·
                refine ⟨14359220710183075790682629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9572813806788717193788419 14359220710183075790682629)
                ·
                  refine ⟨2692353883159326710752993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14359220710183075790682629 2692353883159326710752993)
                  ·
                    refine ⟨2019265412369495033064745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2692353883159326710752993 2019265412369495033064745)
                    ·
                      refine ⟨1514449059277121274798559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2019265412369495033064745 1514449059277121274798559)
                      ·
                        rfl

theorem cell23_2949379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 2, 2].length) (baseStart_2949379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949379 prefixEnd_2949379 := by exact prefixLift 2949379
  have htrace : WordTrace (prefixWord ++ tailWord_2949379) baseStart_2949379 baseEnd_2949379 := by
    simpa [prefixWord, tailWord_2949379, baseEnd_2949379] using wordTrace_append hprefix tailTrace_2949379
  have hstable : (prefixWord ++ tailWord_2949379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949379).length < 2 ^ (prefixWord ++ tailWord_2949379).sum := by decide
  have hdescent : baseEnd_2949379 < baseStart_2949379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949385 : List Nat := [1, 2, 1, 1, 3, 4, 1, 3, 7]
def baseStart_2949385 : Nat := 118140960795 + 2949385 * 2 ^ 59
def prefixEnd_2949385 : Nat := 4983230072969 + 3 ^ 40 * 2949385 * 2
def baseEnd_2949385 : Nat := 168272460017894250147059

theorem tailTrace_2949385 : CollatzResearch.WordTrace tailWord_2949385 prefixEnd_2949385 168272460017894250147059 := by
  unfold tailWord_2949385
  simp only [CollatzResearch.WordTrace]
  refine ⟨107572908419889334700321609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71715272279926223133547739 107572908419889334700321609)
  ·
    refine ⟨80679681314917001025241207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107572908419889334700321609 80679681314917001025241207)
    ·
      refine ⟨121019521972375501537861811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80679681314917001025241207 121019521972375501537861811)
      ·
        refine ⟨181529282958563252306792717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121019521972375501537861811 181529282958563252306792717)
        ·
          refine ⟨68073481109461219615047269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181529282958563252306792717 68073481109461219615047269)
          ·
            refine ⟨12763777708023978677821363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68073481109461219615047269 12763777708023978677821363)
            ·
              refine ⟨19145666562035968016732045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12763777708023978677821363 19145666562035968016732045)
              ·
                refine ⟨7179624960763488006274517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19145666562035968016732045 7179624960763488006274517)
                ·
                  refine ⟨168272460017894250147059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7179624960763488006274517 168272460017894250147059)
                  ·
                    rfl

theorem cell23_2949385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 7].length) (baseStart_2949385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949385 prefixEnd_2949385 := by exact prefixLift 2949385
  have htrace : WordTrace (prefixWord ++ tailWord_2949385) baseStart_2949385 baseEnd_2949385 := by
    simpa [prefixWord, tailWord_2949385, baseEnd_2949385] using wordTrace_append hprefix tailTrace_2949385
  have hstable : (prefixWord ++ tailWord_2949385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949385).length < 2 ^ (prefixWord ++ tailWord_2949385).sum := by decide
  have hdescent : baseEnd_2949385 < baseStart_2949385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949452 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 4, 1, 4]
def baseStart_2949452 : Nat := 118140960795 + 2949452 * 2 ^ 59
def prefixEnd_2949452 : Nat := 4983230072969 + 3 ^ 40 * 2949452 * 2
def baseEnd_2949452 : Nat := 1514486543364899489185723

theorem tailTrace_2949452 : CollatzResearch.WordTrace tailWord_2949452 prefixEnd_2949452 1514486543364899489185723 := by
  unfold tailWord_2949452
  simp only [CollatzResearch.WordTrace]
  refine ⟨53787676055323302571505305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71716901407097736762007073 53787676055323302571505305)
  ·
    refine ⟨40340757041492476928628979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53787676055323302571505305 40340757041492476928628979)
    ·
      refine ⟨60511135562238715392943469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40340757041492476928628979 60511135562238715392943469)
      ·
        refine ⟨22691675835839518272353801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60511135562238715392943469 22691675835839518272353801)
        ·
          refine ⟨17018756876879638704265351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22691675835839518272353801 17018756876879638704265351)
          ·
            refine ⟨25528135315319458056398027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17018756876879638704265351 25528135315319458056398027)
            ·
              refine ⟨38292202972979187084597041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25528135315319458056398027 38292202972979187084597041)
              ·
                refine ⟨28719152229734390313447781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38292202972979187084597041 28719152229734390313447781)
                ·
                  refine ⟨5384841043075198183771459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28719152229734390313447781 5384841043075198183771459)
                  ·
                    refine ⟨8077261564612797275657189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5384841043075198183771459 8077261564612797275657189)
                    ·
                      refine ⟨1514486543364899489185723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8077261564612797275657189 1514486543364899489185723)
                      ·
                        rfl

theorem cell23_2949452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_2949452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949452 prefixEnd_2949452 := by exact prefixLift 2949452
  have htrace : WordTrace (prefixWord ++ tailWord_2949452) baseStart_2949452 baseEnd_2949452 := by
    simpa [prefixWord, tailWord_2949452, baseEnd_2949452] using wordTrace_append hprefix tailTrace_2949452
  have hstable : (prefixWord ++ tailWord_2949452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949452).length < 2 ^ (prefixWord ++ tailWord_2949452).sum := by decide
  have hdescent : baseEnd_2949452 < baseStart_2949452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949465 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 1, 3, 6]
def baseStart_2949465 : Nat := 118140960795 + 2949465 * 2 ^ 59
def prefixEnd_2949465 : Nat := 4983230072969 + 3 ^ 40 * 2949465 * 2
def baseEnd_2949465 : Nat := 1514493218613407938323163

theorem tailTrace_2949465 : CollatzResearch.WordTrace tailWord_2949465 prefixEnd_2949465 1514493218613407938323163 := by
  unfold tailWord_2949465
  simp only [CollatzResearch.WordTrace]
  refine ⟨107575826259599508363233849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71717217506399672242155899 107575826259599508363233849)
  ·
    refine ⟨80681869694699631272425387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107575826259599508363233849 80681869694699631272425387)
    ·
      refine ⟨121022804542049446908638081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80681869694699631272425387 121022804542049446908638081)
      ·
        refine ⟨90767103406537085181478561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121022804542049446908638081 90767103406537085181478561)
        ·
          refine ⟨68075327554902813886108921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90767103406537085181478561 68075327554902813886108921)
          ·
            refine ⟨51056495666177110414581691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68075327554902813886108921 51056495666177110414581691)
            ·
              refine ⟨76584743499265665621872537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51056495666177110414581691 76584743499265665621872537)
              ·
                refine ⟨57438557624449249216404403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76584743499265665621872537 57438557624449249216404403)
                ·
                  refine ⟨86157836436673873824606605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57438557624449249216404403 86157836436673873824606605)
                  ·
                    refine ⟨32309188663752702684227477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86157836436673873824606605 32309188663752702684227477)
                    ·
                      refine ⟨1514493218613407938323163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32309188663752702684227477 1514493218613407938323163)
                      ·
                        rfl

theorem cell23_2949465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_2949465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949465 prefixEnd_2949465 := by exact prefixLift 2949465
  have htrace : WordTrace (prefixWord ++ tailWord_2949465) baseStart_2949465 baseEnd_2949465 := by
    simpa [prefixWord, tailWord_2949465, baseEnd_2949465] using wordTrace_append hprefix tailTrace_2949465
  have hstable : (prefixWord ++ tailWord_2949465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949465).length < 2 ^ (prefixWord ++ tailWord_2949465).sum := by decide
  have hdescent : baseEnd_2949465 < baseStart_2949465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949529 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 1, 5, 2]
def baseStart_2949529 : Nat := 118140960795 + 2949529 * 2 ^ 59
def prefixEnd_2949529 : Nat := 4983230072969 + 3 ^ 40 * 2949529 * 2
def baseEnd_2949529 : Nat := 1514526081375295687922869

theorem tailTrace_2949529 : CollatzResearch.WordTrace tailWord_2949529 prefixEnd_2949529 1514526081375295687922869 := by
  unfold tailWord_2949529
  simp only [CollatzResearch.WordTrace]
  refine ⟨107578160531367647293563641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71718773687578431529042427 107578160531367647293563641)
  ·
    refine ⟨80683620398525735470172731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107578160531367647293563641 80683620398525735470172731)
    ·
      refine ⟨121025430597788603205259097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80683620398525735470172731 121025430597788603205259097)
      ·
        refine ⟨90769072948341452403944323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121025430597788603205259097 90769072948341452403944323)
        ·
          refine ⟨136153609422512178605916485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90769072948341452403944323 136153609422512178605916485)
          ·
            refine ⟨25528801766721033488609341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136153609422512178605916485 25528801766721033488609341)
            ·
              refine ⟨9573300662520387558228503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25528801766721033488609341 9573300662520387558228503)
              ·
                refine ⟨14359950993780581337342755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9573300662520387558228503 14359950993780581337342755)
                ·
                  refine ⟨21539926490670872006014133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14359950993780581337342755 21539926490670872006014133)
                  ·
                    refine ⟨2019368108500394250563825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21539926490670872006014133 2019368108500394250563825)
                    ·
                      refine ⟨1514526081375295687922869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2019368108500394250563825 1514526081375295687922869)
                      ·
                        rfl

theorem cell23_2949529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 5, 2].length) (baseStart_2949529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949529 prefixEnd_2949529 := by exact prefixLift 2949529
  have htrace : WordTrace (prefixWord ++ tailWord_2949529) baseStart_2949529 baseEnd_2949529 := by
    simpa [prefixWord, tailWord_2949529, baseEnd_2949529] using wordTrace_append hprefix tailTrace_2949529
  have hstable : (prefixWord ++ tailWord_2949529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949529).length < 2 ^ (prefixWord ++ tailWord_2949529).sum := by decide
  have hdescent : baseEnd_2949529 < baseStart_2949529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949539 : List Nat := [1, 1, 1, 4, 1, 5, 1, 3, 1, 5]
def baseStart_2949539 : Nat := 118140960795 + 2949539 * 2 ^ 59
def prefixEnd_2949539 : Nat := 4983230072969 + 3 ^ 40 * 2949539 * 2
def baseEnd_2949539 : Nat := 504843738727280216265941

theorem tailTrace_2949539 : CollatzResearch.WordTrace tailWord_2949539 prefixEnd_2949539 504843738727280216265941 := by
  unfold tailWord_2949539
  simp only [CollatzResearch.WordTrace]
  refine ⟨107578525261331419001427671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71719016840887612667618447 107578525261331419001427671)
  ·
    refine ⟨161367787891997128502141507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107578525261331419001427671 161367787891997128502141507)
    ·
      refine ⟨242051681837995692753212261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161367787891997128502141507 242051681837995692753212261)
      ·
        refine ⟨45384690344624192391227299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242051681837995692753212261 45384690344624192391227299)
        ·
          refine ⟨68077035516936288586840949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45384690344624192391227299 68077035516936288586840949)
          ·
            refine ⟨6382222079712777055016339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68077035516936288586840949 6382222079712777055016339)
            ·
              refine ⟨9573333119569165582524509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6382222079712777055016339 9573333119569165582524509)
              ·
                refine ⟨3589999919838437093446691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9573333119569165582524509 3589999919838437093446691)
                ·
                  refine ⟨5384999879757655640170037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3589999919838437093446691 5384999879757655640170037)
                  ·
                    refine ⟨504843738727280216265941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5384999879757655640170037 504843738727280216265941)
                    ·
                      rfl

theorem cell23_2949539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 5].length) (baseStart_2949539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949539 prefixEnd_2949539 := by exact prefixLift 2949539
  have htrace : WordTrace (prefixWord ++ tailWord_2949539) baseStart_2949539 baseEnd_2949539 := by
    simpa [prefixWord, tailWord_2949539, baseEnd_2949539] using wordTrace_append hprefix tailTrace_2949539
  have hstable : (prefixWord ++ tailWord_2949539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949539).length < 2 ^ (prefixWord ++ tailWord_2949539).sum := by decide
  have hdescent : baseEnd_2949539 < baseStart_2949539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949553 : List Nat := [1, 2, 2, 4, 1, 2, 2, 4, 1, 1, 3]
def baseStart_2949553 : Nat := 118140960795 + 2949553 * 2 ^ 59
def prefixEnd_2949553 : Nat := 4983230072969 + 3 ^ 40 * 2949553 * 2
def baseEnd_2949553 : Nat := 1514538404911003594022759

theorem tailTrace_2949553 : CollatzResearch.WordTrace tailWord_2949553 prefixEnd_2949553 1514538404911003594022759 := by
  unfold tailWord_2949553
  simp only [CollatzResearch.WordTrace]
  refine ⟨107579035883280699392437313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71719357255520466261624875 107579035883280699392437313)
  ·
    refine ⟨80684276912460524544327985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107579035883280699392437313 80684276912460524544327985)
    ·
      refine ⟨60513207684345393408245989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80684276912460524544327985 60513207684345393408245989)
      ·
        refine ⟨11346226440814761264046123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60513207684345393408245989 11346226440814761264046123)
        ·
          refine ⟨17019339661222141896069185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11346226440814761264046123 17019339661222141896069185)
          ·
            refine ⟨12764504745916606422051889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17019339661222141896069185 12764504745916606422051889)
            ·
              refine ⟨9573378559437454816538917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12764504745916606422051889 9573378559437454816538917)
              ·
                refine ⟨1795008479894522778101047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9573378559437454816538917 1795008479894522778101047)
                ·
                  refine ⟨2692512719841784167151571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1795008479894522778101047 2692512719841784167151571)
                  ·
                    refine ⟨4038769079762676250727357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2692512719841784167151571 4038769079762676250727357)
                    ·
                      refine ⟨1514538404911003594022759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4038769079762676250727357 1514538404911003594022759)
                      ·
                        rfl

theorem cell23_2949553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_2949553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949553 prefixEnd_2949553 := by exact prefixLift 2949553
  have htrace : WordTrace (prefixWord ++ tailWord_2949553) baseStart_2949553 baseEnd_2949553 := by
    simpa [prefixWord, tailWord_2949553, baseEnd_2949553] using wordTrace_append hprefix tailTrace_2949553
  have hstable : (prefixWord ++ tailWord_2949553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949553).length < 2 ^ (prefixWord ++ tailWord_2949553).sum := by decide
  have hdescent : baseEnd_2949553 < baseStart_2949553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949576 : List Nat := [2, 1, 3, 1, 3, 3, 2, 2, 1, 1, 4]
def baseStart_2949576 : Nat := 118140960795 + 2949576 * 2 ^ 59
def prefixEnd_2949576 : Nat := 4983230072969 + 3 ^ 40 * 2949576 * 2
def baseEnd_2949576 : Nat := 1514550214966057004035153

theorem tailTrace_2949576 : CollatzResearch.WordTrace tailWord_2949576 prefixEnd_2949576 1514550214966057004035153 := by
  unfold tailWord_2949576
  simp only [CollatzResearch.WordTrace]
  refine ⟨53789937381098687160262291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71719916508131582880349721 53789937381098687160262291)
  ·
    refine ⟨80684906071648030740393437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53789937381098687160262291 80684906071648030740393437)
    ·
      refine ⟨30256839776868011527647539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80684906071648030740393437 30256839776868011527647539)
      ·
        refine ⟨45385259665302017291471309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30256839776868011527647539 45385259665302017291471309)
        ·
          refine ⟨17019472374488256484301741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45385259665302017291471309 17019472374488256484301741)
          ·
            refine ⟨6382302140433096181613153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17019472374488256484301741 6382302140433096181613153)
            ·
              refine ⟨4786726605324822136209865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6382302140433096181613153 4786726605324822136209865)
              ·
                refine ⟨3590044953993616602157399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4786726605324822136209865 3590044953993616602157399)
                ·
                  refine ⟨5385067430990424903236099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3590044953993616602157399 5385067430990424903236099)
                  ·
                    refine ⟨8077601146485637354854149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5385067430990424903236099 8077601146485637354854149)
                    ·
                      refine ⟨1514550214966057004035153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8077601146485637354854149 1514550214966057004035153)
                      ·
                        rfl

theorem cell23_2949576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_2949576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949576 prefixEnd_2949576 := by exact prefixLift 2949576
  have htrace : WordTrace (prefixWord ++ tailWord_2949576) baseStart_2949576 baseEnd_2949576 := by
    simpa [prefixWord, tailWord_2949576, baseEnd_2949576] using wordTrace_append hprefix tailTrace_2949576
  have hstable : (prefixWord ++ tailWord_2949576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949576).length < 2 ^ (prefixWord ++ tailWord_2949576).sum := by decide
  have hdescent : baseEnd_2949576 < baseStart_2949576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949610 : List Nat := [3, 1, 3, 1, 3, 3, 1, 1, 3, 2, 2]
def baseStart_2949610 : Nat := 118140960795 + 2949610 * 2 ^ 59
def prefixEnd_2949610 : Nat := 4983230072969 + 3 ^ 40 * 2949610 * 2
def baseEnd_2949610 : Nat := 1514567673308309871009997

theorem tailTrace_2949610 : CollatzResearch.WordTrace tailWord_2949610 prefixEnd_2949610 1514567673308309871009997 := by
  unfold tailWord_2949610
  simp only [CollatzResearch.WordTrace]
  refine ⟨26895278711018549531815571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71720743229382798751508189 26895278711018549531815571)
  ·
    refine ⟨40342918066527824297723357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26895278711018549531815571 40342918066527824297723357)
    ·
      refine ⟨15128594274947934111646259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40342918066527824297723357 15128594274947934111646259)
      ·
        refine ⟨22692891412421901167469389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15128594274947934111646259 22692891412421901167469389)
        ·
          refine ⟨8509834279658212937801021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22692891412421901167469389 8509834279658212937801021)
          ·
            refine ⟨3191187854871829851675383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8509834279658212937801021 3191187854871829851675383)
            ·
              refine ⟨4786781782307744777513075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3191187854871829851675383 4786781782307744777513075)
              ·
                refine ⟨7180172673461617166269613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4786781782307744777513075 7180172673461617166269613)
                ·
                  refine ⟨2692564752548106437351105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7180172673461617166269613 2692564752548106437351105)
                  ·
                    refine ⟨2019423564411079828013329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2692564752548106437351105 2019423564411079828013329)
                    ·
                      refine ⟨1514567673308309871009997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2019423564411079828013329 1514567673308309871009997)
                      ·
                        rfl

theorem cell23_2949610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_2949610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949610 prefixEnd_2949610 := by exact prefixLift 2949610
  have htrace : WordTrace (prefixWord ++ tailWord_2949610) baseStart_2949610 baseEnd_2949610 := by
    simpa [prefixWord, tailWord_2949610, baseEnd_2949610] using wordTrace_append hprefix tailTrace_2949610
  have hstable : (prefixWord ++ tailWord_2949610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949610).length < 2 ^ (prefixWord ++ tailWord_2949610).sum := by decide
  have hdescent : baseEnd_2949610 < baseStart_2949610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949612 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 2, 7]
def baseStart_2949612 : Nat := 118140960795 + 2949612 * 2 ^ 59
def prefixEnd_2949612 : Nat := 4983230072969 + 3 ^ 40 * 2949612 * 2
def baseEnd_2949612 : Nat := 504856233423206287728329

theorem tailTrace_2949612 : CollatzResearch.WordTrace tailWord_2949612 prefixEnd_2949612 504856233423206287728329 := by
  unfold tailWord_2949612
  simp only [CollatzResearch.WordTrace]
  refine ⟨53790593895033476234417545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71720791860044634979223393 53790593895033476234417545)
  ·
    refine ⟨40342945421275107175813159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53790593895033476234417545 40342945421275107175813159)
    ·
      refine ⟨60514418131912660763719739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40342945421275107175813159 60514418131912660763719739)
      ·
        refine ⟨90771627197868991145579609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60514418131912660763719739 90771627197868991145579609)
        ·
          refine ⟨68078720398401743359184707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90771627197868991145579609 68078720398401743359184707)
          ·
            refine ⟨102118080597602615038777061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68078720398401743359184707 102118080597602615038777061)
            ·
              refine ⟨19147140112050490319770699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102118080597602615038777061 19147140112050490319770699)
              ·
                refine ⟨28720710168075735479656049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19147140112050490319770699 28720710168075735479656049)
                ·
                  refine ⟨21540532626056801609742037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28720710168075735479656049 21540532626056801609742037)
                  ·
                    refine ⟨504856233423206287728329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21540532626056801609742037 504856233423206287728329)
                    ·
                      rfl

theorem cell23_2949612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_2949612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949612 prefixEnd_2949612 := by exact prefixLift 2949612
  have htrace : WordTrace (prefixWord ++ tailWord_2949612) baseStart_2949612 baseEnd_2949612 := by
    simpa [prefixWord, tailWord_2949612, baseEnd_2949612] using wordTrace_append hprefix tailTrace_2949612
  have hstable : (prefixWord ++ tailWord_2949612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949612).length < 2 ^ (prefixWord ++ tailWord_2949612).sum := by decide
  have hdescent : baseEnd_2949612 < baseStart_2949612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949666 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 5, 4, 2]
def baseStart_2949666 : Nat := 118140960795 + 2949666 * 2 ^ 59
def prefixEnd_2949666 : Nat := 4983230072969 + 3 ^ 40 * 2949666 * 2
def baseEnd_2949666 : Nat := 1514596428224961651909739

theorem tailTrace_2949666 : CollatzResearch.WordTrace tailWord_2949666 prefixEnd_2949666 1514596428224961651909739 := by
  unfold tailWord_2949666
  simp only [CollatzResearch.WordTrace]
  refine ⟨26895789332967829922825213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71722104887914213127533901 26895789332967829922825213)
  ·
    refine ⟨10085920999862936221059455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26895789332967829922825213 10085920999862936221059455)
    ·
      refine ⟨15128881499794404331589183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10085920999862936221059455 15128881499794404331589183)
      ·
        refine ⟨22693322249691606497383775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15128881499794404331589183 22693322249691606497383775)
        ·
          refine ⟨34039983374537409746075663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22693322249691606497383775 34039983374537409746075663)
          ·
            refine ⟨51059975061806114619113495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34039983374537409746075663 51059975061806114619113495)
            ·
              refine ⟨76589962592709171928670243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51059975061806114619113495 76589962592709171928670243)
              ·
                refine ⟨114884943889063757893005365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76589962592709171928670243 114884943889063757893005365)
                ·
                  refine ⟨10770463489599727302469253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114884943889063757893005365 10770463489599727302469253)
                  ·
                    refine ⟨2019461904299948869212985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10770463489599727302469253 2019461904299948869212985)
                    ·
                      refine ⟨1514596428224961651909739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2019461904299948869212985 1514596428224961651909739)
                      ·
                        rfl

theorem cell23_2949666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_2949666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949666 prefixEnd_2949666 := by exact prefixLift 2949666
  have htrace : WordTrace (prefixWord ++ tailWord_2949666) baseStart_2949666 baseEnd_2949666 := by
    simpa [prefixWord, tailWord_2949666, baseEnd_2949666] using wordTrace_append hprefix tailTrace_2949666
  have hstable : (prefixWord ++ tailWord_2949666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949666).length < 2 ^ (prefixWord ++ tailWord_2949666).sum := by decide
  have hdescent : baseEnd_2949666 < baseStart_2949666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949669 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 2, 4, 3]
def baseStart_2949669 : Nat := 118140960795 + 2949669 * 2 ^ 59
def prefixEnd_2949669 : Nat := 4983230072969 + 3 ^ 40 * 2949669 * 2
def baseEnd_2949669 : Nat := 1514597968666925140172225

theorem tailTrace_2949669 : CollatzResearch.WordTrace tailWord_2949669 prefixEnd_2949669 1514597968666925140172225 := by
  unfold tailWord_2949669
  simp only [CollatzResearch.WordTrace]
  refine ⟨107583266750860451203660061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71722177833906967469106707 107583266750860451203660061)
  ·
    refine ⟨40343725031572669201372523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107583266750860451203660061 40343725031572669201372523)
    ·
      refine ⟨60515587547359003802058785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40343725031572669201372523 60515587547359003802058785)
      ·
        refine ⟨45386690660519252851544089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60515587547359003802058785 45386690660519252851544089)
        ·
          refine ⟨34040017995389439638658067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45386690660519252851544089 34040017995389439638658067)
          ·
            refine ⟨51060026993084159457987101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34040017995389439638658067 51060026993084159457987101)
            ·
              refine ⟨19147510122406559796745163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51060026993084159457987101 19147510122406559796745163)
              ·
                refine ⟨28721265183609839695117745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19147510122406559796745163 28721265183609839695117745)
                ·
                  refine ⟨21540948887707379771338309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28721265183609839695117745 21540948887707379771338309)
                  ·
                    refine ⟨4038927916445133707125933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21540948887707379771338309 4038927916445133707125933)
                    ·
                      refine ⟨1514597968666925140172225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4038927916445133707125933 1514597968666925140172225)
                      ·
                        rfl

theorem cell23_2949669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_2949669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949669 prefixEnd_2949669 := by exact prefixLift 2949669
  have htrace : WordTrace (prefixWord ++ tailWord_2949669) baseStart_2949669 baseEnd_2949669 := by
    simpa [prefixWord, tailWord_2949669, baseEnd_2949669] using wordTrace_append hprefix tailTrace_2949669
  have hstable : (prefixWord ++ tailWord_2949669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949669).length < 2 ^ (prefixWord ++ tailWord_2949669).sum := by decide
  have hdescent : baseEnd_2949669 < baseStart_2949669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949677 : List Nat := [1, 5, 4, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2949677 : Nat := 118140960795 + 2949677 * 2 ^ 59
def prefixEnd_2949677 : Nat := 4983230072969 + 3 ^ 40 * 2949677 * 2
def baseEnd_2949677 : Nat := 1514602076512161108872189

theorem tailTrace_2949677 : CollatzResearch.WordTrace tailWord_2949677 prefixEnd_2949677 1514602076512161108872189 := by
  unfold tailWord_2949677
  simp only [CollatzResearch.WordTrace]
  refine ⟨107583558534831468569951285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71722372356554312379967523 107583558534831468569951285)
  ·
    refine ⟨10085958612640450178432933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107583558534831468569951285 10085958612640450178432933)
    ·
      refine ⟨1891117239870084408456175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10085958612640450178432933 1891117239870084408456175)
      ·
        refine ⟨2836675859805126612684263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1891117239870084408456175 2836675859805126612684263)
        ·
          refine ⟨4255013789707689919026395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2836675859805126612684263 4255013789707689919026395)
          ·
            refine ⟨6382520684561534878539593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4255013789707689919026395 6382520684561534878539593)
            ·
              refine ⟨4786890513421151158904695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6382520684561534878539593 4786890513421151158904695)
              ·
                refine ⟨7180335770131726738357043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4786890513421151158904695 7180335770131726738357043)
                ·
                  refine ⟨10770503655197590107535565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7180335770131726738357043 10770503655197590107535565)
                  ·
                    refine ⟨4038938870699096290325837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10770503655197590107535565 4038938870699096290325837)
                    ·
                      refine ⟨1514602076512161108872189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4038938870699096290325837 1514602076512161108872189)
                      ·
                        rfl

theorem cell23_2949677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2949677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949677 prefixEnd_2949677 := by exact prefixLift 2949677
  have htrace : WordTrace (prefixWord ++ tailWord_2949677) baseStart_2949677 baseEnd_2949677 := by
    simpa [prefixWord, tailWord_2949677, baseEnd_2949677] using wordTrace_append hprefix tailTrace_2949677
  have hstable : (prefixWord ++ tailWord_2949677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949677).length < 2 ^ (prefixWord ++ tailWord_2949677).sum := by decide
  have hdescent : baseEnd_2949677 < baseStart_2949677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949683 : List Nat := [1, 1, 1, 2, 4, 2, 1, 5, 2, 2, 2]
def baseStart_2949683 : Nat := 118140960795 + 2949683 * 2 ^ 59
def prefixEnd_2949683 : Nat := 4983230072969 + 3 ^ 40 * 2949683 * 2
def baseEnd_2949683 : Nat := 1514605157396088085397161

theorem tailTrace_2949683 : CollatzResearch.WordTrace tailWord_2949683 prefixEnd_2949683 1514605157396088085397161 := by
  unfold tailWord_2949683
  simp only [CollatzResearch.WordTrace]
  refine ⟨107583777372809731594669703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71722518248539821063113135 107583777372809731594669703)
  ·
    refine ⟨161375666059214597392004555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107583777372809731594669703 161375666059214597392004555)
    ·
      refine ⟨242063499088821896088006833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161375666059214597392004555 242063499088821896088006833)
      ·
        refine ⟨181547624316616422066005125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242063499088821896088006833 181547624316616422066005125)
        ·
          refine ⟨34040179559365579137375961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181547624316616422066005125 34040179559365579137375961)
          ·
            refine ⟨25530134669524184353031971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34040179559365579137375961 25530134669524184353031971)
            ·
              refine ⟨38295202004286276529547957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25530134669524184353031971 38295202004286276529547957)
              ·
                refine ⟨3590175187901838424645121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38295202004286276529547957 3590175187901838424645121)
                ·
                  refine ⟨2692631390926378818483841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3590175187901838424645121 2692631390926378818483841)
                  ·
                    refine ⟨2019473543194784113862881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2692631390926378818483841 2019473543194784113862881)
                    ·
                      refine ⟨1514605157396088085397161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2019473543194784113862881 1514605157396088085397161)
                      ·
                        rfl

theorem cell23_2949683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 2, 2].length) (baseStart_2949683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949683 prefixEnd_2949683 := by exact prefixLift 2949683
  have htrace : WordTrace (prefixWord ++ tailWord_2949683) baseStart_2949683 baseEnd_2949683 := by
    simpa [prefixWord, tailWord_2949683, baseEnd_2949683] using wordTrace_append hprefix tailTrace_2949683
  have hstable : (prefixWord ++ tailWord_2949683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949683).length < 2 ^ (prefixWord ++ tailWord_2949683).sum := by decide
  have hdescent : baseEnd_2949683 < baseStart_2949683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949689 : List Nat := [1, 2, 1, 5, 1, 1, 3, 2, 7]
def baseStart_2949689 : Nat := 118140960795 + 2949689 * 2 ^ 59
def prefixEnd_2949689 : Nat := 4983230072969 + 3 ^ 40 * 2949689 * 2
def baseEnd_2949689 : Nat := 168289804253335006880237

theorem tailTrace_2949689 : CollatzResearch.WordTrace tailWord_2949689 prefixEnd_2949689 168289804253335006880237 := by
  unfold tailWord_2949689
  simp only [CollatzResearch.WordTrace]
  refine ⟨107583996210787994619388121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71722664140525329746258747 107583996210787994619388121)
  ·
    refine ⟨80687997158090995964541091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107583996210787994619388121 80687997158090995964541091)
    ·
      refine ⟨121031995737136493946811637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80687997158090995964541091 121031995737136493946811637)
      ·
        refine ⟨11346749600356546307513591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121031995737136493946811637 11346749600356546307513591)
        ·
          refine ⟨17020124400534819461270387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11346749600356546307513591 17020124400534819461270387)
          ·
            refine ⟨25530186600802229191905581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17020124400534819461270387 25530186600802229191905581)
            ·
              refine ⟨9573819975300835946964593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25530186600802229191905581 9573819975300835946964593)
              ·
                refine ⟨7180364981475626960223445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9573819975300835946964593 7180364981475626960223445)
                ·
                  refine ⟨168289804253335006880237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7180364981475626960223445 168289804253335006880237)
                  ·
                    rfl

theorem cell23_2949689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 7].length) (baseStart_2949689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949689 prefixEnd_2949689 := by exact prefixLift 2949689
  have htrace : WordTrace (prefixWord ++ tailWord_2949689) baseStart_2949689 baseEnd_2949689 := by
    simpa [prefixWord, tailWord_2949689, baseEnd_2949689] using wordTrace_append hprefix tailTrace_2949689
  have hstable : (prefixWord ++ tailWord_2949689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949689).length < 2 ^ (prefixWord ++ tailWord_2949689).sum := by decide
  have hdescent : baseEnd_2949689 < baseStart_2949689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949706 : List Nat := [3, 1, 2, 1, 1, 4, 1, 5, 5]
def baseStart_2949706 : Nat := 118140960795 + 2949706 * 2 ^ 59
def prefixEnd_2949706 : Nat := 4983230072969 + 3 ^ 40 * 2949706 * 2
def baseEnd_2949706 : Nat := 168290774161237943934395

theorem tailTrace_2949706 : CollatzResearch.WordTrace tailWord_2949706 prefixEnd_2949706 168290774161237943934395 := by
  unfold tailWord_2949706
  simp only [CollatzResearch.WordTrace]
  refine ⟨26896154062931601630689243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71723077501150937681837981 26896154062931601630689243)
  ·
    refine ⟨40344231094397402446033865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26896154062931601630689243 40344231094397402446033865)
    ·
      refine ⟨30258173320798051834525399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40344231094397402446033865 30258173320798051834525399)
      ·
        refine ⟨45387259981197077751788099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30258173320798051834525399 45387259981197077751788099)
        ·
          refine ⟨68080889971795616627682149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45387259981197077751788099 68080889971795616627682149)
          ·
            refine ⟨12765166869711678117690403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68080889971795616627682149 12765166869711678117690403)
            ·
              refine ⟨19147750304567517176535605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12765166869711678117690403 19147750304567517176535605)
              ·
                refine ⟨1795101591053204735300213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19147750304567517176535605 1795101591053204735300213)
                ·
                  refine ⟨168290774161237943934395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1795101591053204735300213 168290774161237943934395)
                  ·
                    rfl

theorem cell23_2949706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 5].length) (baseStart_2949706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949706 prefixEnd_2949706 := by exact prefixLift 2949706
  have htrace : WordTrace (prefixWord ++ tailWord_2949706) baseStart_2949706 baseEnd_2949706 := by
    simpa [prefixWord, tailWord_2949706, baseEnd_2949706] using wordTrace_append hprefix tailTrace_2949706
  have hstable : (prefixWord ++ tailWord_2949706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949706).length < 2 ^ (prefixWord ++ tailWord_2949706).sum := by decide
  have hdescent : baseEnd_2949706 < baseStart_2949706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949716 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_2949716 : Nat := 118140960795 + 2949716 * 2 ^ 59
def prefixEnd_2949716 : Nat := 4983230072969 + 3 ^ 40 * 2949716 * 2
def baseEnd_2949716 : Nat := 1514622102257686456284509

theorem tailTrace_2949716 : CollatzResearch.WordTrace tailWord_2949716 prefixEnd_2949716 1514622102257686456284509 := by
  unfold tailWord_2949716
  simp only [CollatzResearch.WordTrace]
  refine ⟨53792490490845089115310501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71723320654460118820414001 53792490490845089115310501)
  ·
    refine ⟨10086091967033454209120719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53792490490845089115310501 10086091967033454209120719)
    ·
      refine ⟨15129137950550181313681079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10086091967033454209120719 15129137950550181313681079)
      ·
        refine ⟨22693706925825271970521619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15129137950550181313681079 22693706925825271970521619)
        ·
          refine ⟨34040560388737907955782429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22693706925825271970521619 34040560388737907955782429)
          ·
            refine ⟨12765210145776715483418411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34040560388737907955782429 12765210145776715483418411)
            ·
              refine ⟨19147815218665073225127617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12765210145776715483418411 19147815218665073225127617)
              ·
                refine ⟨14360861413998804918845713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19147815218665073225127617 14360861413998804918845713)
                ·
                  refine ⟨10770646060499103689134285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14360861413998804918845713 10770646060499103689134285)
                  ·
                    refine ⟨4038992272687163883425357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10770646060499103689134285 4038992272687163883425357)
                    ·
                      refine ⟨1514622102257686456284509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4038992272687163883425357 1514622102257686456284509)
                      ·
                        rfl

theorem cell23_2949716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_2949716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949716 prefixEnd_2949716 := by exact prefixLift 2949716
  have htrace : WordTrace (prefixWord ++ tailWord_2949716) baseStart_2949716 baseEnd_2949716 := by
    simpa [prefixWord, tailWord_2949716, baseEnd_2949716] using wordTrace_append hprefix tailTrace_2949716
  have hstable : (prefixWord ++ tailWord_2949716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949716).length < 2 ^ (prefixWord ++ tailWord_2949716).sum := by decide
  have hdescent : baseEnd_2949716 < baseStart_2949716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949719 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 4, 5]
def baseStart_2949719 : Nat := 118140960795 + 2949719 * 2 ^ 59
def prefixEnd_2949719 : Nat := 4983230072969 + 3 ^ 40 * 2949719 * 2
def baseEnd_2949719 : Nat := 504874547566549981515665

theorem tailTrace_2949719 : CollatzResearch.WordTrace tailWord_2949719 prefixEnd_2949719 504874547566549981515665 := by
  unfold tailWord_2949719
  simp only [CollatzResearch.WordTrace]
  refine ⟨107585090400679309742980211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71723393600452873161986807 107585090400679309742980211)
  ·
    refine ⟨161377635601018964614470317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107585090400679309742980211 161377635601018964614470317)
    ·
      refine ⟨60516613350382111730426369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161377635601018964614470317 60516613350382111730426369)
      ·
        refine ⟨45387460012786583797819777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60516613350382111730426369 45387460012786583797819777)
        ·
          refine ⟨34040595009589937848364833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45387460012786583797819777 34040595009589937848364833)
          ·
            refine ⟨25530446257192453386273625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34040595009589937848364833 25530446257192453386273625)
            ·
              refine ⟨19147834692894340039705219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25530446257192453386273625 19147834692894340039705219)
              ·
                refine ⟨28721752039341510059557829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19147834692894340039705219 28721752039341510059557829)
                ·
                  refine ⟨5385328507376533136167093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28721752039341510059557829 5385328507376533136167093)
                  ·
                    refine ⟨504874547566549981515665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5385328507376533136167093 504874547566549981515665)
                    ·
                      rfl

theorem cell23_2949719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_2949719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949719 prefixEnd_2949719 := by exact prefixLift 2949719
  have htrace : WordTrace (prefixWord ++ tailWord_2949719) baseStart_2949719 baseEnd_2949719 := by
    simpa [prefixWord, tailWord_2949719, baseEnd_2949719] using wordTrace_append hprefix tailTrace_2949719
  have hstable : (prefixWord ++ tailWord_2949719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949719).length < 2 ^ (prefixWord ++ tailWord_2949719).sum := by decide
  have hdescent : baseEnd_2949719 < baseStart_2949719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949739 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 4]
def baseStart_2949739 : Nat := 118140960795 + 2949739 * 2 ^ 59
def prefixEnd_2949739 : Nat := 4983230072969 + 3 ^ 40 * 2949739 * 2
def baseEnd_2949739 : Nat := 1514633912312739866296903

theorem tailTrace_2949739 : CollatzResearch.WordTrace tailWord_2949739 prefixEnd_2949739 1514633912312739866296903 := by
  unfold tailWord_2949739
  simp only [CollatzResearch.WordTrace]
  refine ⟨107585819860606853158708271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71723879907071235439138847 107585819860606853158708271)
  ·
    refine ⟨161378729790910279738062407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107585819860606853158708271 161378729790910279738062407)
    ·
      refine ⟨242068094686365419607093611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161378729790910279738062407 242068094686365419607093611)
      ·
        refine ⟨363102142029548129410640417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242068094686365419607093611 363102142029548129410640417)
        ·
          refine ⟨272326606522161097057980313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363102142029548129410640417 272326606522161097057980313)
          ·
            refine ⟨204244954891620822793485235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272326606522161097057980313 204244954891620822793485235)
            ·
              refine ⟨306367432337431234190227853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204244954891620822793485235 306367432337431234190227853)
              ·
                refine ⟨114887787126536712821335445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306367432337431234190227853 114887787126536712821335445)
                ·
                  refine ⟨5385365021556408413500099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 114887787126536712821335445 5385365021556408413500099)
                  ·
                    refine ⟨8078047532334612620250149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5385365021556408413500099 8078047532334612620250149)
                    ·
                      refine ⟨1514633912312739866296903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8078047532334612620250149 1514633912312739866296903)
                      ·
                        rfl

theorem cell23_2949739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 4].length) (baseStart_2949739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949739 prefixEnd_2949739 := by exact prefixLift 2949739
  have htrace : WordTrace (prefixWord ++ tailWord_2949739) baseStart_2949739 baseEnd_2949739 := by
    simpa [prefixWord, tailWord_2949739, baseEnd_2949739] using wordTrace_append hprefix tailTrace_2949739
  have hstable : (prefixWord ++ tailWord_2949739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949739).length < 2 ^ (prefixWord ++ tailWord_2949739).sum := by decide
  have hdescent : baseEnd_2949739 < baseStart_2949739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949756 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 1, 6, 2]
def baseStart_2949756 : Nat := 118140960795 + 2949756 * 2 ^ 59
def prefixEnd_2949756 : Nat := 4983230072969 + 3 ^ 40 * 2949756 * 2
def baseEnd_2949756 : Nat := 1514642641483866299784325

theorem tailTrace_2949756 : CollatzResearch.WordTrace tailWord_2949756 prefixEnd_2949756 1514642641483866299784325 := by
  unfold tailWord_2949756
  simp only [CollatzResearch.WordTrace]
  refine ⟨53793219950772632531038561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71724293267696843374718081 53793219950772632531038561)
  ·
    refine ⟨40344914963079474398278921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53793219950772632531038561 40344914963079474398278921)
    ·
      refine ⟨30258686222309605798709191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40344914963079474398278921 30258686222309605798709191)
      ·
        refine ⟨45388029333464408698063787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30258686222309605798709191 45388029333464408698063787)
        ·
          refine ⟨68082044000196613047095681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45388029333464408698063787 68082044000196613047095681)
          ·
            refine ⟨51061533000147459785321761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68082044000196613047095681 51061533000147459785321761)
            ·
              refine ⟨38296149750110594838991321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51061533000147459785321761 38296149750110594838991321)
              ·
                refine ⟨28722112312582946129243491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38296149750110594838991321 28722112312582946129243491)
                ·
                  refine ⟨43083168468874419193865237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28722112312582946129243491 43083168468874419193865237)
                  ·
                    refine ⟨2019523521978488399712433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43083168468874419193865237 2019523521978488399712433)
                    ·
                      refine ⟨1514642641483866299784325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2019523521978488399712433 1514642641483866299784325)
                      ·
                        rfl

theorem cell23_2949756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_2949756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949756 prefixEnd_2949756 := by exact prefixLift 2949756
  have htrace : WordTrace (prefixWord ++ tailWord_2949756) baseStart_2949756 baseEnd_2949756 := by
    simpa [prefixWord, tailWord_2949756, baseEnd_2949756] using wordTrace_append hprefix tailTrace_2949756
  have hstable : (prefixWord ++ tailWord_2949756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949756).length < 2 ^ (prefixWord ++ tailWord_2949756).sum := by decide
  have hdescent : baseEnd_2949756 < baseStart_2949756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949796 : List Nat := [2, 3, 1, 2, 2, 1, 3, 3, 6]
def baseStart_2949796 : Nat := 118140960795 + 2949796 * 2 ^ 59
def prefixEnd_2949796 : Nat := 4983230072969 + 3 ^ 40 * 2949796 * 2
def baseEnd_2949796 : Nat := 168295908967782904809349

theorem tailTrace_2949796 : CollatzResearch.WordTrace tailWord_2949796 prefixEnd_2949796 168295908967782904809349 := by
  unfold tailWord_2949796
  simp only [CollatzResearch.WordTrace]
  refine ⟨53793949410700175946766621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71725265880933567929022161 53793949410700175946766621)
  ·
    refine ⟨20172731029012565980037483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53793949410700175946766621 20172731029012565980037483)
    ·
      refine ⟨30259096543518848970056225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20172731029012565980037483 30259096543518848970056225)
      ·
        refine ⟨22694322407639136727542169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30259096543518848970056225 22694322407639136727542169)
        ·
          refine ⟨17020741805729352545656627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22694322407639136727542169 17020741805729352545656627)
          ·
            refine ⟨25531112708594028818484941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17020741805729352545656627 25531112708594028818484941)
            ·
              refine ⟨9574167265722760806931853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25531112708594028818484941 9574167265722760806931853)
              ·
                refine ⟨3590312724646035302599445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9574167265722760806931853 3590312724646035302599445)
                ·
                  refine ⟨168295908967782904809349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3590312724646035302599445 168295908967782904809349)
                  ·
                    rfl

theorem cell23_2949796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_2949796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949796 prefixEnd_2949796 := by exact prefixLift 2949796
  have htrace : WordTrace (prefixWord ++ tailWord_2949796) baseStart_2949796 baseEnd_2949796 := by
    simpa [prefixWord, tailWord_2949796, baseEnd_2949796] using wordTrace_append hprefix tailTrace_2949796
  have hstable : (prefixWord ++ tailWord_2949796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949796).length < 2 ^ (prefixWord ++ tailWord_2949796).sum := by decide
  have hdescent : baseEnd_2949796 < baseStart_2949796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949856 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 6, 4]
def baseStart_2949856 : Nat := 118140960795 + 2949856 * 2 ^ 59
def prefixEnd_2949856 : Nat := 4983230072969 + 3 ^ 40 * 2949856 * 2
def baseEnd_2949856 : Nat := 504897996516438636177955

theorem tailTrace_2949856 : CollatzResearch.WordTrace tailWord_2949856 prefixEnd_2949856 504897996516438636177955 := by
  unfold tailWord_2949856
  simp only [CollatzResearch.WordTrace]
  refine ⟨53795043600591491070358711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71726724800788654760478281 53795043600591491070358711)
  ·
    refine ⟨80692565400887236605538067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53795043600591491070358711 80692565400887236605538067)
    ·
      refine ⟨121038848101330854908307101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80692565400887236605538067 121038848101330854908307101)
      ·
        refine ⟨45389568037999070590615163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121038848101330854908307101 45389568037999070590615163)
        ·
          refine ⟨68084352056998605885922745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45389568037999070590615163 68084352056998605885922745)
          ·
            refine ⟨51063264042748954414442059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68084352056998605885922745 51063264042748954414442059)
            ·
              refine ⟨76594896064123431621663089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51063264042748954414442059 76594896064123431621663089)
              ·
                refine ⟨57446172048092573716247317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76594896064123431621663089 57446172048092573716247317)
                ·
                  refine ⟨2692789314754339392949093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57446172048092573716247317 2692789314754339392949093)
                  ·
                    refine ⟨504897996516438636177955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2692789314754339392949093 504897996516438636177955)
                    ·
                      rfl

theorem cell23_2949856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 6, 4].length) (baseStart_2949856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949856 prefixEnd_2949856 := by exact prefixLift 2949856
  have htrace : WordTrace (prefixWord ++ tailWord_2949856) baseStart_2949856 baseEnd_2949856 := by
    simpa [prefixWord, tailWord_2949856, baseEnd_2949856] using wordTrace_append hprefix tailTrace_2949856
  have hstable : (prefixWord ++ tailWord_2949856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949856).length < 2 ^ (prefixWord ++ tailWord_2949856).sum := by decide
  have hdescent : baseEnd_2949856 < baseStart_2949856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949890 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_2949890 : Nat := 118140960795 + 2949890 * 2 ^ 59
def prefixEnd_2949890 : Nat := 4983230072969 + 3 ^ 40 * 2949890 * 2
def baseEnd_2949890 : Nat := 504903815963856258502903

theorem tailTrace_2949890 : CollatzResearch.WordTrace tailWord_2949890 prefixEnd_2949890 504903815963856258502903 := by
  unfold tailWord_2949890
  simp only [CollatzResearch.WordTrace]
  refine ⟨26897831820764951486863781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71727551522039870631636749 26897831820764951486863781)
  ·
    refine ⟨5043343466393428403786959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26897831820764951486863781 5043343466393428403786959)
    ·
      refine ⟨7565015199590142605680439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5043343466393428403786959 7565015199590142605680439)
      ·
        refine ⟨11347522799385213908520659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7565015199590142605680439 11347522799385213908520659)
        ·
          refine ⟨17021284199077820862780989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11347522799385213908520659 17021284199077820862780989)
          ·
            refine ⟨6382981574654182823542871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17021284199077820862780989 6382981574654182823542871)
            ·
              refine ⟨9574472361981274235314307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6382981574654182823542871 9574472361981274235314307)
              ·
                refine ⟨14361708542971911352971461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9574472361981274235314307 14361708542971911352971461)
                ·
                  refine ⟨2692820351807233378682149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14361708542971911352971461 2692820351807233378682149)
                  ·
                    refine ⟨504903815963856258502903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2692820351807233378682149 504903815963856258502903)
                    ·
                      rfl

theorem cell23_2949890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_2949890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949890 prefixEnd_2949890 := by exact prefixLift 2949890
  have htrace : WordTrace (prefixWord ++ tailWord_2949890) baseStart_2949890 baseEnd_2949890 := by
    simpa [prefixWord, tailWord_2949890, baseEnd_2949890] using wordTrace_append hprefix tailTrace_2949890
  have hstable : (prefixWord ++ tailWord_2949890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949890).length < 2 ^ (prefixWord ++ tailWord_2949890).sum := by decide
  have hdescent : baseEnd_2949890 < baseStart_2949890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949897 : List Nat := [1, 2, 1, 1, 3, 2, 4, 4, 1, 2, 2]
def baseStart_2949897 : Nat := 118140960795 + 2949897 * 2 ^ 59
def prefixEnd_2949897 : Nat := 4983230072969 + 3 ^ 40 * 2949897 * 2
def baseEnd_2949897 : Nat := 1514715042256150248121177

theorem tailTrace_2949897 : CollatzResearch.WordTrace tailWord_2949897 prefixEnd_2949897 1514715042256150248121177 := by
  unfold tailWord_2949897
  simp only [CollatzResearch.WordTrace]
  refine ⟨107591582594034446142959945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71727721729356297428639963 107591582594034446142959945)
  ·
    refine ⟨80693686945525834607219959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107591582594034446142959945 80693686945525834607219959)
    ·
      refine ⟨121040530418288751910829939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80693686945525834607219959 121040530418288751910829939)
      ·
        refine ⟨181560795627433127866244909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121040530418288751910829939 181560795627433127866244909)
        ·
          refine ⟨68085298360287422949841841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181560795627433127866244909 68085298360287422949841841)
          ·
            refine ⟨51063973770215567212381381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68085298360287422949841841 51063973770215567212381381)
            ·
              refine ⟨9574495081915418852321509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51063973770215567212381381 9574495081915418852321509)
              ·
                refine ⟨1795217827859141034810283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9574495081915418852321509 1795217827859141034810283)
                ·
                  refine ⟨2692826741788711552215425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1795217827859141034810283 2692826741788711552215425)
                  ·
                    refine ⟨2019620056341533664161569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2692826741788711552215425 2019620056341533664161569)
                    ·
                      refine ⟨1514715042256150248121177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2019620056341533664161569 1514715042256150248121177)
                      ·
                        rfl

theorem cell23_2949897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 1, 2, 2].length) (baseStart_2949897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949897 prefixEnd_2949897 := by exact prefixLift 2949897
  have htrace : WordTrace (prefixWord ++ tailWord_2949897) baseStart_2949897 baseEnd_2949897 := by
    simpa [prefixWord, tailWord_2949897, baseEnd_2949897] using wordTrace_append hprefix tailTrace_2949897
  have hstable : (prefixWord ++ tailWord_2949897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949897).length < 2 ^ (prefixWord ++ tailWord_2949897).sum := by decide
  have hdescent : baseEnd_2949897 < baseStart_2949897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949958 : List Nat := [6, 1, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_2949958 : Nat := 118140960795 + 2949958 * 2 ^ 59
def prefixEnd_2949958 : Nat := 4983230072969 + 3 ^ 40 * 2949958 * 2
def baseEnd_2949958 : Nat := 504915454858691503152799

theorem tailTrace_2949958 : CollatzResearch.WordTrace tailWord_2949958 prefixEnd_2949958 504915454858691503152799 := by
  unfold tailWord_2949958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3362306482712920423779079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71729204964542302373953685 3362306482712920423779079)
  ·
    refine ⟨5043459724069380635668619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3362306482712920423779079 5043459724069380635668619)
    ·
      refine ⟨7565189586104070953502929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5043459724069380635668619 7565189586104070953502929)
      ·
        refine ⟨5673892189578053215127197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7565189586104070953502929 5673892189578053215127197)
        ·
          refine ⟨2127709571091769955672699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5673892189578053215127197 2127709571091769955672699)
          ·
            refine ⟨3191564356637654933509049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2127709571091769955672699 3191564356637654933509049)
            ·
              refine ⟨2393673267478241200131787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3191564356637654933509049 2393673267478241200131787)
              ·
                refine ⟨3590509901217361800197681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2393673267478241200131787 3590509901217361800197681)
                ·
                  refine ⟨2692882425913021350148261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3590509901217361800197681 2692882425913021350148261)
                  ·
                    refine ⟨504915454858691503152799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2692882425913021350148261 504915454858691503152799)
                    ·
                      rfl

theorem cell23_2949958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_2949958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949958 prefixEnd_2949958 := by exact prefixLift 2949958
  have htrace : WordTrace (prefixWord ++ tailWord_2949958) baseStart_2949958 baseEnd_2949958 := by
    simpa [prefixWord, tailWord_2949958, baseEnd_2949958] using wordTrace_append hprefix tailTrace_2949958
  have hstable : (prefixWord ++ tailWord_2949958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949958).length < 2 ^ (prefixWord ++ tailWord_2949958).sum := by decide
  have hdescent : baseEnd_2949958 < baseStart_2949958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949964 : List Nat := [2, 2, 1, 3, 3, 3, 2, 1, 2, 1, 3]
def baseStart_2949964 : Nat := 118140960795 + 2949964 * 2 ^ 59
def prefixEnd_2949964 : Nat := 4983230072969 + 3 ^ 40 * 2949964 * 2
def baseEnd_2949964 : Nat := 1514749445460001485983369

theorem tailTrace_2949964 : CollatzResearch.WordTrace tailWord_2949964 prefixEnd_2949964 1514749445460001485983369 := by
  unfold tailWord_2949964
  simp only [CollatzResearch.WordTrace]
  refine ⟨53797013142395858292824473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71729350856527811057099297 53797013142395858292824473)
  ·
    refine ⟨40347759856796893719618355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53797013142395858292824473 40347759856796893719618355)
    ·
      refine ⟨60521639785195340579427533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40347759856796893719618355 60521639785195340579427533)
      ·
        refine ⟨22695614919448252717285325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60521639785195340579427533 22695614919448252717285325)
        ·
          refine ⟨8510855594793094768981997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22695614919448252717285325 8510855594793094768981997)
          ·
            refine ⟨3191570848047410538368249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8510855594793094768981997 3191570848047410538368249)
            ·
              refine ⟨2393678136035557903776187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3191570848047410538368249 2393678136035557903776187)
              ·
                refine ⟨3590517204053336855664281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2393678136035557903776187 3590517204053336855664281)
                ·
                  refine ⟨2692887903040002641748211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3590517204053336855664281 2692887903040002641748211)
                  ·
                    refine ⟨4039331854560003962622317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2692887903040002641748211 4039331854560003962622317)
                    ·
                      refine ⟨1514749445460001485983369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4039331854560003962622317 1514749445460001485983369)
                      ·
                        rfl

theorem cell23_2949964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_2949964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949964 prefixEnd_2949964 := by exact prefixLift 2949964
  have htrace : WordTrace (prefixWord ++ tailWord_2949964) baseStart_2949964 baseEnd_2949964 := by
    simpa [prefixWord, tailWord_2949964, baseEnd_2949964] using wordTrace_append hprefix tailTrace_2949964
  have hstable : (prefixWord ++ tailWord_2949964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949964).length < 2 ^ (prefixWord ++ tailWord_2949964).sum := by decide
  have hdescent : baseEnd_2949964 < baseStart_2949964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949966 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_2949966 : Nat := 118140960795 + 2949966 * 2 ^ 59
def prefixEnd_2949966 : Nat := 4983230072969 + 3 ^ 40 * 2949966 * 2
def baseEnd_2949966 : Nat := 1514750472421310478158359

theorem tailTrace_2949966 : CollatzResearch.WordTrace tailWord_2949966 prefixEnd_2949966 1514750472421310478158359 := by
  unfold tailWord_2949966
  simp only [CollatzResearch.WordTrace]
  refine ⟨13449262403848058865902719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71729399487189647284814501 13449262403848058865902719)
  ·
    refine ⟨20173893605772088298854079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13449262403848058865902719 20173893605772088298854079)
    ·
      refine ⟨30260840408658132448281119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20173893605772088298854079 30260840408658132448281119)
      ·
        refine ⟨45391260612987198672421679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30260840408658132448281119 45391260612987198672421679)
        ·
          refine ⟨68086890919480798008632519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45391260612987198672421679 68086890919480798008632519)
          ·
            refine ⟨102130336379221197012948779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68086890919480798008632519 102130336379221197012948779)
            ·
              refine ⟨153195504568831795519423169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102130336379221197012948779 153195504568831795519423169)
              ·
                refine ⟨114896628426623846639567377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153195504568831795519423169 114896628426623846639567377)
                ·
                  refine ⟨86172471319967884979675533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114896628426623846639567377 86172471319967884979675533)
                  ·
                    refine ⟨32314676744987956867378325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86172471319967884979675533 32314676744987956867378325)
                    ·
                      refine ⟨1514750472421310478158359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32314676744987956867378325 1514750472421310478158359)
                      ·
                        rfl

theorem cell23_2949966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_2949966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949966 prefixEnd_2949966 := by exact prefixLift 2949966
  have htrace : WordTrace (prefixWord ++ tailWord_2949966) baseStart_2949966 baseEnd_2949966 := by
    simpa [prefixWord, tailWord_2949966, baseEnd_2949966] using wordTrace_append hprefix tailTrace_2949966
  have hstable : (prefixWord ++ tailWord_2949966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949966).length < 2 ^ (prefixWord ++ tailWord_2949966).sum := by decide
  have hdescent : baseEnd_2949966 < baseStart_2949966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949970 : List Nat := [3, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2]
def baseStart_2949970 : Nat := 118140960795 + 2949970 * 2 ^ 59
def prefixEnd_2949970 : Nat := 4983230072969 + 3 ^ 40 * 2949970 * 2
def baseEnd_2949970 : Nat := 1514752526343928462508341

theorem tailTrace_2949970 : CollatzResearch.WordTrace tailWord_2949970 prefixEnd_2949970 1514752526343928462508341 := by
  unfold tailWord_2949970
  simp only [CollatzResearch.WordTrace]
  refine ⟨26898561280692494902591841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71729496748513319740244909 26898561280692494902591841)
  ·
    refine ⟨20173920960519371176943881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26898561280692494902591841 20173920960519371176943881)
    ·
      refine ⟨15130440720389528382707911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20173920960519371176943881 15130440720389528382707911)
      ·
        refine ⟨22695661080584292574061867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15130440720389528382707911 22695661080584292574061867)
        ·
          refine ⟨34043491620876438861092801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22695661080584292574061867 34043491620876438861092801)
          ·
            refine ⟨25532618715657329145819601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34043491620876438861092801 25532618715657329145819601)
            ·
              refine ⟨19149464036742996859364701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25532618715657329145819601 19149464036742996859364701)
              ·
                refine ⟨7181049013778623822261763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19149464036742996859364701 7181049013778623822261763)
                ·
                  refine ⟨10771573520667935733392645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7181049013778623822261763 10771573520667935733392645)
                  ·
                    refine ⟨2019670035125237950011121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10771573520667935733392645 2019670035125237950011121)
                    ·
                      refine ⟨1514752526343928462508341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2019670035125237950011121 1514752526343928462508341)
                      ·
                        rfl

theorem cell23_2949970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_2949970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949970 prefixEnd_2949970 := by exact prefixLift 2949970
  have htrace : WordTrace (prefixWord ++ tailWord_2949970) baseStart_2949970 baseEnd_2949970 := by
    simpa [prefixWord, tailWord_2949970, baseEnd_2949970] using wordTrace_append hprefix tailTrace_2949970
  have hstable : (prefixWord ++ tailWord_2949970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949970).length < 2 ^ (prefixWord ++ tailWord_2949970).sum := by decide
  have hdescent : baseEnd_2949970 < baseStart_2949970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2949976 : List Nat := [2, 1, 2, 2, 1, 1, 1, 6, 7]
def baseStart_2949976 : Nat := 118140960795 + 2949976 * 2 ^ 59
def prefixEnd_2949976 : Nat := 4983230072969 + 3 ^ 40 * 2949976 * 2
def baseEnd_2949976 : Nat := 168306178580872826559257

theorem tailTrace_2949976 : CollatzResearch.WordTrace tailWord_2949976 prefixEnd_2949976 168306178580872826559257 := by
  unfold tailWord_2949976
  simp only [CollatzResearch.WordTrace]
  refine ⟨53797231980374121317542891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71729642640498828423390521 53797231980374121317542891)
  ·
    refine ⟨80695847970561181976314337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53797231980374121317542891 80695847970561181976314337)
    ·
      refine ⟨60521885977920886482235753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80695847970561181976314337 60521885977920886482235753)
      ·
        refine ⟨45391414483440664861676815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60521885977920886482235753 45391414483440664861676815)
        ·
          refine ⟨68087121725160997292515223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45391414483440664861676815 68087121725160997292515223)
          ·
            refine ⟨102130682587741495938772835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68087121725160997292515223 102130682587741495938772835)
            ·
              refine ⟨153196023881612243908159253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102130682587741495938772835 153196023881612243908159253)
              ·
                refine ⟨7181063619450573933194965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153196023881612243908159253 7181063619450573933194965)
                ·
                  refine ⟨168306178580872826559257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7181063619450573933194965 168306178580872826559257)
                  ·
                    rfl

theorem cell23_2949976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 7].length) (baseStart_2949976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2949976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2949976 prefixEnd_2949976 := by exact prefixLift 2949976
  have htrace : WordTrace (prefixWord ++ tailWord_2949976) baseStart_2949976 baseEnd_2949976 := by
    simpa [prefixWord, tailWord_2949976, baseEnd_2949976] using wordTrace_append hprefix tailTrace_2949976
  have hstable : (prefixWord ++ tailWord_2949976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2949976).length < 2 ^ (prefixWord ++ tailWord_2949976).sum := by decide
  have hdescent : baseEnd_2949976 < baseStart_2949976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2949976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950016 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 7]
def baseStart_2950016 : Nat := 118140960795 + 2950016 * 2 ^ 59
def prefixEnd_2950016 : Nat := 4983230072969 + 3 ^ 40 * 2950016 * 2
def baseEnd_2950016 : Nat := 1514776146454035282533129

theorem tailTrace_2950016 : CollatzResearch.WordTrace tailWord_2950016 prefixEnd_2950016 1514776146454035282533129 := by
  unfold tailWord_2950016
  simp only [CollatzResearch.WordTrace]
  refine ⟨53797961440301664733270951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71730615253735552977694601 53797961440301664733270951)
  ·
    refine ⟨80696942160452497099906427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53797961440301664733270951 80696942160452497099906427)
    ·
      refine ⟨121045413240678745649859641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80696942160452497099906427 121045413240678745649859641)
      ·
        refine ⟨90784059930509059237394731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121045413240678745649859641 90784059930509059237394731)
        ·
          refine ⟨136176089895763588856092097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90784059930509059237394731 136176089895763588856092097)
          ·
            refine ⟨102132067421822691642069073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136176089895763588856092097 102132067421822691642069073)
            ·
              refine ⟨76599050566367018731551805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102132067421822691642069073 76599050566367018731551805)
              ·
                refine ⟨28724643962387632024331927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76599050566367018731551805 28724643962387632024331927)
                ·
                  refine ⟨43086965943581448036497891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28724643962387632024331927 43086965943581448036497891)
                  ·
                    refine ⟨64630448915372172054746837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43086965943581448036497891 64630448915372172054746837)
                    ·
                      refine ⟨1514776146454035282533129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64630448915372172054746837 1514776146454035282533129)
                      ·
                        rfl

theorem cell23_2950016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_2950016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950016 prefixEnd_2950016 := by exact prefixLift 2950016
  have htrace : WordTrace (prefixWord ++ tailWord_2950016) baseStart_2950016 baseEnd_2950016 := by
    simpa [prefixWord, tailWord_2950016, baseEnd_2950016] using wordTrace_append hprefix tailTrace_2950016
  have hstable : (prefixWord ++ tailWord_2950016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950016).length < 2 ^ (prefixWord ++ tailWord_2950016).sum := by decide
  have hdescent : baseEnd_2950016 < baseStart_2950016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950104 : List Nat := [2, 1, 2, 2, 2, 5, 1, 3, 1, 4]
def baseStart_2950104 : Nat := 118140960795 + 2950104 * 2 ^ 59
def prefixEnd_2950104 : Nat := 4983230072969 + 3 ^ 40 * 2950104 * 2
def baseEnd_2950104 : Nat := 504940444250543646077575

theorem tailTrace_2950104 : CollatzResearch.WordTrace tailWord_2950104 prefixEnd_2950104 504940444250543646077575 := by
  unfold tailWord_2950104
  simp only [CollatzResearch.WordTrace]
  refine ⟨53799566252142260247872683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71732755002856346997163577 53799566252142260247872683)
  ·
    refine ⟨80699349378213390371809025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53799566252142260247872683 80699349378213390371809025)
    ·
      refine ⟨60524512033660042778856769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80699349378213390371809025 60524512033660042778856769)
      ·
        refine ⟨45393384025245032084142577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60524512033660042778856769 45393384025245032084142577)
        ·
          refine ⟨34045038018933774063106933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45393384025245032084142577 34045038018933774063106933)
          ·
            refine ⟨3191722314275041318416275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34045038018933774063106933 3191722314275041318416275)
            ·
              refine ⟨4787583471412561977624413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3191722314275041318416275 4787583471412561977624413)
              ·
                refine ⟨1795343801779710741609155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4787583471412561977624413 1795343801779710741609155)
                ·
                  refine ⟨2693015702669566112413733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1795343801779710741609155 2693015702669566112413733)
                  ·
                    refine ⟨504940444250543646077575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2693015702669566112413733 504940444250543646077575)
                    ·
                      rfl

theorem cell23_2950104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 1, 4].length) (baseStart_2950104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950104 prefixEnd_2950104 := by exact prefixLift 2950104
  have htrace : WordTrace (prefixWord ++ tailWord_2950104) baseStart_2950104 baseEnd_2950104 := by
    simpa [prefixWord, tailWord_2950104, baseEnd_2950104] using wordTrace_append hprefix tailTrace_2950104
  have hstable : (prefixWord ++ tailWord_2950104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950104).length < 2 ^ (prefixWord ++ tailWord_2950104).sum := by decide
  have hdescent : baseEnd_2950104 < baseStart_2950104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950113 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 5, 5]
def baseStart_2950113 : Nat := 118140960795 + 2950113 * 2 ^ 59
def prefixEnd_2950113 : Nat := 4983230072969 + 3 ^ 40 * 2950113 * 2
def baseEnd_2950113 : Nat := 504941984692507134340061

theorem tailTrace_2950113 : CollatzResearch.WordTrace tailWord_2950113 prefixEnd_2950113 504941984692507134340061 := by
  unfold tailWord_2950113
  simp only [CollatzResearch.WordTrace]
  refine ⟨107599460761251915032822993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71732973840834610021881995 107599460761251915032822993)
  ·
    refine ⟨80699595570938936274617245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107599460761251915032822993 80699595570938936274617245)
    ·
      refine ⟨30262348339102101102981467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80699595570938936274617245 30262348339102101102981467)
      ·
        refine ⟨45393522508653151654472201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30262348339102101102981467 45393522508653151654472201)
        ·
          refine ⟨34045141881489863740854151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45393522508653151654472201 34045141881489863740854151)
          ·
            refine ⟨51067712822234795611281227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34045141881489863740854151 51067712822234795611281227)
            ·
              refine ⟨76601569233352193416921841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51067712822234795611281227 76601569233352193416921841)
              ·
                refine ⟨57451176925014145062691381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76601569233352193416921841 57451176925014145062691381)
                ·
                  refine ⟨5386047836720076099627317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57451176925014145062691381 5386047836720076099627317)
                  ·
                    refine ⟨504941984692507134340061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5386047836720076099627317 504941984692507134340061)
                    ·
                      rfl

theorem cell23_2950113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_2950113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950113 prefixEnd_2950113 := by exact prefixLift 2950113
  have htrace : WordTrace (prefixWord ++ tailWord_2950113) baseStart_2950113 baseEnd_2950113 := by
    simpa [prefixWord, tailWord_2950113, baseEnd_2950113] using wordTrace_append hprefix tailTrace_2950113
  have hstable : (prefixWord ++ tailWord_2950113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950113).length < 2 ^ (prefixWord ++ tailWord_2950113).sum := by decide
  have hdescent : baseEnd_2950113 < baseStart_2950113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950114 : List Nat := [3, 3, 3, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_2950114 : Nat := 118140960795 + 2950114 * 2 ^ 59
def prefixEnd_2950114 : Nat := 4983230072969 + 3 ^ 40 * 2950114 * 2
def baseEnd_2950114 : Nat := 1514826467558175899107679

theorem tailTrace_2950114 : CollatzResearch.WordTrace tailWord_2950114 prefixEnd_2950114 1514826467558175899107679 := by
  unfold tailWord_2950114
  simp only [CollatzResearch.WordTrace]
  refine ⟨26899874308562073050902349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71732998156165528135739597 26899874308562073050902349)
  ·
    refine ⟨10087452865710777394088381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26899874308562073050902349 10087452865710777394088381)
    ·
      refine ⟨3782794824641541522783143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10087452865710777394088381 3782794824641541522783143)
      ·
        refine ⟨5674192236962312284174715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3782794824641541522783143 5674192236962312284174715)
        ·
          refine ⟨8511288355443468426262073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5674192236962312284174715 8511288355443468426262073)
          ·
            refine ⟨6383466266582601319696555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8511288355443468426262073 6383466266582601319696555)
            ·
              refine ⟨9575199399873901979544833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6383466266582601319696555 9575199399873901979544833)
              ·
                refine ⟨7181399549905426484658625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9575199399873901979544833 7181399549905426484658625)
                ·
                  refine ⟨5386049662429069863493969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7181399549905426484658625 5386049662429069863493969)
                  ·
                    refine ⟨4039537246821802397620477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5386049662429069863493969 4039537246821802397620477)
                    ·
                      refine ⟨1514826467558175899107679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4039537246821802397620477 1514826467558175899107679)
                      ·
                        rfl

theorem cell23_2950114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_2950114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950114 prefixEnd_2950114 := by exact prefixLift 2950114
  have htrace : WordTrace (prefixWord ++ tailWord_2950114) baseStart_2950114 baseEnd_2950114 := by
    simpa [prefixWord, tailWord_2950114, baseEnd_2950114] using wordTrace_append hprefix tailTrace_2950114
  have hstable : (prefixWord ++ tailWord_2950114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950114).length < 2 ^ (prefixWord ++ tailWord_2950114).sum := by decide
  have hdescent : baseEnd_2950114 < baseStart_2950114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950127 : List Nat := [1, 1, 2, 1, 4, 3, 3, 1, 3, 1, 3]
def baseStart_2950127 : Nat := 118140960795 + 2950127 * 2 ^ 59
def prefixEnd_2950127 : Nat := 4983230072969 + 3 ^ 40 * 2950127 * 2
def baseEnd_2950127 : Nat := 1514833142806684348245119

theorem tailTrace_2950127 : CollatzResearch.WordTrace tailWord_2950127 prefixEnd_2950127 1514833142806684348245119 := by
  unfold tailWord_2950127
  simp only [CollatzResearch.WordTrace]
  refine ⟨107599971383201195423832635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71733314255467463615888423 107599971383201195423832635)
  ·
    refine ⟨161399957074801793135748953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107599971383201195423832635 161399957074801793135748953)
    ·
      refine ⟨121049967806101344851811715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161399957074801793135748953 121049967806101344851811715)
      ·
        refine ⟨181574951709152017277717573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121049967806101344851811715 181574951709152017277717573)
        ·
          refine ⟨34045303445466003239572045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181574951709152017277717573 34045303445466003239572045)
          ·
            refine ⟨12766988792049751214839517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34045303445466003239572045 12766988792049751214839517)
            ·
              refine ⟨4787620797018656705564819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12766988792049751214839517 4787620797018656705564819)
              ·
                refine ⟨7181431195527985058347229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4787620797018656705564819 7181431195527985058347229)
                ·
                  refine ⟨2693036698322994396880211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7181431195527985058347229 2693036698322994396880211)
                  ·
                    refine ⟨4039555047484491595320317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2693036698322994396880211 4039555047484491595320317)
                    ·
                      refine ⟨1514833142806684348245119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4039555047484491595320317 1514833142806684348245119)
                      ·
                        rfl

theorem cell23_2950127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 1, 3].length) (baseStart_2950127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950127 prefixEnd_2950127 := by exact prefixLift 2950127
  have htrace : WordTrace (prefixWord ++ tailWord_2950127) baseStart_2950127 baseEnd_2950127 := by
    simpa [prefixWord, tailWord_2950127, baseEnd_2950127] using wordTrace_append hprefix tailTrace_2950127
  have hstable : (prefixWord ++ tailWord_2950127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950127).length < 2 ^ (prefixWord ++ tailWord_2950127).sum := by decide
  have hdescent : baseEnd_2950127 < baseStart_2950127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950134 : List Nat := [5, 1, 1, 1, 3, 3, 2, 1, 6]
def baseStart_2950134 : Nat := 118140960795 + 2950134 * 2 ^ 59
def prefixEnd_2950134 : Nat := 4983230072969 + 3 ^ 40 * 2950134 * 2
def baseEnd_2950134 : Nat := 168315193019029535650843

theorem tailTrace_2950134 : CollatzResearch.WordTrace tailWord_2950134 prefixEnd_2950134 168315193019029535650843 := by
  unfold tailWord_2950134
  simp only [CollatzResearch.WordTrace]
  refine ⟨6725014168385989726208591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71733484462783890412891637 6725014168385989726208591)
  ·
    refine ⟨10087521252578984589312887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6725014168385989726208591 10087521252578984589312887)
    ·
      refine ⟨15131281878868476883969331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10087521252578984589312887 15131281878868476883969331)
      ·
        refine ⟨22696922818302715325953997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15131281878868476883969331 22696922818302715325953997)
        ·
          refine ⟨8511346056863518247232749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22696922818302715325953997 8511346056863518247232749)
          ·
            refine ⟨3191754771323819342712281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8511346056863518247232749 3191754771323819342712281)
            ·
              refine ⟨2393816078492864507034211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3191754771323819342712281 2393816078492864507034211)
              ·
                refine ⟨3590724117739296760551317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2393816078492864507034211 3590724117739296760551317)
                ·
                  refine ⟨168315193019029535650843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3590724117739296760551317 168315193019029535650843)
                  ·
                    rfl

theorem cell23_2950134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_2950134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950134 prefixEnd_2950134 := by exact prefixLift 2950134
  have htrace : WordTrace (prefixWord ++ tailWord_2950134) baseStart_2950134 baseEnd_2950134 := by
    simpa [prefixWord, tailWord_2950134, baseEnd_2950134] using wordTrace_append hprefix tailTrace_2950134
  have hstable : (prefixWord ++ tailWord_2950134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950134).length < 2 ^ (prefixWord ++ tailWord_2950134).sum := by decide
  have hdescent : baseEnd_2950134 < baseStart_2950134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950153 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 3, 1, 5]
def baseStart_2950153 : Nat := 118140960795 + 2950153 * 2 ^ 59
def prefixEnd_2950153 : Nat := 4983230072969 + 3 ^ 40 * 2950153 * 2
def baseEnd_2950153 : Nat := 1514846493303701246519999

theorem tailTrace_2950153 : CollatzResearch.WordTrace tailWord_2950153 prefixEnd_2950153 1514846493303701246519999 := by
  unfold tailWord_2950153
  simp only [CollatzResearch.WordTrace]
  refine ⟨107600919681107001864279113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71733946454071334576186075 107600919681107001864279113)
  ·
    refine ⟨80700689760830251398209335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107600919681107001864279113 80700689760830251398209335)
    ·
      refine ⟨121051034641245377097314003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80700689760830251398209335 121051034641245377097314003)
      ·
        refine ⟨181576551961868065645971005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121051034641245377097314003 181576551961868065645971005)
        ·
          refine ⟨68091206985700524617239127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181576551961868065645971005 68091206985700524617239127)
          ·
            refine ⟨102136810478550786925858691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68091206985700524617239127 102136810478550786925858691)
            ·
              refine ⟨153205215717826180388788037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102136810478550786925858691 153205215717826180388788037)
              ·
                refine ⟨28725977947092408822897757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153205215717826180388788037 28725977947092408822897757)
                ·
                  refine ⟨10772241730159653308586659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28725977947092408822897757 10772241730159653308586659)
                  ·
                    refine ⟨16158362595239479962879989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10772241730159653308586659 16158362595239479962879989)
                    ·
                      refine ⟨1514846493303701246519999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16158362595239479962879989 1514846493303701246519999)
                      ·
                        rfl

theorem cell23_2950153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 1, 5].length) (baseStart_2950153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950153 prefixEnd_2950153 := by exact prefixLift 2950153
  have htrace : WordTrace (prefixWord ++ tailWord_2950153) baseStart_2950153 baseEnd_2950153 := by
    simpa [prefixWord, tailWord_2950153, baseEnd_2950153] using wordTrace_append hprefix tailTrace_2950153
  have hstable : (prefixWord ++ tailWord_2950153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950153).length < 2 ^ (prefixWord ++ tailWord_2950153).sum := by decide
  have hdescent : baseEnd_2950153 < baseStart_2950153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950154 : List Nat := [3, 1, 2, 2, 3, 2, 2, 1, 2, 3, 2]
def baseStart_2950154 : Nat := 118140960795 + 2950154 * 2 ^ 59
def prefixEnd_2950154 : Nat := 4983230072969 + 3 ^ 40 * 2950154 * 2
def baseEnd_2950154 : Nat := 1514847006784355742607495

theorem tailTrace_2950154 : CollatzResearch.WordTrace tailWord_2950154 prefixEnd_2950154 1514847006784355742607495 := by
  unfold tailWord_2950154
  simp only [CollatzResearch.WordTrace]
  refine ⟨26900239038525844758766379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71733970769402252690043677 26900239038525844758766379)
  ·
    refine ⟨40350358557788767138149569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26900239038525844758766379 40350358557788767138149569)
    ·
      refine ⟨30262768918341575353612177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40350358557788767138149569 30262768918341575353612177)
      ·
        refine ⟨22697076688756181515209133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30262768918341575353612177 22697076688756181515209133)
        ·
          refine ⟨8511403758283568068203425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22697076688756181515209133 8511403758283568068203425)
          ·
            refine ⟨6383552818712676051152569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8511403758283568068203425 6383552818712676051152569)
            ·
              refine ⟨4787664614034507038364427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6383552818712676051152569 4787664614034507038364427)
              ·
                refine ⟨7181496921051760557546641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4787664614034507038364427 7181496921051760557546641)
                ·
                  refine ⟨5386122690788820418159981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7181496921051760557546641 5386122690788820418159981)
                  ·
                    refine ⟨2019796009045807656809993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5386122690788820418159981 2019796009045807656809993)
                    ·
                      refine ⟨1514847006784355742607495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2019796009045807656809993 1514847006784355742607495)
                      ·
                        rfl

theorem cell23_2950154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_2950154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950154 prefixEnd_2950154 := by exact prefixLift 2950154
  have htrace : WordTrace (prefixWord ++ tailWord_2950154) baseStart_2950154 baseEnd_2950154 := by
    simpa [prefixWord, tailWord_2950154, baseEnd_2950154] using wordTrace_append hprefix tailTrace_2950154
  have hstable : (prefixWord ++ tailWord_2950154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950154).length < 2 ^ (prefixWord ++ tailWord_2950154).sum := by decide
  have hdescent : baseEnd_2950154 < baseStart_2950154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950173 : List Nat := [1, 4, 2, 2, 14]
def baseStart_2950173 : Nat := 118140960795 + 2950173 * 2 ^ 59
def prefixEnd_2950173 : Nat := 4983230072969 + 3 ^ 40 * 2950173 * 2
def baseEnd_2950173 : Nat := 2077992816072415868683

theorem tailTrace_2950173 : CollatzResearch.WordTrace tailWord_2950173 prefixEnd_2950173 2077992816072415868683 := by
  unfold tailWord_2950173
  simp only [CollatzResearch.WordTrace]
  refine ⟨107601649141034545280007173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71734432760689696853338115 107601649141034545280007173)
  ·
    refine ⟨20175309213943977240001345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107601649141034545280007173 20175309213943977240001345)
    ·
      refine ⟨15131481910457982930001009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20175309213943977240001345 15131481910457982930001009)
      ·
        refine ⟨11348611432843487197500757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15131481910457982930001009 11348611432843487197500757)
        ·
          refine ⟨2077992816072415868683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 11348611432843487197500757 2077992816072415868683)
          ·
            rfl

theorem cell23_2950173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 14].length) (baseStart_2950173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950173 prefixEnd_2950173 := by exact prefixLift 2950173
  have htrace : WordTrace (prefixWord ++ tailWord_2950173) baseStart_2950173 baseEnd_2950173 := by
    simpa [prefixWord, tailWord_2950173, baseEnd_2950173] using wordTrace_append hprefix tailTrace_2950173
  have hstable : (prefixWord ++ tailWord_2950173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950173).length < 2 ^ (prefixWord ++ tailWord_2950173).sum := by decide
  have hdescent : baseEnd_2950173 < baseStart_2950173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950177 : List Nat := [1, 2, 3, 2, 3, 1, 1, 4, 2, 4]
def baseStart_2950177 : Nat := 118140960795 + 2950177 * 2 ^ 59
def prefixEnd_2950177 : Nat := 4983230072969 + 3 ^ 40 * 2950177 * 2
def baseEnd_2950177 : Nat := 504952938946469717539963

theorem tailTrace_2950177 : CollatzResearch.WordTrace tailWord_2950177 prefixEnd_2950177 504952938946469717539963 := by
  unfold tailWord_2950177
  simp only [CollatzResearch.WordTrace]
  refine ⟨107601795033020053963152785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71734530022013369308768523 107601795033020053963152785)
  ·
    refine ⟨80701346274765040472364589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107601795033020053963152785 80701346274765040472364589)
    ·
      refine ⟨30263004853036890177136721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80701346274765040472364589 30263004853036890177136721)
      ·
        refine ⟨22697253639777667632852541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30263004853036890177136721 22697253639777667632852541)
        ·
          refine ⟨8511470114916625362319703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22697253639777667632852541 8511470114916625362319703)
          ·
            refine ⟨12767205172374938043479555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8511470114916625362319703 12767205172374938043479555)
            ·
              refine ⟨19150807758562407065219333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12767205172374938043479555 19150807758562407065219333)
              ·
                refine ⟨3590776454730451324728625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19150807758562407065219333 3590776454730451324728625)
                ·
                  refine ⟨2693082341047838493546469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3590776454730451324728625 2693082341047838493546469)
                  ·
                    refine ⟨504952938946469717539963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2693082341047838493546469 504952938946469717539963)
                    ·
                      rfl

theorem cell23_2950177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_2950177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950177 prefixEnd_2950177 := by exact prefixLift 2950177
  have htrace : WordTrace (prefixWord ++ tailWord_2950177) baseStart_2950177 baseEnd_2950177 := by
    simpa [prefixWord, tailWord_2950177, baseEnd_2950177] using wordTrace_append hprefix tailTrace_2950177
  have hstable : (prefixWord ++ tailWord_2950177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950177).length < 2 ^ (prefixWord ++ tailWord_2950177).sum := by decide
  have hdescent : baseEnd_2950177 < baseStart_2950177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950178 : List Nat := [3, 3, 1, 1, 1, 5, 2, 2, 1, 1, 3]
def baseStart_2950178 : Nat := 118140960795 + 2950178 * 2 ^ 59
def prefixEnd_2950178 : Nat := 4983230072969 + 3 ^ 40 * 2950178 * 2
def baseEnd_2950178 : Nat := 1514859330320063648707385

theorem tailTrace_2950178 : CollatzResearch.WordTrace tailWord_2950178 prefixEnd_2950178 1514859330320063648707385 := by
  unfold tailWord_2950178
  simp only [CollatzResearch.WordTrace]
  refine ⟨26900457876504107783484797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71734554337344287422626125 26900457876504107783484797)
  ·
    refine ⟨10087671703689040418806799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26900457876504107783484797 10087671703689040418806799)
    ·
      refine ⟨15131507555533560628210199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10087671703689040418806799 15131507555533560628210199)
      ·
        refine ⟨22697261333300340942315299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15131507555533560628210199 22697261333300340942315299)
        ·
          refine ⟨34045891999950511413472949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22697261333300340942315299 34045891999950511413472949)
          ·
            refine ⟨3191802374995360445013089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34045891999950511413472949 3191802374995360445013089)
            ·
              refine ⟨2393851781246520333759817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3191802374995360445013089 2393851781246520333759817)
              ·
                refine ⟨1795388835934890250319863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2393851781246520333759817 1795388835934890250319863)
                ·
                  refine ⟨2693083253902335375479795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1795388835934890250319863 2693083253902335375479795)
                  ·
                    refine ⟨4039624880853503063219693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2693083253902335375479795 4039624880853503063219693)
                    ·
                      refine ⟨1514859330320063648707385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4039624880853503063219693 1514859330320063648707385)
                      ·
                        rfl

theorem cell23_2950178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_2950178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950178 prefixEnd_2950178 := by exact prefixLift 2950178
  have htrace : WordTrace (prefixWord ++ tailWord_2950178) baseStart_2950178 baseEnd_2950178 := by
    simpa [prefixWord, tailWord_2950178, baseEnd_2950178] using wordTrace_append hprefix tailTrace_2950178
  have hstable : (prefixWord ++ tailWord_2950178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950178).length < 2 ^ (prefixWord ++ tailWord_2950178).sum := by decide
  have hdescent : baseEnd_2950178 < baseStart_2950178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950214 : List Nat := [6, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_2950214 : Nat := 118140960795 + 2950214 * 2 ^ 59
def prefixEnd_2950214 : Nat := 4983230072969 + 3 ^ 40 * 2950214 * 2
def baseEnd_2950214 : Nat := 1514877815623625507857219

theorem tailTrace_2950214 : CollatzResearch.WordTrace tailWord_2950214 prefixEnd_2950214 1514877815623625507857219 := by
  unfold tailWord_2950214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3362598266683937790070303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71735429689257339521499797 3362598266683937790070303)
  ·
    refine ⟨5043897400025906685105455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3362598266683937790070303 5043897400025906685105455)
    ·
      refine ⟨7565846100038860027658183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5043897400025906685105455 7565846100038860027658183)
      ·
        refine ⟨11348769150058290041487275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7565846100038860027658183 11348769150058290041487275)
        ·
          refine ⟨17023153725087435062230913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11348769150058290041487275 17023153725087435062230913)
          ·
            refine ⟨12767365293815576296673185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17023153725087435062230913 12767365293815576296673185)
            ·
              refine ⟨9575523970361682222504889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12767365293815576296673185 9575523970361682222504889)
              ·
                refine ⟨7181642977771261666878667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9575523970361682222504889 7181642977771261666878667)
                ·
                  refine ⟨10772464466656892500318001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7181642977771261666878667 10772464466656892500318001)
                  ·
                    refine ⟨8079348349992669375238501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10772464466656892500318001 8079348349992669375238501)
                    ·
                      refine ⟨1514877815623625507857219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8079348349992669375238501 1514877815623625507857219)
                      ·
                        rfl

theorem cell23_2950214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_2950214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950214 prefixEnd_2950214 := by exact prefixLift 2950214
  have htrace : WordTrace (prefixWord ++ tailWord_2950214) baseStart_2950214 baseEnd_2950214 := by
    simpa [prefixWord, tailWord_2950214, baseEnd_2950214] using wordTrace_append hprefix tailTrace_2950214
  have hstable : (prefixWord ++ tailWord_2950214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950214).length < 2 ^ (prefixWord ++ tailWord_2950214).sum := by decide
  have hdescent : baseEnd_2950214 < baseStart_2950214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950221 : List Nat := [1, 6, 1, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_2950221 : Nat := 118140960795 + 2950221 * 2 ^ 59
def prefixEnd_2950221 : Nat := 4983230072969 + 3 ^ 40 * 2950221 * 2
def baseEnd_2950221 : Nat := 1514881409988206980469687

theorem tailTrace_2950221 : CollatzResearch.WordTrace tailWord_2950221 prefixEnd_2950221 1514881409988206980469687 := by
  unfold tailWord_2950221
  simp only [CollatzResearch.WordTrace]
  refine ⟨107603399844860649477754517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71735599896573766318503011 107603399844860649477754517)
  ·
    refine ⟨5043909367727842944269743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 107603399844860649477754517 5043909367727842944269743)
    ·
      refine ⟨7565864051591764416404615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5043909367727842944269743 7565864051591764416404615)
      ·
        refine ⟨11348796077387646624606923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7565864051591764416404615 11348796077387646624606923)
        ·
          refine ⟨17023194116081469936910385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11348796077387646624606923 17023194116081469936910385)
          ·
            refine ⟨12767395587061102452682789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17023194116081469936910385 12767395587061102452682789)
            ·
              refine ⟨2393886672573956709878023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12767395587061102452682789 2393886672573956709878023)
              ·
                refine ⟨3590830008860935064817035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2393886672573956709878023 3590830008860935064817035)
                ·
                  refine ⟨5386245013291402597225553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3590830008860935064817035 5386245013291402597225553)
                  ·
                    refine ⟨4039683759968551947919165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5386245013291402597225553 4039683759968551947919165)
                    ·
                      refine ⟨1514881409988206980469687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4039683759968551947919165 1514881409988206980469687)
                      ·
                        rfl

theorem cell23_2950221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_2950221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950221 prefixEnd_2950221 := by exact prefixLift 2950221
  have htrace : WordTrace (prefixWord ++ tailWord_2950221) baseStart_2950221 baseEnd_2950221 := by
    simpa [prefixWord, tailWord_2950221, baseEnd_2950221] using wordTrace_append hprefix tailTrace_2950221
  have hstable : (prefixWord ++ tailWord_2950221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950221).length < 2 ^ (prefixWord ++ tailWord_2950221).sum := by decide
  have hdescent : baseEnd_2950221 < baseStart_2950221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950257 : List Nat := [1, 2, 2, 2, 1, 1, 2, 5, 1, 4, 2]
def baseStart_2950257 : Nat := 118140960795 + 2950257 * 2 ^ 59
def prefixEnd_2950257 : Nat := 4983230072969 + 3 ^ 40 * 2950257 * 2
def baseEnd_2950257 : Nat := 1514899895291768839619521

theorem tailTrace_2950257 : CollatzResearch.WordTrace tailWord_2950257 prefixEnd_2950257 1514899895291768839619521 := by
  unfold tailWord_2950257
  simp only [CollatzResearch.WordTrace]
  refine ⟨107604712872730227626065025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71736475248486818417376683 107604712872730227626065025)
  ·
    refine ⟨80703534654547670719548769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107604712872730227626065025 80703534654547670719548769)
    ·
      refine ⟨60527650990910753039661577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80703534654547670719548769 60527650990910753039661577)
      ·
        refine ⟨45395738243183064779746183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60527650990910753039661577 45395738243183064779746183)
        ·
          refine ⟨68093607364774597169619275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45395738243183064779746183 68093607364774597169619275)
          ·
            refine ⟨102140411047161895754428913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68093607364774597169619275 102140411047161895754428913)
            ·
              refine ⟨76605308285371421815821685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102140411047161895754428913 76605308285371421815821685)
              ·
                refine ⟨7181747651753570795233283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76605308285371421815821685 7181747651753570795233283)
                ·
                  refine ⟨10772621477630356192849925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7181747651753570795233283 10772621477630356192849925)
                  ·
                    refine ⟨2019866527055691786159361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10772621477630356192849925 2019866527055691786159361)
                    ·
                      refine ⟨1514899895291768839619521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2019866527055691786159361 1514899895291768839619521)
                      ·
                        rfl

theorem cell23_2950257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_2950257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950257 prefixEnd_2950257 := by exact prefixLift 2950257
  have htrace : WordTrace (prefixWord ++ tailWord_2950257) baseStart_2950257 baseEnd_2950257 := by
    simpa [prefixWord, tailWord_2950257, baseEnd_2950257] using wordTrace_append hprefix tailTrace_2950257
  have hstable : (prefixWord ++ tailWord_2950257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950257).length < 2 ^ (prefixWord ++ tailWord_2950257).sum := by decide
  have hdescent : baseEnd_2950257 < baseStart_2950257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950277 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 2, 1, 5]
def baseStart_2950277 : Nat := 118140960795 + 2950277 * 2 ^ 59
def prefixEnd_2950277 : Nat := 4983230072969 + 3 ^ 40 * 2950277 * 2
def baseEnd_2950277 : Nat := 1514910164904858761369429

theorem tailTrace_2950277 : CollatzResearch.WordTrace tailWord_2950277 prefixEnd_2950277 1514910164904858761369429 := by
  unfold tailWord_2950277
  simp only [CollatzResearch.WordTrace]
  refine ⟨107605442332657771041793085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71736961555105180694528723 107605442332657771041793085)
  ·
    refine ⟨40352040874746664140672407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107605442332657771041793085 40352040874746664140672407)
    ·
      refine ⟨60528061312119996211008611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40352040874746664140672407 60528061312119996211008611)
      ·
        refine ⟨90792091968179994316512917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60528061312119996211008611 90792091968179994316512917)
        ·
          refine ⟨4255879311008437233586543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90792091968179994316512917 4255879311008437233586543)
          ·
            refine ⟨6383818966512655850379815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4255879311008437233586543 6383818966512655850379815)
            ·
              refine ⟨9575728449768983775569723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6383818966512655850379815 9575728449768983775569723)
              ·
                refine ⟨14363592674653475663354585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9575728449768983775569723 14363592674653475663354585)
                ·
                  refine ⟨10772694505990106747515939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14363592674653475663354585 10772694505990106747515939)
                  ·
                    refine ⟨16159041758985160121273909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10772694505990106747515939 16159041758985160121273909)
                    ·
                      refine ⟨1514910164904858761369429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16159041758985160121273909 1514910164904858761369429)
                      ·
                        rfl

theorem cell23_2950277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_2950277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950277 prefixEnd_2950277 := by exact prefixLift 2950277
  have htrace : WordTrace (prefixWord ++ tailWord_2950277) baseStart_2950277 baseEnd_2950277 := by
    simpa [prefixWord, tailWord_2950277, baseEnd_2950277] using wordTrace_append hprefix tailTrace_2950277
  have hstable : (prefixWord ++ tailWord_2950277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950277).length < 2 ^ (prefixWord ++ tailWord_2950277).sum := by decide
  have hdescent : baseEnd_2950277 < baseStart_2950277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950308 : List Nat := [2, 3, 1, 2, 3, 1, 4, 1, 2, 2, 2]
def baseStart_2950308 : Nat := 118140960795 + 2950308 * 2 ^ 59
def prefixEnd_2950308 : Nat := 4983230072969 + 3 ^ 40 * 2950308 * 2
def baseEnd_2950308 : Nat := 1514926082805148140081787

theorem tailTrace_2950308 : CollatzResearch.WordTrace tailWord_2950308 prefixEnd_2950308 1514926082805148140081787 := by
  unfold tailWord_2950308
  simp only [CollatzResearch.WordTrace]
  refine ⟨53803286497772731668085789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71737715330363642224114385 53803286497772731668085789)
  ·
    refine ⟨20176232436664774375532171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53803286497772731668085789 20176232436664774375532171)
    ·
      refine ⟨30264348654997161563298257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20176232436664774375532171 30264348654997161563298257)
      ·
        refine ⟨22698261491247871172473693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30264348654997161563298257 22698261491247871172473693)
        ·
          refine ⟨8511848059217951689677635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22698261491247871172473693 8511848059217951689677635)
          ·
            refine ⟨12767772088826927534516453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8511848059217951689677635 12767772088826927534516453)
            ·
              refine ⟨2393957266655048912721835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12767772088826927534516453 2393957266655048912721835)
              ·
                refine ⟨3590935899982573369082753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2393957266655048912721835 3590935899982573369082753)
                ·
                  refine ⟨2693201924986930026812065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3590935899982573369082753 2693201924986930026812065)
                  ·
                    refine ⟨2019901443740197520109049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2693201924986930026812065 2019901443740197520109049)
                    ·
                      refine ⟨1514926082805148140081787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2019901443740197520109049 1514926082805148140081787)
                      ·
                        rfl

theorem cell23_2950308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_2950308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950308 prefixEnd_2950308 := by exact prefixLift 2950308
  have htrace : WordTrace (prefixWord ++ tailWord_2950308) baseStart_2950308 baseEnd_2950308 := by
    simpa [prefixWord, tailWord_2950308, baseEnd_2950308] using wordTrace_append hprefix tailTrace_2950308
  have hstable : (prefixWord ++ tailWord_2950308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950308).length < 2 ^ (prefixWord ++ tailWord_2950308).sum := by decide
  have hdescent : baseEnd_2950308 < baseStart_2950308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950327 : List Nat := [1, 1, 3, 1, 4, 1, 4, 1, 2, 5]
def baseStart_2950327 : Nat := 118140960795 + 2950327 * 2 ^ 59
def prefixEnd_2950327 : Nat := 4983230072969 + 3 ^ 40 * 2950327 * 2
def baseEnd_2950327 : Nat := 504978612979194521914733

theorem tailTrace_2950327 : CollatzResearch.WordTrace tailWord_2950327 prefixEnd_2950327 504978612979194521914733 := by
  unfold tailWord_2950327
  simp only [CollatzResearch.WordTrace]
  refine ⟨107607265982476629581113235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71738177321651086387408823 107607265982476629581113235)
  ·
    refine ⟨161410898973714944371669853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107607265982476629581113235 161410898973714944371669853)
    ·
      refine ⟨60529087115143104139376195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161410898973714944371669853 60529087115143104139376195)
      ·
        refine ⟨90793630672714656209064293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60529087115143104139376195 90793630672714656209064293)
        ·
          refine ⟨17023805751133998039199555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90793630672714656209064293 17023805751133998039199555)
          ·
            refine ⟨25535708626700997058799333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17023805751133998039199555 25535708626700997058799333)
            ·
              refine ⟨4787945367506436948524875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25535708626700997058799333 4787945367506436948524875)
              ·
                refine ⟨7181918051259655422787313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4787945367506436948524875 7181918051259655422787313)
                ·
                  refine ⟨5386438538444741567090485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7181918051259655422787313 5386438538444741567090485)
                  ·
                    refine ⟨504978612979194521914733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5386438538444741567090485 504978612979194521914733)
                    ·
                      rfl

theorem cell23_2950327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_2950327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950327 prefixEnd_2950327 := by exact prefixLift 2950327
  have htrace : WordTrace (prefixWord ++ tailWord_2950327) baseStart_2950327 baseEnd_2950327 := by
    simpa [prefixWord, tailWord_2950327, baseEnd_2950327] using wordTrace_append hprefix tailTrace_2950327
  have hstable : (prefixWord ++ tailWord_2950327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950327).length < 2 ^ (prefixWord ++ tailWord_2950327).sum := by decide
  have hdescent : baseEnd_2950327 < baseStart_2950327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950367 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 3]
def baseStart_2950367 : Nat := 118140960795 + 2950367 * 2 ^ 59
def prefixEnd_2950367 : Nat := 4983230072969 + 3 ^ 40 * 2950367 * 2
def baseEnd_2950367 : Nat := 1514956378163763409244015

theorem tailTrace_2950367 : CollatzResearch.WordTrace tailWord_2950367 prefixEnd_2950367 1514956378163763409244015 := by
  unfold tailWord_2950367
  simp only [CollatzResearch.WordTrace]
  refine ⟨107608724902331716412569355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71739149934887810941712903 107608724902331716412569355)
  ·
    refine ⟨161413087353497574618854033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107608724902331716412569355 161413087353497574618854033)
    ·
      refine ⟨121059815515123180964140525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161413087353497574618854033 121059815515123180964140525)
      ·
        refine ⟨45397430818171192861552697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121059815515123180964140525 45397430818171192861552697)
        ·
          refine ⟨34048073113628394646164523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45397430818171192861552697 34048073113628394646164523)
          ·
            refine ⟨51072109670442591969246785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34048073113628394646164523 51072109670442591969246785)
            ·
              refine ⟨38304082252831943976935089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51072109670442591969246785 38304082252831943976935089)
              ·
                refine ⟨28728061689623957982701317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38304082252831943976935089 28728061689623957982701317)
                ·
                  refine ⟨5386511566804492121756497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28728061689623957982701317 5386511566804492121756497)
                  ·
                    refine ⟨4039883675103369091317373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5386511566804492121756497 4039883675103369091317373)
                    ·
                      refine ⟨1514956378163763409244015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4039883675103369091317373 1514956378163763409244015)
                      ·
                        rfl

theorem cell23_2950367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_2950367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950367 prefixEnd_2950367 := by exact prefixLift 2950367
  have htrace : WordTrace (prefixWord ++ tailWord_2950367) baseStart_2950367 baseEnd_2950367 := by
    simpa [prefixWord, tailWord_2950367, baseEnd_2950367] using wordTrace_append hprefix tailTrace_2950367
  have hstable : (prefixWord ++ tailWord_2950367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950367).length < 2 ^ (prefixWord ++ tailWord_2950367).sum := by decide
  have hdescent : baseEnd_2950367 < baseStart_2950367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950381 : List Nat := [1, 5, 1, 2, 2, 3, 1, 1, 2, 1, 4]
def baseStart_2950381 : Nat := 118140960795 + 2950381 * 2 ^ 59
def prefixEnd_2950381 : Nat := 4983230072969 + 3 ^ 40 * 2950381 * 2
def baseEnd_2950381 : Nat := 1514963566892926354468951

theorem tailTrace_2950381 : CollatzResearch.WordTrace tailWord_2950381 prefixEnd_2950381 1514963566892926354468951 := by
  unfold tailWord_2950381
  simp only [CollatzResearch.WordTrace]
  refine ⟨107609235524280996803578997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71739490349520664535719331 107609235524280996803578997)
  ·
    refine ⟨10088365830401343450335531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107609235524280996803578997 10088365830401343450335531)
    ·
      refine ⟨15132548745602015175503297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10088365830401343450335531 15132548745602015175503297)
      ·
        refine ⟨11349411559201511381627473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15132548745602015175503297 11349411559201511381627473)
        ·
          refine ⟨8512058669401133536220605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11349411559201511381627473 8512058669401133536220605)
          ·
            refine ⟨3192022001025425076082727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8512058669401133536220605 3192022001025425076082727)
            ·
              refine ⟨4788033001538137614124091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3192022001025425076082727 4788033001538137614124091)
              ·
                refine ⟨7182049502307206421186137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4788033001538137614124091 7182049502307206421186137)
                ·
                  refine ⟨5386537126730404815889603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7182049502307206421186137 5386537126730404815889603)
                  ·
                    refine ⟨8079805690095607223834405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5386537126730404815889603 8079805690095607223834405)
                    ·
                      refine ⟨1514963566892926354468951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8079805690095607223834405 1514963566892926354468951)
                      ·
                        rfl

theorem cell23_2950381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_2950381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950381 prefixEnd_2950381 := by exact prefixLift 2950381
  have htrace : WordTrace (prefixWord ++ tailWord_2950381) baseStart_2950381 baseEnd_2950381 := by
    simpa [prefixWord, tailWord_2950381, baseEnd_2950381] using wordTrace_append hprefix tailTrace_2950381
  have hstable : (prefixWord ++ tailWord_2950381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950381).length < 2 ^ (prefixWord ++ tailWord_2950381).sum := by decide
  have hdescent : baseEnd_2950381 < baseStart_2950381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950404 : List Nat := [2, 3, 2, 2, 2, 1, 3, 2, 6]
def baseStart_2950404 : Nat := 118140960795 + 2950404 * 2 ^ 59
def prefixEnd_2950404 : Nat := 4983230072969 + 3 ^ 40 * 2950404 * 2
def baseEnd_2950404 : Nat := 168330597438664418275705

theorem tailTrace_2950404 : CollatzResearch.WordTrace tailWord_2950404 prefixEnd_2950404 168330597438664418275705 := by
  unfold tailWord_2950404
  simp only [CollatzResearch.WordTrace]
  refine ⟨53805037201598835865833133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71740049602131781154444177 53805037201598835865833133)
  ·
    refine ⟨20176888950599563449687425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53805037201598835865833133 20176888950599563449687425)
    ·
      refine ⟨15132666712949672587265569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20176888950599563449687425 15132666712949672587265569)
      ·
        refine ⟨11349500034712254440449177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15132666712949672587265569 11349500034712254440449177)
        ·
          refine ⟨8512125026034190830336883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11349500034712254440449177 8512125026034190830336883)
          ·
            refine ⟨12768187539051286245505325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8512125026034190830336883 12768187539051286245505325)
            ·
              refine ⟨4788070327144232342064497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12768187539051286245505325 4788070327144232342064497)
              ·
                refine ⟨3591052745358174256548373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4788070327144232342064497 3591052745358174256548373)
                ·
                  refine ⟨168330597438664418275705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3591052745358174256548373 168330597438664418275705)
                  ·
                    rfl

theorem cell23_2950404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_2950404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950404 prefixEnd_2950404 := by exact prefixLift 2950404
  have htrace : WordTrace (prefixWord ++ tailWord_2950404) baseStart_2950404 baseEnd_2950404 := by
    simpa [prefixWord, tailWord_2950404, baseEnd_2950404] using wordTrace_append hprefix tailTrace_2950404
  have hstable : (prefixWord ++ tailWord_2950404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950404).length < 2 ^ (prefixWord ++ tailWord_2950404).sum := by decide
  have hdescent : baseEnd_2950404 < baseStart_2950404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950424 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 1, 5, 2]
def baseStart_2950424 : Nat := 118140960795 + 2950424 * 2 ^ 59
def prefixEnd_2950424 : Nat := 4983230072969 + 3 ^ 40 * 2950424 * 2
def baseEnd_2950424 : Nat := 1514985646561069686231253

theorem tailTrace_2950424 : CollatzResearch.WordTrace tailWord_2950424 prefixEnd_2950424 1514985646561069686231253 := by
  unfold tailWord_2950424
  simp only [CollatzResearch.WordTrace]
  refine ⟨53805401931562607573697163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71740535908750143431596217 53805401931562607573697163)
  ·
    refine ⟨80708102897343911360545745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53805401931562607573697163 80708102897343911360545745)
    ·
      refine ⟨60531077173007933520409309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80708102897343911360545745 60531077173007933520409309)
      ·
        refine ⟨22699153939877975070153491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60531077173007933520409309 22699153939877975070153491)
        ·
          refine ⟨34048730909816962605230237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22699153939877975070153491 34048730909816962605230237)
          ·
            refine ⟨12768274091181360976961339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34048730909816962605230237 12768274091181360976961339)
            ·
              refine ⟨19152411136772041465442009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12768274091181360976961339 19152411136772041465442009)
              ·
                refine ⟨14364308352579031099081507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19152411136772041465442009 14364308352579031099081507)
                ·
                  refine ⟨21546462528868546648622261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14364308352579031099081507 21546462528868546648622261)
                  ·
                    refine ⟨2019980862081426248308337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21546462528868546648622261 2019980862081426248308337)
                    ·
                      refine ⟨1514985646561069686231253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2019980862081426248308337 1514985646561069686231253)
                      ·
                        rfl

theorem cell23_2950424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_2950424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950424 prefixEnd_2950424 := by exact prefixLift 2950424
  have htrace : WordTrace (prefixWord ++ tailWord_2950424) baseStart_2950424 baseEnd_2950424 := by
    simpa [prefixWord, tailWord_2950424, baseEnd_2950424] using wordTrace_append hprefix tailTrace_2950424
  have hstable : (prefixWord ++ tailWord_2950424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950424).length < 2 ^ (prefixWord ++ tailWord_2950424).sum := by decide
  have hdescent : baseEnd_2950424 < baseStart_2950424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950464 : List Nat := [2, 1, 1, 2, 2, 1, 4, 4, 2, 4]
def baseStart_2950464 : Nat := 118140960795 + 2950464 * 2 ^ 59
def prefixEnd_2950464 : Nat := 4983230072969 + 3 ^ 40 * 2950464 * 2
def baseEnd_2950464 : Nat := 505002061929083176577023

theorem tailTrace_2950464 : CollatzResearch.WordTrace tailWord_2950464 prefixEnd_2950464 505002061929083176577023 := by
  unfold tailWord_2950464
  simp only [CollatzResearch.WordTrace]
  refine ⟨53806131391490150989425223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71741508521986867985900297 53806131391490150989425223)
  ·
    refine ⟨80709197087235226484137835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53806131391490150989425223 80709197087235226484137835)
    ·
      refine ⟨121063795630852839726206753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80709197087235226484137835 121063795630852839726206753)
      ·
        refine ⟨90797846723139629794655065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121063795630852839726206753 90797846723139629794655065)
        ·
          refine ⟨68098385042354722345991299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90797846723139629794655065 68098385042354722345991299)
          ·
            refine ⟨102147577563532083518986949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68098385042354722345991299 102147577563532083518986949)
            ·
              refine ⟨19152670793162265659810053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102147577563532083518986949 19152670793162265659810053)
              ·
                refine ⟨3591125773717924811214385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19152670793162265659810053 3591125773717924811214385)
                ·
                  refine ⟨2693344330288443608410789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3591125773717924811214385 2693344330288443608410789)
                  ·
                    refine ⟨505002061929083176577023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2693344330288443608410789 505002061929083176577023)
                    ·
                      rfl

theorem cell23_2950464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 2, 4].length) (baseStart_2950464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950464 prefixEnd_2950464 := by exact prefixLift 2950464
  have htrace : WordTrace (prefixWord ++ tailWord_2950464) baseStart_2950464 baseEnd_2950464 := by
    simpa [prefixWord, tailWord_2950464, baseEnd_2950464] using wordTrace_append hprefix tailTrace_2950464
  have hstable : (prefixWord ++ tailWord_2950464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950464).length < 2 ^ (prefixWord ++ tailWord_2950464).sum := by decide
  have hdescent : baseEnd_2950464 < baseStart_2950464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950484 : List Nat := [2, 4, 1, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_2950484 : Nat := 118140960795 + 2950484 * 2 ^ 59
def prefixEnd_2950484 : Nat := 4983230072969 + 3 ^ 40 * 2950484 * 2
def baseEnd_2950484 : Nat := 1515016455400339451480977

theorem tailTrace_2950484 : CollatzResearch.WordTrace tailWord_2950484 prefixEnd_2950484 1515016455400339451480977 := by
  unfold tailWord_2950484
  simp only [CollatzResearch.WordTrace]
  refine ⟨53806496121453922697289253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71741994828605230263052337 53806496121453922697289253)
  ·
    refine ⟨10088718022772610505741735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53806496121453922697289253 10088718022772610505741735)
    ·
      refine ⟨15133077034158915758612603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10088718022772610505741735 15133077034158915758612603)
      ·
        refine ⟨22699615551238373637918905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15133077034158915758612603 22699615551238373637918905)
        ·
          refine ⟨17024711663428780228439179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22699615551238373637918905 17024711663428780228439179)
          ·
            refine ⟨25537067495143170342658769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17024711663428780228439179 25537067495143170342658769)
            ·
              refine ⟨19152800621357377756994077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25537067495143170342658769 19152800621357377756994077)
              ·
                refine ⟨7182300233009016658872779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19152800621357377756994077 7182300233009016658872779)
                ·
                  refine ⟨10773450349513524988309169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7182300233009016658872779 10773450349513524988309169)
                  ·
                    refine ⟨8080087762135143741231877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10773450349513524988309169 8080087762135143741231877)
                    ·
                      refine ⟨1515016455400339451480977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8080087762135143741231877 1515016455400339451480977)
                      ·
                        rfl

theorem cell23_2950484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_2950484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950484 prefixEnd_2950484 := by exact prefixLift 2950484
  have htrace : WordTrace (prefixWord ++ tailWord_2950484) baseStart_2950484 baseEnd_2950484 := by
    simpa [prefixWord, tailWord_2950484, baseEnd_2950484] using wordTrace_append hprefix tailTrace_2950484
  have hstable : (prefixWord ++ tailWord_2950484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950484).length < 2 ^ (prefixWord ++ tailWord_2950484).sum := by decide
  have hdescent : baseEnd_2950484 < baseStart_2950484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950508 : List Nat := [2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 3]
def baseStart_2950508 : Nat := 118140960795 + 2950508 * 2 ^ 59
def prefixEnd_2950508 : Nat := 4983230072969 + 3 ^ 40 * 2950508 * 2
def baseEnd_2950508 : Nat := 1515028778936047357580867

theorem tailTrace_2950508 : CollatzResearch.WordTrace tailWord_2950508 prefixEnd_2950508 1515028778936047357580867 := by
  unfold tailWord_2950508
  simp only [CollatzResearch.WordTrace]
  refine ⟨53806933797410448746726089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71742578396547264995634785 53806933797410448746726089)
  ·
    refine ⟨40355200348057836560044567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53806933797410448746726089 40355200348057836560044567)
    ·
      refine ⟨60532800522086754840066851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40355200348057836560044567 60532800522086754840066851)
      ·
        refine ⟨90799200783130132260100277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60532800522086754840066851 90799200783130132260100277)
        ·
          refine ⟨8512425073418449899384401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90799200783130132260100277 8512425073418449899384401)
          ·
            refine ⟨6384318805063837424538301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8512425073418449899384401 6384318805063837424538301)
            ·
              refine ⟨2394119551898939034201863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6384318805063837424538301 2394119551898939034201863)
              ·
                refine ⟨3591179327848408551302795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2394119551898939034201863 3591179327848408551302795)
                ·
                  refine ⟨5386768991772612826954193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3591179327848408551302795 5386768991772612826954193)
                  ·
                    refine ⟨4040076743829459620215645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5386768991772612826954193 4040076743829459620215645)
                    ·
                      refine ⟨1515028778936047357580867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4040076743829459620215645 1515028778936047357580867)
                      ·
                        rfl

theorem cell23_2950508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 3].length) (baseStart_2950508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950508 prefixEnd_2950508 := by exact prefixLift 2950508
  have htrace : WordTrace (prefixWord ++ tailWord_2950508) baseStart_2950508 baseEnd_2950508 := by
    simpa [prefixWord, tailWord_2950508, baseEnd_2950508] using wordTrace_append hprefix tailTrace_2950508
  have hstable : (prefixWord ++ tailWord_2950508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950508).length < 2 ^ (prefixWord ++ tailWord_2950508).sum := by decide
  have hdescent : baseEnd_2950508 < baseStart_2950508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950521 : List Nat := [1, 2, 1, 3, 2, 1, 3, 4, 2, 1, 3]
def baseStart_2950521 : Nat := 118140960795 + 2950521 * 2 ^ 59
def prefixEnd_2950521 : Nat := 4983230072969 + 3 ^ 40 * 2950521 * 2
def baseEnd_2950521 : Nat := 1515035454184555806718307

theorem tailTrace_2950521 : CollatzResearch.WordTrace tailWord_2950521 prefixEnd_2950521 1515035454184555806718307 := by
  unfold tailWord_2950521
  simp only [CollatzResearch.WordTrace]
  refine ⟨107614341743773800713675417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71742894495849200475783611 107614341743773800713675417)
  ·
    refine ⟨80710756307830350535256563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107614341743773800713675417 80710756307830350535256563)
    ·
      refine ⟨121066134461745525802884845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80710756307830350535256563 121066134461745525802884845)
      ·
        refine ⟨45399800423154572176081817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121066134461745525802884845 45399800423154572176081817)
        ·
          refine ⟨34049850317365929132061363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45399800423154572176081817 34049850317365929132061363)
          ·
            refine ⟨51074775476048893698092045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34049850317365929132061363 51074775476048893698092045)
            ·
              refine ⟨19153040803518335136784517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51074775476048893698092045 19153040803518335136784517)
              ·
                refine ⟨3591195150659687838147097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19153040803518335136784517 3591195150659687838147097)
                ·
                  refine ⟨2693396362994765878610323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3591195150659687838147097 2693396362994765878610323)
                  ·
                    refine ⟨4040094544492148817915485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2693396362994765878610323 4040094544492148817915485)
                    ·
                      refine ⟨1515035454184555806718307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4040094544492148817915485 1515035454184555806718307)
                      ·
                        rfl

theorem cell23_2950521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_2950521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950521 prefixEnd_2950521 := by exact prefixLift 2950521
  have htrace : WordTrace (prefixWord ++ tailWord_2950521) baseStart_2950521 baseEnd_2950521 := by
    simpa [prefixWord, tailWord_2950521, baseEnd_2950521] using wordTrace_append hprefix tailTrace_2950521
  have hstable : (prefixWord ++ tailWord_2950521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950521).length < 2 ^ (prefixWord ++ tailWord_2950521).sum := by decide
  have hdescent : baseEnd_2950521 < baseStart_2950521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950531 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 3, 3, 2]
def baseStart_2950531 : Nat := 118140960795 + 2950531 * 2 ^ 59
def prefixEnd_2950531 : Nat := 4983230072969 + 3 ^ 40 * 2950531 * 2
def baseEnd_2950531 : Nat := 1515040588991100767593261

theorem tailTrace_2950531 : CollatzResearch.WordTrace tailWord_2950531 prefixEnd_2950531 1515040588991100767593261 := by
  unfold tailWord_2950531
  simp only [CollatzResearch.WordTrace]
  refine ⟨107614706473737572421539447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71743137649158381614359631 107614706473737572421539447)
  ·
    refine ⟨161422059710606358632309171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107614706473737572421539447 161422059710606358632309171)
    ·
      refine ⟨242133089565909537948463757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161422059710606358632309171 242133089565909537948463757)
      ·
        refine ⟨90799908587216076730673909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242133089565909537948463757 90799908587216076730673909)
        ·
          refine ⟨8512491430051507193500679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90799908587216076730673909 8512491430051507193500679)
          ·
            refine ⟨12768737145077260790251019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8512491430051507193500679 12768737145077260790251019)
            ·
              refine ⟨19153105717615891185376529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12768737145077260790251019 19153105717615891185376529)
              ·
                refine ⟨14364829288211918389032397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19153105717615891185376529 14364829288211918389032397)
                ·
                  refine ⟨5386810983079469395887149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14364829288211918389032397 5386810983079469395887149)
                  ·
                    refine ⟨2020054118654801023457681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5386810983079469395887149 2020054118654801023457681)
                    ·
                      refine ⟨1515040588991100767593261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2020054118654801023457681 1515040588991100767593261)
                      ·
                        rfl

theorem cell23_2950531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 3, 2].length) (baseStart_2950531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950531 prefixEnd_2950531 := by exact prefixLift 2950531
  have htrace : WordTrace (prefixWord ++ tailWord_2950531) baseStart_2950531 baseEnd_2950531 := by
    simpa [prefixWord, tailWord_2950531, baseEnd_2950531] using wordTrace_append hprefix tailTrace_2950531
  have hstable : (prefixWord ++ tailWord_2950531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950531).length < 2 ^ (prefixWord ++ tailWord_2950531).sum := by decide
  have hdescent : baseEnd_2950531 < baseStart_2950531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950548 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_2950548 : Nat := 118140960795 + 2950548 * 2 ^ 59
def prefixEnd_2950548 : Nat := 4983230072969 + 3 ^ 40 * 2950548 * 2
def baseEnd_2950548 : Nat := 1515049318162227201080683

theorem tailTrace_2950548 : CollatzResearch.WordTrace tailWord_2950548 prefixEnd_2950548 1515049318162227201080683 := by
  unfold tailWord_2950548
  simp only [CollatzResearch.WordTrace]
  refine ⟨53807663257337992162454149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71743551009783989549938865 53807663257337992162454149)
  ·
    refine ⟨10088936860750873530460153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53807663257337992162454149 10088936860750873530460153)
    ·
      refine ⟨7566702645563155147845115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10088936860750873530460153 7566702645563155147845115)
      ·
        refine ⟨11350053968344732721767673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7566702645563155147845115 11350053968344732721767673)
        ·
          refine ⟨8512540476258549541325755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11350053968344732721767673 8512540476258549541325755)
          ·
            refine ⟨12768810714387824311988633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8512540476258549541325755 12768810714387824311988633)
            ·
              refine ⟨9576608035790868233991475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12768810714387824311988633 9576608035790868233991475)
              ·
                refine ⟨14364912053686302350987213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9576608035790868233991475 14364912053686302350987213)
                ·
                  refine ⟨5386842020132363381620205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14364912053686302350987213 5386842020132363381620205)
                  ·
                    refine ⟨2020065757549636268107577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5386842020132363381620205 2020065757549636268107577)
                    ·
                      refine ⟨1515049318162227201080683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2020065757549636268107577 1515049318162227201080683)
                      ·
                        rfl

theorem cell23_2950548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_2950548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950548 prefixEnd_2950548 := by exact prefixLift 2950548
  have htrace : WordTrace (prefixWord ++ tailWord_2950548) baseStart_2950548 baseEnd_2950548 := by
    simpa [prefixWord, tailWord_2950548, baseEnd_2950548] using wordTrace_append hprefix tailTrace_2950548
  have hstable : (prefixWord ++ tailWord_2950548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950548).length < 2 ^ (prefixWord ++ tailWord_2950548).sum := by decide
  have hdescent : baseEnd_2950548 < baseStart_2950548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950578 : List Nat := [3, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2]
def baseStart_2950578 : Nat := 118140960795 + 2950578 * 2 ^ 59
def prefixEnd_2950578 : Nat := 4983230072969 + 3 ^ 40 * 2950578 * 2
def baseEnd_2950578 : Nat := 1515064722581862083705545

theorem tailTrace_2950578 : CollatzResearch.WordTrace tailWord_2950578 prefixEnd_2950578 1515064722581862083705545 := by
  unfold tailWord_2950578
  simp only [CollatzResearch.WordTrace]
  refine ⟨26904105176141824862125097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71744280469711532965666925 26904105176141824862125097)
  ·
    refine ⟨20178078882106368646593823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26904105176141824862125097 20178078882106368646593823)
    ·
      refine ⟨30267118323159552969890735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20178078882106368646593823 30267118323159552969890735)
      ·
        refine ⟨45400677484739329454836103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30267118323159552969890735 45400677484739329454836103)
        ·
          refine ⟨68101016227108994182254155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45400677484739329454836103 68101016227108994182254155)
          ·
            refine ⟨102151524340663491273381233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68101016227108994182254155 102151524340663491273381233)
            ·
              refine ⟨76613643255497618455035925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102151524340663491273381233 76613643255497618455035925)
              ·
                refine ⟨3591264527601450865079809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76613643255497618455035925 3591264527601450865079809)
                ·
                  refine ⟨2693448395701088148809857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3591264527601450865079809 2693448395701088148809857)
                  ·
                    refine ⟨2020086296775816111607393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2693448395701088148809857 2020086296775816111607393)
                    ·
                      refine ⟨1515064722581862083705545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2020086296775816111607393 1515064722581862083705545)
                      ·
                        rfl

theorem cell23_2950578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_2950578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950578 prefixEnd_2950578 := by exact prefixLift 2950578
  have htrace : WordTrace (prefixWord ++ tailWord_2950578) baseStart_2950578 baseEnd_2950578 := by
    simpa [prefixWord, tailWord_2950578, baseEnd_2950578] using wordTrace_append hprefix tailTrace_2950578
  have hstable : (prefixWord ++ tailWord_2950578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950578).length < 2 ^ (prefixWord ++ tailWord_2950578).sum := by decide
  have hdescent : baseEnd_2950578 < baseStart_2950578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950618 : List Nat := [3, 1, 1, 2, 3, 4, 1, 3, 5]
def baseStart_2950618 : Nat := 118140960795 + 2950618 * 2 ^ 59
def prefixEnd_2950618 : Nat := 4983230072969 + 3 ^ 40 * 2950618 * 2
def baseEnd_2950618 : Nat := 168342806867560214133929

theorem tailTrace_2950618 : CollatzResearch.WordTrace tailWord_2950618 prefixEnd_2950618 168342806867560214133929 := by
  unfold tailWord_2950618
  simp only [CollatzResearch.WordTrace]
  refine ⟨26904469906105596569989127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71745253082948257519971005 26904469906105596569989127)
  ·
    refine ⟨40356704859158394854983691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26904469906105596569989127 40356704859158394854983691)
    ·
      refine ⟨60535057288737592282475537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40356704859158394854983691 60535057288737592282475537)
      ·
        refine ⟨45401292966553194211856653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60535057288737592282475537 45401292966553194211856653)
        ·
          refine ⟨17025484862457447829446245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45401292966553194211856653 17025484862457447829446245)
          ·
            refine ⟨3192278411710771468021171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17025484862457447829446245 3192278411710771468021171)
            ·
              refine ⟨4788417617566157202031757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3192278411710771468021171 4788417617566157202031757)
              ·
                refine ⟨1795656606587308950761909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4788417617566157202031757 1795656606587308950761909)
                ·
                  refine ⟨168342806867560214133929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1795656606587308950761909 168342806867560214133929)
                  ·
                    rfl

theorem cell23_2950618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 5].length) (baseStart_2950618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950618 prefixEnd_2950618 := by exact prefixLift 2950618
  have htrace : WordTrace (prefixWord ++ tailWord_2950618) baseStart_2950618 baseEnd_2950618 := by
    simpa [prefixWord, tailWord_2950618, baseEnd_2950618] using wordTrace_append hprefix tailTrace_2950618
  have hstable : (prefixWord ++ tailWord_2950618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950618).length < 2 ^ (prefixWord ++ tailWord_2950618).sum := by decide
  have hdescent : baseEnd_2950618 < baseStart_2950618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950631 : List Nat := [1, 1, 5, 2, 1, 3, 1, 2, 2, 5]
def baseStart_2950631 : Nat := 118140960795 + 2950631 * 2 ^ 59
def prefixEnd_2950631 : Nat := 4983230072969 + 3 ^ 40 * 2950631 * 2
def baseEnd_2950631 : Nat := 505030645685516792114267

theorem tailTrace_2950631 : CollatzResearch.WordTrace tailWord_2950631 prefixEnd_2950631 505030645685516792114267 := by
  unfold tailWord_2950631
  simp only [CollatzResearch.WordTrace]
  refine ⟨107618353773375289500179747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71745569182250193000119831 107618353773375289500179747)
  ·
    refine ⟨161427530660062934250269621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107618353773375289500179747 161427530660062934250269621)
    ·
      refine ⟨15133830999380900085962777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161427530660062934250269621 15133830999380900085962777)
      ·
        refine ⟨11350373249535675064472083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15133830999380900085962777 11350373249535675064472083)
        ·
          refine ⟨17025559874303512596708125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11350373249535675064472083 17025559874303512596708125)
          ·
            refine ⟨6384584952863817223765547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17025559874303512596708125 6384584952863817223765547)
            ·
              refine ⟨9576877429295725835648321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6384584952863817223765547 9576877429295725835648321)
              ·
                refine ⟨7182658071971794376736241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9576877429295725835648321 7182658071971794376736241)
                ·
                  refine ⟨5386993553978845782552181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7182658071971794376736241 5386993553978845782552181)
                  ·
                    refine ⟨505030645685516792114267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5386993553978845782552181 505030645685516792114267)
                    ·
                      rfl

theorem cell23_2950631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_2950631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950631 prefixEnd_2950631 := by exact prefixLift 2950631
  have htrace : WordTrace (prefixWord ++ tailWord_2950631) baseStart_2950631 baseEnd_2950631 := by
    simpa [prefixWord, tailWord_2950631, baseEnd_2950631] using wordTrace_append hprefix tailTrace_2950631
  have hstable : (prefixWord ++ tailWord_2950631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950631).length < 2 ^ (prefixWord ++ tailWord_2950631).sum := by decide
  have hdescent : baseEnd_2950631 < baseStart_2950631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950664 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_2950664 : Nat := 118140960795 + 2950664 * 2 ^ 59
def prefixEnd_2950664 : Nat := 4983230072969 + 3 ^ 40 * 2950664 * 2
def baseEnd_2950664 : Nat := 1515108881918148747230149

theorem tailTrace_2950664 : CollatzResearch.WordTrace tailWord_2950664 prefixEnd_2950664 1515108881918148747230149 := by
  unfold tailWord_2950664
  simp only [CollatzResearch.WordTrace]
  refine ⟨53809778691127868068065523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71746371588170490757420697 53809778691127868068065523)
  ·
    refine ⟨80714668036691802102098285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53809778691127868068065523 80714668036691802102098285)
    ·
      refine ⟨30268000513759425788286857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80714668036691802102098285 30268000513759425788286857)
      ·
        refine ⟨22701000385319569341215143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30268000513759425788286857 22701000385319569341215143)
        ·
          refine ⟨34051500577979354011822715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22701000385319569341215143 34051500577979354011822715)
          ·
            refine ⟨51077250866969031017734073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34051500577979354011822715 51077250866969031017734073)
            ·
              refine ⟨38307938150226773263300555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51077250866969031017734073 38307938150226773263300555)
              ·
                refine ⟨57461907225340159894950833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38307938150226773263300555 57461907225340159894950833)
                ·
                  refine ⟨43096430419005119921213125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57461907225340159894950833 43096430419005119921213125)
                  ·
                    refine ⟨8080580703563459985227461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43096430419005119921213125 8080580703563459985227461)
                    ·
                      refine ⟨1515108881918148747230149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8080580703563459985227461 1515108881918148747230149)
                      ·
                        rfl

theorem cell23_2950664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_2950664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950664 prefixEnd_2950664 := by exact prefixLift 2950664
  have htrace : WordTrace (prefixWord ++ tailWord_2950664) baseStart_2950664 baseEnd_2950664 := by
    simpa [prefixWord, tailWord_2950664, baseEnd_2950664] using wordTrace_append hprefix tailTrace_2950664
  have hstable : (prefixWord ++ tailWord_2950664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950664).length < 2 ^ (prefixWord ++ tailWord_2950664).sum := by decide
  have hdescent : baseEnd_2950664 < baseStart_2950664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950668 : List Nat := [2, 2, 1, 2, 5, 1, 2, 1, 2, 1, 4]
def baseStart_2950668 : Nat := 118140960795 + 2950668 * 2 ^ 59
def prefixEnd_2950668 : Nat := 4983230072969 + 3 ^ 40 * 2950668 * 2
def baseEnd_2950668 : Nat := 1515110935840766731580131

theorem tailTrace_2950668 : CollatzResearch.WordTrace tailWord_2950668 prefixEnd_2950668 1515110935840766731580131 := by
  unfold tailWord_2950668
  simp only [CollatzResearch.WordTrace]
  refine ⟨53809851637120622409638329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71746468849494163212851105 53809851637120622409638329)
  ·
    refine ⟨40357388727840466807228747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53809851637120622409638329 40357388727840466807228747)
    ·
      refine ⟨60536083091760700210843121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40357388727840466807228747 60536083091760700210843121)
      ·
        refine ⟨45402062318820525158132341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60536083091760700210843121 45402062318820525158132341)
        ·
          refine ⟨4256443342389424233574907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45402062318820525158132341 4256443342389424233574907)
          ·
            refine ⟨6384665013584136350362361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4256443342389424233574907 6384665013584136350362361)
            ·
              refine ⟨4788498760188102262771771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6384665013584136350362361 4788498760188102262771771)
              ·
                refine ⟨7182748140282153394157657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4788498760188102262771771 7182748140282153394157657)
                ·
                  refine ⟨5387061105211615045618243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7182748140282153394157657 5387061105211615045618243)
                  ·
                    refine ⟨8080591657817422568427365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5387061105211615045618243 8080591657817422568427365)
                    ·
                      refine ⟨1515110935840766731580131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8080591657817422568427365 1515110935840766731580131)
                      ·
                        rfl

theorem cell23_2950668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_2950668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950668 prefixEnd_2950668 := by exact prefixLift 2950668
  have htrace : WordTrace (prefixWord ++ tailWord_2950668) baseStart_2950668 baseEnd_2950668 := by
    simpa [prefixWord, tailWord_2950668, baseEnd_2950668] using wordTrace_append hprefix tailTrace_2950668
  have hstable : (prefixWord ++ tailWord_2950668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950668).length < 2 ^ (prefixWord ++ tailWord_2950668).sum := by decide
  have hdescent : baseEnd_2950668 < baseStart_2950668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950686 : List Nat := [4, 3, 3, 1, 1, 2, 2, 2, 5]
def baseStart_2950686 : Nat := 118140960795 + 2950686 * 2 ^ 59
def prefixEnd_2950686 : Nat := 4983230072969 + 3 ^ 40 * 2950686 * 2
def baseEnd_2950686 : Nat := 168346686499171962350561

theorem tailTrace_2950686 : CollatzResearch.WordTrace tailWord_2950686 prefixEnd_2950686 168346686499171962350561 := by
  unfold tailWord_2950686
  simp only [CollatzResearch.WordTrace]
  refine ⟨13452544973522004236678989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71746906525450689262287941 13452544973522004236678989)
  ·
    refine ⟨5044704365070751588754621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13452544973522004236678989 5044704365070751588754621)
    ·
      refine ⟨1891764136901531845782983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5044704365070751588754621 1891764136901531845782983)
      ·
        refine ⟨2837646205352297768674475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1891764136901531845782983 2837646205352297768674475)
        ·
          refine ⟨4256469308028446653011713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2837646205352297768674475 4256469308028446653011713)
          ·
            refine ⟨3192351981021334989758785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4256469308028446653011713 3192351981021334989758785)
            ·
              refine ⟨2394263985766001242319089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3192351981021334989758785 2394263985766001242319089)
              ·
                refine ⟨1795697989324500931739317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2394263985766001242319089 1795697989324500931739317)
                ·
                  refine ⟨168346686499171962350561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1795697989324500931739317 168346686499171962350561)
                  ·
                    rfl

theorem cell23_2950686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_2950686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950686 prefixEnd_2950686 := by exact prefixLift 2950686
  have htrace : WordTrace (prefixWord ++ tailWord_2950686) baseStart_2950686 baseEnd_2950686 := by
    simpa [prefixWord, tailWord_2950686, baseEnd_2950686] using wordTrace_append hprefix tailTrace_2950686
  have hstable : (prefixWord ++ tailWord_2950686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950686).length < 2 ^ (prefixWord ++ tailWord_2950686).sum := by decide
  have hdescent : baseEnd_2950686 < baseStart_2950686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950688 : List Nat := [2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 3]
def baseStart_2950688 : Nat := 118140960795 + 2950688 * 2 ^ 59
def prefixEnd_2950688 : Nat := 4983230072969 + 3 ^ 40 * 2950688 * 2
def baseEnd_2950688 : Nat := 1515121205453856653330039

theorem tailTrace_2950688 : CollatzResearch.WordTrace tailWord_2950688 prefixEnd_2950688 1515121205453856653330039 := by
  unfold tailWord_2950688
  simp only [CollatzResearch.WordTrace]
  refine ⟨53810216367084394117502359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71746955156112525490003145 53810216367084394117502359)
  ·
    refine ⟨80715324550626591176253539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53810216367084394117502359 80715324550626591176253539)
    ·
      refine ⟨121072986825939886764380309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80715324550626591176253539 121072986825939886764380309)
      ·
        refine ⟨5675296257465932192080327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 121072986825939886764380309 5675296257465932192080327)
        ·
          refine ⟨8512944386198898288120491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5675296257465932192080327 8512944386198898288120491)
          ·
            refine ⟨12769416579298347432180737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8512944386198898288120491 12769416579298347432180737)
            ·
              refine ⟨9577062434473760574135553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12769416579298347432180737 9577062434473760574135553)
              ·
                refine ⟨7182796825855320430601665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9577062434473760574135553 7182796825855320430601665)
                ·
                  refine ⟨5387097619391490322951249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7182796825855320430601665 5387097619391490322951249)
                  ·
                    refine ⟨4040323214543617742213437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5387097619391490322951249 4040323214543617742213437)
                    ·
                      refine ⟨1515121205453856653330039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4040323214543617742213437 1515121205453856653330039)
                      ·
                        rfl

theorem cell23_2950688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_2950688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950688 prefixEnd_2950688 := by exact prefixLift 2950688
  have htrace : WordTrace (prefixWord ++ tailWord_2950688) baseStart_2950688 baseEnd_2950688 := by
    simpa [prefixWord, tailWord_2950688, baseEnd_2950688] using wordTrace_append hprefix tailTrace_2950688
  have hstable : (prefixWord ++ tailWord_2950688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950688).length < 2 ^ (prefixWord ++ tailWord_2950688).sum := by decide
  have hdescent : baseEnd_2950688 < baseStart_2950688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950714 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7]
def baseStart_2950714 : Nat := 118140960795 + 2950714 * 2 ^ 59
def prefixEnd_2950714 : Nat := 4983230072969 + 3 ^ 40 * 2950714 * 2
def baseEnd_2950714 : Nat := 1515134555950873551604919

theorem tailTrace_2950714 : CollatzResearch.WordTrace tailWord_2950714 prefixEnd_2950714 1515134555950873551604919 := by
  unfold tailWord_2950714
  simp only [CollatzResearch.WordTrace]
  refine ⟨26905345258018648668862799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71747587354716396450300797 26905345258018648668862799)
  ·
    refine ⟨40358017887027973003294199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26905345258018648668862799 40358017887027973003294199)
    ·
      refine ⟨60537026830541959504941299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40358017887027973003294199 60537026830541959504941299)
      ·
        refine ⟨90805540245812939257411949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60537026830541959504941299 90805540245812939257411949)
        ·
          refine ⟨34052077592179852221529481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90805540245812939257411949 34052077592179852221529481)
          ·
            refine ⟨25539058194134889166147111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34052077592179852221529481 25539058194134889166147111)
            ·
              refine ⟨38308587291202333749220667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25539058194134889166147111 38308587291202333749220667)
              ·
                refine ⟨57462880936803500623831001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38308587291202333749220667 57462880936803500623831001)
                ·
                  refine ⟨43097160702602625467873251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57462880936803500623831001 43097160702602625467873251)
                  ·
                    refine ⟨64645741053903938201809877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43097160702602625467873251 64645741053903938201809877)
                    ·
                      refine ⟨1515134555950873551604919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64645741053903938201809877 1515134555950873551604919)
                      ·
                        rfl

theorem cell23_2950714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_2950714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950714 prefixEnd_2950714 := by exact prefixLift 2950714
  have htrace : WordTrace (prefixWord ++ tailWord_2950714) baseStart_2950714 baseEnd_2950714 := by
    simpa [prefixWord, tailWord_2950714, baseEnd_2950714] using wordTrace_append hprefix tailTrace_2950714
  have hstable : (prefixWord ++ tailWord_2950714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950714).length < 2 ^ (prefixWord ++ tailWord_2950714).sum := by decide
  have hdescent : baseEnd_2950714 < baseStart_2950714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950721 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 3, 5]
def baseStart_2950721 : Nat := 118140960795 + 2950721 * 2 ^ 59
def prefixEnd_2950721 : Nat := 4983230072969 + 3 ^ 40 * 2950721 * 2
def baseEnd_2950721 : Nat := 505046050105151674739129

theorem tailTrace_2950721 : CollatzResearch.WordTrace tailWord_2950721 prefixEnd_2950721 505046050105151674739129 := by
  unfold tailWord_2950721
  simp only [CollatzResearch.WordTrace]
  refine ⟨107621636343049234870956017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71747757562032823247304011 107621636343049234870956017)
  ·
    refine ⟨80716227257286926153217013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107621636343049234870956017 80716227257286926153217013)
    ·
      refine ⟨7567146305370649326864095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80716227257286926153217013 7567146305370649326864095)
      ·
        refine ⟨11350719458055973990296143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7567146305370649326864095 11350719458055973990296143)
        ·
          refine ⟨17026079187083960985444215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11350719458055973990296143 17026079187083960985444215)
          ·
            refine ⟨25539118780625941478166323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17026079187083960985444215 25539118780625941478166323)
            ·
              refine ⟨38308678170938912217249485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25539118780625941478166323 38308678170938912217249485)
              ·
                refine ⟨14365754314102092081468557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38308678170938912217249485 14365754314102092081468557)
                ·
                  refine ⟨5387157867788284530550709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14365754314102092081468557 5387157867788284530550709)
                  ·
                    refine ⟨505046050105151674739129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5387157867788284530550709 505046050105151674739129)
                    ·
                      rfl

theorem cell23_2950721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_2950721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950721 prefixEnd_2950721 := by exact prefixLift 2950721
  have htrace : WordTrace (prefixWord ++ tailWord_2950721) baseStart_2950721 baseEnd_2950721 := by
    simpa [prefixWord, tailWord_2950721, baseEnd_2950721] using wordTrace_append hprefix tailTrace_2950721
  have hstable : (prefixWord ++ tailWord_2950721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950721).length < 2 ^ (prefixWord ++ tailWord_2950721).sum := by decide
  have hdescent : baseEnd_2950721 < baseStart_2950721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950738 : List Nat := [3, 2, 2, 1, 2, 3, 1, 3, 1, 5]
def baseStart_2950738 : Nat := 118140960795 + 2950738 * 2 ^ 59
def prefixEnd_2950738 : Nat := 4983230072969 + 3 ^ 40 * 2950738 * 2
def baseEnd_2950738 : Nat := 505048959828860485901603

theorem tailTrace_2950738 : CollatzResearch.WordTrace tailWord_2950738 prefixEnd_2950738 505048959828860485901603 := by
  unfold tailWord_2950738
  simp only [CollatzResearch.WordTrace]
  refine ⟨26905564095996911693581217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71748170922658431182883245 26905564095996911693581217)
  ·
    refine ⟨20179173071997683770185913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26905564095996911693581217 20179173071997683770185913)
    ·
      refine ⟨15134379803998262827639435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20179173071997683770185913 15134379803998262827639435)
      ·
        refine ⟨22701569705997394241459153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15134379803998262827639435 22701569705997394241459153)
        ·
          refine ⟨17026177279498045681094365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22701569705997394241459153 17026177279498045681094365)
          ·
            refine ⟨6384816479811767130410387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17026177279498045681094365 6384816479811767130410387)
            ·
              refine ⟨9577224719717650695615581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6384816479811767130410387 9577224719717650695615581)
              ·
                refine ⟨3591459269894119010855843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9577224719717650695615581 3591459269894119010855843)
                ·
                  refine ⟨5387188904841178516283765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3591459269894119010855843 5387188904841178516283765)
                  ·
                    refine ⟨505048959828860485901603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5387188904841178516283765 505048959828860485901603)
                    ·
                      rfl

theorem cell23_2950738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_2950738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950738 prefixEnd_2950738 := by exact prefixLift 2950738
  have htrace : WordTrace (prefixWord ++ tailWord_2950738) baseStart_2950738 baseEnd_2950738 := by
    simpa [prefixWord, tailWord_2950738, baseEnd_2950738] using wordTrace_append hprefix tailTrace_2950738
  have hstable : (prefixWord ++ tailWord_2950738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950738).length < 2 ^ (prefixWord ++ tailWord_2950738).sum := by decide
  have hdescent : baseEnd_2950738 < baseStart_2950738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950761 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 5, 2, 3]
def baseStart_2950761 : Nat := 118140960795 + 2950761 * 2 ^ 59
def prefixEnd_2950761 : Nat := 4983230072969 + 3 ^ 40 * 2950761 * 2
def baseEnd_2950761 : Nat := 1515158689541634867717203

theorem tailTrace_2950761 : CollatzResearch.WordTrace tailWord_2950761 prefixEnd_2950761 1515158689541634867717203 := by
  unfold tailWord_2950761
  simp only [CollatzResearch.WordTrace]
  refine ⟨107623095262904321702412137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71748730175269547801608091 107623095262904321702412137)
  ·
    refine ⟨80717321447178241276809103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107623095262904321702412137 80717321447178241276809103)
    ·
      refine ⟨121075982170767361915213655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80717321447178241276809103 121075982170767361915213655)
      ·
        refine ⟨181613973256151042872820483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121075982170767361915213655 181613973256151042872820483)
        ·
          refine ⟨272420959884226564309230725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181613973256151042872820483 272420959884226564309230725)
          ·
            refine ⟨51078929978292480807980761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 272420959884226564309230725 51078929978292480807980761)
            ·
              refine ⟨38309197483719360605985571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51078929978292480807980761 38309197483719360605985571)
              ·
                refine ⟨57463796225579040908978357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38309197483719360605985571 57463796225579040908978357)
                ·
                  refine ⟨5387230896148035085216721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57463796225579040908978357 5387230896148035085216721)
                  ·
                    refine ⟨4040423172111026313912541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5387230896148035085216721 4040423172111026313912541)
                    ·
                      refine ⟨1515158689541634867717203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4040423172111026313912541 1515158689541634867717203)
                      ·
                        rfl

theorem cell23_2950761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 2, 3].length) (baseStart_2950761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950761 prefixEnd_2950761 := by exact prefixLift 2950761
  have htrace : WordTrace (prefixWord ++ tailWord_2950761) baseStart_2950761 baseEnd_2950761 := by
    simpa [prefixWord, tailWord_2950761, baseEnd_2950761] using wordTrace_append hprefix tailTrace_2950761
  have hstable : (prefixWord ++ tailWord_2950761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950761).length < 2 ^ (prefixWord ++ tailWord_2950761).sum := by decide
  have hdescent : baseEnd_2950761 < baseStart_2950761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950764 : List Nat := [2, 2, 1, 1, 3, 1, 1, 12]
def baseStart_2950764 : Nat := 118140960795 + 2950764 * 2 ^ 59
def prefixEnd_2950764 : Nat := 4983230072969 + 3 ^ 40 * 2950764 * 2
def baseEnd_2950764 : Nat := 56117045554948087258507

theorem tailTrace_2950764 : CollatzResearch.WordTrace tailWord_2950764 prefixEnd_2950764 56117045554948087258507 := by
  unfold tailWord_2950764
  simp only [CollatzResearch.WordTrace]
  refine ⟨53811602340946726607385673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71748803121262302143180897 53811602340946726607385673)
  ·
    refine ⟨40358701755710044955539255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53811602340946726607385673 40358701755710044955539255)
    ·
      refine ⟨60538052633565067433308883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40358701755710044955539255 60538052633565067433308883)
      ·
        refine ⟨90807078950347601149963325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60538052633565067433308883 90807078950347601149963325)
        ·
          refine ⟨34052654606380350431236247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90807078950347601149963325 34052654606380350431236247)
          ·
            refine ⟨51078981909570525646854371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34052654606380350431236247 51078981909570525646854371)
            ·
              refine ⟨76618472864355788470281557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51078981909570525646854371 76618472864355788470281557)
              ·
                refine ⟨56117045554948087258507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 76618472864355788470281557 56117045554948087258507)
                ·
                  rfl

theorem cell23_2950764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 12].length) (baseStart_2950764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950764 prefixEnd_2950764 := by exact prefixLift 2950764
  have htrace : WordTrace (prefixWord ++ tailWord_2950764) baseStart_2950764 baseEnd_2950764 := by
    simpa [prefixWord, tailWord_2950764, baseEnd_2950764] using wordTrace_append hprefix tailTrace_2950764
  have hstable : (prefixWord ++ tailWord_2950764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950764).length < 2 ^ (prefixWord ++ tailWord_2950764).sum := by decide
  have hdescent : baseEnd_2950764 < baseStart_2950764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950768 : List Nat := [2, 1, 1, 1, 6, 3, 1, 1, 1, 6]
def baseStart_2950768 : Nat := 118140960795 + 2950768 * 2 ^ 59
def prefixEnd_2950768 : Nat := 4983230072969 + 3 ^ 40 * 2950768 * 2
def baseEnd_2950768 : Nat := 505054094635405446776557

theorem tailTrace_2950768 : CollatzResearch.WordTrace tailWord_2950768 prefixEnd_2950768 505054094635405446776557 := by
  unfold tailWord_2950768
  simp only [CollatzResearch.WordTrace]
  refine ⟨53811675286939480948958479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71748900382585974598611305 53811675286939480948958479)
  ·
    refine ⟨80717512930409221423437719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53811675286939480948958479 80717512930409221423437719)
    ·
      refine ⟨121076269395613832135156579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80717512930409221423437719 121076269395613832135156579)
      ·
        refine ⟨181614404093420748202734869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121076269395613832135156579 181614404093420748202734869)
        ·
          refine ⟨8513175191879097572003197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 181614404093420748202734869 8513175191879097572003197)
          ·
            refine ⟨3192440696954661589501199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8513175191879097572003197 3192440696954661589501199)
            ·
              refine ⟨4788661045431992384251799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3192440696954661589501199 4788661045431992384251799)
              ·
                refine ⟨7182991568147988576377699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4788661045431992384251799 7182991568147988576377699)
                ·
                  refine ⟨10774487352221982864566549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7182991568147988576377699 10774487352221982864566549)
                  ·
                    refine ⟨505054094635405446776557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10774487352221982864566549 505054094635405446776557)
                    ·
                      rfl

theorem cell23_2950768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 1, 6].length) (baseStart_2950768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950768 prefixEnd_2950768 := by exact prefixLift 2950768
  have htrace : WordTrace (prefixWord ++ tailWord_2950768) baseStart_2950768 baseEnd_2950768 := by
    simpa [prefixWord, tailWord_2950768, baseEnd_2950768] using wordTrace_append hprefix tailTrace_2950768
  have hstable : (prefixWord ++ tailWord_2950768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950768).length < 2 ^ (prefixWord ++ tailWord_2950768).sum := by decide
  have hdescent : baseEnd_2950768 < baseStart_2950768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950781 : List Nat := [1, 4, 1, 1, 4, 2, 1, 9]
def baseStart_2950781 : Nat := 118140960795 + 2950781 * 2 ^ 59
def prefixEnd_2950781 : Nat := 4983230072969 + 3 ^ 40 * 2950781 * 2
def baseEnd_2950781 : Nat := 56117368857582399609893

theorem tailTrace_2950781 : CollatzResearch.WordTrace tailWord_2950781 prefixEnd_2950781 56117368857582399609893 := by
  unfold tailWord_2950781
  simp only [CollatzResearch.WordTrace]
  refine ⟨107623824722831865118140197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71749216481887910078760131 107623824722831865118140197)
  ·
    refine ⟨20179467135530974709651287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107623824722831865118140197 20179467135530974709651287)
    ·
      refine ⟨30269200703296462064476931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20179467135530974709651287 30269200703296462064476931)
      ·
        refine ⟨45403801054944693096715397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30269200703296462064476931 45403801054944693096715397)
        ·
          refine ⟨8513212697802129955634137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45403801054944693096715397 8513212697802129955634137)
          ·
            refine ⟨6384909523351597466725603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8513212697802129955634137 6384909523351597466725603)
            ·
              refine ⟨9577364285027396200088405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6384909523351597466725603 9577364285027396200088405)
              ·
                refine ⟨56117368857582399609893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9577364285027396200088405 56117368857582399609893)
                ·
                  rfl

theorem cell23_2950781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 9].length) (baseStart_2950781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950781 prefixEnd_2950781 := by exact prefixLift 2950781
  have htrace : WordTrace (prefixWord ++ tailWord_2950781) baseStart_2950781 baseEnd_2950781 := by
    simpa [prefixWord, tailWord_2950781, baseEnd_2950781] using wordTrace_append hprefix tailTrace_2950781
  have hstable : (prefixWord ++ tailWord_2950781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950781).length < 2 ^ (prefixWord ++ tailWord_2950781).sum := by decide
  have hdescent : baseEnd_2950781 < baseStart_2950781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950851 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 3]
def baseStart_2950851 : Nat := 118140960795 + 2950851 * 2 ^ 59
def prefixEnd_2950851 : Nat := 4983230072969 + 3 ^ 40 * 2950851 * 2
def baseEnd_2950851 : Nat := 1515204902800539515591789

theorem tailTrace_2950851 : CollatzResearch.WordTrace tailWord_2950851 prefixEnd_2950851 1515204902800539515591789 := by
  unfold tailWord_2950851
  simp only [CollatzResearch.WordTrace]
  refine ⟨107626377832578267073188407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71750918555052178048792271 107626377832578267073188407)
  ·
    refine ⟨161439566748867400609782611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107626377832578267073188407 161439566748867400609782611)
    ·
      refine ⟨242159350123301100914673917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161439566748867400609782611 242159350123301100914673917)
      ·
        refine ⟨90809756296237912843002719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242159350123301100914673917 90809756296237912843002719)
        ·
          refine ⟨136214634444356869264504079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90809756296237912843002719 136214634444356869264504079)
          ·
            refine ⟨204321951666535303896756119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136214634444356869264504079 204321951666535303896756119)
            ·
              refine ⟨306482927499802955845134179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204321951666535303896756119 306482927499802955845134179)
              ·
                refine ⟨459724391249704433767701269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306482927499802955845134179 459724391249704433767701269)
                ·
                  refine ⟨21549580839829895332860997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 459724391249704433767701269 21549580839829895332860997)
                  ·
                    refine ⟨4040546407468105374911437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21549580839829895332860997 4040546407468105374911437)
                    ·
                      refine ⟨1515204902800539515591789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4040546407468105374911437 1515204902800539515591789)
                      ·
                        rfl

theorem cell23_2950851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_2950851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950851 prefixEnd_2950851 := by exact prefixLift 2950851
  have htrace : WordTrace (prefixWord ++ tailWord_2950851) baseStart_2950851 baseEnd_2950851 := by
    simpa [prefixWord, tailWord_2950851, baseEnd_2950851] using wordTrace_append hprefix tailTrace_2950851
  have hstable : (prefixWord ++ tailWord_2950851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950851).length < 2 ^ (prefixWord ++ tailWord_2950851).sum := by decide
  have hdescent : baseEnd_2950851 < baseStart_2950851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950871 : List Nat := [1, 1, 3, 2, 1, 3, 2, 3, 7]
def baseStart_2950871 : Nat := 118140960795 + 2950871 * 2 ^ 59
def prefixEnd_2950871 : Nat := 4983230072969 + 3 ^ 40 * 2950871 * 2
def baseEnd_2950871 : Nat := 168357241379292159704633

theorem tailTrace_2950871 : CollatzResearch.WordTrace tailWord_2950871 prefixEnd_2950871 168357241379292159704633 := by
  unfold tailWord_2950871
  simp only [CollatzResearch.WordTrace]
  refine ⟨107627107292505810488916467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71751404861670540325944311 107627107292505810488916467)
  ·
    refine ⟨161440660938758715733374701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107627107292505810488916467 161440660938758715733374701)
    ·
      refine ⟨60540247852034518400015513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161440660938758715733374701 60540247852034518400015513)
      ·
        refine ⟨45405185889025888800011635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60540247852034518400015513 45405185889025888800011635)
        ·
          refine ⟨68107778833538833200017453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45405185889025888800011635 68107778833538833200017453)
          ·
            refine ⟨25540417062577062450006545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68107778833538833200017453 25540417062577062450006545)
            ·
              refine ⟨19155312796932796837504909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25540417062577062450006545 19155312796932796837504909)
              ·
                refine ⟨7183242298849798814064341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19155312796932796837504909 7183242298849798814064341)
                ·
                  refine ⟨168357241379292159704633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7183242298849798814064341 168357241379292159704633)
                  ·
                    rfl

theorem cell23_2950871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 7].length) (baseStart_2950871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950871 prefixEnd_2950871 := by exact prefixLift 2950871
  have htrace : WordTrace (prefixWord ++ tailWord_2950871) baseStart_2950871 baseEnd_2950871 := by
    simpa [prefixWord, tailWord_2950871, baseEnd_2950871] using wordTrace_append hprefix tailTrace_2950871
  have hstable : (prefixWord ++ tailWord_2950871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950871).length < 2 ^ (prefixWord ++ tailWord_2950871).sum := by decide
  have hdescent : baseEnd_2950871 < baseStart_2950871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950888 : List Nat := [2, 1, 4, 1, 3, 2, 1, 2, 7]
def baseStart_2950888 : Nat := 118140960795 + 2950888 * 2 ^ 59
def prefixEnd_2950888 : Nat := 4983230072969 + 3 ^ 40 * 2950888 * 2
def baseEnd_2950888 : Nat := 168358211287195096758791

theorem tailTrace_2950888 : CollatzResearch.WordTrace tailWord_2950888 prefixEnd_2950888 168358211287195096758791 := by
  unfold tailWord_2950888
  simp only [CollatzResearch.WordTrace]
  refine ⟨53813863666722111196142659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71751818222296148261523545 53813863666722111196142659)
  ·
    refine ⟨80720795500083166794213989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53813863666722111196142659 80720795500083166794213989)
    ·
      refine ⟨15135149156265593773915123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80720795500083166794213989 15135149156265593773915123)
      ·
        refine ⟨22702723734398390660872685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15135149156265593773915123 22702723734398390660872685)
        ·
          refine ⟨8513521400399396497827257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22702723734398390660872685 8513521400399396497827257)
          ·
            refine ⟨6385141050299547373370443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8513521400399396497827257 6385141050299547373370443)
            ·
              refine ⟨9577711575449321060055665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6385141050299547373370443 9577711575449321060055665)
              ·
                refine ⟨7183283681586990795041749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9577711575449321060055665 7183283681586990795041749)
                ·
                  refine ⟨168358211287195096758791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7183283681586990795041749 168358211287195096758791)
                  ·
                    rfl

theorem cell23_2950888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 7].length) (baseStart_2950888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950888 prefixEnd_2950888 := by exact prefixLift 2950888
  have htrace : WordTrace (prefixWord ++ tailWord_2950888) baseStart_2950888 baseEnd_2950888 := by
    simpa [prefixWord, tailWord_2950888, baseEnd_2950888] using wordTrace_append hprefix tailTrace_2950888
  have hstable : (prefixWord ++ tailWord_2950888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950888).length < 2 ^ (prefixWord ++ tailWord_2950888).sum := by decide
  have hdescent : baseEnd_2950888 < baseStart_2950888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950898 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 1, 5, 3]
def baseStart_2950898 : Nat := 118140960795 + 2950898 * 2 ^ 59
def prefixEnd_2950898 : Nat := 4983230072969 + 3 ^ 40 * 2950898 * 2
def baseEnd_2950898 : Nat := 1515229036391300831704073

theorem tailTrace_2950898 : CollatzResearch.WordTrace tailWord_2950898 prefixEnd_2950898 1515229036391300831704073 := by
  unfold tailWord_2950898
  simp only [CollatzResearch.WordTrace]
  refine ⟨26907023015851998525037337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71752061375605329400099565 26907023015851998525037337)
  ·
    refine ⟨20180267261888998893778003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26907023015851998525037337 20180267261888998893778003)
    ·
      refine ⟨30270400892833498340667005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20180267261888998893778003 30270400892833498340667005)
      ·
        refine ⟨11351400334812561877750127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30270400892833498340667005 11351400334812561877750127)
        ·
          refine ⟨17027100502218842816625191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11351400334812561877750127 17027100502218842816625191)
          ·
            refine ⟨25540650753328264224937787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17027100502218842816625191 25540650753328264224937787)
            ·
              refine ⟨38310976129992396337406681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25540650753328264224937787 38310976129992396337406681)
              ·
                refine ⟨28733232097494297253055011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38310976129992396337406681 28733232097494297253055011)
                ·
                  refine ⟨43099848146241445879582517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28733232097494297253055011 43099848146241445879582517)
                  ·
                    refine ⟨4040610763710135551210861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43099848146241445879582517 4040610763710135551210861)
                    ·
                      refine ⟨1515229036391300831704073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4040610763710135551210861 1515229036391300831704073)
                      ·
                        rfl

theorem cell23_2950898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_2950898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950898 prefixEnd_2950898 := by exact prefixLift 2950898
  have htrace : WordTrace (prefixWord ++ tailWord_2950898) baseStart_2950898 baseEnd_2950898 := by
    simpa [prefixWord, tailWord_2950898, baseEnd_2950898] using wordTrace_append hprefix tailTrace_2950898
  have hstable : (prefixWord ++ tailWord_2950898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950898).length < 2 ^ (prefixWord ++ tailWord_2950898).sum := by decide
  have hdescent : baseEnd_2950898 < baseStart_2950898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950911 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 5]
def baseStart_2950911 : Nat := 118140960795 + 2950911 * 2 ^ 59
def prefixEnd_2950911 : Nat := 4983230072969 + 3 ^ 40 * 2950911 * 2
def baseEnd_2950911 : Nat := 1515235711639809280841513

theorem tailTrace_2950911 : CollatzResearch.WordTrace tailWord_2950911 prefixEnd_2950911 1515235711639809280841513 := by
  unfold tailWord_2950911
  simp only [CollatzResearch.WordTrace]
  refine ⟨107628566212360897320372587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71752377474907264880248391 107628566212360897320372587)
  ·
    refine ⟨161442849318541345980558881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107628566212360897320372587 161442849318541345980558881)
    ·
      refine ⟨121082136988906009485419161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161442849318541345980558881 121082136988906009485419161)
      ·
        refine ⟨90811602741679507114064371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121082136988906009485419161 90811602741679507114064371)
        ·
          refine ⟨136217404112519260671096557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90811602741679507114064371 136217404112519260671096557)
          ·
            refine ⟨51081526542194722751661209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136217404112519260671096557 51081526542194722751661209)
            ·
              refine ⟨38311144906646042063745907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51081526542194722751661209 38311144906646042063745907)
              ·
                refine ⟨57466717359969063095618861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38311144906646042063745907 57466717359969063095618861)
                ·
                  refine ⟨21550019009988398660857073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57466717359969063095618861 21550019009988398660857073)
                  ·
                    refine ⟨16162514257491298995642805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21550019009988398660857073 16162514257491298995642805)
                    ·
                      refine ⟨1515235711639809280841513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16162514257491298995642805 1515235711639809280841513)
                      ·
                        rfl

theorem cell23_2950911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_2950911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950911 prefixEnd_2950911 := by exact prefixLift 2950911
  have htrace : WordTrace (prefixWord ++ tailWord_2950911) baseStart_2950911 baseEnd_2950911 := by
    simpa [prefixWord, tailWord_2950911, baseEnd_2950911] using wordTrace_append hprefix tailTrace_2950911
  have hstable : (prefixWord ++ tailWord_2950911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950911).length < 2 ^ (prefixWord ++ tailWord_2950911).sum := by decide
  have hdescent : baseEnd_2950911 < baseStart_2950911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2950938 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4]
def baseStart_2950938 : Nat := 118140960795 + 2950938 * 2 ^ 59
def prefixEnd_2950938 : Nat := 4983230072969 + 3 ^ 40 * 2950938 * 2
def baseEnd_2950938 : Nat := 1515249575617480675203889

theorem tailTrace_2950938 : CollatzResearch.WordTrace tailWord_2950938 prefixEnd_2950938 1515249575617480675203889 := by
  unfold tailWord_2950938
  simp only [CollatzResearch.WordTrace]
  refine ⟨26907387745815770232901367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71753033988842053954403645 26907387745815770232901367)
  ·
    refine ⟨40361081618723655349352051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26907387745815770232901367 40361081618723655349352051)
    ·
      refine ⟨60541622428085483024028077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40361081618723655349352051 60541622428085483024028077)
      ·
        refine ⟨22703108410532056134010529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60541622428085483024028077 22703108410532056134010529)
        ·
          refine ⟨17027331307899042100507897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22703108410532056134010529 17027331307899042100507897)
          ·
            refine ⟨12770498480924281575380923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17027331307899042100507897 12770498480924281575380923)
            ·
              refine ⟨19155747721386422363071385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12770498480924281575380923 19155747721386422363071385)
              ·
                refine ⟨14366810791039816772303539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19155747721386422363071385 14366810791039816772303539)
                ·
                  refine ⟨21550216186559725158455309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14366810791039816772303539 21550216186559725158455309)
                  ·
                    refine ⟨8081331069959896934420741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21550216186559725158455309 8081331069959896934420741)
                    ·
                      refine ⟨1515249575617480675203889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8081331069959896934420741 1515249575617480675203889)
                      ·
                        rfl

theorem cell23_2950938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_2950938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2950938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2950938 prefixEnd_2950938 := by exact prefixLift 2950938
  have htrace : WordTrace (prefixWord ++ tailWord_2950938) baseStart_2950938 baseEnd_2950938 := by
    simpa [prefixWord, tailWord_2950938, baseEnd_2950938] using wordTrace_append hprefix tailTrace_2950938
  have hstable : (prefixWord ++ tailWord_2950938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2950938).length < 2 ^ (prefixWord ++ tailWord_2950938).sum := by decide
  have hdescent : baseEnd_2950938 < baseStart_2950938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2950938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951065 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 3, 2, 3]
def baseStart_2951065 : Nat := 118140960795 + 2951065 * 2 ^ 59
def prefixEnd_2951065 : Nat := 4983230072969 + 3 ^ 40 * 2951065 * 2
def baseEnd_2951065 : Nat := 1515314787660601678315805

theorem tailTrace_2951065 : CollatzResearch.WordTrace tailWord_2951065 prefixEnd_2951065 1515314787660601678315805 := by
  unfold tailWord_2951065
  simp only [CollatzResearch.WordTrace]
  refine ⟨107634183053802981621478649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71756122035868654414319099 107634183053802981621478649)
  ·
    refine ⟨80725637290352236216108987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107634183053802981621478649 80725637290352236216108987)
    ·
      refine ⟨121088455935528354324163481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80725637290352236216108987 121088455935528354324163481)
      ·
        refine ⟨90816341951646265743122611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121088455935528354324163481 90816341951646265743122611)
        ·
          refine ⟨136224512927469398614683917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90816341951646265743122611 136224512927469398614683917)
          ·
            refine ⟨51084192347801024480506469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136224512927469398614683917 51084192347801024480506469)
            ·
              refine ⟨9578286065212692090094963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51084192347801024480506469 9578286065212692090094963)
              ·
                refine ⟨14367429097819038135142445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9578286065212692090094963 14367429097819038135142445)
                ·
                  refine ⟨5387785911682139300678417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14367429097819038135142445 5387785911682139300678417)
                  ·
                    refine ⟨4040839433761604475508813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5387785911682139300678417 4040839433761604475508813)
                    ·
                      refine ⟨1515314787660601678315805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4040839433761604475508813 1515314787660601678315805)
                      ·
                        rfl

theorem cell23_2951065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_2951065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951065 prefixEnd_2951065 := by exact prefixLift 2951065
  have htrace : WordTrace (prefixWord ++ tailWord_2951065) baseStart_2951065 baseEnd_2951065 := by
    simpa [prefixWord, tailWord_2951065, baseEnd_2951065] using wordTrace_append hprefix tailTrace_2951065
  have hstable : (prefixWord ++ tailWord_2951065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951065).length < 2 ^ (prefixWord ++ tailWord_2951065).sum := by decide
  have hdescent : baseEnd_2951065 < baseStart_2951065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951079 : List Nat := [1, 1, 6, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_2951079 : Nat := 118140960795 + 2951079 * 2 ^ 59
def prefixEnd_2951079 : Nat := 4983230072969 + 3 ^ 40 * 2951079 * 2
def baseEnd_2951079 : Nat := 1515321976389764623540741

theorem tailTrace_2951079 : CollatzResearch.WordTrace tailWord_2951079 prefixEnd_2951079 1515321976389764623540741 := by
  unfold tailWord_2951079
  simp only [CollatzResearch.WordTrace]
  refine ⟨107634693675752262012488291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71756462450501508008325527 107634693675752262012488291)
  ·
    refine ⟨161452040513628393018732437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107634693675752262012488291 161452040513628393018732437)
    ·
      refine ⟨7568064399076330922753083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 161452040513628393018732437 7568064399076330922753083)
      ·
        refine ⟨11352096598614496384129625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7568064399076330922753083 11352096598614496384129625)
        ·
          refine ⟨8514072448960872288097219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11352096598614496384129625 8514072448960872288097219)
          ·
            refine ⟨12771108673441308432145829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8514072448960872288097219 12771108673441308432145829)
            ·
              refine ⟨2394582876270245331027343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12771108673441308432145829 2394582876270245331027343)
              ·
                refine ⟨3591874314405367996541015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2394582876270245331027343 3591874314405367996541015)
                ·
                  refine ⟨5387811471608051994811523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3591874314405367996541015 5387811471608051994811523)
                  ·
                    refine ⟨8081717207412077992217285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5387811471608051994811523 8081717207412077992217285)
                    ·
                      refine ⟨1515321976389764623540741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8081717207412077992217285 1515321976389764623540741)
                      ·
                        rfl

theorem cell23_2951079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_2951079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951079 prefixEnd_2951079 := by exact prefixLift 2951079
  have htrace : WordTrace (prefixWord ++ tailWord_2951079) baseStart_2951079 baseEnd_2951079 := by
    simpa [prefixWord, tailWord_2951079, baseEnd_2951079] using wordTrace_append hprefix tailTrace_2951079
  have hstable : (prefixWord ++ tailWord_2951079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951079).length < 2 ^ (prefixWord ++ tailWord_2951079).sum := by decide
  have hdescent : baseEnd_2951079 < baseStart_2951079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951089 : List Nat := [1, 2, 2, 4, 2, 3, 1, 2, 2, 4]
def baseStart_2951089 : Nat := 118140960795 + 2951089 * 2 ^ 59
def prefixEnd_2951089 : Nat := 4983230072969 + 3 ^ 40 * 2951089 * 2
def baseEnd_2951089 : Nat := 505109037065436528138565

theorem tailTrace_2951089 : CollatzResearch.WordTrace tailWord_2951089 prefixEnd_2951089 505109037065436528138565 := by
  unfold tailWord_2951089
  simp only [CollatzResearch.WordTrace]
  refine ⟨107635058405716033720352321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71756705603810689146901547 107635058405716033720352321)
  ·
    refine ⟨80726293804287025290264241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107635058405716033720352321 80726293804287025290264241)
    ·
      refine ⟨60544720353215268967698181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80726293804287025290264241 60544720353215268967698181)
      ·
        refine ⟨11352135066227862931443409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60544720353215268967698181 11352135066227862931443409)
        ·
          refine ⟨8514101299670897198582557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11352135066227862931443409 8514101299670897198582557)
          ·
            refine ⟨3192787987376586449468459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8514101299670897198582557 3192787987376586449468459)
            ·
              refine ⟨4789181981064879674202689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3192787987376586449468459 4789181981064879674202689)
              ·
                refine ⟨3591886485798659755652017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4789181981064879674202689 3591886485798659755652017)
                ·
                  refine ⟨2693914864348994816739013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3591886485798659755652017 2693914864348994816739013)
                  ·
                    refine ⟨505109037065436528138565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2693914864348994816739013 505109037065436528138565)
                    ·
                      rfl

theorem cell23_2951089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 4].length) (baseStart_2951089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951089 prefixEnd_2951089 := by exact prefixLift 2951089
  have htrace : WordTrace (prefixWord ++ tailWord_2951089) baseStart_2951089 baseEnd_2951089 := by
    simpa [prefixWord, tailWord_2951089, baseEnd_2951089] using wordTrace_append hprefix tailTrace_2951089
  have hstable : (prefixWord ++ tailWord_2951089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951089).length < 2 ^ (prefixWord ++ tailWord_2951089).sum := by decide
  have hdescent : baseEnd_2951089 < baseStart_2951089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951098 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 2, 7]
def baseStart_2951098 : Nat := 118140960795 + 2951098 * 2 ^ 59
def prefixEnd_2951098 : Nat := 4983230072969 + 3 ^ 40 * 2951098 * 2
def baseEnd_2951098 : Nat := 505110577507400016401051

theorem tailTrace_2951098 : CollatzResearch.WordTrace tailWord_2951098 prefixEnd_2951098 505110577507400016401051 := by
  unfold tailWord_2951098
  simp only [CollatzResearch.WordTrace]
  refine ⟨26908846665670857064357487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71756924441788952171619965 26908846665670857064357487)
  ·
    refine ⟨40363269998506285596536231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26908846665670857064357487 40363269998506285596536231)
    ·
      refine ⟨60544904997759428394804347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40363269998506285596536231 60544904997759428394804347)
      ·
        refine ⟨90817357496639142592206521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60544904997759428394804347 90817357496639142592206521)
        ·
          refine ⟨68113018122479356944154891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90817357496639142592206521 68113018122479356944154891)
          ·
            refine ⟨102169527183719035416232337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68113018122479356944154891 102169527183719035416232337)
            ·
              refine ⟨76627145387789276562174253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102169527183719035416232337 76627145387789276562174253)
              ·
                refine ⟨28735179520420978710815345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76627145387789276562174253 28735179520420978710815345)
                ·
                  refine ⟨21551384640315734033111509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28735179520420978710815345 21551384640315734033111509)
                  ·
                    refine ⟨505110577507400016401051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21551384640315734033111509 505110577507400016401051)
                    ·
                      rfl

theorem cell23_2951098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_2951098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951098 prefixEnd_2951098 := by exact prefixLift 2951098
  have htrace : WordTrace (prefixWord ++ tailWord_2951098) baseStart_2951098 baseEnd_2951098 := by
    simpa [prefixWord, tailWord_2951098, baseEnd_2951098] using wordTrace_append hprefix tailTrace_2951098
  have hstable : (prefixWord ++ tailWord_2951098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951098).length < 2 ^ (prefixWord ++ tailWord_2951098).sum := by decide
  have hdescent : baseEnd_2951098 < baseStart_2951098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951112 : List Nat := [2, 1, 3, 1, 4, 1, 3, 1, 1, 3, 3]
def baseStart_2951112 : Nat := 118140960795 + 2951112 * 2 ^ 59
def prefixEnd_2951112 : Nat := 4983230072969 + 3 ^ 40 * 2951112 * 2
def baseEnd_2951112 : Nat := 1515338921251362994428089

theorem tailTrace_2951112 : CollatzResearch.WordTrace tailWord_2951112 prefixEnd_2951112 1515338921251362994428089 := by
  unfold tailWord_2951112
  simp only [CollatzResearch.WordTrace]
  refine ⟨53817948642316354324219795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71757264856421805765626393 53817948642316354324219795)
  ·
    refine ⟨80726922963474531486329693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53817948642316354324219795 80726922963474531486329693)
    ·
      refine ⟨30272596111302949307373635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80726922963474531486329693 30272596111302949307373635)
      ·
        refine ⟨45408894166954423961060453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30272596111302949307373635 45408894166954423961060453)
        ·
          refine ⟨8514167656303954492698835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45408894166954423961060453 8514167656303954492698835)
          ·
            refine ⟨12771251484455931739048253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8514167656303954492698835 12771251484455931739048253)
            ·
              refine ⟨4789219306670974402143095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12771251484455931739048253 4789219306670974402143095)
              ·
                refine ⟨7183828960006461603214643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4789219306670974402143095 7183828960006461603214643)
                ·
                  refine ⟨10775743440009692404821965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7183828960006461603214643 10775743440009692404821965)
                  ·
                    refine ⟨4040903790003634651808237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10775743440009692404821965 4040903790003634651808237)
                    ·
                      refine ⟨1515338921251362994428089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4040903790003634651808237 1515338921251362994428089)
                      ·
                        rfl

theorem cell23_2951112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_2951112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951112 prefixEnd_2951112 := by exact prefixLift 2951112
  have htrace : WordTrace (prefixWord ++ tailWord_2951112) baseStart_2951112 baseEnd_2951112 := by
    simpa [prefixWord, tailWord_2951112, baseEnd_2951112] using wordTrace_append hprefix tailTrace_2951112
  have hstable : (prefixWord ++ tailWord_2951112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951112).length < 2 ^ (prefixWord ++ tailWord_2951112).sum := by decide
  have hdescent : baseEnd_2951112 < baseStart_2951112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951125 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_2951125 : Nat := 118140960795 + 2951125 * 2 ^ 59
def prefixEnd_2951125 : Nat := 4983230072969 + 3 ^ 40 * 2951125 * 2
def baseEnd_2951125 : Nat := 1515345596499871443565529

theorem tailTrace_2951125 : CollatzResearch.WordTrace tailWord_2951125 prefixEnd_2951125 1515345596499871443565529 := by
  unfold tailWord_2951125
  simp only [CollatzResearch.WordTrace]
  refine ⟨107636371433585611868662829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71757580955723741245775219 107636371433585611868662829)
  ·
    refine ⟨40363639287594604450748561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107636371433585611868662829 40363639287594604450748561)
    ·
      refine ⟨30272729465695953338061421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40363639287594604450748561 30272729465695953338061421)
      ·
        refine ⟨11352273549635982501773033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30272729465695953338061421 11352273549635982501773033)
        ·
          refine ⟨8514205162226986876329775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11352273549635982501773033 8514205162226986876329775)
          ·
            refine ⟨12771307743340480314494663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8514205162226986876329775 12771307743340480314494663)
            ·
              refine ⟨19156961615010720471741995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12771307743340480314494663 19156961615010720471741995)
              ·
                refine ⟨28735442422516080707612993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19156961615010720471741995 28735442422516080707612993)
                ·
                  refine ⟨21551581816887060530709745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28735442422516080707612993 21551581816887060530709745)
                  ·
                    refine ⟨16163686362665295398032309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21551581816887060530709745 16163686362665295398032309)
                    ·
                      refine ⟨1515345596499871443565529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16163686362665295398032309 1515345596499871443565529)
                      ·
                        rfl

theorem cell23_2951125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_2951125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951125 prefixEnd_2951125 := by exact prefixLift 2951125
  have htrace : WordTrace (prefixWord ++ tailWord_2951125) baseStart_2951125 baseEnd_2951125 := by
    simpa [prefixWord, tailWord_2951125, baseEnd_2951125] using wordTrace_append hprefix tailTrace_2951125
  have hstable : (prefixWord ++ tailWord_2951125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951125).length < 2 ^ (prefixWord ++ tailWord_2951125).sum := by decide
  have hdescent : baseEnd_2951125 < baseStart_2951125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951130 : List Nat := [3, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2]
def baseStart_2951130 : Nat := 118140960795 + 2951130 * 2 ^ 59
def prefixEnd_2951130 : Nat := 4983230072969 + 3 ^ 40 * 2951130 * 2
def baseEnd_2951130 : Nat := 1515348163903143924003007

theorem tailTrace_2951130 : CollatzResearch.WordTrace tailWord_2951130 prefixEnd_2951130 1515348163903143924003007 := by
  unfold tailWord_2951130
  simp only [CollatzResearch.WordTrace]
  refine ⟨26909138449641874430648711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71757702532378331815063229 26909138449641874430648711)
  ·
    refine ⟨40363707674462811645973067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26909138449641874430648711 40363707674462811645973067)
    ·
      refine ⟨60545561511694217468959601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40363707674462811645973067 60545561511694217468959601)
      ·
        refine ⟨45409171133770663101719701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60545561511694217468959601 45409171133770663101719701)
        ·
          refine ⟨2128554896895499832893111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45409171133770663101719701 2128554896895499832893111)
          ·
            refine ⟨3192832345343249749339667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2128554896895499832893111 3192832345343249749339667)
            ·
              refine ⟨4789248518014874624009501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3192832345343249749339667 4789248518014874624009501)
              ·
                refine ⟨1795968194255577984003563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4789248518014874624009501 1795968194255577984003563)
                ·
                  refine ⟨2693952291383366976005345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1795968194255577984003563 2693952291383366976005345)
                  ·
                    refine ⟨2020464218537525232004009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2693952291383366976005345 2020464218537525232004009)
                    ·
                      refine ⟨1515348163903143924003007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2020464218537525232004009 1515348163903143924003007)
                      ·
                        rfl

theorem cell23_2951130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2].length) (baseStart_2951130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951130 prefixEnd_2951130 := by exact prefixLift 2951130
  have htrace : WordTrace (prefixWord ++ tailWord_2951130) baseStart_2951130 baseEnd_2951130 := by
    simpa [prefixWord, tailWord_2951130, baseEnd_2951130] using wordTrace_append hprefix tailTrace_2951130
  have hstable : (prefixWord ++ tailWord_2951130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951130).length < 2 ^ (prefixWord ++ tailWord_2951130).sum := by decide
  have hdescent : baseEnd_2951130 < baseStart_2951130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951139 : List Nat := [1, 1, 1, 6, 1, 2, 2, 3, 1, 3, 2]
def baseStart_2951139 : Nat := 118140960795 + 2951139 * 2 ^ 59
def prefixEnd_2951139 : Nat := 4983230072969 + 3 ^ 40 * 2951139 * 2
def baseEnd_2951139 : Nat := 1515352785229034388790465

theorem tailTrace_2951139 : CollatzResearch.WordTrace tailWord_2951139 prefixEnd_2951139 1515352785229034388790465 := by
  unfold tailWord_2951139
  simp only [CollatzResearch.WordTrace]
  refine ⟨107636882055534892259672471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71757921370356594839781647 107636882055534892259672471)
  ·
    refine ⟨161455323083302338389508707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107636882055534892259672471 161455323083302338389508707)
    ·
      refine ⟨242182984624953507584263061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161455323083302338389508707 242182984624953507584263061)
      ·
        refine ⟨11352327404294695668012331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 242182984624953507584263061 11352327404294695668012331)
        ·
          refine ⟨17028491106442043502018497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11352327404294695668012331 17028491106442043502018497)
          ·
            refine ⟨12771368329831532626513873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17028491106442043502018497 12771368329831532626513873)
            ·
              refine ⟨9578526247373649469885405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12771368329831532626513873 9578526247373649469885405)
              ·
                refine ⟨3591947342765118551207027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9578526247373649469885405 3591947342765118551207027)
                ·
                  refine ⟨5387921014147677826810541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3591947342765118551207027 5387921014147677826810541)
                  ·
                    refine ⟨2020470380305379185053953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5387921014147677826810541 2020470380305379185053953)
                    ·
                      refine ⟨1515352785229034388790465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2020470380305379185053953 1515352785229034388790465)
                      ·
                        rfl

theorem cell23_2951139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_2951139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951139 prefixEnd_2951139 := by exact prefixLift 2951139
  have htrace : WordTrace (prefixWord ++ tailWord_2951139) baseStart_2951139 baseEnd_2951139 := by
    simpa [prefixWord, tailWord_2951139, baseEnd_2951139] using wordTrace_append hprefix tailTrace_2951139
  have hstable : (prefixWord ++ tailWord_2951139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951139).length < 2 ^ (prefixWord ++ tailWord_2951139).sum := by decide
  have hdescent : baseEnd_2951139 < baseStart_2951139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951165 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_2951165 : Nat := 118140960795 + 2951165 * 2 ^ 59
def prefixEnd_2951165 : Nat := 4983230072969 + 3 ^ 40 * 2951165 * 2
def baseEnd_2951165 : Nat := 1515366135726051287065345

theorem tailTrace_2951165 : CollatzResearch.WordTrace tailWord_2951165 prefixEnd_2951165 1515366135726051287065345 := by
  unfold tailWord_2951165
  simp only [CollatzResearch.WordTrace]
  refine ⟨107637830353440698700118949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71758553568960465800079299 107637830353440698700118949)
  ·
    refine ⟨20182093191270131006272303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107637830353440698700118949 20182093191270131006272303)
    ·
      refine ⟨30273139786905196509408455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20182093191270131006272303 30273139786905196509408455)
      ·
        refine ⟨45409709680357794764112683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30273139786905196509408455 45409709680357794764112683)
        ·
          refine ⟨68114564520536692146169025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45409709680357794764112683 68114564520536692146169025)
          ·
            refine ⟨51085923390402519109626769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68114564520536692146169025 51085923390402519109626769)
            ·
              refine ⟨38314442542801889332220077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51085923390402519109626769 38314442542801889332220077)
              ·
                refine ⟨14367915953550708499582529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38314442542801889332220077 14367915953550708499582529)
                ·
                  refine ⟨10775936965163031374686897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14367915953550708499582529 10775936965163031374686897)
                  ·
                    refine ⟨8081952723872273531015173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10775936965163031374686897 8081952723872273531015173)
                    ·
                      refine ⟨1515366135726051287065345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8081952723872273531015173 1515366135726051287065345)
                      ·
                        rfl

theorem cell23_2951165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_2951165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951165 prefixEnd_2951165 := by exact prefixLift 2951165
  have htrace : WordTrace (prefixWord ++ tailWord_2951165) baseStart_2951165 baseEnd_2951165 := by
    simpa [prefixWord, tailWord_2951165, baseEnd_2951165] using wordTrace_append hprefix tailTrace_2951165
  have hstable : (prefixWord ++ tailWord_2951165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951165).length < 2 ^ (prefixWord ++ tailWord_2951165).sum := by decide
  have hdescent : baseEnd_2951165 < baseStart_2951165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951185 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 3]
def baseStart_2951185 : Nat := 118140960795 + 2951185 * 2 ^ 59
def prefixEnd_2951185 : Nat := 4983230072969 + 3 ^ 40 * 2951185 * 2
def baseEnd_2951185 : Nat := 1515376405339141208815253

theorem tailTrace_2951185 : CollatzResearch.WordTrace tailWord_2951185 prefixEnd_2951185 1515376405339141208815253 := by
  unfold tailWord_2951185
  simp only [CollatzResearch.WordTrace]
  refine ⟨107638559813368242115847009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71759039875578828077231339 107638559813368242115847009)
  ·
    refine ⟨80728919860026181586885257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107638559813368242115847009 80728919860026181586885257)
    ·
      refine ⟨60546689895019636190163943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80728919860026181586885257 60546689895019636190163943)
      ·
        refine ⟨90820034842529454285245915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60546689895019636190163943 90820034842529454285245915)
        ·
          refine ⟨136230052263794181427868873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90820034842529454285245915 136230052263794181427868873)
          ·
            refine ⟨102172539197845636070901655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136230052263794181427868873 102172539197845636070901655)
            ·
              refine ⟨153258808796768454106352483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102172539197845636070901655 153258808796768454106352483)
              ·
                refine ⟨229888213195152681159528725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153258808796768454106352483 229888213195152681159528725)
                ·
                  refine ⟨10776009993522781929352909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 229888213195152681159528725 10776009993522781929352909)
                  ·
                    refine ⟨4041003747571043223507341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10776009993522781929352909 4041003747571043223507341)
                    ·
                      refine ⟨1515376405339141208815253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4041003747571043223507341 1515376405339141208815253)
                      ·
                        rfl

theorem cell23_2951185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_2951185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951185 prefixEnd_2951185 := by exact prefixLift 2951185
  have htrace : WordTrace (prefixWord ++ tailWord_2951185) baseStart_2951185 baseEnd_2951185 := by
    simpa [prefixWord, tailWord_2951185, baseEnd_2951185] using wordTrace_append hprefix tailTrace_2951185
  have hstable : (prefixWord ++ tailWord_2951185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951185).length < 2 ^ (prefixWord ++ tailWord_2951185).sum := by decide
  have hdescent : baseEnd_2951185 < baseStart_2951185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951192 : List Nat := [2, 1, 2, 3, 2, 1, 2, 5, 5]
def baseStart_2951192 : Nat := 118140960795 + 2951192 * 2 ^ 59
def prefixEnd_2951192 : Nat := 4983230072969 + 3 ^ 40 * 2951192 * 2
def baseEnd_2951192 : Nat := 168375555522635853491969

theorem tailTrace_2951192 : CollatzResearch.WordTrace tailWord_2951192 prefixEnd_2951192 168375555522635853491969 := by
  unfold tailWord_2951192
  simp only [CollatzResearch.WordTrace]
  refine ⟨53819407562171441155675915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71759210082895254874234553 53819407562171441155675915)
  ·
    refine ⟨80729111343257161733513873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53819407562171441155675915 80729111343257161733513873)
    ·
      refine ⟨60546833507442871300135405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80729111343257161733513873 60546833507442871300135405)
      ·
        refine ⟨22705062565291076737550777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60546833507442871300135405 22705062565291076737550777)
        ·
          refine ⟨17028796923968307553163083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22705062565291076737550777 17028796923968307553163083)
          ·
            refine ⟨25543195385952461329744625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17028796923968307553163083 25543195385952461329744625)
            ·
              refine ⟨19157396539464345997308469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25543195385952461329744625 19157396539464345997308469)
              ·
                refine ⟨1796005925574782437247669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19157396539464345997308469 1796005925574782437247669)
                ·
                  refine ⟨168375555522635853491969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1796005925574782437247669 168375555522635853491969)
                  ·
                    rfl

theorem cell23_2951192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 5].length) (baseStart_2951192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951192 prefixEnd_2951192 := by exact prefixLift 2951192
  have htrace : WordTrace (prefixWord ++ tailWord_2951192) baseStart_2951192 baseEnd_2951192 := by
    simpa [prefixWord, tailWord_2951192, baseEnd_2951192] using wordTrace_append hprefix tailTrace_2951192
  have hstable : (prefixWord ++ tailWord_2951192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951192).length < 2 ^ (prefixWord ++ tailWord_2951192).sum := by decide
  have hdescent : baseEnd_2951192 < baseStart_2951192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951202 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_2951202 : Nat := 118140960795 + 2951202 * 2 ^ 59
def prefixEnd_2951202 : Nat := 4983230072969 + 3 ^ 40 * 2951202 * 2
def baseEnd_2951202 : Nat := 1515385134510267642302675

theorem tailTrace_2951202 : CollatzResearch.WordTrace tailWord_2951202 prefixEnd_2951202 1515385134510267642302675 := by
  unfold tailWord_2951202
  simp only [CollatzResearch.WordTrace]
  refine ⟨26909794963576663504803965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71759453236204436012810573 26909794963576663504803965)
  ·
    refine ⟨10091173111341248814301487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26909794963576663504803965 10091173111341248814301487)
    ·
      refine ⟨15136759667011873221452231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10091173111341248814301487 15136759667011873221452231)
      ·
        refine ⟨22705139500517809832178347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15136759667011873221452231 22705139500517809832178347)
        ·
          refine ⟨34057709250776714748267521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22705139500517809832178347 34057709250776714748267521)
          ·
            refine ⟨25543281938082536061200641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34057709250776714748267521 25543281938082536061200641)
            ·
              refine ⟨19157461453561902045900481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25543281938082536061200641 19157461453561902045900481)
              ·
                refine ⟨14368096090171426534425361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19157461453561902045900481 14368096090171426534425361)
                ·
                  refine ⟨10776072067628569900819021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14368096090171426534425361 10776072067628569900819021)
                  ·
                    refine ⟨4041027025360713712807133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10776072067628569900819021 4041027025360713712807133)
                    ·
                      refine ⟨1515385134510267642302675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4041027025360713712807133 1515385134510267642302675)
                      ·
                        rfl

theorem cell23_2951202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_2951202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951202 prefixEnd_2951202 := by exact prefixLift 2951202
  have htrace : WordTrace (prefixWord ++ tailWord_2951202) baseStart_2951202 baseEnd_2951202 := by
    simpa [prefixWord, tailWord_2951202, baseEnd_2951202] using wordTrace_append hprefix tailTrace_2951202
  have hstable : (prefixWord ++ tailWord_2951202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951202).length < 2 ^ (prefixWord ++ tailWord_2951202).sum := by decide
  have hdescent : baseEnd_2951202 < baseStart_2951202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951222 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_2951222 : Nat := 118140960795 + 2951222 * 2 ^ 59
def prefixEnd_2951222 : Nat := 4983230072969 + 3 ^ 40 * 2951222 * 2
def baseEnd_2951222 : Nat := 505131801374452521350861

theorem tailTrace_2951222 : CollatzResearch.WordTrace tailWord_2951222 prefixEnd_2951222 505131801374452521350861 := by
  unfold tailWord_2951222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6727494332139637339683995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71759939542822798289962613 6727494332139637339683995)
  ·
    refine ⟨10091241498209456009525993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6727494332139637339683995 10091241498209456009525993)
    ·
      refine ⟨7568431123657092007144495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10091241498209456009525993 7568431123657092007144495)
      ·
        refine ⟨11352646685485638010716743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7568431123657092007144495 11352646685485638010716743)
        ·
          refine ⟨17028970028228457016075115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11352646685485638010716743 17028970028228457016075115)
          ·
            refine ⟨25543455042342685524112673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17028970028228457016075115 25543455042342685524112673)
            ·
              refine ⟨19157591281757014143084505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25543455042342685524112673 19157591281757014143084505)
              ·
                refine ⟨14368193461317760607313379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19157591281757014143084505 14368193461317760607313379)
                ·
                  refine ⟨21552290191976640910970069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14368193461317760607313379 21552290191976640910970069)
                  ·
                    refine ⟨505131801374452521350861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21552290191976640910970069 505131801374452521350861)
                    ·
                      rfl

theorem cell23_2951222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_2951222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951222 prefixEnd_2951222 := by exact prefixLift 2951222
  have htrace : WordTrace (prefixWord ++ tailWord_2951222) baseStart_2951222 baseEnd_2951222 := by
    simpa [prefixWord, tailWord_2951222, baseEnd_2951222] using wordTrace_append hprefix tailTrace_2951222
  have hstable : (prefixWord ++ tailWord_2951222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951222).length < 2 ^ (prefixWord ++ tailWord_2951222).sum := by decide
  have hdescent : baseEnd_2951222 < baseStart_2951222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951242 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 3, 6, 2]
def baseStart_2951242 : Nat := 118140960795 + 2951242 * 2 ^ 59
def prefixEnd_2951242 : Nat := 4983230072969 + 3 ^ 40 * 2951242 * 2
def baseEnd_2951242 : Nat := 1515405673736447485802491

theorem tailTrace_2951242 : CollatzResearch.WordTrace tailWord_2951242 prefixEnd_2951242 1515405673736447485802491 := by
  unfold tailWord_2951242
  simp only [CollatzResearch.WordTrace]
  refine ⟨26910159693540435212667995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71760425849441160567114653 26910159693540435212667995)
  ·
    refine ⟨40365239540310652819001993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26910159693540435212667995 40365239540310652819001993)
    ·
      refine ⟨30273929655232989614251495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40365239540310652819001993 30273929655232989614251495)
      ·
        refine ⟨45410894482849484421377243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30273929655232989614251495 45410894482849484421377243)
        ·
          refine ⟨68116341724274226632065865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45410894482849484421377243 68116341724274226632065865)
          ·
            refine ⟨51087256293205669974049399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68116341724274226632065865 51087256293205669974049399)
            ·
              refine ⟨76630884439808504961074099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51087256293205669974049399 76630884439808504961074099)
              ·
                refine ⟨114946326659712757441611149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76630884439808504961074099 114946326659712757441611149)
                ·
                  refine ⟨43104872497392284040604181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114946326659712757441611149 43104872497392284040604181)
                  ·
                    refine ⟨2020540898315263314403321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43104872497392284040604181 2020540898315263314403321)
                    ·
                      refine ⟨1515405673736447485802491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2020540898315263314403321 1515405673736447485802491)
                      ·
                        rfl

theorem cell23_2951242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_2951242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951242 prefixEnd_2951242 := by exact prefixLift 2951242
  have htrace : WordTrace (prefixWord ++ tailWord_2951242) baseStart_2951242 baseEnd_2951242 := by
    simpa [prefixWord, tailWord_2951242, baseEnd_2951242] using wordTrace_append hprefix tailTrace_2951242
  have hstable : (prefixWord ++ tailWord_2951242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951242).length < 2 ^ (prefixWord ++ tailWord_2951242).sum := by decide
  have hdescent : baseEnd_2951242 < baseStart_2951242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951252 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_2951252 : Nat := 118140960795 + 2951252 * 2 ^ 59
def prefixEnd_2951252 : Nat := 4983230072969 + 3 ^ 40 * 2951252 * 2
def baseEnd_2951252 : Nat := 505136936180997482225815

theorem tailTrace_2951252 : CollatzResearch.WordTrace tailWord_2951252 prefixEnd_2951252 505136936180997482225815 := by
  unfold tailWord_2951252
  simp only [CollatzResearch.WordTrace]
  refine ⟨53820501752062756279268005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71760669002750341705690673 53820501752062756279268005)
  ·
    refine ⟨10091344078511766802362751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53820501752062756279268005 10091344078511766802362751)
    ·
      refine ⟨15137016117767650203544127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10091344078511766802362751 15137016117767650203544127)
      ·
        refine ⟨22705524176651475305316191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15137016117767650203544127 22705524176651475305316191)
        ·
          refine ⟨34058286264977212957974287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22705524176651475305316191 34058286264977212957974287)
          ·
            refine ⟨51087429397465819436961431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34058286264977212957974287 51087429397465819436961431)
            ·
              refine ⟨76631144096198729155442147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51087429397465819436961431 76631144096198729155442147)
              ·
                refine ⟨114946716144298093733163221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76631144096198729155442147 114946716144298093733163221)
                ·
                  refine ⟨2694063659631986571871013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 114946716144298093733163221 2694063659631986571871013)
                  ·
                    refine ⟨505136936180997482225815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2694063659631986571871013 505136936180997482225815)
                    ·
                      rfl

theorem cell23_2951252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_2951252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951252 prefixEnd_2951252 := by exact prefixLift 2951252
  have htrace : WordTrace (prefixWord ++ tailWord_2951252) baseStart_2951252 baseEnd_2951252 := by
    simpa [prefixWord, tailWord_2951252, baseEnd_2951252] using wordTrace_append hprefix tailTrace_2951252
  have hstable : (prefixWord ++ tailWord_2951252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951252).length < 2 ^ (prefixWord ++ tailWord_2951252).sum := by decide
  have hdescent : baseEnd_2951252 < baseStart_2951252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951255 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 6]
def baseStart_2951255 : Nat := 118140960795 + 2951255 * 2 ^ 59
def prefixEnd_2951255 : Nat := 4983230072969 + 3 ^ 40 * 2951255 * 2
def baseEnd_2951255 : Nat := 1515412348984955934939931

theorem tailTrace_2951255 : CollatzResearch.WordTrace tailWord_2951255 prefixEnd_2951255 1515412348984955934939931 := by
  unfold tailWord_2951255
  simp only [CollatzResearch.WordTrace]
  refine ⟨107641112923114644070895219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71760741948743096047263479 107641112923114644070895219)
  ·
    refine ⟨161461669384671966106342829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107641112923114644070895219 161461669384671966106342829)
    ·
      refine ⟨60548126019251987289878561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161461669384671966106342829 60548126019251987289878561)
      ·
        refine ⟨45411094514438990467408921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60548126019251987289878561 45411094514438990467408921)
        ·
          refine ⟨34058320885829242850556691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45411094514438990467408921 34058320885829242850556691)
          ·
            refine ⟨51087481328743864275835037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34058320885829242850556691 51087481328743864275835037)
            ·
              refine ⟨19157805498278949103438139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51087481328743864275835037 19157805498278949103438139)
              ·
                refine ⟨28736708247418423655157209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19157805498278949103438139 28736708247418423655157209)
                ·
                  refine ⟨21552531185563817741367907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28736708247418423655157209 21552531185563817741367907)
                  ·
                    refine ⟨32328796778345726612051861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21552531185563817741367907 32328796778345726612051861)
                    ·
                      refine ⟨1515412348984955934939931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32328796778345726612051861 1515412348984955934939931)
                      ·
                        rfl

theorem cell23_2951255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_2951255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951255 prefixEnd_2951255 := by exact prefixLift 2951255
  have htrace : WordTrace (prefixWord ++ tailWord_2951255) baseStart_2951255 baseEnd_2951255 := by
    simpa [prefixWord, tailWord_2951255, baseEnd_2951255] using wordTrace_append hprefix tailTrace_2951255
  have hstable : (prefixWord ++ tailWord_2951255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951255).length < 2 ^ (prefixWord ++ tailWord_2951255).sum := by decide
  have hdescent : baseEnd_2951255 < baseStart_2951255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951269 : List Nat := [1, 3, 1, 3, 2, 3, 2, 1, 3, 4]
def baseStart_2951269 : Nat := 118140960795 + 2951269 * 2 ^ 59
def prefixEnd_2951269 : Nat := 4983230072969 + 3 ^ 40 * 2951269 * 2
def baseEnd_2951269 : Nat := 505139845904706293388289

theorem tailTrace_2951269 : CollatzResearch.WordTrace tailWord_2951269 prefixEnd_2951269 505139845904706293388289 := by
  unfold tailWord_2951269
  simp only [CollatzResearch.WordTrace]
  refine ⟨107641623545063924461904861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71761082363375949641269907 107641623545063924461904861)
  ·
    refine ⟨40365608829398971673214323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107641623545063924461904861 40365608829398971673214323)
    ·
      refine ⟨60548413244098457509821485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40365608829398971673214323 60548413244098457509821485)
      ·
        refine ⟨22705654966536921566183057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60548413244098457509821485 22705654966536921566183057)
        ·
          refine ⟨17029241224902691174637293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22705654966536921566183057 17029241224902691174637293)
          ·
            refine ⟨6385965459338509190488985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17029241224902691174637293 6385965459338509190488985)
            ·
              refine ⟨4789474094503881892866739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6385965459338509190488985 4789474094503881892866739)
              ·
                refine ⟨7184211141755822839300109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4789474094503881892866739 7184211141755822839300109)
                ·
                  refine ⟨2694079178158433564737541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7184211141755822839300109 2694079178158433564737541)
                  ·
                    refine ⟨505139845904706293388289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2694079178158433564737541 505139845904706293388289)
                    ·
                      rfl

theorem cell23_2951269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 4].length) (baseStart_2951269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951269 prefixEnd_2951269 := by exact prefixLift 2951269
  have htrace : WordTrace (prefixWord ++ tailWord_2951269) baseStart_2951269 baseEnd_2951269 := by
    simpa [prefixWord, tailWord_2951269, baseEnd_2951269] using wordTrace_append hprefix tailTrace_2951269
  have hstable : (prefixWord ++ tailWord_2951269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951269).length < 2 ^ (prefixWord ++ tailWord_2951269).sum := by decide
  have hdescent : baseEnd_2951269 < baseStart_2951269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951312 : List Nat := [2, 1, 1, 1, 1, 1, 5, 5, 1, 5]
def baseStart_2951312 : Nat := 118140960795 + 2951312 * 2 ^ 59
def prefixEnd_2951312 : Nat := 4983230072969 + 3 ^ 40 * 2951312 * 2
def baseEnd_2951312 : Nat := 505147205794087403975723

theorem tailTrace_2951312 : CollatzResearch.WordTrace tailWord_2951312 prefixEnd_2951312 505147205794087403975723 := by
  unfold tailWord_2951312
  simp only [CollatzResearch.WordTrace]
  refine ⟨53821595941954071402860095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71762127922605428537146793 53821595941954071402860095)
  ·
    refine ⟨80732393912931107104290143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53821595941954071402860095 80732393912931107104290143)
    ·
      refine ⟨121098590869396660656435215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80732393912931107104290143 121098590869396660656435215)
      ·
        refine ⟨181647886304094990984652823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121098590869396660656435215 181647886304094990984652823)
        ·
          refine ⟨272471829456142486476979235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181647886304094990984652823 272471829456142486476979235)
          ·
            refine ⟨408707744184213729715468853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272471829456142486476979235 408707744184213729715468853)
            ·
              refine ⟨38316351017270037160825205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 408707744184213729715468853 38316351017270037160825205)
              ·
                refine ⟨3592157907869065983827363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38316351017270037160825205 3592157907869065983827363)
                ·
                  refine ⟨5388236861803598975741045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3592157907869065983827363 5388236861803598975741045)
                  ·
                    refine ⟨505147205794087403975723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5388236861803598975741045 505147205794087403975723)
                    ·
                      rfl

theorem cell23_2951312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 1, 5].length) (baseStart_2951312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951312 prefixEnd_2951312 := by exact prefixLift 2951312
  have htrace : WordTrace (prefixWord ++ tailWord_2951312) baseStart_2951312 baseEnd_2951312 := by
    simpa [prefixWord, tailWord_2951312, baseEnd_2951312] using wordTrace_append hprefix tailTrace_2951312
  have hstable : (prefixWord ++ tailWord_2951312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951312).length < 2 ^ (prefixWord ++ tailWord_2951312).sum := by decide
  have hdescent : baseEnd_2951312 < baseStart_2951312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2951355 : List Nat := [1, 1, 1, 1, 1, 2, 5, 11]
def baseStart_2951355 : Nat := 118140960795 + 2951355 * 2 ^ 59
def prefixEnd_2951355 : Nat := 4983230072969 + 3 ^ 40 * 2951355 * 2
def baseEnd_2951355 : Nat := 56128285075940946062573

theorem tailTrace_2951355 : CollatzResearch.WordTrace tailWord_2951355 prefixEnd_2951355 56128285075940946062573 := by
  unfold tailWord_2951355
  simp only [CollatzResearch.WordTrace]
  refine ⟨107644760222752361149535519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71763173481834907433023679 107644760222752361149535519)
  ·
    refine ⟨161467140334128541724303279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107644760222752361149535519 161467140334128541724303279)
    ·
      refine ⟨242200710501192812586454919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161467140334128541724303279 242200710501192812586454919)
      ·
        refine ⟨363301065751789218879682379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242200710501192812586454919 363301065751789218879682379)
        ·
          refine ⟨544951598627683828319523569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363301065751789218879682379 544951598627683828319523569)
          ·
            refine ⟨408713698970762871239642677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 544951598627683828319523569 408713698970762871239642677)
            ·
              refine ⟨38316909278509019178716501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 408713698970762871239642677 38316909278509019178716501)
              ·
                refine ⟨56128285075940946062573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 38316909278509019178716501 56128285075940946062573)
                ·
                  rfl

theorem cell23_2951355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 11].length) (baseStart_2951355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2951355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2951355 prefixEnd_2951355 := by exact prefixLift 2951355
  have htrace : WordTrace (prefixWord ++ tailWord_2951355) baseStart_2951355 baseEnd_2951355 := by
    simpa [prefixWord, tailWord_2951355, baseEnd_2951355] using wordTrace_append hprefix tailTrace_2951355
  have hstable : (prefixWord ++ tailWord_2951355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2951355).length < 2 ^ (prefixWord ++ tailWord_2951355).sum := by decide
  have hdescent : baseEnd_2951355 < baseStart_2951355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2951355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
